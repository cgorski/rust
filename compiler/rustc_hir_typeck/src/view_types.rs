//! Validation for view types annotations.
//!
//! View types allow specifying which fields of a struct a function can access:
//!
//! ```text
//! struct S {
//!     field_a: i32,
//!     field_b: String,
//! }
//!
//! impl S {
//!     fn foo(&{mut field_a} mut self) {
//!         self.field_a = 42; // OK - field_a is in the view
//!         // self.field_b = String::new(); // ERROR - field_b not in view
//!     }
//! }
//! ```
//!
//! This module validates that function bodies respect their view type annotations.

use rustc_data_structures::fx::FxHashSet;
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use rustc_span::symbol::Symbol;

/// Information about a parameter with a view type annotation.
#[derive(Debug)]
struct ViewTypeParam {
    /// Parameter HirId (for matching against expressions)
    param_hir_id: hir::HirId,
    /// Name of the parameter (e.g., "self")
    param_name: Symbol,
    /// Fields that are allowed to be accessed
    allowed_fields: FxHashSet<Symbol>,
    /// Span of the view type annotation
    annotation_span: Span,
}

/// Validates that a function body respects view type annotations on its parameters.
pub(crate) fn check_view_types(tcx: TyCtxt<'_>, def_id: LocalDefId) {
    let hir_id = tcx.local_def_id_to_hir_id(def_id);
    let node = tcx.hir_node(hir_id);

    // RESTRICTION: Check if view types are allowed for this function type
    // Reject trait methods and free functions early to prevent ICEs and provide clear errors
    match node {
        // Case 1: Trait method definitions (required methods without body)
        hir::Node::TraitItem(hir::TraitItem {
            kind: hir::TraitItemKind::Fn(_, hir::TraitFn::Required(_)),
            ..
        }) => {
            if has_view_type_params(node) {
                emit_trait_method_error(tcx, node, true);
                return;
            }
        }

        // Case 2: Trait method definitions (provided/default methods with body)
        hir::Node::TraitItem(hir::TraitItem {
            kind: hir::TraitItemKind::Fn(_, hir::TraitFn::Provided(_)),
            ..
        }) => {
            if has_view_type_params(node) {
                emit_trait_method_error(tcx, node, true);
                return;
            }
        }

        // Case 3: Methods in impl blocks (check if it's a trait impl)
        hir::Node::ImplItem(hir::ImplItem { kind: hir::ImplItemKind::Fn(_, _), .. }) => {
            // Check if parent is a trait impl
            let parent_id = tcx.parent_hir_id(hir_id);
            if let hir::Node::Item(hir::Item { kind: hir::ItemKind::Impl(impl_), .. }) =
                tcx.hir_node(parent_id)
            {
                if impl_.of_trait.is_some() && has_view_type_params(node) {
                    emit_trait_method_error(tcx, node, false);
                    return;
                }
            }
            // Otherwise, it's an inherent impl method - allowed, continue validation
        }

        // Case 4: Free functions (not in an impl block)
        hir::Node::Item(hir::Item { kind: hir::ItemKind::Fn { .. }, .. }) => {
            if has_view_type_params(node) {
                emit_free_function_error(tcx, node);
                return;
            }
        }

        _ => {
            // Other node types - continue with normal validation
        }
    }

    let body_id = match node {
        hir::Node::Item(hir::Item { kind: hir::ItemKind::Fn { body, .. }, .. }) => body,
        hir::Node::ImplItem(hir::ImplItem { kind: hir::ImplItemKind::Fn(_, body_id), .. }) => {
            body_id
        }
        hir::Node::TraitItem(hir::TraitItem {
            kind: hir::TraitItemKind::Fn(_, hir::TraitFn::Provided(body_id)),
            ..
        }) => body_id,
        _ => return, // Not a function with a body
    };

    let body = tcx.hir_body(*body_id);

    // Get function signature
    let fn_sig = match node.fn_sig() {
        Some(sig) => sig,
        None => return,
    };

    // Extract view type annotations from parameters
    let view_params = extract_view_params(tcx, fn_sig, body);

    if view_params.is_empty() {
        return; // No view types to validate
    }

    // RESTRICTION: View types only allowed on pub(crate) or less visible functions
    // This matches the paper's recommendation to avoid semver/encapsulation issues
    let visibility = tcx.visibility(def_id);
    if matches!(visibility, rustc_middle::ty::Visibility::Public) {
        let span = view_params[0].annotation_span; // Use first view annotation's span
        tcx.dcx()
            .struct_span_err(span, "view types are not allowed on public functions")
            .with_note("view types are limited to `pub(crate)` or private functions")
            .with_note("this restriction avoids semver coupling and encapsulation issues")
            .with_help("change `pub fn` to `pub(crate) fn`, or remove the view type annotation")
            .emit();
        return; // Don't validate further if visibility is wrong
    }

    // RESTRICTION: View-typed methods cannot return references
    // This prevents a soundness bug where returned references can create aliasing
    // See formalization/Lifetimes_Returns.v for formal proof and Option 3 roadmap
    if returns_reference_type(fn_sig) {
        let span = view_params[0].annotation_span; // Use first view annotation's span
        tcx.dcx()
            .struct_span_err(span, "view-typed functions cannot return references")
            .with_note("returning references from view-typed methods can cause soundness issues")
            .with_note(
                "this restriction may be lifted in a future version with proper region inference integration",
            )
            .with_help("consider returning an owned value or restructuring the code")

            .emit();
        return;
    }

    // Validate the function body
    let mut visitor = ViewTypeValidator { tcx, view_params };
    visitor.visit_body(body);
}

/// Check if the function returns a reference type.
/// Used for restriction on view-typed methods.
fn returns_reference_type(fn_sig: &hir::FnSig<'_>) -> bool {
    match &fn_sig.decl.output {
        hir::FnRetTy::DefaultReturn(_) => false,
        hir::FnRetTy::Return(ty) => is_reference_type(ty),
    }
}

/// Recursively check if a type is or contains a reference.
fn is_reference_type(ty: &hir::Ty<'_>) -> bool {
    match &ty.kind {
        hir::TyKind::Ref(_, _, _) => true,
        hir::TyKind::Tup(types) => types.iter().any(is_reference_type),
        _ => false,
    }
}

/// Check if two field paths overlap (one is a prefix of the other).
/// Returns true if paths are duplicates or if one is a parent of the other.
fn paths_overlap(path1: &[Symbol], path2: &[Symbol]) -> bool {
    if path1.len() == path2.len() {
        return path1 == path2; // Exact duplicate
    }

    let (shorter, longer) = if path1.len() < path2.len() { (path1, path2) } else { (path2, path1) };

    // Check if shorter is a prefix of longer
    longer.starts_with(shorter)
}

/// Extract view type annotations from function parameters.
fn extract_view_params(
    tcx: TyCtxt<'_>,
    fn_sig: &hir::FnSig<'_>,
    body: &hir::Body<'_>,
) -> Vec<ViewTypeParam> {
    let mut view_params = Vec::new();

    for (param, param_ty) in body.params.iter().zip(fn_sig.decl.inputs.iter()) {
        if let hir::TyKind::Ref(_, _, Some(view_spec)) = &param_ty.kind {
            let (param_name, param_hir_id) = match param.pat.kind {
                hir::PatKind::Binding(_, hir_id, ident, _) => (ident.name, hir_id),
                _ => continue, // Complex pattern, skip for now
            };

            // Validate: check for overlapping paths in the view spec
            for (i, field1) in view_spec.fields.iter().enumerate() {
                for field2 in view_spec.fields.iter().skip(i + 1) {
                    if paths_overlap(&field1.path, &field2.path) {
                        let path1_str =
                            field1.path.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(".");
                        let path2_str =
                            field2.path.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(".");

                        tcx.dcx()
                            .struct_span_err(
                                param_ty.span,
                                format!("overlapping paths in view specification: `{}` and `{}`", path1_str, path2_str)
                            )
                            .with_note("a parent path and its child path cannot both be specified in the same view")
                            .with_help("remove one of the overlapping paths")
                            .emit();
                    }
                }
            }

            // Extract the first component of each path for validation
            // Note: Nested path access is validated by the borrow checker
            let allowed_fields: FxHashSet<Symbol> =
                view_spec.fields.iter().map(|field| field.path[0]).collect();

            view_params.push(ViewTypeParam {
                param_hir_id,
                param_name,
                allowed_fields,
                annotation_span: param_ty.span,
            });
        }
    }

    view_params
}

/// HIR visitor that validates field accesses respect view type annotations.
struct ViewTypeValidator<'tcx> {
    tcx: TyCtxt<'tcx>,
    view_params: Vec<ViewTypeParam>,
}

impl<'tcx> ViewTypeValidator<'tcx> {
    /// Check if an expression is a reference to a view-typed parameter.
    fn is_view_param(&self, expr: &hir::Expr<'tcx>) -> Option<&ViewTypeParam> {
        match expr.kind {
            hir::ExprKind::Path(hir::QPath::Resolved(None, path)) => {
                if let hir::def::Res::Local(local_hir_id) = path.res {
                    return self.view_params.iter().find(|vp| vp.param_hir_id == local_hir_id);
                }
            }
            _ => {}
        }
        None
    }
}

impl<'tcx> Visitor<'tcx> for ViewTypeValidator<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        // Check field accesses
        if let hir::ExprKind::Field(base, field) = expr.kind {
            if let Some(view_param) = self.is_view_param(base) {
                // Check first-level field access; nested paths are validated by borrow checker
                if !view_param.allowed_fields.contains(&field.name) {
                    // SAFETY: We immediately sort the collected values, so the iteration
                    // order of the FxHashSet doesn't affect the final result
                    #[allow(rustc::potential_query_instability)]
                    let mut allowed_syms: Vec<Symbol> =
                        view_param.allowed_fields.iter().copied().collect();
                    allowed_syms.sort();
                    let allowed: Vec<String> =
                        allowed_syms.iter().map(|f| format!("`{}`", f)).collect();

                    self.tcx
                        .dcx()
                        .struct_span_err(
                            expr.span,
                            format!(
                                "cannot access field `{}` through view-typed parameter `{}`",
                                field.name, view_param.param_name
                            ),
                        )
                        .with_span_note(
                            view_param.annotation_span,
                            format!("view type only allows access to: {}", allowed.join(", ")),
                        )
                        .emit();
                }
            }
        }

        // Note: Method calls on view-typed parameters
        // View composition (view-typed functions calling other view-typed functions) is handled
        // by delegating validation to the borrow checker rather than HIR validation.
        // if let hir::ExprKind::MethodCall(_, receiver, _, _) = expr.kind {
        // Method calls on view-typed parameters are allowed.
        // The borrow checker handles validation at the proper layer:
        // - If the called method has a view type, its field borrows are tracked
        // - If the called method has no view type, it borrows all of self
        // - Conflicts are detected by the borrow checker's existing conflict detection
        //
        // This delegation is correct because:
        // 1. View types specify what CAN be borrowed, not what operations are allowed
        // 2. The borrow checker validates actual borrowing conflicts
        // 3. A view-typed function calling another view-typed function is safe
        //    if their views are disjoint (proven in Core_Proven.v)
        //
        // No additional validation needed here.

        intravisit::walk_expr(self, expr);
    }
}

/// Check if a function has any view type parameters.
/// Used to detect view types on unsupported function types (traits, free functions).
fn has_view_type_params(node: hir::Node<'_>) -> bool {
    let fn_sig = match node.fn_sig() {
        Some(sig) => sig,
        None => return false,
    };

    fn_sig
        .decl
        .inputs
        .iter()
        .any(|param_ty| matches!(param_ty.kind, hir::TyKind::Ref(_, _, Some(_))))
}

/// Emit error for trait method with view type.
/// is_definition: true for trait definitions, false for trait impls.
fn emit_trait_method_error(tcx: TyCtxt<'_>, node: hir::Node<'_>, is_definition: bool) {
    let fn_sig = node.fn_sig().unwrap();

    // Find the first view type parameter for span
    let span = fn_sig
        .decl
        .inputs
        .iter()
        .find_map(|param_ty| {
            if matches!(param_ty.kind, hir::TyKind::Ref(_, _, Some(_))) {
                Some(param_ty.span)
            } else {
                None
            }
        })
        .unwrap();

    let context =
        if is_definition { "trait method definitions" } else { "trait method implementations" };

    tcx.dcx()
        .struct_span_err(span, format!("view types are not supported on {}", context))
        .with_note("view types are restricted to inherent methods")
        .with_note("trait method support requires trait system integration")
        .with_help("consider using regular references without view type annotations")
        .emit();
}

/// Emit error for free function with view type.
fn emit_free_function_error(tcx: TyCtxt<'_>, node: hir::Node<'_>) {
    let fn_sig = node.fn_sig().unwrap();

    // Find the first view type parameter for span
    let span = fn_sig
        .decl
        .inputs
        .iter()
        .find_map(|param_ty| {
            if matches!(param_ty.kind, hir::TyKind::Ref(_, _, Some(_))) {
                Some(param_ty.span)
            } else {
                None
            }
        })
        .unwrap();

    tcx.dcx()
        .struct_span_err(span, "view types are not supported on free functions")
        .with_note("view types are restricted to inherent methods (methods in impl blocks)")
        .with_note("free function support requires additional infrastructure")
        .with_help("consider moving this function into an impl block as a method")
        .with_help("or use regular references without view type annotations")
        .emit();
}
