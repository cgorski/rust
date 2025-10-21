//! View specifications for partial borrows.
//!
//! This module defines view specifications, which specify which fields of a struct
//! are accessible through a reference. View types enable field-level borrowing,
//! allowing different fields of the same struct to be borrowed simultaneously.
//!
//! # Example
//!
//! ```rust,ignore
//! struct S {
//!     field_a: u32,
//!     field_b: String,
//! }
//!
//! // &{mut field_a} S - can mutably access field_a only
//! // &{field_b} S - can immutably access field_b only
//! // &{mut field_a, field_b} S - can mutably access field_a and immutably access field_b
//! ```
//!
//! # Formal Foundation
//!
//! The design and soundness of view specifications is formally verified.
//! See `formalization/Core_Proven.v` for machine-checked proofs that:
//! - Different fields never conflict
//! - Mutable access is exclusive per field
//! - Immutable access can be shared per field
//! - The conflict detection algorithm is correct

use rustc_data_structures::intern::Interned;
use rustc_hir::def_id::DefId;
use rustc_macros::HashStable;
use rustc_span::Symbol;
use rustc_type_ir::Mutability;

use crate::ty::TyCtxt;

/// A single field access in a view specification.
///
/// Represents access to a specific field path with a particular mutability.
/// For nested access like `outer.inner.value`, path = ["outer", "inner", "value"].
/// For simple access like `field`, path = ["field"].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[derive(HashStable)]
pub struct FieldAccess<'a> {
    /// The path to the field being accessed (e.g., ["outer", "inner", "value"]).
    /// Single-element slice for simple fields, multiple elements for nested access.
    /// Borrowed from HIR or arena-allocated.
    pub path: &'a [Symbol],
    /// Whether the access is mutable or immutable.
    pub mutability: Mutability,
}

impl<'a> FieldAccess<'a> {
    /// Create a new field access with a path (slice must be arena-allocated or static).
    pub fn new_path(path: &'a [Symbol], mutability: Mutability) -> Self {
        FieldAccess { path, mutability }
    }

    /// Create a new field access with a single field name (requires arena allocation).
    /// For tests, you can use a static slice.
    pub fn new(path: &'a [Symbol], mutability: Mutability) -> Self {
        FieldAccess { path, mutability }
    }

    /// Create a mutable field access (requires arena-allocated slice).
    pub fn mutable(path: &'a [Symbol]) -> Self {
        Self::new(path, Mutability::Mut)
    }

    /// Create an immutable field access (requires arena-allocated slice).
    pub fn immutable(path: &'a [Symbol]) -> Self {
        Self::new(path, Mutability::Not)
    }

    /// Get the first component of the path (for simple access).
    pub fn first_component(&self) -> Symbol {
        self.path[0]
    }

    /// Check if this is a simple (non-nested) field access.
    pub fn is_simple(&self) -> bool {
        self.path.len() == 1
    }

    /// Check if this field access is mutable.
    pub fn is_mutable(&self) -> bool {
        self.mutability == Mutability::Mut
    }

    /// Check if this field access conflicts with another.
    ///
    /// Two field accesses conflict if:
    /// - Their paths overlap (same path or prefix relationship), AND
    /// - At least one is mutable
    ///
    /// This is proven correct in `formalization/Core_Proven.v`:
    /// - Theorem: `different_fields_no_conflict` (single fields)
    /// - Theorem: `disjoint_paths_no_conflict` (nested paths)
    /// - Theorem: `prefix_paths_conflict_if_mut` (parent/child)
    pub fn conflicts_with(&self, other: &FieldAccess<'_>) -> bool {
        if self.paths_overlap(other) {
            // Paths overlap (same or prefix): conflict if any is mutable
            matches!(
                (self.mutability, other.mutability),
                (Mutability::Mut, _) | (_, Mutability::Mut)
            )
        } else {
            // Disjoint paths: never conflict (PROVEN in Core_Proven.v)
            false
        }
    }

    /// Check if this path overlaps with another (same or prefix relationship).
    fn paths_overlap(&self, other: &FieldAccess<'_>) -> bool {
        self.is_prefix_of(&other.path) || other.is_prefix_of(&self.path)
    }

    /// Check if this path is a prefix of another path.
    fn is_prefix_of(&self, other: &[Symbol]) -> bool {
        if self.path.len() > other.len() {
            return false;
        }
        self.path.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

/// View specification: a list of field accesses.
///
/// Represents which fields are accessible through a reference and with what mutability.
/// Empty view specifications are not allowed (rejected during parsing).
///
/// # Invariants
///
/// - All field paths are unique within a view spec
/// - All referenced fields must exist in the target struct
/// - These are validated during type checking
///
/// # Encoding/Serialization
///
/// ViewSpec is NOT serialized to the incremental compilation cache.
/// Instead, view specs are recomputed from HIR when needed.
/// This simplifies the implementation and avoids encoding complexity.
/// The performance impact is negligible since view specs are small and
/// only needed during type checking and borrow checking.
///
/// This is acceptable. Future versions may add caching if needed.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[derive(HashStable)]
pub struct ViewSpec<'tcx> {
    /// The list of field accesses in this view.
    /// Stored as an arena-allocated slice for efficient comparison.
    pub fields: &'tcx [FieldAccess<'tcx>],
}

impl<'tcx> ViewSpec<'tcx> {
    /// Create a new view specification.
    ///
    /// # Panics
    ///
    /// Panics if the field list is empty. Empty views are not allowed.
    pub fn new(tcx: TyCtxt<'tcx>, fields: &[FieldAccess<'tcx>]) -> Self {
        assert!(!fields.is_empty(), "view specification cannot be empty");
        ViewSpec { fields: tcx.arena.alloc_slice(fields) }
    }

    /// Create a view spec for a single field access.
    pub fn single(tcx: TyCtxt<'tcx>, field: FieldAccess<'tcx>) -> Self {
        ViewSpec { fields: tcx.arena.alloc_slice(&[field]) }
    }

    /// Create a view spec for a single mutable field (simple, non-nested).
    pub fn single_mut(tcx: TyCtxt<'tcx>, field_name: Symbol) -> Self {
        let path = tcx.arena.alloc_slice(&[field_name]);
        Self::single(tcx, FieldAccess::mutable(path))
    }

    /// Create a view spec for a single immutable field (simple, non-nested).
    pub fn single_imm(tcx: TyCtxt<'tcx>, field_name: Symbol) -> Self {
        let path = tcx.arena.alloc_slice(&[field_name]);
        Self::single(tcx, FieldAccess::immutable(path))
    }

    /// Get the field accesses in this view.
    pub fn field_accesses(&self) -> &[FieldAccess<'_>] {
        self.fields
    }

    /// Check if this view spec contains a specific field (first component match).
    pub fn contains_field(&self, field_name: Symbol) -> bool {
        self.fields.iter().any(|fa| fa.path[0] == field_name)
    }

    /// Check if this view spec grants mutable access to a specific field (first component).
    pub fn grants_mutable_access(&self, field_name: Symbol) -> bool {
        self.fields.iter().any(|fa| fa.path[0] == field_name && fa.mutability == Mutability::Mut)
    }

    /// Check if this view spec grants any mutable access.
    pub fn has_any_mutable_access(&self) -> bool {
        self.fields.iter().any(|fa| fa.mutability == Mutability::Mut)
    }

    /// Check if this view spec conflicts with another.
    ///
    /// Two view specs conflict if they have any field access that conflicts.
    ///
    /// Proven correct in `formalization/Core_Proven.v`:
    /// - Theorem: `disjoint_fields_no_conflict`
    /// - Theorem: `simultaneous_disjoint_field_borrow_safety`
    pub fn conflicts_with(&self, other: &ViewSpec<'tcx>) -> bool {
        self.fields.iter().any(|fa1| other.fields.iter().any(|fa2| fa1.conflicts_with(fa2)))
    }

    /// Check if this view spec is a subview of another.
    ///
    /// `v1` is a subview of `v2` if every field in `v1` is present in `v2`
    /// with equal or weaker permissions:
    /// - Immutable access in v1 can match immutable or mutable in v2
    /// - Mutable access in v1 requires mutable in v2
    ///
    /// This implements the subview relation proven in `formalization/BasicProofs_Clean.v`.
    pub fn is_subview_of(&self, other: &ViewSpec<'tcx>) -> bool {
        self.fields.iter().all(|fa1| {
            other.fields.iter().any(|fa2| {
                // Same field path
                fa1.path == fa2.path &&
                // Compatible mutability
                match (fa1.mutability, fa2.mutability) {
                    // Immutable can match anything
                    (Mutability::Not, _) => true,
                    // Mutable requires mutable
                    (Mutability::Mut, Mutability::Mut) => true,
                    // Mutable cannot match immutable
                    (Mutability::Mut, Mutability::Not) => false,
                }
            })
        })
    }

    /// Check if this view spec has duplicate field names.
    ///
    /// This should be rejected during parsing/validation, but we check here for safety.
    pub fn has_duplicates(&self) -> bool {
        for (i, fa1) in self.fields.iter().enumerate() {
            for fa2 in self.fields.iter().skip(i + 1) {
                if fa1.path == fa2.path {
                    return true;
                }
            }
        }
        false
    }

    /// Validate this view spec against a struct definition.
    ///
    /// Checks that:
    /// - All field names exist in the struct
    /// - No duplicate fields in the view
    ///
    /// Privacy checking is done separately during type checking.
    pub fn validate_for_struct(
        &self,
        tcx: TyCtxt<'tcx>,
        struct_def_id: DefId,
    ) -> Result<(), Symbol> {
        // Check for duplicates
        if self.has_duplicates() {
            // Return the first component of first duplicate path (for error reporting)
            for (i, fa1) in self.fields.iter().enumerate() {
                for fa2 in self.fields.iter().skip(i + 1) {
                    if fa1.path == fa2.path {
                        return Err(fa1.path[0]);
                    }
                }
            }
        }

        // Check that all fields exist in the struct
        let adt = tcx.adt_def(struct_def_id);
        let variant = adt.non_enum_variant(); // For structs, there's only one variant

        for fa in self.fields.iter() {
            // Currently, validate only the first component of the path
            // TODO: Full nested validation should check all path components exist
            let field_exists = variant.fields.iter().any(|f| f.name == fa.path[0]);
            if !field_exists {
                return Err(fa.path[0]);
            }
        }

        Ok(())
    }
}

impl<'tcx> std::fmt::Debug for ViewSpec<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (i, fa) in self.fields.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            if fa.mutability == Mutability::Mut {
                write!(f, "mut ")?;
            }
            // Print path components with dots
            for (j, component) in fa.path.iter().enumerate() {
                if j > 0 {
                    write!(f, ".")?;
                }
                write!(f, "{}", component)?;
            }
        }
        write!(f, "}}")
    }
}

impl<'tcx> std::fmt::Display for ViewSpec<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

/// Type alias for interned view specs (future optimization).
pub type InternedViewSpec<'tcx> = Interned<'tcx, ViewSpec<'tcx>>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_field_access_conflicts() {
        use rustc_span::Symbol;
        let field_a = Symbol::intern("a");
        let field_b = Symbol::intern("b");

        // Static slices for testing (leaked but only in tests)
        let path_a: &'static [Symbol] = Box::leak(vec![field_a].into_boxed_slice());
        let path_b: &'static [Symbol] = Box::leak(vec![field_b].into_boxed_slice());

        // Same field, both mutable - conflicts
        let fa1 = FieldAccess::mutable(path_a);
        let fa2 = FieldAccess::mutable(path_a);
        assert!(fa1.conflicts_with(&fa2));

        // Same field, one mutable - conflicts
        let fa3 = FieldAccess::mutable(path_a);
        let fa4 = FieldAccess::immutable(path_a);
        assert!(fa3.conflicts_with(&fa4));
        assert!(fa4.conflicts_with(&fa3)); // Symmetric

        // Same field, both immutable - no conflict
        let fa5 = FieldAccess::immutable(path_a);
        let fa6 = FieldAccess::immutable(path_a);
        assert!(!fa5.conflicts_with(&fa6));

        // Different fields - never conflict (THE KEY PROPERTY!)
        let fa7 = FieldAccess::mutable(path_a);
        let fa8 = FieldAccess::mutable(path_b);
        assert!(!fa7.conflicts_with(&fa8));
    }

    #[test]
    fn test_nested_path_conflicts() {
        use rustc_span::Symbol;

        // Nested paths for testing
        let transform = Symbol::intern("transform");
        let position = Symbol::intern("position");
        let rotation = Symbol::intern("rotation");
        let value = Symbol::intern("value");

        let path_transform_position: &'static [Symbol] =
            Box::leak(vec![transform, position].into_boxed_slice());
        let path_transform_rotation: &'static [Symbol] =
            Box::leak(vec![transform, rotation].into_boxed_slice());
        let path_transform: &'static [Symbol] = Box::leak(vec![transform].into_boxed_slice());
        let path_transform_position_value: &'static [Symbol] =
            Box::leak(vec![transform, position, value].into_boxed_slice());

        // Disjoint nested paths - no conflict
        let fa1 = FieldAccess::mutable(path_transform_position);
        let fa2 = FieldAccess::mutable(path_transform_rotation);
        assert!(
            !fa1.conflicts_with(&fa2),
            "transform.position vs transform.rotation should not conflict"
        );

        // Parent-child relationship - conflicts
        let parent = FieldAccess::mutable(path_transform);
        let child = FieldAccess::mutable(path_transform_position);
        assert!(parent.conflicts_with(&child), "transform vs transform.position should conflict");
        assert!(child.conflicts_with(&parent), "conflict should be symmetric");

        // Prefix chain - conflicts
        let fa3 = FieldAccess::mutable(path_transform_position);
        let fa4 = FieldAccess::mutable(path_transform_position_value);
        assert!(
            fa3.conflicts_with(&fa4),
            "transform.position vs transform.position.value should conflict"
        );
    }

    // Note: Full ViewSpec tests require TyCtxt which is not available in unit tests.
    // Integration tests in tests/ui/view-types/ cover the full functionality.
}
