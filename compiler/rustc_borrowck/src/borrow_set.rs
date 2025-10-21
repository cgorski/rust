use std::fmt;
use std::ops::{Index, IndexMut};

use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::visit::{MutatingUseContext, NonUseContext, PlaceContext, Visitor};
use rustc_middle::mir::{self, Body, Local, Location, traversal};
use rustc_middle::span_bug;
use rustc_middle::ty::{self, RegionVid, Ty, TyCtxt};
use rustc_mir_dataflow::move_paths::MoveData;
use rustc_span::Symbol;
use tracing::debug;

use crate::BorrowIndex;
use crate::place_ext::PlaceExt;

/// OPTION 3: Tracks information about view-typed calls that return references.
/// This allows us to extend field borrows through the return value's lifetime.
#[derive(Debug, Clone)]
#[allow(dead_code)] // TODO: Will be used when Option 3 implementation is complete
pub(crate) struct ViewTypedCallInfo<'tcx> {
    /// The local that receives the return value
    pub destination: mir::Local,
    /// The fields from the view spec that are borrowed
    pub fields: Vec<Symbol>,
    /// The place that was borrowed (e.g., the self argument)
    pub borrowed_place: mir::Place<'tcx>,
    /// Location of the call
    pub call_location: Location,
}

pub struct BorrowSet<'tcx> {
    /// The fundamental map relating bitvector indexes to the borrows
    /// in the MIR. Each borrow is also uniquely identified in the MIR
    /// by the `Location` of the assignment statement in which it
    /// appears on the right hand side. Thus the location is the map
    /// key, and its position in the map corresponds to `BorrowIndex`.
    /// NOTE: Changed to Vec<BorrowData> to support multiple borrows per location.
    /// This is needed for multi-field view types where each field creates a separate borrow.
    pub(crate) location_map: FxIndexMap<Location, Vec<BorrowData<'tcx>>>,

    /// Locations which activate borrows.
    /// NOTE: a given location may activate more than one borrow in the future
    /// when more general two-phase borrow support is introduced, but for now we
    /// only need to store one borrow index.
    pub(crate) activation_map: FxIndexMap<Location, Vec<BorrowIndex>>,

    /// Map from local to all the borrows on that local.
    pub(crate) local_map: FxIndexMap<mir::Local, FxIndexSet<BorrowIndex>>,

    pub(crate) locals_state_at_exit: LocalsStateAtExit,

    /// OPTION 3: Track view-typed calls that return references.
    /// Maps from destination local to call information.
    #[allow(dead_code)] // TODO: Will be used when Option 3 implementation is complete
    pub(crate) view_typed_call_returns: FxIndexMap<mir::Local, ViewTypedCallInfo<'tcx>>,
}

// These methods are public to support borrowck consumers.
impl<'tcx> BorrowSet<'tcx> {
    pub fn location_map(&self) -> &FxIndexMap<Location, Vec<BorrowData<'tcx>>> {
        &self.location_map
    }

    pub fn activation_map(&self) -> &FxIndexMap<Location, Vec<BorrowIndex>> {
        &self.activation_map
    }

    pub fn local_map(&self) -> &FxIndexMap<mir::Local, FxIndexSet<BorrowIndex>> {
        &self.local_map
    }

    pub fn locals_state_at_exit(&self) -> &LocalsStateAtExit {
        &self.locals_state_at_exit
    }
}

impl<'tcx> Index<BorrowIndex> for BorrowSet<'tcx> {
    type Output = BorrowData<'tcx>;

    fn index(&self, index: BorrowIndex) -> &BorrowData<'tcx> {
        // Flatten the Vec<BorrowData> to get the borrow by absolute index
        let mut count = 0;
        for borrows in self.location_map.values() {
            if count + borrows.len() > index.as_usize() {
                return &borrows[index.as_usize() - count];
            }
            count += borrows.len();
        }
        panic!("BorrowIndex out of range: {:?}", index)
    }
}

impl<'tcx> IndexMut<BorrowIndex> for BorrowSet<'tcx> {
    fn index_mut(&mut self, index: BorrowIndex) -> &mut BorrowData<'tcx> {
        // Flatten the Vec<BorrowData> to get the borrow by absolute index (mutable)
        let mut count = 0;
        for borrows in self.location_map.values_mut() {
            if count + borrows.len() > index.as_usize() {
                return &mut borrows[index.as_usize() - count];
            }
            count += borrows.len();
        }
        panic!("BorrowIndex out of range: {:?}", index)
    }
}

/// Location where a two-phase borrow is activated, if a borrow
/// is in fact a two-phase borrow.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum TwoPhaseActivation {
    NotTwoPhase,
    NotActivated,
    ActivatedAt(Location),
}

#[derive(Debug, Clone)]
pub struct BorrowData<'tcx> {
    /// Location where the borrow reservation starts.
    /// In many cases, this will be equal to the activation location but not always.
    pub(crate) reserve_location: Location,
    /// Location where the borrow is activated.
    pub(crate) activation_location: TwoPhaseActivation,
    /// What kind of borrow this is
    pub(crate) kind: mir::BorrowKind,
    /// The region for which this borrow is live
    pub(crate) region: RegionVid,
    /// Place from which we are borrowing
    pub(crate) borrowed_place: mir::Place<'tcx>,
    /// Place to which the borrow was stored
    pub(crate) assigned_place: mir::Place<'tcx>,
    /// View specification if this is a view-typed borrow
    pub(crate) view_spec: Option<ty::ViewSpec<'tcx>>,
}

// These methods are public to support borrowck consumers.
impl<'tcx> BorrowData<'tcx> {
    pub fn reserve_location(&self) -> Location {
        self.reserve_location
    }

    pub fn activation_location(&self) -> TwoPhaseActivation {
        self.activation_location
    }

    pub fn kind(&self) -> mir::BorrowKind {
        self.kind
    }

    pub fn region(&self) -> RegionVid {
        self.region
    }

    pub fn borrowed_place(&self) -> mir::Place<'tcx> {
        self.borrowed_place
    }

    pub fn assigned_place(&self) -> mir::Place<'tcx> {
        self.assigned_place
    }
}

impl<'tcx> fmt::Display for BorrowData<'tcx> {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        let kind = match self.kind {
            mir::BorrowKind::Shared => "",
            mir::BorrowKind::Fake(mir::FakeBorrowKind::Deep) => "fake ",
            mir::BorrowKind::Fake(mir::FakeBorrowKind::Shallow) => "fake shallow ",
            mir::BorrowKind::Mut { kind: mir::MutBorrowKind::ClosureCapture } => "uniq ",
            // FIXME: differentiate `TwoPhaseBorrow`
            mir::BorrowKind::Mut {
                kind: mir::MutBorrowKind::Default | mir::MutBorrowKind::TwoPhaseBorrow,
            } => "mut ",
        };
        write!(w, "&{:?} {}{:?}", self.region, kind, self.borrowed_place)
    }
}

pub enum LocalsStateAtExit {
    AllAreInvalidated,
    SomeAreInvalidated { has_storage_dead_or_moved: DenseBitSet<Local> },
}

impl LocalsStateAtExit {
    fn build<'tcx>(
        locals_are_invalidated_at_exit: bool,
        body: &Body<'tcx>,
        move_data: &MoveData<'tcx>,
    ) -> Self {
        struct HasStorageDead(DenseBitSet<Local>);

        impl<'tcx> Visitor<'tcx> for HasStorageDead {
            fn visit_local(&mut self, local: Local, ctx: PlaceContext, _: Location) {
                if ctx == PlaceContext::NonUse(NonUseContext::StorageDead) {
                    self.0.insert(local);
                }
            }
        }

        if locals_are_invalidated_at_exit {
            LocalsStateAtExit::AllAreInvalidated
        } else {
            let mut has_storage_dead =
                HasStorageDead(DenseBitSet::new_empty(body.local_decls.len()));
            has_storage_dead.visit_body(body);
            let mut has_storage_dead_or_moved = has_storage_dead.0;
            for move_out in &move_data.moves {
                has_storage_dead_or_moved.insert(move_data.base_local(move_out.path));
            }
            LocalsStateAtExit::SomeAreInvalidated { has_storage_dead_or_moved }
        }
    }
}

impl<'tcx> BorrowSet<'tcx> {
    pub fn build(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        locals_are_invalidated_at_exit: bool,
        move_data: &MoveData<'tcx>,
    ) -> Self {
        let mut visitor = GatherBorrows {
            tcx,
            body,
            location_map: Default::default(),
            activation_map: Default::default(),
            local_map: Default::default(),
            pending_activations: Default::default(),
            locals_state_at_exit: LocalsStateAtExit::build(
                locals_are_invalidated_at_exit,
                body,
                move_data,
            ),
            view_typed_call_returns: Default::default(),
        };

        for (block, block_data) in traversal::preorder(body) {
            visitor.visit_basic_block_data(block, block_data);
        }

        BorrowSet {
            location_map: visitor.location_map,
            activation_map: visitor.activation_map,
            local_map: visitor.local_map,
            locals_state_at_exit: visitor.locals_state_at_exit,
            view_typed_call_returns: visitor.view_typed_call_returns,
        }
    }

    pub(crate) fn activations_at_location(&self, location: Location) -> &[BorrowIndex] {
        self.activation_map.get(&location).map_or(&[], |activations| &activations[..])
    }

    pub(crate) fn len(&self) -> usize {
        // Sum of all borrows across all locations
        self.location_map.values().map(|v| v.len()).sum()
    }

    pub(crate) fn iter_enumerated(&self) -> impl Iterator<Item = (BorrowIndex, &BorrowData<'tcx>)> {
        // Flatten the Vec<BorrowData> and enumerate with cumulative indices
        let mut result = Vec::new();
        let mut idx = 0;
        for borrows in self.location_map.values() {
            for borrow in borrows {
                result.push((BorrowIndex::from_usize(idx), borrow));
                idx += 1;
            }
        }
        result.into_iter()
    }

    pub(crate) fn get_index_of(&self, location: &Location) -> Option<BorrowIndex> {
        // Calculate the cumulative index up to this location
        let mut count = 0;
        for (loc, borrows) in &self.location_map {
            if loc == location {
                // Return the index of the first borrow at this location
                return if borrows.is_empty() {
                    None
                } else {
                    Some(BorrowIndex::from_usize(count))
                };
            }
            count += borrows.len();
        }
        None
    }
}

struct GatherBorrows<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    location_map: FxIndexMap<Location, Vec<BorrowData<'tcx>>>,
    activation_map: FxIndexMap<Location, Vec<BorrowIndex>>,
    local_map: FxIndexMap<mir::Local, FxIndexSet<BorrowIndex>>,

    /// When we encounter a 2-phase borrow statement, it will always
    /// be assigning into a temporary TEMP:
    ///
    ///    TEMP = &foo
    ///
    /// We add TEMP into this map with `b`, where `b` is the index of
    /// the borrow. When we find a later use of this activation, we
    /// remove from the map (and add to the "tombstone" set below).
    pending_activations: FxIndexMap<mir::Local, BorrowIndex>,

    locals_state_at_exit: LocalsStateAtExit,

    /// OPTION 3: Track view-typed calls that return references
    view_typed_call_returns: FxIndexMap<mir::Local, ViewTypedCallInfo<'tcx>>,
}

impl<'a, 'tcx> Visitor<'tcx> for GatherBorrows<'a, 'tcx> {
    fn visit_assign(
        &mut self,
        assigned_place: &mir::Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
        location: mir::Location,
    ) {
        if let &mir::Rvalue::Ref(region, kind, borrowed_place) = rvalue {
            if borrowed_place.ignore_borrow(self.tcx, self.body, &self.locals_state_at_exit) {
                debug!("ignoring_borrow of {:?}", borrowed_place);
                return;
            }

            let region = region.as_var();

            // Check if this borrow is for a view-typed call
            // If so, record borrow of whole struct with view spec attached
            if let Some((callee_def_id, param_idx)) =
                self.find_view_typed_call_use(*assigned_place, location)
            {
                if let Some(hir_view_spec) = self.get_view_spec(callee_def_id, param_idx) {
                    // Convert HIR view spec to ty view spec for conflict detection
                    let ty_view_spec = self.convert_view_spec(hir_view_spec);

                    let place_ty = borrowed_place.ty(&self.body.local_decls, self.tcx).ty;

                    // STEP 1: Pre-compute all field places (only immutable borrows of self)
                    // This avoids borrow checker conflicts when we mutably borrow location_map later
                    let mut field_places = Vec::new();
                    for hir_field in hir_view_spec.fields.iter() {
                        // Build nested field place (handles both simple and nested paths)
                        if let Some(field_place) =
                            self.build_nested_field_place(borrowed_place, &hir_field.path, place_ty)
                        {
                            field_places.push(field_place);
                        } else {
                            // Path invalid - this should be rare since typeck validates the first component.
                            // If this happens, it likely means a nested component doesn't exist.
                            // Fall back to normal borrow to avoid ICE.
                            debug!(
                                "Failed to build nested field place for view spec - falling back to normal borrow"
                            );
                            self.super_assign(assigned_place, rvalue, location);
                            return;
                        }
                    }

                    // STEP 2: Now calculate starting index and get mutable borrow
                    let starting_idx = BorrowIndex::from_usize(
                        self.location_map.values().map(|v| v.len()).sum::<usize>(),
                    );

                    let borrows_at_location =
                        self.location_map.entry(location).or_insert_with(Vec::new);

                    // STEP 3: Create and insert BorrowData for each field
                    for (field_idx, field_place) in field_places.iter().enumerate() {
                        let borrow = BorrowData {
                            kind,
                            region,
                            reserve_location: location,
                            activation_location: TwoPhaseActivation::NotTwoPhase,
                            borrowed_place: *field_place,
                            assigned_place: *assigned_place,
                            view_spec: Some(ty_view_spec), // Attach FULL view spec to each
                        };

                        let idx = BorrowIndex::from_usize(starting_idx.as_usize() + field_idx);

                        borrows_at_location.push(borrow);
                        self.local_map.entry(field_place.local).or_default().insert(idx);
                    }

                    // Call insert_as_pending_if_two_phase ONCE with the first borrow index
                    if !field_places.is_empty() {
                        self.insert_as_pending_if_two_phase(
                            location,
                            assigned_place,
                            kind,
                            starting_idx,
                        );
                    }

                    // DEBUG: Verify we recorded the correct number of borrows
                    debug!(
                        "VIEW_TYPES: Recorded {} field borrows at location {:?} for view spec with {} fields",
                        field_places.len(),
                        location,
                        hir_view_spec.fields.len()
                    );

                    // Verify borrows were actually added to location_map
                    let recorded_count =
                        self.location_map.get(&location).map(|v| v.len()).unwrap_or(0);
                    assert_eq!(
                        recorded_count,
                        field_places.len(),
                        "VIEW_TYPES: Mismatch in recorded borrows! Expected {} (field count), got {} at {:?}",
                        field_places.len(),
                        recorded_count,
                        location
                    );

                    // OPTION 3: Check if this call returns a reference
                    // If so, we need to track it for lifetime extension
                    if let Some(call_info) = self.check_view_typed_call_returns_ref(
                        callee_def_id,
                        borrowed_place,
                        location,
                        hir_view_spec,
                    ) {
                        debug!(
                            "VIEW_TYPES_OPTION3: Call returns reference, tracking destination {:?}",
                            call_info.destination
                        );
                        self.view_typed_call_returns.insert(call_info.destination, call_info);
                    }

                    // Early return - we've recorded all field borrows
                    self.super_assign(assigned_place, rvalue, location);
                    return;
                }
            }

            // Normal path: record borrow of the whole place
            let borrow = BorrowData {
                kind,
                region,
                reserve_location: location,
                activation_location: TwoPhaseActivation::NotTwoPhase,
                borrowed_place,
                assigned_place: *assigned_place,
                view_spec: None,
            };
            // Calculate the BorrowIndex BEFORE getting mutable entry
            // (cumulative across all locations)
            let idx =
                BorrowIndex::from_usize(self.location_map.values().map(|v| v.len()).sum::<usize>());

            // Get or create the Vec for this location
            let borrows_at_location = self.location_map.entry(location).or_insert_with(Vec::new);

            // Add this borrow to the Vec
            borrows_at_location.push(borrow);

            self.insert_as_pending_if_two_phase(location, assigned_place, kind, idx);

            self.local_map.entry(borrowed_place.local).or_default().insert(idx);
        }

        self.super_assign(assigned_place, rvalue, location)
    }

    fn visit_local(&mut self, temp: Local, context: PlaceContext, location: Location) {
        if !context.is_use() {
            return;
        }

        // We found a use of some temporary TMP
        // check whether we (earlier) saw a 2-phase borrow like
        //
        //     TMP = &mut place
        if let Some(&borrow_index) = self.pending_activations.get(&temp) {
            // Find the borrow in the flattened structure
            let borrow_data = {
                let mut count = 0;
                let mut found = None;
                for borrows in self.location_map.values_mut() {
                    if count + borrows.len() > borrow_index.as_usize() {
                        found = Some(&mut borrows[borrow_index.as_usize() - count]);
                        break;
                    }
                    count += borrows.len();
                }
                found.expect("borrow_index not found in location_map")
            };

            // Watch out: the use of TMP in the borrow itself
            // doesn't count as an activation. =)
            if borrow_data.reserve_location == location
                && context == PlaceContext::MutatingUse(MutatingUseContext::Store)
            {
                return;
            }

            if let TwoPhaseActivation::ActivatedAt(other_location) = borrow_data.activation_location
            {
                span_bug!(
                    self.body.source_info(location).span,
                    "found two uses for 2-phase borrow temporary {:?}: \
                     {:?} and {:?}",
                    temp,
                    location,
                    other_location,
                );
            }

            // Otherwise, this is the unique later use that we expect.
            // Double check: This borrow is indeed a two-phase borrow (that is,
            // we are 'transitioning' from `NotActivated` to `ActivatedAt`) and
            // we've not found any other activations (checked above).
            assert_eq!(
                borrow_data.activation_location,
                TwoPhaseActivation::NotActivated,
                "never found an activation for this borrow!",
            );
            self.activation_map.entry(location).or_default().push(borrow_index);

            borrow_data.activation_location = TwoPhaseActivation::ActivatedAt(location);
        }
    }

    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) {
        if let &mir::Rvalue::Ref(region, kind, place) = rvalue {
            // double-check that we already registered BorrowData for this location

            // For async functions with view types (not yet implemented), the borrow
            // may not be in location_map because future creation and execution are in
            // different blocks. Skip validation in this case.
            let Some(borrows) = self.location_map.get(&location) else {
                return;
            };
            // For view-typed borrows, there may be multiple borrows (one per field)
            // For normal borrows, there should be exactly one
            // Check the first borrow (all should have same location, kind, region)
            if let Some(borrow_data) = borrows.first() {
                assert_eq!(borrow_data.reserve_location, location);
                assert_eq!(borrow_data.kind, kind);
                assert_eq!(borrow_data.region, region.as_var());

                // For view-typed borrows, borrowed_place will be a field projection
                // and won't match the place from the MIR (which is the whole struct)
                // So we skip this assertion for view-typed calls
                let assigned = borrow_data.assigned_place;
                if self.find_view_typed_call_use(assigned, location).is_none() {
                    // Not a view-typed borrow - normal assertion
                    assert_eq!(borrow_data.borrowed_place, place);
                } else {
                    // View-typed borrow - borrowed_place is the field, not the whole place
                    // Assertion skipped - expected mismatch
                }
            }
        }

        self.super_rvalue(rvalue, location)
    }
}

impl<'a, 'tcx> GatherBorrows<'a, 'tcx> {
    /// Look ahead to find if this place will be used in a view-typed call
    fn find_view_typed_call_use(
        &self,
        place: mir::Place<'tcx>,
        location: mir::Location,
    ) -> Option<(rustc_hir::def_id::DefId, usize)> {
        use rustc_middle::mir::TerminatorKind;

        let block = &self.body.basic_blocks[location.block];
        let terminator = block.terminator.as_ref()?;

        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            // Extract callee DefId
            let callee_def_id = match func {
                mir::Operand::Constant(box constant) => {
                    if let ty::FnDef(def_id, _) = constant.const_.ty().kind() {
                        *def_id
                    } else {
                        return None;
                    }
                }
                _ => return None,
            };

            // Check if callee has view types
            if !self.has_view_types(callee_def_id) {
                return None;
            }

            // Find which parameter uses this place
            for (param_idx, arg) in args.iter().enumerate() {
                let arg_place = match &arg.node {
                    mir::Operand::Move(p) | mir::Operand::Copy(p) => p,
                    _ => continue,
                };

                if arg_place.local == place.local && arg_place.projection == place.projection {
                    return Some((callee_def_id, param_idx));
                }
            }
        }

        None
    }

    /// Check if a function has view type annotations
    fn has_view_types(&self, def_id: rustc_hir::def_id::DefId) -> bool {
        let Some(local_def_id) = def_id.as_local() else {
            return false;
        };

        let hir_id = self.tcx.local_def_id_to_hir_id(local_def_id);
        let node = self.tcx.hir_node(hir_id);

        // LAYER 2 DEFENSE: Two-Layer Strategy for Unsupported View Types
        //
        // Even though type checking (Layer 1, in rustc_hir_typeck/view_types.rs) reports
        // errors for view types on traits/free functions, the borrow checker may still
        // encounter them due to:
        //
        // 1. Continued analysis of other functions after type errors:
        //    - Type checking emits errors but doesn't stop compilation immediately
        //    - The borrow checker runs on functions that call the problematic code
        //    - Example: `use_trait()` calls a trait method with view types
        //
        // 2. Cross-crate scenarios:
        //    - A trait with view types might be defined in another crate
        //    - Type checking in the importing crate might not catch all cases
        //    - Generic monomorphization can surface these at borrow check time
        //
        // 3. Macro-generated code:
        //    - Macros might generate code that bypasses some type checking
        //    - The borrow checker must handle all MIR regardless of source
        //
        // By returning false here, we skip view type processing for unsupported cases,
        // treating them as regular (non-view-typed) functions. This prevents ICE from
        // BorrowIndex mismatches when the dataflow analysis expects borrows that were
        // never recorded during borrow gathering.
        //
        // RESTRICTION: View types only supported on inherent methods
        match node {
            // Trait method definitions (required or provided)
            rustc_hir::Node::TraitItem(_) => return false,

            // Trait method implementations
            rustc_hir::Node::ImplItem(_) => {
                // Check if parent is a trait impl
                let parent_id = self.tcx.parent_hir_id(hir_id);
                if let rustc_hir::Node::Item(rustc_hir::Item {
                    kind: rustc_hir::ItemKind::Impl(impl_),
                    ..
                }) = self.tcx.hir_node(parent_id)
                {
                    if impl_.of_trait.is_some() {
                        // This is a trait impl method - skip view type handling
                        return false;
                    }
                }
                // Otherwise, it's an inherent impl method - continue checking
            }

            // Free functions - skip view type handling (not supported)
            rustc_hir::Node::Item(rustc_hir::Item {
                kind: rustc_hir::ItemKind::Fn { .. }, ..
            }) => return false,

            _ => {
                // Other node types - continue checking
            }
        }

        let fn_sig = match node.fn_sig() {
            Some(sig) => sig,
            None => return false,
        };

        fn_sig
            .decl
            .inputs
            .iter()
            .any(|param_ty| matches!(param_ty.kind, rustc_hir::TyKind::Ref(_, _, Some(_))))
    }

    /// Get view spec for a parameter
    fn get_view_spec(
        &self,
        def_id: rustc_hir::def_id::DefId,
        param_idx: usize,
    ) -> Option<&'tcx rustc_hir::ViewSpec<'tcx>> {
        let local_def_id = def_id.as_local()?;
        let hir_id = self.tcx.local_def_id_to_hir_id(local_def_id);
        let node = self.tcx.hir_node(hir_id);
        let fn_sig = node.fn_sig()?;
        let param_ty = fn_sig.decl.inputs.get(param_idx)?;

        if let rustc_hir::TyKind::Ref(_, _, Some(view_spec)) = &param_ty.kind {
            Some(*view_spec)
        } else {
            None
        }
    }

    /// Convert HIR view spec to ty::ViewSpec
    fn convert_view_spec(&self, hir_view_spec: &rustc_hir::ViewSpec<'tcx>) -> ty::ViewSpec<'tcx> {
        // Convert each HIR field to a ty::FieldAccess
        let field_accesses: Vec<_> = hir_view_spec
            .fields
            .iter()
            .map(|hir_field| {
                // Convert HIR mutability to ty mutability
                let mutability = match hir_field.mutability {
                    rustc_hir::Mutability::Mut => ty::Mutability::Mut,
                    rustc_hir::Mutability::Not => ty::Mutability::Not,
                };

                // Arena-allocate the field path
                let path = self.tcx.arena.alloc_slice(hir_field.path);

                ty::FieldAccess::new(path, mutability)
            })
            .collect();

        // Create the view spec (this also arena-allocates the field list)
        ty::ViewSpec::new(self.tcx, &field_accesses)
    }

    /// Get field index from field name in a struct type
    fn get_field_index(
        &self,
        ty: Ty<'tcx>,
        field_name: rustc_span::Symbol,
    ) -> Option<rustc_abi::FieldIdx> {
        match ty.kind() {
            ty::Adt(adt_def, _) if adt_def.is_struct() => {
                let variant = adt_def.non_enum_variant();
                variant.fields.iter_enumerated().find_map(|(idx, field)| {
                    if field.name == field_name { Some(idx) } else { None }
                })
            }
            _ => None,
        }
    }

    /// Build a place for nested field access (e.g., `transform.position.x`).
    ///
    /// Given a base place and a path of field names, builds the complete MIR projection
    /// by walking the path component-by-component, resolving field indices and types.
    ///
    /// This is used for view types with nested field paths like `&{mut outer.inner.value}`.
    /// Each component of the path is projected in sequence, with proper type resolution
    /// at each level to handle generic types correctly.
    ///
    /// # Example
    /// ```ignore
    /// base_place = self
    /// field_path = ["transform", "position"]
    /// base_ty = Entity
    ///
    /// Iteration 1: project to "transform", get Transform type
    /// Iteration 2: project to "position" on Transform, get Vec3 type
    ///
    /// Returns: self.transform.position (2 projections)
    /// ```
    ///
    /// # Arguments
    /// * `base_place` - Starting place (e.g., `self`, `_1`)
    /// * `field_path` - Slice of field names forming the nested path
    /// * `base_ty` - Type of the base place
    ///
    /// # Returns
    /// `Some(place)` with nested projections, or `None` if any component of the path
    /// is invalid (field doesn't exist or intermediate type is not a struct).
    ///
    /// # Implementation Note
    /// This function performs type resolution at each step to correctly handle generic
    /// types. When projecting through `Container<T>.inner` where `inner: Wrapper<T>`,
    /// the substitutions are properly threaded through via `field.ty(tcx, substs)`.
    fn build_nested_field_place(
        &self,
        base_place: mir::Place<'tcx>,
        field_path: &[rustc_span::Symbol],
        mut current_ty: Ty<'tcx>,
    ) -> Option<mir::Place<'tcx>> {
        // Start with existing projections from base place
        let mut projections = base_place.projection.to_vec();

        // Walk each component of the path, building projections incrementally
        for &field_name in field_path {
            // Get field index in current struct type
            let field_idx = self.get_field_index(current_ty, field_name)?;

            // Get field type with proper generic substitutions
            let field_ty = match current_ty.kind() {
                ty::Adt(adt_def, substs) => {
                    let variant = adt_def.non_enum_variant();
                    variant.fields[field_idx].ty(self.tcx, substs)
                }
                _ => {
                    // Not a struct - path is invalid
                    // This shouldn't happen as typeck validates the first component,
                    // but we defend against edge cases to avoid ICE.
                    debug!(
                        "build_nested_field_place: expected struct type, found {:?}",
                        current_ty.kind()
                    );
                    return None;
                }
            };

            // Add field projection to the growing list
            projections.push(mir::PlaceElem::Field(field_idx, field_ty));

            // Update current type for next iteration
            current_ty = field_ty;
        }

        // Build final place with all nested projections
        Some(mir::Place {
            local: base_place.local,
            projection: self.tcx.mk_place_elems(&projections),
        })
    }

    /// If this is a two-phase borrow, then we will record it
    /// as "pending" until we find the activating use.
    fn insert_as_pending_if_two_phase(
        &mut self,
        start_location: Location,
        assigned_place: &mir::Place<'tcx>,
        kind: mir::BorrowKind,
        borrow_index: BorrowIndex,
    ) {
        debug!(
            "Borrows::insert_as_pending_if_two_phase({:?}, {:?}, {:?})",
            start_location, assigned_place, borrow_index,
        );

        if !kind.allows_two_phase_borrow() {
            debug!("  -> {:?}", start_location);
            return;
        }

        // When we encounter a 2-phase borrow statement, it will always
        // be assigning into a temporary TEMP:
        //
        //    TEMP = &foo
        //
        // so extract `temp`.
        let Some(temp) = assigned_place.as_local() else {
            span_bug!(
                self.body.source_info(start_location).span,
                "expected 2-phase borrow to assign to a local, not `{:?}`",
                assigned_place,
            );
        };

        // Consider the borrow not activated to start. When we find an activation, we'll update
        // this field.
        {
            // Find the borrow in the flattened structure
            let mut count = 0;
            for borrows in self.location_map.values_mut() {
                if count + borrows.len() > borrow_index.as_usize() {
                    let borrow_data = &mut borrows[borrow_index.as_usize() - count];
                    borrow_data.activation_location = TwoPhaseActivation::NotActivated;
                    break;
                }
                count += borrows.len();
            }
        }

        // Insert `temp` into the list of pending activations. From
        // now on, we'll be on the lookout for a use of it. Note that
        // we are guaranteed that this use will come after the
        // assignment.
        let old_value = self.pending_activations.insert(temp, borrow_index);
        if let Some(old_index) = old_value {
            span_bug!(
                self.body.source_info(start_location).span,
                "found already pending activation for temp: {:?} \
                       at borrow_index: {:?}",
                temp,
                old_index
            );
        }
    }

    /// OPTION 3: Check if a view-typed call returns a reference.
    /// If so, we need to track the destination for lifetime extension.
    fn check_view_typed_call_returns_ref(
        &self,
        callee_def_id: rustc_hir::def_id::DefId,
        borrowed_place: mir::Place<'tcx>,
        location: mir::Location,
        hir_view_spec: &rustc_hir::ViewSpec<'_>,
    ) -> Option<ViewTypedCallInfo<'tcx>> {
        // Check if function returns a reference
        let fn_sig = self.tcx.fn_sig(callee_def_id).skip_binder();
        let return_ty = fn_sig.output().skip_binder();

        if !matches!(return_ty.kind(), ty::Ref(..)) {
            return None;
        }

        // Find the Call terminator to get the destination
        let block = &self.body.basic_blocks[location.block];
        let terminator = block.terminator.as_ref()?;

        if let mir::TerminatorKind::Call { destination, .. } = &terminator.kind {
            // Extract field names from view spec
            let fields: Vec<Symbol> = hir_view_spec.fields.iter().map(|f| f.path[0]).collect();

            Some(ViewTypedCallInfo {
                destination: destination.local,
                fields,
                borrowed_place,
                call_location: location,
            })
        } else {
            None
        }
    }
}
