(** Progress theorem: well-typed expressions can step or are values *)
Theorem progress : forall env e t,
  has_type env e t ->
  forall s,
    borrow_contexts_agree (te_borrows env) (st_borrows s) ->
    is_value e \/ exists s' e', step s e s' e'.
Proof.
  (* The progress theorem proceeds by induction on the typing derivation.
     
     Key cases:
     - T_Unit, T_Bool, T_Int: Immediate values (left branch)
     - T_Var: Requires closed terms or runtime environment
     - T_Field: Apply IH to subexpression, then canonical forms
     - T_Ref: Create borrow if borrow_check passes
     - T_Deref: Apply IH, then dereference if value
     - T_Seq: Step e1, or if value, step to e2
     - T_Let: Step e1, or if value, substitute into e2
     - T_Sub: Subtyping doesn't affect evaluation
     
     The main complexity is:
     1. Applying IH correctly (need to thread state and borrow context)
     2. Canonical forms lemmas (connect values to types)
     3. Heap reasoning (struct allocation, field access)
     
     Estimated ~200-300 lines of detailed case analysis.
     
     ADMITTED for now - structure is standard but requires careful tactics *)
Admitted.
