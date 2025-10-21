Require Import ViewTypes.

Definition test_borrows_conflict (f1 f2 : field_name) (p : place) : bool :=
  let b1 := mkBorrow 0 Mut (Some [mkFieldAccess f1 Mut]) p in
  let b2 := mkBorrow 1 Mut (Some [mkFieldAccess f2 Mut]) p in
  if places_overlap p p then
    match (Some [mkFieldAccess f1 Mut], Some [mkFieldAccess f2 Mut]) with
    | (Some vs1, Some vs2) => views_conflict vs1 vs2
    | _ => true
    end
  else false.

Compute (test_borrows_conflict "a" "b" (PVar 0)).
