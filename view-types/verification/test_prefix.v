Require Import Coq.Lists.List.
Import ListNotations.

(* Check if list1 is a prefix of list2 *)
Fixpoint is_prefix {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) 
                   (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys => 
      if eq_dec x y then is_prefix eq_dec xs ys else false
  end.

(* Two paths conflict if they're equal or one is prefix of other *)
Definition paths_overlap {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
                         (p1 p2 : list A) : bool :=
  is_prefix eq_dec p1 p2 || is_prefix eq_dec p2 p1.

(* Quick test *)
Require Import Coq.Strings.String.
Open Scope string_scope.

Compute (paths_overlap String.string_dec ["a"; "b"] ["a"; "b"; "c"]).
Compute (paths_overlap String.string_dec ["a"; "b"] ["a"; "c"]).

