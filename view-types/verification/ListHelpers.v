(** * Helper Lemmas for List Operations

    This file contains helper lemmas about list operations, particularly
    existsb (exists with boolean predicate) and membership (In).

    These lemmas support the main view types proofs by providing
    reusable facts about list reasoning.
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

Require Import ViewTypes.

(** * Section 1: Basic existsb Properties *)

(** ** existsb on empty list is false *)
Lemma existsb_nil : forall {A : Type} (f : A -> bool),
  existsb f [] = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** ** existsb on singleton *)
Lemma existsb_singleton : forall {A : Type} (f : A -> bool) (x : A),
  existsb f [x] = f x.
Proof.
  intros. simpl. rewrite orb_false_r. reflexivity.
Qed.

(** ** existsb distributes over append *)
Lemma existsb_app : forall {A : Type} (f : A -> bool) (l1 l2 : list A),
  existsb f (l1 ++ l2) = existsb f l1 || existsb f l2.
Proof.
  intros A f l1 l2.
  induction l1 as [| a l1' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite orb_assoc. reflexivity.
Qed.

(** ** If existsb is true, there exists an element satisfying the predicate *)
Lemma existsb_exists : forall {A : Type} (f : A -> bool) (l : list A),
  existsb f l = true <-> exists x, In x l /\ f x = true.
Proof.
  intros A f l. split.
  - (* -> *)
    intros H.
    induction l as [| a l' IH].
    + simpl in H. discriminate.
    + simpl in H. apply orb_true_iff in H.
      destruct H as [Hfa | Hexist].
      * exists a. split.
        -- simpl. left. reflexivity.
        -- assumption.
      * apply IH in Hexist. destruct Hexist as [x [Hin Hfx]].
        exists x. split.
        -- simpl. right. assumption.
        -- assumption.
  - (* <- *)
    intros [x [Hin Hfx]].
    induction l as [| a l' IH].
    + inversion Hin.
    + simpl. simpl in Hin. destruct Hin as [Heq | Hin'].
      * subst. rewrite Hfx. simpl. reflexivity.
      * apply orb_true_iff. right. apply IH. assumption.
Qed.

(** ** If existsb is false, no element satisfies the predicate *)
Lemma existsb_false : forall {A : Type} (f : A -> bool) (l : list A),
  existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
  intros A f l. split.
  - (* -> *)
    intros H x Hin.
    induction l as [| a l' IH].
    + inversion Hin.
    + simpl in H. apply orb_false_iff in H. destruct H as [Hfa Hl'].
      simpl in Hin. destruct Hin as [Heq | Hin'].
      * subst. assumption.
      * apply IH; assumption.
  - (* <- *)
    intros H.
    induction l as [| a l' IH].
    + simpl. reflexivity.
    + simpl. apply orb_false_iff. split.
      * apply H. simpl. left. reflexivity.
      * apply IH. intros x Hin. apply H. simpl. right. assumption.
Qed.

(** * Section 2: Membership Properties *)

(** ** Membership is decidable for types with decidable equality *)
Lemma In_dec_field_access : forall (fa : field_access) (l : list field_access),
  (exists fa', In fa' l /\ fa_name fa = fa_name fa') \/
  (forall fa', In fa' l -> fa_name fa <> fa_name fa').
Proof.
  intros fa l.
  induction l as [| fa' l' IH].
  - right. intros fa'' Hin. inversion Hin.
  - destruct IH as [IHleft | IHright].
    + left. destruct IHleft as [fa'' [Hin Heq]].
      exists fa''. split.
      * simpl. right. assumption.
      * assumption.
    + destruct (String.eqb (fa_name fa) (fa_name fa')) eqn:E.
      * left. exists fa'. split.
        -- simpl. left. reflexivity.
        -- apply String.eqb_eq. assumption.
      * right. intros fa'' Hin. simpl in Hin.
        destruct Hin as [Heq | Hin'].
        -- subst. apply String.eqb_neq in E. assumption.
        -- apply IHright. assumption.
Qed.

(** ** If an element is in a list, existsb with its property is true *)
Lemma In_existsb : forall {A : Type} (f : A -> bool) (x : A) (l : list A),
  In x l -> f x = true -> existsb f l = true.
Proof.
  intros A f x l Hin Hfx.
  induction l as [| a l' IH].
  - inversion Hin.
  - simpl. simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst. rewrite Hfx. simpl. reflexivity.
    + apply orb_true_iff. right. apply IH. assumption.
Qed.

(** * Section 3: Field Access Specific Lemmas *)

(** ** If a field access is in a list, we can find it with existsb *)
Lemma field_in_list_existsb : forall fa l,
  In fa l ->
  existsb (fun fa2 => String.eqb (fa_name fa) (fa_name fa2)) l = true.
Proof.
  intros fa l Hin.
  apply existsb_exists.
  exists fa. split.
  - assumption.
  - apply String.eqb_refl.
Qed.

(** ** If field name is in view, we can find compatible access *)
Lemma field_name_in_view_existsb : forall fname fmut l,
  In (mkFieldAccess fname fmut) l ->
  existsb (fun fa2 => String.eqb fname (fa_name fa2)) l = true.
Proof.
  intros fname fmut l Hin.
  apply existsb_exists.
  exists (mkFieldAccess fname fmut). split.
  - assumption.
  - simpl. apply String.eqb_refl.
Qed.

(** ** Subview element property *)
Lemma subview_element : forall fa rest v2,
  subview (fa :: rest) v2 = true ->
  exists fa2, In fa2 v2 /\
    String.eqb (fa_name fa) (fa_name fa2) = true /\
    match (fa_mutability fa, fa_mutability fa2) with
    | (Imm, _) => true
    | (Mut, Mut) => true
    | _ => false
    end = true.
Proof.
  intros [fname fmut] rest v2 H.
  simpl in H.
  destruct (existsb
    (fun fa2 : field_access =>
     String.eqb fname (fa_name fa2) &&
     match fmut with
     | Imm => true
     | Mut => match fa_mutability fa2 with
              | Imm => false
              | Mut => true
              end
     end) v2) eqn:E.
  - (* Found compatible element *)
    apply existsb_exists in E.
    destruct E as [fa2 [Hin Hprop]].
    apply andb_true_iff in Hprop.
    destruct Hprop as [Hname Hmut].
    exists fa2. split; [assumption | split; assumption].
  - (* Not found - contradiction *)
    discriminate.
Qed.

(** ** Subview preserves field names *)
Lemma subview_preserves_names : forall v1 v2 fa1,
  subview v1 v2 = true ->
  In fa1 v1 ->
  exists fa2, In fa2 v2 /\ fa_name fa1 = fa_name fa2.
Proof.
  intros v1 v2 fa1 Hsub Hin.
  generalize dependent v2.
  induction v1 as [| fa1' rest1 IH].
  - inversion Hin.
  - intros v2 Hsub.
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + (* fa1 = fa1' *)
      subst fa1'.
      apply subview_element in Hsub.
      destruct Hsub as [fa2 [Hin2 [Hname _]]].
      exists fa2. split.
      * assumption.
      * apply String.eqb_eq. assumption.
    + (* In fa1 rest1 *)
      simpl in Hsub.
      destruct (existsb _ v2) eqn:E.
      * (* existsb found element, so subview rest1 v2 = true *)
        apply IH; assumption.
      * (* existsb returned false, so Hsub : false = true *)
        discriminate.
Qed.

(** ** Mutability weakening in subview *)
Lemma subview_mutability_preserved : forall v1 v2 fname,
  subview v1 v2 = true ->
  In (mkFieldAccess fname Mut) v1 ->
  exists m, In (mkFieldAccess fname m) v2 /\
    match m with Mut => true | Imm => false end = true.
Proof.
  intros v1 v2 fname Hsub Hin.
  (* This proof is complex due to nested induction over lists.
     The key insight: if Mut access is in v1 and v1 is a subview of v2,
     then Mut access must be in v2 (cannot downgrade Mut to Imm in subview).
     We admit this for now as it's a helper lemma. *)
Admitted.

(** * Section 4: Subview Transitivity Support *)

(** ** Key lemma for transitivity *)
Lemma subview_trans_element : forall fa v1 v2 v3,
  In fa v1 ->
  subview v1 v2 = true ->
  subview v2 v3 = true ->
  exists fa', In fa' v3 /\
    String.eqb (fa_name fa) (fa_name fa') = true /\
    match (fa_mutability fa, fa_mutability fa') with
    | (Imm, _) => true
    | (Mut, Mut) => true
    | (Mut, Imm) => false
    end = true.
Proof.
  intros fa v1 v2 v3 Hin H12 H23.
  (* fa is in v1, so it has a compatible element in v2 *)
  apply subview_preserves_names with (fa1 := fa) in H12; [| assumption].
  destruct H12 as [fa2 [Hin2 Hname2]].
  (* fa2 is in v2, so it has a compatible element in v3 *)
  apply subview_preserves_names with (fa1 := fa2) in H23; [| assumption].
  destruct H23 as [fa3 [Hin3 Hname3]].
  exists fa3. split; [assumption | split].
  - (* Names transitively equal *)
    rewrite <- Hname3. rewrite <- Hname2. apply String.eqb_refl.
  - (* Mutability preserved *)
    destruct fa as [fn1 m1].
    destruct fa2 as [fn2 m2].
    destruct fa3 as [fn3 m3].
    (* Need to reason about mutability preservation through subview *)
    destruct m1, m3; try reflexivity.
    (* m1 = Mut, m3 = Imm - need to show this is impossible *)
    (* If m1 = Mut and it's in v1, and subview v1 v2,
       then m2 must be Mut (by subview_mutability_preserved) *)
    (* Then if m2 = Mut and subview v2 v3, m3 must be Mut *)
    admit. (* This needs more detailed reasoning about mutability flow *)
Admitted.

(** * Section 5: Well-Formedness Support *)

(** ** If all fields in view exist, specific field exists *)
Lemma view_wf_field_exists : forall fa rest fields,
  view_spec_wf (fa :: rest) fields = true ->
  field_in_struct (fa_name fa) fields = true.
Proof.
  intros fa rest fields H.
  simpl in H.
  apply andb_true_iff in H.
  destruct H as [Hfa _].
  assumption.
Qed.

(** ** existsb with field lookup *)
Lemma existsb_field_in_struct : forall fname l fields,
  existsb (fun fa => String.eqb fname (fa_name fa)) l = true ->
  view_spec_wf l fields = true ->
  field_in_struct fname fields = true.
Proof.
  intros fname l fields Hexist Hwf.
  apply existsb_exists in Hexist.
  destruct Hexist as [fa [Hin Hname]].
  apply String.eqb_eq in Hname. subst fname.
  induction l as [| fa' rest IH].
  - inversion Hin.
  - simpl in Hwf. apply andb_true_iff in Hwf.
    destruct Hwf as [Hfa' Hrest].
    simpl in Hin. destruct Hin as [Heq | Hin'].
    + subst. assumption.
    + apply IH; assumption.
Qed.

(** * Section 6: Summary *)

(**
  These helper lemmas provide the foundation for reasoning about:
  - existsb and its relationship to In
  - Field access in view specifications
  - Subview transitivity (partial)
  - Well-formedness preservation

  Key lemmas for main proofs:
  - subview_element: extracts compatible element from subview
  - subview_preserves_names: names preserved through subview
  - subview_trans_element: key lemma for transitivity
  - existsb_field_in_struct: connects existsb to field existence
*)
