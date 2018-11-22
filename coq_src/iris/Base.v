(*
This file includes the basis for the lattice theory.
It is is pretty much compiled from the source in Iris and Coq code base
*)

From Coq Require Export Utf8 ssreflect.
From stdpp Require Export prelude finite gmap.
From stdpp Require Import sorting.

Global Open Scope general_if_scope.
Global Set SsrOldRewriteGoalsOrder. (* See Coq issue #5706 *)
Ltac done := stdpp.tactics.done.

Set Default Proof Using "Type".

Section gmap_top.
Set Default Proof Using "Type*".
Context `{Countable K} {A : Type}
        (R: relation K)
        `{∀ x y, Decision (R x y)} `{!PartialOrder R} `{!Total R}.

Implicit Type (m: gmap K A).

Definition gmap_top m : option (K * A) :=
  let tlst := merge_sort R (elements (dom (gset K) m)) in
  match tlst with
  | nil => None
  | head :: _ =>
      match m !! head with
      | None => None
      | Some a => Some (head, a)
      end
  end.

Lemma gmap_top_lookup k a m:
  gmap_top m = Some (k,a) → m !! k = Some a.
Proof.
  rewrite /gmap_top. case_match; first done. case_match; last done.
  inversion 1. by subst.
Qed.

Lemma gmap_top_top k a m:
  gmap_top m = Some (k,a)
  → ∀ k', k' ∈ (dom (gset K) m) → R k k'.
Proof.
  rewrite /gmap_top. case_match; first done. case_match; last done.
  inversion 1. subst. move => k' In.
  assert (Hk': k' ∈ k :: l).
  { by rewrite -Heql merge_sort_Permutation elem_of_elements. }
  move : Hk' => /elem_of_cons [-> //|Hk'].
  assert (HS:= StronglySorted_merge_sort R (elements (dom (gset K) m))).
  rewrite Heql in HS. inversion HS as [|a' l' HA FA].
  subst. rewrite -> Forall_forall in FA. by apply FA.
Qed.

Lemma gmap_top_inv k a m:
   m !! k = Some a
   → (∀ k', k' ∈ (dom (gset K) m) → R k k')
   → gmap_top m = Some (k,a).
Proof.
  rewrite /gmap_top => In TOP.
  assert (IS: is_Some (m !! k)) by (eexists; eauto).
  destruct merge_sort as [|head ?] eqn: EQ.
  - exfalso. apply (elem_of_dom (D:=gset K)) in IS. move:IS.
    rewrite -elem_of_elements. rewrite <-(merge_sort_Permutation R).
    by rewrite EQ elem_of_nil.
  - assert (head ∈ dom (gset _) m) as InD.
    { rewrite -elem_of_elements. rewrite <-(merge_sort_Permutation R).
      rewrite EQ elem_of_cons. by left. }
    case_match.
    + have Eqt: head = k.
      { apply: anti_symm; last by apply TOP.
        assert (HS:= StronglySorted_merge_sort R (elements (dom (gset K) m))).
        inversion HS as [Eq|a' l' HA FA Eq]; rewrite -Eq in EQ;
          [done|inversion EQ; subst].
        rewrite -> Forall_forall in FA.
        have Hk': k ∈ head :: l.
        { rewrite Eq merge_sort_Permutation elem_of_elements.
          by apply elem_of_dom. }
        move : Hk' => /elem_of_cons [-> //|Hk']. by apply FA. }
      rewrite Eqt In in Heqo. inversion Heqo. by subst.
    + move : InD => /elem_of_dom [?]. by rewrite Heqo.
Qed.

Lemma gmap_top_equiv k a m:
  gmap_top m = Some (k,a) ↔ (m !! k = Some a ∧ (∀ k', k' ∈ (dom (gset K) m) → R k k')).
Proof.
  split.
  - move => ?. split; [by apply gmap_top_lookup|by eapply gmap_top_top].
  - move => [? ?]. by apply gmap_top_inv.
Qed.

Lemma gmap_top_nonempty m (NEMP: m ≠ ∅) :
  ∃ k a, gmap_top m = Some (k, a).
Proof.
  rewrite /gmap_top.
  destruct merge_sort as [|head ?] eqn: EQ.
  - exfalso. apply NEMP, (dom_empty_inv (D:=gset K)) => k.
    rewrite -elem_of_elements. rewrite <-(merge_sort_Permutation R).
    by rewrite EQ elem_of_nil.
  - assert (is_Some (m !! head)) as [a Eqa].
    { apply (elem_of_dom (D:=gset K)). rewrite -elem_of_elements.
      rewrite <-(merge_sort_Permutation R). rewrite EQ. by left. }
    exists head, a. by rewrite Eqa.
Qed.

Lemma gmap_top_nonempty_2 k a m (Eq: m !! k = Some a) :
  ∃ k' a', gmap_top m = Some (k', a').
Proof. apply gmap_top_nonempty => EqE. by rewrite EqE lookup_empty in Eq. Qed.

Lemma gmap_top_nonempty_inv k a m :
  gmap_top m = Some (k, a) → m ≠ ∅.
Proof. move => /gmap_top_lookup Eq ?. subst. by rewrite lookup_empty in Eq. Qed.

Lemma gmap_top_empty : gmap_top ∅ = None.
Proof. by rewrite /gmap_top dom_empty_L elements_empty /=. Qed.

Lemma gmap_top_singleton k a : gmap_top {[k := a]} = Some (k,a).
Proof.
  rewrite /gmap_top.
  rewrite (_: elements (dom (gset K) {[k := a]}) = [k]);
    last by rewrite dom_singleton_L elements_singleton.
  by rewrite /= lookup_insert.
Qed.

Lemma gmap_top_insert_eq m k a a' (CH: gmap_top m = Some (k, a)):
  gmap_top (<[k := a']> m) = Some (k, a').
Proof.
  apply gmap_top_inv; eauto; first by rewrite lookup_insert.
  move => k'. rewrite dom_insert subseteq_union_1.
  - by eapply gmap_top_top.
  - rewrite -elem_of_subseteq_singleton elem_of_dom.
    apply gmap_top_lookup in CH. by eexists.
Qed.

Lemma gmap_top_insert_ne_old m k a k' a'
  (CH: gmap_top m = Some (k,a))
  (NEQ: k' ≠ k)
  (LE: R k k'):
  gmap_top (<[k' := a']> m) = Some (k, a).
Proof.
  apply gmap_top_inv; eauto.
  - rewrite lookup_insert_ne; last done. by eapply gmap_top_lookup.
  - move => k0. rewrite dom_insert elem_of_union elem_of_singleton => [[-> //|]].
    by eapply gmap_top_top.
Qed.

Lemma gmap_top_insert_new m k a k' a'
  (CH: gmap_top m = Some (k,a))
  (LE: R k' k):
  gmap_top (<[k' := a']> m) = Some (k', a').
Proof.
  apply gmap_top_inv; eauto; first by rewrite lookup_insert.
  move => k0. rewrite dom_insert elem_of_union elem_of_singleton => [[-> //|]].
  move => InD. etrans; [exact LE| by eapply gmap_top_top].
Qed.

Lemma gmap_top_insert_new_2 m k a
  (TOP: ∀ k', k' ∈ (dom (gset K) m) → R k k'):
  gmap_top (<[k := a]> m) = Some (k, a).
Proof.
  apply gmap_top_inv; eauto; first by rewrite lookup_insert.
  move => k'. rewrite dom_insert elem_of_union elem_of_singleton => [[-> //|]].
  by apply TOP.
Qed.
End gmap_top.


(* TODO: move to stdpp *)
(* Some extra lemmas for map_Filter *)
Section map_Filter.
  Context `{FinMap K M} {A} (P : K * A → Prop) `{!∀ x, Decision (P x)}.
  Implicit Types (m : M A) (k: K) (v: A).

  Lemma map_filter_subseteq m:
    filter P m ⊆ m.
  Proof.
    intros k. destruct (filter P m !! k) as [a|] eqn: Hk; simpl.
    - apply map_filter_lookup_Some in Hk as [Hk _].
      by rewrite Hk.
    - by destruct (m !! k).
  Qed.

  Global Instance map_filter_map_subseteq :
    Proper (((⊆) : relation (M A)) ==> (⊆)) (filter P).
  Proof.
    intros m1 m2 Le k. specialize (Le k).
    destruct (filter P m1 !! k) as [a|] eqn: Ha; simpl.
    - apply map_filter_lookup_Some in Ha as [Ha HP].
      rewrite Ha /= in Le.
      destruct (m2 !! k) as [b|] eqn:Hb; [subst a|done].
      rewrite (_: filter P m2 !! k = Some b); [done|].
      by apply map_filter_lookup_Some.
    - by destruct (filter P m2 !! k).
  Qed.

  Lemma map_filter_singleton k v:
    P (k,v) → filter P ({[k := v]} : M A) = {[k := v]}.
  Proof.
    intros HP. apply map_eq. intros k'.
    case (decide (k' = k)) => [->|?].
    - rewrite lookup_singleton. apply map_filter_lookup_Some.
      by rewrite lookup_singleton.
    - rewrite lookup_singleton_ne; [|auto]. apply map_filter_lookup_None.
      left. by rewrite lookup_singleton_None.
  Qed.

  Lemma map_filter_unsat_empty m (UNSAT: map_Forall (λ k v, ¬ P (k,v)) m):
    filter P m = ∅.
  Proof.
    apply map_eq. intros k'. rewrite lookup_empty.
    apply map_filter_lookup_None. right. apply UNSAT.
  Qed.

  Lemma map_filter_delete_eq k m:
    delete k (filter P m) = filter P (delete k m).
  Proof.
    apply map_eq. intros k'.
    case (decide (k' = k)) => [->|?].
    - rewrite lookup_delete. symmetry. apply map_filter_lookup_None.
      left. by rewrite lookup_delete.
    - rewrite lookup_delete_ne; [|done].
      destruct (filter P m !! k') as [a|] eqn: Hk; simpl; symmetry.
      + apply map_filter_lookup_Some in Hk.
        apply map_filter_lookup_Some. by rewrite lookup_delete_ne.
      + apply map_filter_lookup_None in Hk.
        apply map_filter_lookup_None. by rewrite lookup_delete_ne.
  Qed.
End map_Filter.

Lemma map_filter_comm `{FinMap K M} {A}
  `{!∀ x, Decision (P1 x)} `{!∀ x, Decision (P2 x)} (m : M A) :
  filter P1 (filter P2 m) = filter P2 (filter P1 m).
Proof.
  apply map_eq => k.
  destruct (filter P2 (filter P1 m) !! k) as [a|] eqn:Ha.
  - move : Ha. rewrite !map_filter_lookup_Some. firstorder.
  - move : Ha. rewrite !map_filter_lookup_None.
    move => [[Hk|Hk]|Hk]; [by left; left|..].
    + right. by move => v /map_filter_lookup_Some [/Hk].
    + right. move => v /map_filter_lookup_Some [Hv /Hk HP2] HP1.
      by apply HP2, map_filter_lookup_Some.
Qed.

Lemma map_filter_impl_idemp `{FinMap K M} {A}
  `{!∀ x, Decision (P1 x)} `{!∀ x, Decision (P2 x)} (m : M A) :
  (∀ a, P1 a → P2 a) → filter P1 (filter P2 m) = filter P1 m.
Proof.
  intros IMP. apply map_eq => k.
  destruct (filter P1 m !! k) as [a|] eqn:Ha.
  - move : Ha. rewrite !map_filter_lookup_Some => [[Hk HP]].
    repeat split; auto.
  - move : Ha. rewrite !map_filter_lookup_None => [[Hk|Hk]]; [by left;left|].
    right. by move => v /map_filter_lookup_Some [/Hk].
Qed.

Lemma map_filter_impl_subseteq `{FinMap K M} {A}
  `{!∀ x : K * A, Decision (P1 x)} `{!∀ x : K * A, Decision (P2 x)} (m : M A) :
  (∀ a, P1 a → P2 a) → filter P1 m ⊆ filter P2 m.
Proof.
  move => IMP k.
  destruct (filter P1 m !! k) as [a|] eqn:HP1; simpl; last by case lookup.
  apply map_filter_lookup_Some in HP1 as [HL HP1%IMP].
  have HP2: filter P2 m !! k = Some a by apply map_filter_lookup_Some.
  by rewrite HP2.
Qed.

Lemma map_filter_equiv_eq `{FinMap K M} {A}
  `{!∀ x : K * A, Decision (P1 x)} `{!∀ x : K * A, Decision (P2 x)} (m : M A) :
  (∀ a, P1 a ↔ P2 a) → filter P1 m = filter P2 m.
Proof.
  move => IMP. apply : anti_symm; apply map_filter_impl_subseteq; firstorder.
Qed.

Section map_Difference.
  Context `{FinMap K M} {A : Type}.
  Implicit Types (m : M A) (k: K) (v: A).

  Lemma map_difference_insert_1 k v m1 m2 (NONE: m2 !! k = None) :
    <[k:=v]> m1 ∖ m2 = <[k:=v]> (m1 ∖ m2).
  Proof.
    apply map_eq. intros k'.
    case (decide (k' = k)) => [->|?].
    - rewrite lookup_insert. apply lookup_difference_Some. by rewrite lookup_insert.
    - rewrite lookup_insert_ne; [|done].
      destruct ((m1 ∖ m2) !! k') as [v'|] eqn: Hk'.
      + apply lookup_difference_Some. rewrite lookup_insert_ne; [|done].
        by apply lookup_difference_Some in Hk'.
      + apply lookup_difference_None. rewrite lookup_insert_ne; [|done].
        by apply lookup_difference_None in Hk'.
  Qed.

  Lemma map_difference_insert_2 k v m1 m2 :
    <[k:=v]> m1 ∖ <[k:=v]> m2 ⊆ m1 ∖ m2.
  Proof.
    intros k'.
    destruct ((<[k:=v]> m1 ∖ <[k:=v]> m2) !! k') as [v'|] eqn:Eqk'; simpl;
      last by case_match.
    rewrite (_: (m1 ∖ m2) !! k' = Some v'); [done|].
    apply lookup_difference_Some.
    apply lookup_difference_Some in Eqk' as [Eq1 Eq2].
    have ? : k ≠ k'. { move =>?. subst k'. by rewrite lookup_insert in Eq2. }
    rewrite lookup_insert_ne in Eq1; [|done].
    by rewrite lookup_insert_ne in Eq2.
  Qed.

  Lemma map_difference_delete k v m1 m2 (Eq: m1 !! k = Some v) :
    m1 ∖ delete k m2 = <[k:=v]> (m1 ∖ m2).
  Proof.
    apply map_eq. intros k'.
    case (decide (k' = k)) => [->|?].
    - rewrite lookup_insert. apply lookup_difference_Some. split; [done|].
      apply lookup_delete_None. by left.
    - rewrite lookup_insert_ne; [|done].
      destruct ((m1 ∖ m2) !! k') as [v'|] eqn: Hk'.
      + apply lookup_difference_Some. apply lookup_difference_Some in Hk' as [??].
        split; [done|]. apply lookup_delete_None. by right.
      + apply lookup_difference_None. apply lookup_difference_None in Hk' as [?|[v' ?]].
        by left. right. apply lookup_delete_is_Some. split; [done|by eexists].
  Qed.

  Lemma map_difference_subseteq (m m' : M A) :
    m ∖ m' ⊆ m.
  Proof.
    intros k. destruct ((m ∖ m') !! k) as [a|] eqn:Ha; simpl.
    - by move : Ha => /lookup_difference_Some [->].
    - by case_match.
  Qed.

  Lemma map_singleton_lookup_subseteq (m : M A) k v :
    m !! k = Some v → {[k := v]} ⊆ m.
  Proof.
    intros Hk k'.
    case (decide (k' = k)) => [->|?].
    - by rewrite lookup_insert Hk.
    - rewrite lookup_singleton_ne /=; [|done]. by case lookup.
  Qed.

End map_Difference.

(** Wellformedness *)

Class Wellformed A := Wf : A →  Prop.
Existing Class Wf.

Class WellformedPreserving `{Wellformed A} `{Wellformed B} (R : A → B → Prop) := {
  wf_pre_proper a b : R a b → Wf a → Wf b;
}.

Hint Extern 100 (Wf ?b) =>
  match goal with
  | H : _ ?a b |- _ => apply (wf_pre_proper a b H)
  end : typeclass_instances.

Instance option_wf `{Wellformed A} : Wellformed (option A) :=
  from_option Wf True.

(** SqSubsetEq, Join and Meet notations **)

Infix "⊑*" := (Forall2 (⊑)) (at level 70) : stdpp_scope.
Notation "(⊑*)" := (Forall2 (⊑)) (only parsing) : stdpp_scope.
Infix "⊑**" := (Forall2 (⊑*)) (at level 70) : stdpp_scope.
Infix "⊑1*" := (Forall2 (λ p q, p.1 ⊑ q.1)) (at level 70) : stdpp_scope.
Infix "⊑2*" := (Forall2 (λ p q, p.2 ⊑ q.2)) (at level 70) : stdpp_scope.
Infix "⊑1**" := (Forall2 (λ p q, p.1 ⊑* q.1)) (at level 70) : stdpp_scope.
Infix "⊑2**" := (Forall2 (λ p q, p.2 ⊑* q.2)) (at level 70) : stdpp_scope.

Infix "⊏" := (strict sqsubseteq) (at level 70) : stdpp_scope.
Notation "(⊏)" := (strict sqsubseteq) (only parsing) : stdpp_scope.
Notation "( X ⊏)" := (sqsubseteq X) (only parsing) : stdpp_scope.
Notation "(⊏ X )" := (λ Y, Y ⊏ X) (only parsing) : stdpp_scope.
Infix "⊏*" := (Forall2 (⊏)) (at level 70) : stdpp_scope.
Notation "(⊏*)" := (Forall2 (⊏)) (only parsing) : stdpp_scope.
Infix "⊏**" := (Forall2 (⊏*)) (at level 70) : stdpp_scope.
Infix "⊏1*" := (Forall2 (λ p q, p.1 ⊏ q.1)) (at level 70) : stdpp_scope.
Infix "⊏2*" := (Forall2 (λ p q, p.2 ⊏ q.2)) (at level 70) : stdpp_scope.
Infix "⊏1**" := (Forall2 (λ p q, p.1 ⊏* q.1)) (at level 70) : stdpp_scope.
Infix "⊏2**" := (Forall2 (λ p q, p.2 ⊏* q.2)) (at level 70) : stdpp_scope.
Instance Strict_sqsubseteq_Rewrite `{SqSubsetEq T} : @RewriteRelation T (⊏).

Infix "⊔*" := (zip_with (⊔)) (at level 50, left associativity) : stdpp_scope.
Notation "(⊔*)" := (zip_with (⊔)) (only parsing) : stdpp_scope.
Infix "⊔**" := (zip_with (zip_with (⊔)))
  (at level 50, left associativity) : stdpp_scope.
Infix "⊔*⊔**" := (zip_with (prod_zip (⊔) (⊔*)))
  (at level 50, left associativity) : stdpp_scope.

Infix "⊓*" := (zip_with (⊓)) (at level 40, left associativity) : stdpp_scope.
Notation "(⊓*)" := (zip_with (⊓)) (only parsing) : stdpp_scope.
Infix "⊓**" := (zip_with (zip_with (⊓)))
  (at level 40, left associativity) : stdpp_scope.
Infix "⊓*⊓**" := (zip_with (prod_zip (⊓) (⊓*)))
  (at level 40, left associativity) : stdpp_scope.

(* Lattice canonical structure *)
Structure latticeT : Type := Make_Lat {
  lat_ty :> Type;
  lat_equiv : Equiv lat_ty;
  lat_sqsubseteq : SqSubsetEq lat_ty;
  lat_join : Join lat_ty;
  lat_meet : Meet lat_ty;

  lat_inhabited : Inhabited lat_ty;
  lat_sqsubseteq_proper : Proper ((≡) ==> (≡) ==> iff) (⊑);
  lat_join_proper : Proper ((≡) ==> (≡) ==> (≡)) (⊔);
  lat_meet_proper : Proper ((≡) ==> (≡) ==> (≡)) (⊓);
  lat_equiv_equivalence : Equivalence (≡);
  lat_pre_order : PreOrder (⊑);
  lat_sqsubseteq_antisym : AntiSymm (≡) (⊑);
  lat_join_sqsubseteq_l X Y : X ⊑ X ⊔ Y;
  lat_join_sqsubseteq_r X Y : Y ⊑ X ⊔ Y;
  lat_join_lub X Y Z : X ⊑ Z → Y ⊑ Z → X ⊔ Y ⊑ Z;
  lat_meet_sqsubseteq_l X Y : X ⊓ Y ⊑ X;
  lat_meet_sqsubseteq_r X Y : X ⊓ Y ⊑ Y;
  lat_meet_glb (X Y Z : lat_ty) : X ⊑ Y → X ⊑ Z → X ⊑ Y ⊓ Z
}.
Arguments lat_equiv : simpl never.
Arguments lat_sqsubseteq : simpl never.
Arguments lat_join : simpl never.
Arguments lat_join_sqsubseteq_l {_} _ _.
Arguments lat_join_sqsubseteq_r {_} _ _.
Arguments lat_join_lub {_} _ _ _.
Arguments lat_meet : simpl never.
Arguments lat_meet_sqsubseteq_l {_} _ _.
Arguments lat_meet_sqsubseteq_r {_} _ _.
Arguments lat_meet_glb {_} _ _ _.
Global Existing Instances lat_equiv lat_sqsubseteq lat_join lat_meet
       lat_inhabited lat_sqsubseteq_proper lat_sqsubseteq_antisym
       lat_join_proper lat_meet_proper lat_equiv_equivalence lat_pre_order.

Lemma lat_join_sqsubseteq_or (Lat : latticeT) (X Y Z : Lat) :
  Z ⊑ X ∨ Z ⊑ Y → Z ⊑ X ⊔ Y.
Proof.
  intros [H|H]; (etrans; [apply H|]);
    [apply lat_join_sqsubseteq_l|apply lat_join_sqsubseteq_r].
Qed.

Lemma lat_meet_sqsubseteq_or (Lat : latticeT) (X Y Z : Lat) :
  X ⊑ Z ∨ Y ⊑ Z → X ⊓ Y ⊑ Z.
Proof.
  intros [H|H]; (etrans; [|apply H]);
    [apply lat_meet_sqsubseteq_l|apply lat_meet_sqsubseteq_r].
Qed.

Create HintDb lat.
Ltac solve_lat := by typeclasses eauto with lat core.
Hint Resolve lat_join_lub lat_meet_glb : lat.
Hint Extern 0 (?a ⊑ ?b) =>
  (* We first check whether a and b are unifiable, in order not to
     trigger typeclass search for Reflexivity when this is not needed. *)
  unify a b with lat; reflexivity : lat.
Hint Extern 0 (_ = _) => apply (anti_symm (⊑)) : lat.
Hint Extern 0 (_ ≡ _) => apply (anti_symm (⊑)) : lat.
Hint Resolve lat_join_sqsubseteq_or | 10 : lat.
Hint Resolve lat_meet_sqsubseteq_or | 10 : lat.
Hint Extern 100 (?a ⊑ ?c) =>
  match goal with H : a ⊑ ?b |- _ => transitivity b; [exact H|] end
  : lat.
Hint Extern 200 (?a ⊑ ?c) =>
  match goal with H : ?b ⊑ c |- _ => transitivity b; [|exact H] end
  : lat.

Section Lat.

Context {Lat : latticeT}.

Global Instance lat_sqsubseteq_order_L `{!LeibnizEquiv Lat} :
  PartialOrder (A:=Lat) (⊑).
Proof.
  split; [apply lat_pre_order|] => x y ??.
  by apply leibniz_equiv, (anti_symm (⊑)).
Qed.

Global Instance lat_join_assoc : @Assoc Lat (≡) (⊔).
Proof. intros ???; solve_lat. Qed.
Global Instance lat_join_assoc_L `{!LeibnizEquiv Lat} : @Assoc Lat (=) (⊔).
Proof. intros ???. solve_lat. Qed.

Global Instance lat_join_comm : @Comm Lat Lat (≡) (⊔).
Proof. intros ??; solve_lat. Qed.
Global Instance lat_join_comm_L `{!LeibnizEquiv Lat} : @Comm Lat Lat (=) (⊔).
Proof. intros ??; solve_lat. Qed.

Global Instance lat_join_mono : Proper ((⊑) ==> (⊑) ==> (⊑)) (@join Lat _).
Proof. intros ?????. solve_lat. Qed.
Global Instance lat_join_mono_flip :
  Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (@join Lat _).
Proof. solve_proper. Qed.

Lemma lat_le_join_l (x y : Lat) : y ⊑ x → x ⊔ y ≡ x.
Proof. solve_lat. Qed.
Lemma lat_le_join_l_L `{!LeibnizEquiv Lat} (x y : Lat) : y ⊑ x → x ⊔ y = x.
Proof. solve_lat. Qed.

Lemma lat_le_join_r (x y : Lat) : x ⊑ y → x ⊔ y ≡ y.
Proof. solve_lat. Qed.
Lemma lat_le_join_r_L `{!LeibnizEquiv Lat} (x y : Lat) : x ⊑ y → x ⊔ y = y.
Proof. solve_lat. Qed.

Lemma lat_join_idem (x : Lat) : x ⊔ x ≡ x.
Proof. solve_lat. Qed.
Lemma lat_join_idem_L `{!LeibnizEquiv Lat} (x : Lat) : x ⊔ x = x.
Proof. solve_lat. Qed.

Global Instance lat_meet_assoc : @Assoc Lat (≡) (⊓).
Proof. intros ???; solve_lat. Qed.
Global Instance lat_meet_assoc_L `{!LeibnizEquiv Lat} : @Assoc Lat (=) (⊓).
Proof. intros ???. solve_lat. Qed.

Global Instance lat_meet_comm : @Comm Lat Lat (≡) (⊓).
Proof. intros ??; solve_lat. Qed.
Global Instance lat_meet_comm_L `{!LeibnizEquiv Lat} : @Comm Lat Lat (=) (⊓).
Proof. intros ??; solve_lat. Qed.

Global Instance lat_meet_mono : Proper ((⊑) ==> (⊑) ==> (⊑)) (@meet Lat _).
Proof. intros ?????. solve_lat. Qed.
Global Instance lat_meet_mono_flip :
  Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (@meet Lat _).
Proof. solve_proper. Qed.

Lemma lat_le_meet_l (x y : Lat) : x ⊑ y → x ⊓ y ≡ x.
Proof. solve_lat. Qed.
Lemma lat_le_meet_l_L `{!LeibnizEquiv Lat} (x y : Lat) : x ⊑ y → x ⊓ y = x.
Proof. solve_lat. Qed.

Lemma lat_le_meet_r (x y : Lat) : y ⊑ x → x ⊓ y ≡ y.
Proof. solve_lat. Qed.
Lemma lat_le_meet_r_L `{!LeibnizEquiv Lat} (x y : Lat) : y ⊑ x → x ⊓ y = y.
Proof. solve_lat. Qed.

Lemma lat_meet_idem (x : Lat) : x ⊓ x ≡ x.
Proof. solve_lat. Qed.
Lemma lat_meet_idem_L `{!LeibnizEquiv Lat} (x : Lat) : x ⊓ x = x.
Proof. solve_lat. Qed.

(* Lattices with a bottom element. *)
Class LatBottom (bot : Lat) :=
 lat_bottom_sqsubseteq X : bot ⊑ X.
Hint Resolve lat_bottom_sqsubseteq : lat.

Global Instance lat_join_bottom_rightid `{!LatBottom bot} : RightId (≡) bot (⊔).
Proof. intros ?; solve_lat. Qed.
Global Instance lat_join_bottom_rightid_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
  RightId (=) bot (⊔).
Proof. intros ?; solve_lat. Qed.

Global Instance lat_join_bottom_leftid `{!LatBottom bot} : LeftId (≡) bot (⊔).
Proof. intros ?; solve_lat. Qed.
Global Instance lat_join_bottom_leftid_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
  LeftId (=) bot (⊔).
Proof. intros ?; solve_lat. Qed .

Global Instance lat_meet_bottom_leftabsorb `{!LatBottom bot} (x : Lat) :
  LeftAbsorb (≡) bot (⊓).
Proof. intros ?; solve_lat. Qed.
Global Instance lat_meet_bottom_leftabsorb_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
  LeftAbsorb (=) bot (⊓).
Proof. intros ?. solve_lat. Qed.

Global Instance lat_meet_bottom_rightabsorb `{!LatBottom bot} (x : Lat) :
  RightAbsorb (≡) bot (⊓).
Proof. intros ?; solve_lat. Qed.
Global Instance lat_meet_bottom_rightabsorb_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
  RightAbsorb (=) bot (⊓).
Proof. intros ?. solve_lat. Qed.

End Lat.
Hint Resolve lat_bottom_sqsubseteq : lat.

(** Lattice for product **)

Section Prod.

Context (A B : latticeT).

Program Canonical Structure prod_Lat :=
  Make_Lat (A * B) prod_equiv (prod_relation (⊑) (⊑))
           (λ p1 p2, (p1.1 ⊔ p2.1, p1.2 ⊔ p2.2))
           (λ p1 p2, (p1.1 ⊓ p2.1, p1.2 ⊓ p2.2))
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation.
  intros ??[a b]??[c d]. split=>-[??]; split;
  rewrite -?a -?b // -?c -?d // ?a ?c // ?b ?d //.
Qed.
Next Obligation.
  intros ??[a b]??[c d]. split; rewrite /= ?a ?c // ?b ?d //.
Qed.
Next Obligation.
  intros ??[a b]??[c d]. split; rewrite /= ?a ?c // ?b ?d //.
Qed.
Next Obligation. intros. apply: prod_relation_equiv. Qed.
Next Obligation.
  split; [apply: prod_relation_refl | apply: prod_relation_trans].
Qed.
Next Obligation. intros ??[??][??]; split; by apply (anti_symm (⊑)). Qed.
Next Obligation. intros ??. split; solve_lat. Qed.
Next Obligation. intros ??. split; solve_lat. Qed.
Next Obligation. intros ??? [??] [??]. by split; solve_lat. Qed.
Next Obligation. intros ??. split; solve_lat. Qed.
Next Obligation. intros ??. split; solve_lat. Qed.
Next Obligation. intros ??? [??] [??]. by split; solve_lat. Qed.

Global Instance prod_sqsubseteq_dec :
  RelDecision (A:=A) (⊑) → RelDecision (A:=B) (⊑) → RelDecision (A:=A * B) (⊑).
Proof.
  move => ?? ab ab'.
  case: (decide (fst ab ⊑ fst ab'));
  case: (decide (snd ab ⊑ snd ab'));
    [left => //|right|right|right]; move => []; abstract naive_solver.
Qed.

Global Instance prod_latbottom `{!@LatBottom A botA, !@LatBottom B botB} :
  LatBottom (botA, botB).
Proof. split; solve_lat. Qed.

Global Instance fst_lat_mono : Proper ((⊑) ==> (⊑)) (@fst A B).
Proof. move => [??][??][-> _]//. Qed.

Global Instance snd_lat_mono : Proper ((⊑) ==> (⊑)) (@snd A B).
Proof. move => [??][??][_ ->]//. Qed.

Lemma lat_join_fst x y :
  fst (x ⊔ y) = fst x ⊔ fst y.
Proof. done. Qed.

Lemma lat_join_snd x y :
  snd (x ⊔ y) = snd x ⊔ snd y.
Proof. done. Qed.

End Prod.

(** Lattice for option. None is the bottom element. **)

Instance option_sqsubseteq `{SqSubsetEq A} : SqSubsetEq (option A) :=
  λ o1 o2, if o1 is Some x1 return _ then
              if o2 is Some x2 return _ then x1 ⊑ x2 else False
           else True.

Instance option_sqsubseteq_preorder `{SqSubsetEq A} `{!@PreOrder A (⊑)} :
  @PreOrder (option A) (⊑).
Proof.
  split.
  - move=>[x|] //. apply (@reflexivity A (⊑) _).
  - move=>[x|] [y|] [z|] //. apply (@transitivity A (⊑) _).
Qed.


Instance option_sqsubseteq_po `{SqSubsetEq A} `{!@PartialOrder A (⊑)} :
  @PartialOrder (option A) (⊑).
Proof.
  split; [apply _|].
  move => [?|] [?|] ??; [|done|done|done]. f_equal. by apply : anti_symm.
Qed.

Section option.

Context (Lat : latticeT).

Program Canonical Structure option_Lat :=
  Make_Lat (option Lat) option_equiv option_sqsubseteq
           (λ o1 o2, if o1 is Some x1 return _ then
                       if o2 is Some x2 return _ then Some (x1 ⊔ x2) else o1
                     else o2)
           (λ o1 o2, if o1 is Some x1 return _ then
                       if o2 is Some x2 return _ then Some (x1 ⊓ x2) else None
                     else None) _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation.
  intros ??[???|]??[???|]; try by split. by apply lat_sqsubseteq_proper.
Qed.
Next Obligation.
  intros ??[?? EQ1|]??[?? EQ2|]=>//; constructor; by setoid_subst.
Qed.
Next Obligation.
  intros ??[?? EQ1|]??[?? EQ2|]=>//; constructor; by setoid_subst.
Qed.
Next Obligation. move=>[x|] [y|] //. constructor. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] //. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] //. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] [z|] //. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] //. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] //. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] [z|] //. solve_lat. Qed.

Global Instance option_sqsubseteq_dec :
  RelDecision (A:=Lat) (⊑) → RelDecision (A:=option Lat) (⊑).
Proof.
  move=>DEC [a|][a'|]; unfold Decision; [edestruct (DEC a a')|..]; auto with lat.
Qed.

Global Instance option_latbottom : LatBottom (@None Lat).
Proof. done. Qed.

Global Instance option_Total `{!@Total Lat (⊑)}:
  @Total (option Lat) (⊑).
Proof.
  move => [x|] [y|]; (try by right); (try by left). destruct (total (⊑) x y); auto.
Qed.

Global Instance Some_mono : Proper ((⊑) ==> (⊑)) (@Some Lat).
Proof. solve_proper. Qed.
Global Instance Some_mono_flip : Proper (flip (⊑) ==> flip (⊑)) (@Some Lat).
Proof. solve_proper. Qed.

(* Global Instance fmap_sqsubseteq_mono f : *)
(*   Proper ((⊑) ==> (⊑)) f -> *)
(*   Proper ((⊑) ==> (⊑)) (@fmap option option_fmap Lat (option Lat) f). *)
(* Proof. *)
(*   move => H. *)
(*   repeat move => ? ? S. rewrite /fmap /option_fmap /option_map. *)
(*   repeat case_match; simplify_option_eq; cbn; [by apply H|destruct S|done|done]. *)
(* Qed. *)

Lemma fmap_sqsubseteq `{Lat2 : latticeT} (f : Lat -> Lat2) (x y : option Lat) {H : Proper ((⊑) ==> (⊑)) f} :
  x ⊑ y -> fmap f x ⊑ fmap f y.
Proof.
  rewrite /fmap/option_fmap/option_map.
  repeat case_match; simplify_option_eq; cbn; [by apply H|inversion 1|done|done].
Qed.

End option.


Section Forall2.
  Context {A} (R : relation A).

  Global Instance option_Forall2_refl : Reflexive R → Reflexive (option_Forall2 R).
  Proof. intros ? [?|]; by constructor. Qed.
  Global Instance option_Forall2_sym : Symmetric R → Symmetric (option_Forall2 R).
  Proof. destruct 2; by constructor. Qed.
  Global Instance option_Forall2_trans : Transitive R → Transitive (option_Forall2 R).
  Proof. destruct 2; inversion_clear 1; constructor; etrans; eauto. Qed.
  Global Instance option_Forall2_equiv : Equivalence R → Equivalence (option_Forall2 R).
  Proof. destruct 1; split; apply _. Qed.
End Forall2.

(** Lattice for gmap **)

Section gmap.
Context K `{Countable K}.

Global Instance gmap_sqsubseteq `{SqSubsetEq A} : SqSubsetEq (gmap K A) :=
  λ m1 m2, ∀ i, m1 !! i ⊑ m2 !! i.

Global Instance gmap_sqsubseteq_preorder `{SqSubsetEq A} `{!@PreOrder A (⊑)} :
  @PreOrder (gmap K A) (⊑).
Proof. split=>??//? LE1 LE2 ?; etrans; [apply LE1|apply LE2]. Qed.

Global Instance gmap_sqsubseteq_po `{SqSubsetEq A} `{!@PartialOrder A (⊑)} :
  @PartialOrder (gmap K A) (⊑).
Proof.
  constructor; [apply _|].
  move => ????. apply map_eq => ?. by apply : (anti_symm (⊑)).
Qed.

Global Instance gmap_key_filter {A} : Filter K (gmap K A) :=
  λ P _, filter (λ kv, P (kv.1)).


Context (A : latticeT).

Program Canonical Structure gmap_Lat :=
  Make_Lat (gmap K A) map_equiv gmap_sqsubseteq
           (union_with (λ x1 x2, Some (x1 ⊔ x2)))
           (intersection_with (λ x1 x2, Some (x1 ⊓ x2)))
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation. move=> ??? ???; split=>??; setoid_subst=>//. Qed.
Next Obligation.
  move=> X1 Y1 EQ1 X2 Y2 EQ2 i. rewrite !lookup_union_with.
  by destruct (EQ1 i), (EQ2 i); setoid_subst.
Qed.
Next Obligation.
  move=> X1 Y1 EQ1 X2 Y2 EQ2 i. rewrite !lookup_intersection_with.
  by destruct (EQ1 i), (EQ2 i); setoid_subst.
Qed.
Next Obligation.
  move=>?? LE1 LE2 ?. apply (anti_symm (⊑)); [apply LE1|apply LE2].
Qed.
Next Obligation.
  move=>???. rewrite lookup_union_with.
  repeat destruct lookup=>//. solve_lat.
Qed.
Next Obligation.
  move=>???. rewrite lookup_union_with.
  repeat destruct lookup=>//. solve_lat.
Qed.
Next Obligation.
  move=>??? LE1 LE2 i. rewrite lookup_union_with.
  specialize (LE1 i). specialize (LE2 i).
  repeat destruct lookup=>//. solve_lat.
Qed.
Next Obligation.
  move=>???. rewrite lookup_intersection_with.
  repeat destruct lookup=>//. solve_lat.
Qed.
Next Obligation.
  move=>???. rewrite lookup_intersection_with.
  repeat destruct lookup=>//. solve_lat.
Qed.
Next Obligation.
  move=>??? LE1 LE2 i. rewrite lookup_intersection_with.
  specialize (LE1 i). specialize (LE2 i).
  repeat destruct lookup=>//. solve_lat.
Qed.

Global Instance gmap_bottom : LatBottom (@empty (gmap K A) _).
Proof. done. Qed.

Global Instance gmap_sqsubseteq_dec :
  RelDecision (A:=A) (⊑) → RelDecision (A:=gmap K A) (⊑).
Proof.
  move => ? m m'.
  destruct (decide (set_Forall (λ k, m !! k ⊑ m' !! k) (dom (gset K) m))) as [Y|N].
  - left => k.
    case: (decide (k ∈ dom (gset K) m)).
    + by move/Y.
    + move/not_elem_of_dom => -> //.
  - right.
    apply not_set_Forall_Exists in N; last apply _.
    case : N => x [/elem_of_dom [a ?]] NSqsubseteq ?. by apply NSqsubseteq.
Qed.

Global Instance lookup_mono l :
  Proper ((⊑) ==> (⊑)) (@lookup K A (gmap K A) _ l).
Proof. intros ?? Le. apply Le. Qed.
Global Instance lookup_mono_flip l :
  Proper (flip (⊑) ==> flip (⊑)) (@lookup K A (gmap K A) _ l).
Proof. solve_proper. Qed.

Global Instance gmap_sqsubseteq_dom_proper :
  Proper ((@sqsubseteq (gmap K A) _) ==> (⊆)) (dom (gset K)).
Proof.
  move => m1 m2 Sqsubseteq k /elem_of_dom [a Eqa].
  specialize (Sqsubseteq k). rewrite Eqa in Sqsubseteq.
  destruct (m2 !! k) as [|] eqn:Eq2; last done.
  apply elem_of_dom. by eexists.
Qed.

Lemma gmap_join_dom_union (m1 m2 : gmap K A):
  dom (gset K) (m1 ⊔ m2) ≡ dom (gset K) m1 ∪ dom (gset K) m2.
Proof.
  move => k. rewrite elem_of_union 3!elem_of_dom lookup_union_with /=.
  case (m1 !! k) => [v1|]; case (m2 !! k) => [v2|] /=; naive_solver.
Qed.

Lemma gmap_meet_dom_intersection (m1 m2 : gmap K A):
  dom (gset K) (m1 ⊓ m2) ≡ dom (gset K) m1 ∩ dom (gset K) m2.
Proof.
  move => k. rewrite elem_of_intersection 3!elem_of_dom lookup_intersection_with /=.
  case (m1 !! k) => [v1|]; case (m2 !! k) => [v2|] /=; naive_solver.
Qed.

Lemma lookup_join (m1 m2 : gmap K A) k:
  (m1 ⊔ m2) !! k = m1 !! k ⊔ m2 !! k.
Proof. rewrite lookup_union_with. by do 2!case: (_ !! k). Qed.

Lemma lookup_meet (m1 m2 : gmap K A) k:
  (m1 ⊓ m2) !! k = m1 !! k ⊓ m2 !! k.
Proof. rewrite lookup_intersection_with. by do 2!case: (_ !! k). Qed.

Global Instance gmap_leibniz_eq :
  LeibnizEquiv A → LeibnizEquiv (gmap K A).
Proof. intros. apply map_leibniz. Qed.

End gmap.

Lemma gmap_subseteq_empty `{Countable K} {A} (m : gmap K A) : ∅ ⊆ m.
Proof. intros ?. rewrite lookup_empty. by case lookup. Qed.

Lemma to_gmap_sqsubseteq `{Countable K} `{SqSubsetEq A}
  (m1 m2: gset K) (a b: A) (Sub: m1 ⊆ m2) (Ext: a ⊑ b) :
  to_gmap a m1 ⊑ to_gmap b m2.
Proof.
  intros i.
  destruct (to_gmap a m1 !! i) as [a'|] eqn:Eq; last done.
  apply lookup_to_gmap_Some in Eq as [In ?]. subst a'.
  rewrite (_: to_gmap b m2 !! i = Some b).
  - by apply Ext.
  - apply lookup_to_gmap_Some. split; last done. by apply Sub.
Qed.

(** Lattice for positive *)
Program Canonical Structure pos_Lat :=
  Make_Lat (positive) (=) (≤)%positive
           (λ (p q : positive), if (decide (p ≤ q)%positive) then q else p)
           (λ (p q : positive), if (decide (p ≤ q)%positive) then p else q)
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation. move=>x y ??. erewrite Pos.le_antisym; eauto. Qed.
Next Obligation. move=>x y. unfold join. destruct decide=>//. Qed.
Next Obligation.
  move=> x y. unfold join. destruct decide => //. apply Pos.le_nlt. lia.
Qed.
Next Obligation. move=>x y z. unfold join; destruct decide=>?? //. Qed.
Next Obligation.
  move=>x y. unfold meet. destruct decide => //. apply Pos.le_nlt. lia.
Qed.
Next Obligation. move=>x y. unfold meet. destruct decide=>//. Qed.
Next Obligation. move=>x y z. unfold meet; destruct decide=>?? //. Qed.

Instance pos_leibnizequiv : LeibnizEquiv positive := λ _ _ H, H.

Instance pos_Total : Total (@sqsubseteq positive _).
Proof.
  move => x y. case: (decide (x ≤ y)%positive); first tauto.
  move => /Pos.lt_nle /Pos.lt_le_incl. tauto.
Qed.

Instance pos_sqsubseteq_decision : RelDecision (@sqsubseteq positive _).
Proof. intros ??. apply _. Qed.

(** Lattice for gset  *)
Section gset.
Context (A: Type) `{Countable A}.
(* Lattice of sets with subseteq *)
Program Canonical Structure gset_Lat  :=
  Make_Lat (gset A) (≡) subseteq union intersection
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation. move => ???. by apply union_subseteq_l. Qed.
Next Obligation. move => ???. by apply union_subseteq_r. Qed.
Next Obligation. move => ???. by apply union_least. Qed.
Next Obligation. move => ???. by apply intersection_subseteq_l. Qed.
Next Obligation. move => ???. by apply intersection_subseteq_r. Qed.
Next Obligation. move => ??????. by apply intersection_greatest. Qed.

Global Instance gset_Lat_bot : LatBottom (∅ : gset_Lat).
Proof. done. Qed.

Global Instance gset_sqsubseteq_dec : RelDecision (A:=gset A) (⊑) := _.
End gset.

(* We restrict these to semilattices to avoid divergence. *)
Instance flip_total {A : latticeT} :
  @Total A (⊑) → @Total A (flip (⊑)).
Proof. move=>Ht x y. destruct (Ht y x); auto. Qed.
Instance flip_sqsubseteq_antisymm {A : latticeT} :
  @AntiSymm A (≡) (⊑) → @AntiSymm A (≡) (flip (⊑)).
Proof. move=>?????. by apply (anti_symm (⊑)). Qed.
Instance flip_sqsubseteq_antisymm_L {A : latticeT} :
  @AntiSymm A (=) (⊑) → @AntiSymm A (=) (flip (⊑)).
Proof. move=>?????. by apply (anti_symm (⊑)). Qed.
Instance flip_partialorder {A : latticeT} :
  @PartialOrder A (⊑) → @PartialOrder A (flip (⊑)).
Proof. move=>?. constructor; apply _. Qed.

Infix "∋" := (flip elem_of) (at level 70) : stdpp_scope.
Notation "(∋)" := (flip elem_of) (only parsing) : stdpp_scope.
Notation "( X ∋)" := ((flip elem_of) X) (only parsing) : stdpp_scope.
Notation "(∋ x )" := (λ X, X ∋ x) (only parsing) : stdpp_scope.
Notation "X ∌ x" := (¬X ∋ x) (at level 80) : stdpp_scope.
Notation "(∌)" := (λ X x, X ∌ x) (only parsing) : stdpp_scope.
Notation "( X ∌)" := (λ x, X ∌ x) (only parsing) : stdpp_scope.
Notation "(∌ x )" := (λ X, X ∌ x) (only parsing) : stdpp_scope.

(* 
Section IsoLat.
Context (A : latticeT) (B: Type)
        (fA: lat_ty A → B) (gB: B → lat_ty A) (ISO: ∀ x, gB (fA x) ≡ x).

Program Canonical Structure iso_Lat :=
  Make_Lat B
   (λ b1 b2, gB b1 ≡ gB b2)
   (λ b1 b2, gB b1 ⊑ gB b2)
   (λ b1 b2, fA (gB b1 ⊔ gB b2))
   (λ b1 b2, fA (gB b1 ⊓ gB b2))
   (populate (fA inhabitant)) _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation. solve_proper. Qed.
Next Obligation. move => ??????. rewrite {1}/join {2}/join {1}/equiv 2!ISO. solve_proper. Qed.
Next Obligation. move => ??????. rewrite {1}/meet {2}/meet {1}/equiv 2!ISO. solve_proper. Qed.
Next Obligation. constructor.
  - move => ?. by rewrite {1}/equiv.
  - move => ??. by rewrite {1}/equiv {2}/equiv.
  - move => ???. rewrite {1}/equiv {2}/equiv {3}/equiv => -> //.
Qed.
Next Obligation. constructor.
  - move => ?. by rewrite {1}/sqsubseteq.
  - move => ???. rewrite {1}/sqsubseteq {2}/sqsubseteq {3}/sqsubseteq => -> //.
Qed.
Next Obligation. move => ????. rewrite {1}/equiv. by apply : anti_symm. Qed.
Next Obligation. move => ??. rewrite {1}/join {1}/sqsubseteq ISO. solve_lat. Qed.
Next Obligation. move => ??. rewrite {1}/join {1}/sqsubseteq ISO. solve_lat. Qed.
Next Obligation.
  move => ???. rewrite {1}/join {1}/sqsubseteq {2}/sqsubseteq {3}/sqsubseteq ISO.
  solve_lat.
Qed.
Next Obligation. move => ??. rewrite {1}/meet {1}/sqsubseteq ISO. solve_lat. Qed.
Next Obligation. move => ??. rewrite {1}/meet {1}/sqsubseteq ISO. solve_lat. Qed.
Next Obligation.
  move => ???. rewrite {1}/meet {1}/sqsubseteq {2}/sqsubseteq {3}/sqsubseteq ISO.
  solve_lat.
Qed.

Global Instance iso_Lat_sqsubseteq_dec :
  RelDecision (A:=A) (⊑) → RelDecision (A:=iso_Lat) (⊑).
Proof.
  move => ? m m'. rewrite {1}/sqsubseteq /lat_sqsubseteq /=. apply _.
Qed.

Global Instance iso_Lat_leibniz_eq `{INJ: Inj _ _ (=) (=) gB} :
  LeibnizEquiv A → LeibnizEquiv iso_Lat.
Proof.
  move => ???. rewrite {1}/equiv /lat_equiv /=.
  move => /leibniz_equiv_iff /INJ //.
Qed.

End IsoLat.

 *)
