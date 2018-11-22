Require Import SetoidClass Morphisms.
Require Import Tactics.
Require Import BasicSetoids.

Section SetOfDef.
  Context A `{A_setoid : Setoid A}.
  
 Record Setof := {
   elem :> A -> Prop;
   elem_morph : Proper (equiv ==> iff) elem
 }.
End SetOfDef.



Arguments elem {A} {A_setoid} s _.
 
Section SetOf.

Context {A} `{A_setoid : Setoid A}.

Instance elem_morphism (u:Setof A) :
    Proper (equiv ==> iff) (elem u).
destruct u; cbv; firstorder.
Qed.

Notation "a ∈ u" := (elem u a) (at level 50).

Definition setofeq (u v : Setof A) : Prop :=
   forall a, a ∈ u <-> a ∈ v.

Instance setofeq_equiv : Equivalence setofeq.
firstorder.
Qed.

Instance setof_setoid : Setoid (Setof A) := {equiv := setofeq}.

Instance elem_morphism2 :
    Proper (equiv ==> equiv ==> iff) elem.
repeat intro; rewrite (H x0); rewrite H0; tauto.
Qed.

Definition subsetof (u v : Setof A) : Prop :=
   forall a, a ∈ u -> a ∈ v.

Instance subsetof_preo : PreOrder subsetof.
firstorder.
Qed.

Instance subsetof_morphism : Proper (equiv ==> equiv ==> iff) subsetof.
firstorder.
Qed.

Import Basics.

Instance subsetof_transitive :
    Proper (subsetof --> subsetof ++> impl) subsetof.
firstorder.
Qed.

Instance elem_monotone : Proper (subsetof ==> equiv ==> impl) elem.
repeat intro.
rewr auto.
Qed.

Instance setof_po : PartialOrder equiv subsetof.
firstorder.
Qed.

Inductive setof_preunion (I : Setof A -> Prop) (e : A) : Prop :=
  | witness_union : forall u, I u -> e ∈ u
        -> setof_preunion I e.

Hint Resolve witness_union.

Instance setof_union_morph (I : Setof A -> Prop) :
    Proper (equiv ==> iff) (setof_preunion I).
intros x y H0.
firstorder; apply witness_union with u; rewr auto.
Qed.

Definition setof_union (I : Setof A -> Prop) :=
  {| elem := setof_preunion I |}.

Lemma setof_union_bound :
  forall (I : Setof A -> Prop) (x : Setof A),
        I x -> subsetof x (setof_union I).
intros I x H a H0.
simpl; apply witness_union with x; trivial.
Qed.

Lemma setof_union_lub : 
  forall (I : Setof A -> Prop) (z : Setof A),
   (forall x : Setof A, I x -> subsetof x z) ->
                subsetof (setof_union I) z.
intros I x H a H0.
destruct H0; apply (H u H0); trivial.
Qed.

Definition setof_preintersection (I : Setof A -> Prop) (e : A) : Prop :=
  forall u, I u -> e ∈ u.

Instance setof_intersection_morph (I : Setof A -> Prop) :
    Proper (equiv ==> iff) (setof_preintersection I).
intros x y H0.
unfold setof_preintersection.
firstorder; rewr auto.
Qed.

Definition setof_intersection (I : Setof A -> Prop) :=
  {| elem := setof_preintersection I |}.

Lemma setof_intersection_bound :
  forall (I : Setof A -> Prop) (x : Setof A),
    I x -> subsetof (setof_intersection I) x.
firstorder.
Qed.

Lemma setof_intersection_glb : 
  forall (I : Setof A -> Prop) (z : Setof A),
    (forall x : Setof A, I x -> subsetof z x) ->
        subsetof z (setof_intersection I).
intros. 
unfold subsetof in *.
unfold setof_intersection. 
simpl. 
firstorder. 
Qed.


Instance mkSetof_morph (s : A -> Prop) :
    Proper (equiv ==> iff)
      (fun a : A => exists b : A, s b /\ a == b).
intros x y H.
firstorder;
 exists x0; firstorder; rewr auto.
Qed.

Definition mkSetof (s : A -> Prop) : Setof A :=
  {| elem := (fun a => exists b, s b /\ a == b) |}.

Instance mkSetof_smorph : Proper
    (equiv ==> equiv) mkSetof.
  repeat intro.
  split; destruct 1 as [x']; exists x';
   intuition; apply H; trivial.
Qed.

Definition singleton x := mkSetof  (fun y => y==x).

Lemma single_elem {x y} : x ∈ singleton y -> x == y.
simpl. firstorder. 
rewr trivial.
Qed.

Program Definition emptyset : Setof A
       := {| elem := fun x => False |}.
Solve Obligations with firstorder.

End SetOf.

Existing Instance elem_morphism2.
Existing Instance elem_monotone.
Existing Instance setof_setoid.
Existing Instance subsetof_morphism.
Existing Instance subsetof_transitive.
Existing Instance subsetof_preo.
Existing Instance mkSetof_smorph.

Notation "a ∈ u" := (elem u a) (at level 50).

Ltac singleel := repeat 
  match goal with
   [H : elem (singleton ?Y) ?X |- _] =>
      generalize (single_elem H); clear H; intro H
  end.


Section SetOfs.
Context {A B} `{A_setoid : Setoid A} `{B_setoid : Setoid B}.

Instance so_map_morph_pre (f : A -> B) (u : Setof A) :
  Proper (equiv ==> iff)
   (fun b : B => exists a : A, elem u a /\ b == f a).
intros x y H.
firstorder; exists x0; firstorder; rewr auto.
Qed.

Definition so_map (f : A -> B) (u : Setof A) : Setof B:=
 {| elem := (fun b => exists a, elem u a /\ b == f a) |}.

Instance so_map_morph : Proper (eq ==> equiv ==> equiv) so_map.
intros f f' eq x y equiv a; subst f'.
simpl; push; ssubst; eauto. 
Qed.

Section RelationMap.

Variable (R : A -> B -> Prop).
Context `{R_morphism : Proper _ (equiv ==> equiv ==> iff) R}.

Instance so_map_rel_morph (u : Setof A) :
  Proper (equiv ==> iff)
    (fun b => exists a, u a /\ R a b).
intros x y H.
firstorder; exists x0; firstorder; rewr auto.
Qed.

Definition so_map_rel (u : Setof A) : Setof B :=
 {| elem := (fun b => exists a, u a /\ R a b) |}.

Instance so_map_rel_morphism :
    Proper (setofeq ==> setofeq) so_map_rel.
intro.
unfold so_map_rel.  
unfold setofeq.
simpl. 
firstorder.
Qed.

Instance so_map_rel_monotone :
    Proper (subsetof ++> subsetof) so_map_rel.
unfold so_map_rel. intro. unfold subsetof.  simpl. 
firstorder.
Qed.

End RelationMap.

Instance collapse_morph_pre {A} {_ : Setoid A} (aaa:(Setof (Setof A))): 
  Proper (equiv ==> iff) 
    (fun (a : A) => exists aa, elem aaa aa /\ elem aa a) .
push; repeat ssubst; eauto.
Qed.
 
Definition collapse {A} {_ : Setoid A}
  (aaa : (Setof (Setof A)))  : (Setof A) 
  := {| elem := (fun (a : A) => exists aa, elem aaa aa /\ elem aa a) |}.

Instance collapse_morph {A} {_ : Setoid A} : Proper (equiv ==> equiv) collapse. 
unfold collapse; 
push; simpl in *; push; eexists; push; try eassumption.
rewrite <- H. eassumption.
rewrite H. eassumption.
Qed.

End SetOfs.

Existing Instance so_map_rel_morphism.
Existing Instance so_map_rel_monotone.
