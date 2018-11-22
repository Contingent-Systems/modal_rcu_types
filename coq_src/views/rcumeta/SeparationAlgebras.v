Require Import Monoids.
Require Import SetoidClass.
Require Import MySetoids.
Require Import Language Setof.
Require Import Tactics.
Require Import Framework.


Notation "a ∈ u" := (elem u a) (at level 50).

Section SeparationAlgebras.
 (* A partial value is a value together with a proposition
    that indicates whether the value should be used.
 *)
 Record partial_val {T} := mkVal {defined: Prop; val : T}.

 Definition lift_val {A} (a : A) : partial_val (T:=A) 
    := mkVal A True a. 

 (* Equivalence on partial values *)
 Definition prod_prop_equiv {A} `{Setoid A}
   := (fun (x : partial_val) (y : partial_val) => 
             (defined x) == (defined y) 
             /\ ((defined x /\ defined y) -> val x == val y)).

 Instance prod_prop_equiv_Equiv {A} `{ Setoid A } 
   : Equivalence (prod_prop_equiv (A:=A)).
  unfold prod_prop_equiv.
  split; simpl; repeat intro; rewr intuition.
 Qed.

 Instance setoid_prod_prop A `(Setoid A) : Setoid (partial_val)
  := { equiv := prod_prop_equiv }.

 Instance lift_val_smorph {A} `{Setoid A} : Proper (equiv ==> equiv) (lift_val).
  firstorder.
 Qed.


 (* Representation of a partial binary operator *)
 Definition partial_op T := (T -> T -> partial_val (T:=T)).

 Definition lift_op {A} (op : partial_op A) 
   := 
   fun a b => 
             mkVal A 
                (defined a /\ defined b 
                  /\ defined (op (val a) (val b)))
                (val (op (val a) (val b))).

 (* Separation algebra: a partial commutative monoid
    with multiple units. *)
 Class SepAlg {A} `{A_setoid : Setoid A}
     (sepop : partial_op A) :=
     {
       sa_morph :> Proper (equiv ==> equiv ==> equiv)
                    sepop;
       sa_comm : forall x y, sepop x y == sepop y x;
       sa_assoc : forall m1 m2 m3,
           lift_op sepop (sepop m1 m2) (lift_val m3) 
            == lift_op sepop (lift_val m1) (sepop m2 m3);
       sa_unit : Setof (A:=A);
       sa_unit_exists : forall m, exists i, i ∈ sa_unit /\
                                         sepop i m == lift_val m;
       sa_unit_min : forall m1 m2 i, i ∈ sa_unit ->
                           (sepop i m1) == lift_val m2 ->
                            m1 == m2
     }.

End SeparationAlgebras.

Existing Instance setoid_prod_prop.
Existing Instance lift_val_smorph.

Section SA_Views.
 (* Assume a separation algebra *)
 Context {A} sepop `(SA : SepAlg A sepop).

 (* Three-place relation version of sepop *)
 Definition saop__ (m1 m2 m3 : A) : Prop :=  
   sepop m1 m2 == lift_val m3.

 (* Lift to sets of sepop, nearly *)
 Definition saop_ (p q : Setof (A:=A)) (m : A) : Prop :=
   exists m1, exists m2, m1 ∈ p /\ m2 ∈ q
                          /\ saop__ m1 m2 m.

 Import Morphisms_Prop.

 Instance mkval_morph {A} {_ : Setoid A} : Proper (equiv ==> equiv ==> equiv) (mkVal A).
  compute; rewr intuition.
 Qed.


 Instance saop___smorph
     : Proper (equiv ==> equiv ==> equiv ==> iff) saop__.
  unfold saop__.
  repeat intro; rewr intuition.
 Qed.

 Instance saop__smorph
    : Proper (equiv ==> equiv ==> equiv ==> iff) saop_.
  repeat intro.
  cbv [saop_].
  split; intros;
    push;
    eexists; eexists; intuition; repeat ssubst; eauto. 
 Qed.
 Instance saop__smorph2 :
   Proper (equiv ==> equiv ==> equiv) saop_.
  repeat intro; apply saop__smorph; auto with *.
 Qed.
  

 (* Proper set lift of sepop *)
 Definition saop S1 S2 :=
   mkSetof (saop_ S1 S2)
 .   
  
 Instance saop_smorph
     : Proper (equiv ==> equiv ==> equiv) saop.
  repeat intro.
  unfold saop.
  rewr intuition.
 Qed.

Lemma val_defined x y : x == lift_val y -> defined x.
 destruct 1; ssubst.
 cbv; trivial.
Qed.

Ltac usevaldef := repeat
  match goal with [H : ?X == lift_val ?Y |- _] => 
    lazymatch goal with [H2 : defined X |- _] => fail
     | _ => generalize (val_defined _ _ H); intro end end.

Ltac liftvaldef := repeat
  match goal with
  | [H : context [defined (lift_val ?X)] |- _] => replace (defined (lift_val X)) with True in H by reflexivity
  end.

Ltac saop_tac := match goal with 
  | [ |- _ ∈ saop _ _] => eexists; intuition; try reflexivity
  | [H : _ ∈ (saop _ _ ) |- _] => destruct H; intuition; ssubst
  | [H : saop_ _ _ _ |- _ ] => destruct H; push
  | [H : saop__ _ _ _ |- _] => destruct H; liftvaldef; simpl in *; intuition
  | [ |- saop_ _ _ _] => eexists; eexists; intuition; eauto
end.


Lemma saop_assoc : forall m1 m2 m3, 
   saop (saop m1 m2) m3 == saop m1 (saop m2 m3).
intros.
set (Hsa:=sa_assoc).
split; intro;
repeat (match goal with
  | [H : ?a == ?b |- _] => progress ssubst
  | [Has:=sa_assoc, H : ?x1 ∈ m1, H2 : ?x2 ∈ m2, H3 : ?x3 ∈ m3 |- _] => destruct (Hsa x1 x2 x3); clear Hsa; unfold lift_op in *; simpl in *
  | _ => progress saop_tac
  | _ => cbv; intuition; reflexivity
  end).
Qed.



Lemma left_unit : forall m, saop sa_unit m == m.
split; intro.
 repeat saop_tac.
 rewrite <- sa_unit_min; eauto.
 split; simpl; tauto.

 destruct (sa_unit_exists a).
 repeat saop_tac.
Qed.

Lemma saop_comm : forall m1 m2, saop m1 m2 == saop m2 m1.
split; intro;
repeat saop_tac;
generalize (sa_comm x0 x1); intro;
unfold saop__;
ssubst; cbv; intuition.
Qed.

Lemma right_unit : forall m, saop m sa_unit == m. 
intros. rewrite saop_comm. eapply left_unit.
Qed.


  Local Obligation Tactic := auto.

  Hint Resolve saop_assoc.
  Program Instance saop_semigroup : SemiGroup saop.

  Hint Resolve left_unit.
  Hint Resolve right_unit.
  Program Instance saop_monoid : Monoid saop := {| unit := sa_unit |}.

  Hint Resolve saop_comm.
  Program Instance saop_commut : Commutative saop.

End SA_Views.



Module Type SASafetyParams
    (Import ats : Atomics)
    (Import st : StateTransformers ats).
  Parameter M : Type.
  Declare Instance M_setoid : Setoid M.
  Parameter axioms :
    (Setof (A:=M)) -> Atomic -> (Setof (A:=M)) -> Prop.
  Parameter sepop : partial_op M.
  Declare Instance separationAlgebra : SepAlg sepop.

  Parameter erase : M -> Setof (A:=State).
  Local Infix "*" := (saop sepop).
  Local Notation "|_ A _|" := (collapse (so_map erase A)).
  Axiom soundAxioms :
    forall p a q, axioms p a q ->
      forall (m : M),
        subsetof (so_map_rel (interp a)
              |_ p * singleton m _|
             (R_morphism:=st_morph (interp a)))
                |_ q * singleton m _|.
End SASafetyParams.

Module MakeSafetyParams_SA
    (ats : Atomics)
    (Import st : StateTransformers ats)
    (Import sasp : SASafetyParams ats st)
      <: (SafetyParams ats st).

  Definition V := Setof (A:=M).
  Program Instance V_setoid : Setoid V.
  Definition op : V -> V -> V := saop sepop.
  Instance op_monoid : SemiGroup op := saop_semigroup sepop _.
  Instance op_comm : Commutative op := saop_commut sepop _.

  Definition erase := fun v : V => collapse (so_map sasp.erase v).
  Instance erase_morphism : Proper (equiv ==> equiv) erase.
   split; intro;
   repeat match goal with
   | [ H: elem _ _ |- _] => destruct H; intuition
   | [ |- elem _ _ ] => eexists; intuition; eauto
   end; rewr trivial.
  Qed.

End MakeSafetyParams_SA.

Module SA_Safety
    (ats: Atomics)
    (bs : BasicSyntaxT ats)
    (st : StateTransformers ats)
    (sasp : SASafetyParams ats st).
 Module Import msp := (MakeSafetyParams_SA ats st sasp).
 Module Export sft := (Safety ats bs st msp).

 Local Infix "*" := op.

 Instance op_subsetof_lmorph : Proper
    (subsetof ==> equiv ==> subsetof) op.
  repeat intro.
  ssubst.
  destruct H1; eexists; intuition; eauto.
  destruct H1 as [x2 H1]; exists x2.
  destruct H1 as [x3 H1]; exists x3.
  intuition.
 Qed.

 Lemma subsetof_aimpl : forall p q : V,
    subsetof p q -> aimpl p q.
  repeat intro.
  destruct H0; intuition; destruct H1.
  eexists; intuition; eauto.
  eexists; intuition; eauto.
  rewr trivial.
 Qed.

 Existing Instance saop_monoid.

 Hint Resolve subsetof_aimpl.
 Hint Resolve aimpl_wm_to_aimpl.


 Instance Safe_subsetof : Proper
   (subsetof --> eq ==> subsetof ++> Basics.impl) Safe.
  repeat intro.
  apply Safe_aimpl with x x0 x1;
   unfold Basics.flip in *; intuition;
   apply aimpl_wm_to_aimpl; auto.
 Qed.

 Definition mjoin : Setof (A:=V) -> V := setof_union.
 Lemma op_mjoin_dist : forall (p : V) P,
   p * (mjoin P) == mjoin (so_map (op p) P).
  split; intros.
   repeat destruct H; intuition.
   destruct H2.
   exists (p * u).
   exists u; intuition.
   exists x; intuition.
   eexists; eexists; intuition; eauto.
  
   repeat destruct H.
   ssubst.
   destruct H0.
   exists x0; intuition.
   destruct H1.
   destruct H0; intuition.
   destruct H4.
   exists x1; exists x2.
   intuition.
    exists x; intuition.
    split; simpl in *; intuition.
 Qed.

 Lemma erase_jmorphism : forall P,    
      erase (mjoin P) == setof_union (elem (so_map erase P)).
  split; intros.
   destruct H as [x H]; intuition.
   destruct H0 as [x0 H0]; intuition.
   destruct H as [x1 H].
   exists (erase x1).
    exists x1; intuition.
    exists x; intuition.
    exists x0; intuition.
   
   repeat destruct H; intuition.
   rewrite H1 in H0.
   repeat destruct H0.
   rewrite H3 in H2.
   exists (sasp.erase x1); intuition.
   exists x1; intuition.
   exists x; intuition.
 Qed.

  Hint Resolve op_mjoin_dist.
  Hint Resolve erase_jmorphism.

 Lemma Safe_mjoin_disj : forall P c q,
    (forall p, p ∈ P -> Safe p c q) ->
      Safe (mjoin P) c q.
  apply Safe_disj; auto.
 Qed.

 Lemma singleton_decomp r :
   r == mjoin (mkSetof (fun v => exists m, m ∈ r /\ v == singleton m)).
  split; intuition.
   exists (singleton a).
   exists (singleton a); intuition.
   exists a; intuition.
   exists a; intuition.

   repeat destruct H.
   repeat ssubst.
   destruct H0; intuition; repeat ssubst.
   trivial.
 Qed.

 Import sasp bs.
 Lemma Safe_atomic : forall p a q,
   axioms p a q -> Safe p a q.
  intros.
  apply Safe_asat.
  intro.
  rewrite (singleton_decomp r).
  rewrite op_mjoin_dist.
  rewrite erase_jmorphism.
  repeat intro.
  repeat destruct H0.
  repeat ssubst.
  rewrite op_mjoin_dist.
  rewrite erase_jmorphism.
  exists (msp.erase (q * singleton x3)).
   exists (q * singleton x3); intuition.
   exists (singleton x3); intuition.
   exists (singleton x3); firstorder.

  generalize (soundAxioms _ _ _ H); intro.
  unfold msp.erase.
  apply H3.
  exists x; intuition.
 Qed.

End SA_Safety.