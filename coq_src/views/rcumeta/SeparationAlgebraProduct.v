Require Import SeparationAlgebras.
Require Import SetoidClass.
Require Import Tactics.
Require Import Setof.

Instance defined_morphism {A} `{Setoid A} :
    Proper (equiv ==> equiv) defined.
(* destruct x; destruct y.
 firstorder.*)
Admitted.
 

Section SeparationAlgebraProduct.
  Context A
      {A_setoid : Setoid A}
      (aop :partial_op A)
      {A_SA : SepAlg aop}.
  Context B
      {B_setoid : Setoid B}
      (bop :partial_op B)
      {B_SA : SepAlg bop}.

  Program Instance prod_setoid : Setoid (A*B) :=
    {| equiv := fun c c' =>
      let (a, b) := c in
      let (a', b') := c' in
        a == a' /\ b == b' |}.
  Obligation 1.
   split; cbv.
   destruct x; firstorder.
   destruct x; destruct y; firstorder.
   destruct x; destruct y; destruct z.
   firstorder; rewr auto.
  Qed.

  Program Definition prod_SA_unit : @Setof (A*B) _ :=
    {| elem := (fun c =>
        let (a,b) := c in sa_unit a /\ sa_unit b) |}.
  Obligation 1.
   (*destruct x; destruct y.
   firstorder; rewr trivial.*)
  Admitted.

  Definition prod_sepop : partial_op (A*B) :=
    fun c c' =>
      let (a, b) := c in
      let (a', b') := c' in
      let a'' := aop a a' in let b'' := bop b b' in
          {|
            defined := defined a'' /\ defined b'';
            val := (val a'', val b'')
          |}.

  Instance prod_sepop_morphism : Proper
          (equiv ==> equiv ==> equiv) prod_sepop.
   repeat intro.
   unfold prod_sepop.
   repeat match goal with
    | c : prod A B |- _ => destruct c
    | P : (_,_) == (_,_) |- _ => destruct P
   end.
   destruct (sa_morph _ _ H _ _ H0).
   destruct (sa_morph _ _ H2 _ _ H1).
   split; simpl; intuition; try rewr auto.
  Qed.

  Lemma prod_sepop_comm : forall c c',
     prod_sepop c c' == prod_sepop c' c.
   intuition.
   generalize (sa_comm a a0).
   generalize (sa_comm b b0).
   split; simpl.
    (*rewr auto.
    destruct H.
    destruct H0.
    intuition.*)
 Admitted.
  
  Lemma prod_sepop_assoc : forall c c' c'',
     lift_op prod_sepop (prod_sepop c c') (lift_val c'') 
            == lift_op prod_sepop (lift_val c) (prod_sepop c' c'').
   intuition.
   generalize (sa_assoc a a0 a1).
   generalize (sa_assoc b b0 b1).
   intros H H0; split;
    destruct H; destruct H0;
    unfold lift_op in *; simpl in *;
    intuition.
  Qed.

  Lemma prod_sepop_unit_exists : forall c, exists i,
       elem prod_SA_unit i /\ prod_sepop i c == lift_val c.
   intuition.
   destruct (sa_unit_exists a).
   destruct (sa_unit_exists b).
   exists (x,x0).
   simpl; firstorder.
  Qed.
  
  Lemma prod_sepop_unit_min : forall c c' i,
                elem prod_SA_unit i ->
                    (prod_sepop i c) == lift_val c' ->
                         c == c'.
    intuition.
    destruct i as [ia ib].
    generalize (sa_unit_min b b0 ib).
    generalize (sa_unit_min a a0 ia).
    intros.
    simpl in *; unfold prod_prop_equiv in *; simpl in *.
    intuition.
  Qed.

  Instance prod_SA : SepAlg prod_sepop :=
     {| sa_morph := prod_sepop_morphism;
        sa_comm := prod_sepop_comm;
        sa_assoc := prod_sepop_assoc;
        sa_unit := prod_SA_unit;
        sa_unit_exists := prod_sepop_unit_exists;
        sa_unit_min := prod_sepop_unit_min
     |}.
End SeparationAlgebraProduct.