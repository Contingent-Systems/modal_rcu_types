Require Import SetoidClass.
Require Import BasicSetoids.
Require Import SetOf.
Require Import Tactics.
Require Import EquivalenceClasses.
Require Import Inhabited.

Section TPRStructures.
  Context {A} `{A_setoid : Setoid A}.
  Context (op : A -> A -> A -> Prop).

  Class CTPRRespectful :=
    {
      tpr_morph :> Proper (equiv ==> equiv ==> equiv ==> Basics.impl) op
    }.

  Section TPRRespectfulIff.
    Context `{CTPRRespectful}.
    Program Instance tpr_iff_morph :
       Proper (equiv ==> equiv ==> equiv ==> iff) op.
    Obligation 1.
     repeat intro; split; rewr auto.
    Qed.
  End TPRRespectfulIff.
  Existing Instance tpr_iff_morph.

  Class CTPRAssociative :=
    {
      assoc_assoc_l : forall x y z xyz xy, op x y xy -> op xy z xyz ->
           exists yz, op y z yz /\ op x yz xyz;
      assoc_assoc_r : forall x y z xyz yz, op y z yz -> op x yz xyz ->
           exists xy, op x y xy /\ op xy z xyz
    }.

  Class CTPRCommutative :=
    {
      comm_commut :> forall x y xy, op x y xy -> op y x xy
    }.

  Class CTPRAssociativeCommutative :=
    {
      ac_assoc : forall x y z xyz xy, op x y xy -> op xy z xyz ->
           exists yz, op y z yz /\ op x yz xyz;
      ac_commut :> CTPRCommutative
    }.

  Section AssociativeCommutativeIsAssociative.
    Context `{CTPRAssociativeCommutative}.
    Program Instance assoccomm_is_assoc : CTPRAssociative.
    Hint Resolve ac_assoc.
    Hint Resolve comm_commut.
    Obligation 1.
     eauto.
    Qed.
    Obligation 2.
     apply comm_commut in H0.
     apply comm_commut in H1.
     destruct (ac_assoc _ _ _ _ _ H0 H1) as [x0].
     exists x0.
     intuition.
    Qed.
  End AssociativeCommutativeIsAssociative.

  Class CTPRFunctional :=
    {
      func_functional :> forall x y xy xy', op x y xy -> op x y xy' ->
                 xy == xy'
    }.

  Class CTPRTotal :=
    {
      tot_total :> forall x y, exists xy, op x y xy
    }.

  Class CTPRTotalRespectfulFunction :=
    {
      trf_total :> CTPRTotal;
      trf_respectful :> CTPRRespectful;
      trf_functional :> CTPRFunctional
    }.

  Section UnitSet.
    Context (unit : Setof A).
    Class CTPRLeftUnit :=
     {
      lunit_exists : forall a, exists i, i ∈ unit /\ op i a a;
      lunit_min : forall i a b, i ∈ unit -> op i a b -> a == b
     }.

    Class CTPRRightUnit :=
     {
      runit_exists : forall a, exists i, i ∈ unit /\ op a i a;
      runit_min : forall i a b, i ∈ unit -> op a i b -> a == b
     }.

    Class CTPRTwoSidedUnit :=
     {
      tsu_lunit :> CTPRLeftUnit;
      tsu_runit :> CTPRRightUnit
     }.
  End UnitSet.

  Section RespectfulFunctional.
  Context `{op_resp : CTPRRespectful} `{op_func : CTPRFunctional}.
  Section UniqueUnit.
    Context (unit : A).
    Class CTPRUniqueLeftUnit :=
     {
      ulunit :> forall a, op unit a a
     }.
    Hint Resolve ulunit.
    Instance ULU_LU `{CTPRUniqueLeftUnit} : CTPRLeftUnit (singleton unit).
      split; intuition.
      exists unit; intuition.
      eexists; split; reflexivity.
      eapply func_functional; eauto.
      singleel; rewr auto.
    Qed.

    Class CTPRUniqueRightUnit :=
     {
      urunit :> forall a, op a unit a
     }.
    Hint Resolve urunit.
    Instance URU_RU `{CTPRUniqueRightUnit} : CTPRRightUnit (singleton unit).
      split; intuition.
      exists unit; intuition.
      eexists; split; reflexivity.
      eapply func_functional; eauto.
      singleel; rewr auto.
    Qed.
  End UniqueUnit.
  Class CTPRLeftUniquelyUnital : Prop :=
    {
     the_ulunit : A;
     the_ulunit_is_unit : CTPRUniqueLeftUnit the_ulunit
    }.
  End RespectfulFunctional.
  Section TotalRespectful.
      Context `{op_total : CTPRTotal} `{op_resp : CTPRRespectful}.
      Context `{Ainh : Inhabited A}.
      Context (unit : Setof A) `{LU : CTPRLeftUnit unit}.
      Instance LU_ULU : CTPRLeftUniquelyUnital.
       inversion Ainh.
       destruct (lunit_exists unit inhabitant) as [i].
       exists i.
       constructor; intro.
       destruct (tot_total i a) as [b].
       generalize (lunit_min unit i a b); intuition.
       ssubst; trivial.
      Qed.
   End TotalRespectful.

End TPRStructures.
Existing Instance assoccomm_is_assoc.

    Ltac tpr_assoc :=
      match goal with
       | [ H1 : ?R ?y ?z ?yz, H2 : ?R ?x ?yz ?xyz |- _] =>
           lazymatch goal with
           | [ _ : R x y ?xy, _ : R ?xy z xyz |- _] => fail
           | _ => let H := fresh in assert
                       (H : exists xy, R x y xy /\ R xy z xyz) by
                           (apply assoc_assoc_r with yz; auto with *);
                       let xy := fresh x y in destruct H as [xy H]; destruct H
                  end
       | [ H1 : ?R ?x ?y ?xy, H2 : ?R ?xy ?z ?xyz |- _] =>
           lazymatch goal with
           | [ _ : R y z ?yz, _ : R x ?yz xyz |- _] => fail
           | _ => let H := fresh in assert
                       (H : exists yz, R y z yz /\ R x yz xyz) by
                           (apply assoc_assoc_l with xy; auto with *);
                       let yz := fresh y z in destruct H as [yz H]; destruct H
                  end end.

    Ltac tpr_func :=
      match goal with
       | [ H1 : ?R ?x ?y ?z, H2 : ?R ?x ?y ?z0 |- _ ] =>
            lazymatch goal with
              | [_ : z == z0 |- _] => fail
              | _ => let H := fresh in assert (z == z0) as H by
                  (eapply func_functional; eauto with *) end
              end.

Section TPROptionTotal.

  Context {A} `{A_setoid : Setoid A}.
  Context (op : A -> A -> A -> Prop).

  Hypothesis choose_op : forall a b, 
    (exists c, op a b c) \/ (~exists c, op a b c).

  Notation "? A" := (option A) (at level 0).
  (* Remark: option type is a setoid in BasicSetoids. *)
  
  Notation "! a" := (Some a) (at level 0).
  Inductive opt_tprlift :  ? A -> ? A -> ? A -> Prop :=
    | opt_tprbasic : forall a b c, op a b c -> opt_tprlift !a !b !c
    | opt_tprlnone : forall x, opt_tprlift None x None
    | opt_tprrnone : forall x, opt_tprlift x None None
    | opt_tprundef : forall a b, (forall c, ~ op a b c) ->
       opt_tprlift !a !b None.
   Hint Constructors opt_tprlift.

  Ltac optlift_tac :=
    try constructor; repeat intro;
    repeat (match goal with [x : option A |- _] => destruct x end);
    simpl in *;
    repeat (match goal with [H : opt_tprlift _ _ _ |- _] => inversion H; subst; clear H; auto with * end).


  Lemma opt_trplift_spec : forall x y z, op x y z <-> opt_tprlift !x !y !z.
   intuition.
   inversion H; subst; auto.
  Qed.

  Instance opt_trplift_total : CTPRTotal opt_tprlift.
    optlift_tac; try solve [exists None; constructor].

    destruct (choose_op a0 a).
     destruct H.
     exists !x; constructor; trivial.
     
     exists None.
     constructor.
     intro.
     contradict H.
     exists c; trivial.
  Qed.
Require Import Coq.Program.Equality.
  Section Respectful.
    Context {op_respectful : CTPRRespectful op}.
    Instance opt_tprlift_respectful : CTPRRespectful opt_tprlift.
     optlift_tac; constructor; try rewr auto.
      intro.
      use_foralls. destruct H23; rewrite <-H;rewrite <-H0;assumption.     
    Qed.
  End Respectful.

  Section Functional.
    Context {op_functional : CTPRFunctional op}.
    Instance opt_tprlift_functional : CTPRFunctional opt_tprlift.
      optlift_tac; firstorder.
    Qed.
  End Functional.

  Section Associative.
    Context {op_assoc : CTPRAssociative op}.
    Context {op_respectful : CTPRRespectful op}.
    Context {op_functional : CTPRFunctional op}.
    Hint Resolve assoc_assoc_l.
    Hint Resolve assoc_assoc_r.
    Instance opt_tprlift_associative : CTPRAssociative opt_tprlift.
      optlift_tac;
      try (solve [try tpr_assoc;
      eexists; split; constructor; eauto]);
      match goal with
       | |- context [ opt_tprlift (Some ?x) (Some ?y) _ ] =>
       destruct (choose_op x y); 
       (splitup; eexists; split; constructor; eauto) ||
       (exists None; split; constructor; firstorder)
      end;
      repeat intro; tpr_assoc; try tpr_func;
      match goal with
       | H : forall _, ~ _ |- _ => eapply H; rewr eauto end.
    Qed.
  End Associative.

  Section Commutative.
    Context {op_commut : CTPRCommutative op}.
    Hint Resolve (comm_commut op).
    Instance opt_tprlift_commutative : CTPRCommutative opt_tprlift.
      optlift_tac; constructor; auto.
      intros; use_foralls; auto.
    Qed.
  End Commutative.

  (* The option lift does not preserve arbitrary unit sets,
     but it does preserve unique units. *)
  Section LeftUniqueUnit.
    Context unit {op_luunit : CTPRUniqueLeftUnit op unit}.
    Definition oplift_ulunit := !(unit).
    Hint Resolve (ulunit op).
    Program Instance opt_tprlift_uleftunit :
          CTPRUniqueLeftUnit opt_tprlift oplift_ulunit.
    Obligation 1.
     destruct a; constructor; auto.
    Qed.
  End LeftUniqueUnit.      

  Section RightUniqueUnit.
    Context unit {op_ruunit : CTPRUniqueRightUnit op unit}.
    Definition oplift_urunit := !(unit).
    Hint Resolve (urunit op).
    Program Instance opt_tprlift_urightunit :
          CTPRUniqueRightUnit opt_tprlift oplift_urunit.
    Obligation 1.
     destruct a; constructor; auto.
    Qed.
  End RightUniqueUnit.
End TPROptionTotal.

Section TPRAddUnit.
 
  Context {A} `{A_setoid : Setoid A}.
  
  Inductive united :=
  | un_unit : united
  | un_some : A -> united.

  Notation "¹" := united.

  Coercion un_some : A >-> united.

  Inductive united_eq : united -> united -> Prop :=
  | uneq_unit : united_eq un_unit un_unit
  | uneq_some : forall a a', a == a' ->
          united_eq (un_some a) (un_some a').
  Hint Constructors united_eq.

  Ltac united_tac :=
   repeat match goal with
     | x : united |- _ => destruct x
     | H : united_eq _ _ |- _ => inversion_clear H
     | |- united_eq _ _ => constructor
     | |- @equiv united _ _ _ => constructor
     | H : @equiv united _ _ _ |- _ => inversion_clear H
     end.

  Program Instance united_setoid : Setoid united := {| equiv := united_eq |}.
  Obligation 1.
   split; repeat intro;
   united_tac; rewr intuition.
  Qed.
  
  Instance un_some_resp : Proper (equiv ==> equiv) un_some.
   repeat intro; united_tac; auto.
  Qed.

  Instance united_inhabited : StronglyInhabited united.
   firstorder.
  Qed.

  Context (op : A -> A -> A -> Prop).


  Inductive unop : ¹ -> ¹ -> ¹ -> Prop :=
   | unop_lift : forall a b c, op a b c -> unop a b c
   | unop_lunit : forall a a' : A, a == a' -> unop un_unit a a'
   | unop_runit : forall a a' : A, a == a' -> unop a un_unit a'
   | unop_uunit : unop un_unit un_unit un_unit.
  Hint Constructors unop.

  Ltac unop_tac := united_tac;
   repeat match goal with
     | H : unop _ _ _ |- _ => inversion_clear H
     end; auto.

  Lemma unop_spec : forall a b c, op a b c <-> unop a b c.
   intuition.
   inversion H; subst; trivial.
  Qed.

  Section Respectful.
    Context {op_respectful : CTPRRespectful op}.
    Instance unop_respectful : CTPRRespectful unop.
      split; repeat intro.
      unop_tac;
      constructor; rewr auto.
    Qed.
  End Respectful.
  Section Total.
    Context {op_total : CTPRTotal op}.
    Instance unop_total : CTPRTotal unop.
     split; repeat intro.
     unop_tac; try (solve [eexists; constructor; reflexivity]).
     destruct (tot_total op a0 a).
     eexists; eauto.
    Qed.
  End Total.
  Section Functional.
    Context {op_functional : CTPRFunctional op}.

    Instance unop_functional : CTPRFunctional unop.
     split; repeat intro; unop_tac; rewr firstorder.
    Qed.
  End Functional.

  Instance unop_ulunit : CTPRUniqueLeftUnit unop un_unit.
   firstorder; unop_tac; firstorder.
  Qed.
  Instance unop_urunit : CTPRUniqueRightUnit unop un_unit.
   firstorder; unop_tac; firstorder.
  Qed.
  Hint Resolve (ulunit unop).
  Hint Resolve (urunit unop).
   
  Section Associative.
    Context {op_respectful : CTPRRespectful op}.
    Context {op_associative : CTPRAssociative op}.
    Instance unop_associative : CTPRAssociative unop.
     split; repeat intro;
     unop_tac; repeat tpr_assoc;
     eexists; firstorder; constructor; rewr eauto.
    Qed.
  End Associative.

  Section Commutative.
    Context {op_commutative : CTPRCommutative op}.
    Instance unop_commutative : CTPRCommutative unop.
     firstorder; unop_tac; firstorder.
    Qed.
  End Commutative.
End TPRAddUnit.


Section FStructures.
  Context {A} `{A_setoid : Setoid A}.
  Context (op : A -> A -> A).
  Local Infix "*" := op.

  Class CFRespectful  :=
    {
      fop_morph :> Proper (equiv ==> equiv ==> equiv) op
    }.

  Class CFAssociative  :=
    {
      fop_assoc : forall x y z : A, (x * y) * z == x * (y * z)
    }.

  Class CFCommutative :=
    {
      fop_comm : forall x y : A, x * y == y * x
    }.

  Class CFLeftUnit (unit : A) :=
    {
      fop_lunit : forall x : A, unit * x == x
    }.

  Class CFRightUnit (unit : A) :=
    {
      fop_runit : forall x : A, x * unit == x
    }.
  Class CFUnit (unit : A) :=
    {
      fop_unit_left :> CFLeftUnit unit;
      fop_unit_right :> CFRightUnit unit
    }.

End FStructures.
Existing Instance fop_unit_left.
Existing Instance fop_unit_right.
Existing Instance fop_morph.

Section ECLift.
  Context 
     {A} `{op_trf : CTPRTotalRespectfulFunction A}.
  Hint Resolve trf_total.
  Hint Resolve trf_respectful.
  Hint Resolve trf_functional.
  Section ECLiftParts.
    Context (x y : EC A).
    Definition op_lift_set : Setof A :=
      mkSetof (fun Z =>
           exists X, exists Y, 
            X ∈ x /\ Y ∈ y /\ op X Y Z).

    Lemma op_lift_witness :
      exists w, forall x, x ∈ op_lift_set <-> x == w.
    simpl.
    destruct x as [sx wx].
    destruct wx as [X H].
    destruct y as [sy wy].
    destruct wy as [Y H0].
    destruct (tot_total op X Y) as [XY H1].
    simpl.
    exists XY.
    intuition.
     repeat destruct H2; intuition.
     apply func_functional with op X Y; eauto.
     
     use_foralls; intuition; rewr trivial.

     exists XY; intuition.
     use_foralls.
     eexists; eexists; intuition; eauto.
    Qed.
    Definition op_lift : EC A :=
      {| ec_set := op_lift_set;
         ec_witness := op_lift_witness |}.
  End ECLiftParts.

  Instance op_lift_resp :
     CFRespectful op_lift.
   split; simpl; repeat intro.
   split; intuition;
    destruct H1; repeat splitup;
    eexists; split; eauto;
    eexists; eexists; repeat split; eauto;
    rewr trivial.
  Qed.

  Lemma op_lift_spec : forall x y z, op x y z <-> (op_lift (make_EC x) (make_EC y)) z.
   simpl; intuition.
   eexists; intuition (try reflexivity).
   eexists; eexists; intuition eauto; eexists; split; reflexivity.

   repeat splitup; rewr auto.
  Qed.


  Section ECLiftAssociative.
    Context {op_ass : CTPRAssociative op}.
      
    Instance op_lift_ass :
      CFAssociative op_lift.
     constructor; split;
     simpl; intros; repeat splitup;
     repeat ssubst; tpr_assoc;
     eexists; repeat split; try reflexivity;
     eexists; eexists; repeat split; eauto;
     eexists; intuition; try reflexivity;
     eexists; eauto.
    Qed.
  End ECLiftAssociative.

  Section ECLiftCommutative.
    Context {op_comm : CTPRCommutative op}.
    Hint Resolve (comm_commut op).
    Instance op_lift_comm : CFCommutative op_lift.
     constructor; intros.
     split; simpl; intro;
      repeat splitup; ssubst;
      eexists; repeat split; try reflexivity;
      eexists; eexists; repeat split; eauto.
   Qed.
  End ECLiftCommutative.

  Section ECLiftUnit.
    Context `{A_Inhabited : Inhabited A}.
    Context (unit : Setof A) {op_unit : CTPRTwoSidedUnit op unit}.
    Program Definition ECl_unit : EC A := {| ec_set := unit |}.
    Obligation 1.
     destruct A_Inhabited.
     destruct (lunit_exists op unit inhabitant).
     exists x.
     intuition.
     destruct (tot_total op x x0).
     assert (x0 == x1) by (apply lunit_min with op unit x; auto with *).
     assert (x == x1) by (apply runit_min with op unit x0; auto with *).
     rewr auto.

     rewr auto.
    Qed.
    Instance op_lift_unit : CFUnit op_lift ECl_unit.
     repeat constructor; simpl; intros.
      destruct H; repeat splitup.
      rewrite <- (lunit_min op unit);
      eauto.
      rewr auto.

      exists a; firstorder.

      destruct H; repeat splitup.
      rewrite <- (runit_min op unit);
      rewr eauto.

      exists a; firstorder.
    Qed.
  End ECLiftUnit.
End ECLift.

Existing Instance op_lift_resp.
Existing Instance op_lift_ass.
Existing Instance op_lift_comm.

