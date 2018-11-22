Require Import SetoidClass.
Require Import BasicSetoids.
Require Import Setof.
Require Import Tactics.
Require Import EquivalenceClasses.
Require Import Inhabited.
Require Import Structures.

Section Reification.
  Context {A} {B} `{A_Setoid : Setoid A} `{B_Setoid : Setoid B}.
  Variable reification : A -> Setof B.
  Context (reification_morphism : Proper (equiv ==> equiv) reification).
  Existing Instance reification_morphism.

  Section Option.
    Program Definition option_reification (c : option A) : Setof B :=
      match c with
      | None => emptyset
      | Some a => reification a
      end.
    Instance option_reification_morphism :
            Proper (equiv ==> equiv) option_reification.
     repeat intro; 
     repeat optiondestruct; firstorder.
    Qed.
    Lemma option_reification_spec : forall a b,
       reification a b <-> option_reification (Some a) b.
     firstorder.
    Qed.
  End Option.

  Section AddUnit.
    Program Definition united_reification (c : @united A) : Setof B :=
      match c with
      | un_unit => emptyset
      | un_some a => reification a
      end.

    Existing Instance united_setoid.
    Instance united_reification_morphism : 
            Proper (equiv ==> equiv) united_reification.
     repeat intro;
     repeat match goal with k : united |- _ => destruct k end;
     intuition; simpl;
     match goal with HH : _ == _ |- _ => inversion HH end;
     rewr auto.
    Qed.
    Lemma united_reification_spec : forall a b,
      reification a b <-> united_reification (un_some a) b.
     firstorder.
    Qed.
  End AddUnit.

  Section EC.
  
    Program Definition EC_reification (c : EC A) : Setof B :=
      {| elem := fun b => exists a, c a /\ reification a b |}.
    Obligation 1.
     repeat intro.
     firstorder;
      eexists; intuition eauto; rewr auto.
    Qed.
    Instance EC_reification_morphism :
            Proper (equiv ==> equiv) EC_reification.
     repeat intro; simpl;
     firstorder.
    Qed.
    Lemma EC_reification_spec : forall a b, reification a b <-> EC_reification (make_EC a) b.
     simpl; intuition.
     eexists; intuition eauto.
     eexists; intuition reflexivity.
     repeat splitup; rewr auto.
    Qed.

  End EC.

End Reification.

