Require Import SetoidClass.
Require Import SetOf.
Require Import Tactics.

Section EquivalenceClasses.
  Context A `{A_setoid : Setoid A}.

  Record EC := {
      ec_set :> Setof A;
      ec_witness : exists w, forall x, x ∈ ec_set <-> x == w
    }.

  Program Instance EC_setoid : Setoid EC :=
    {| equiv := fun x y => ec_set x == ec_set y |}.
  Solve Obligations with firstorder.

  Set Implicit Arguments.
  Program Definition make_EC (a : A) : EC :=
    {| ec_set := singleton a |}.
  Obligation 1.
   exists a; rewr firstorder.
  Qed.
  
  Coercion make_EC : A >-> EC.
End EquivalenceClasses.

Existing Instance EC_setoid.
