Require Import SetoidClass.
Require Import Views.BasicSetoids.
Require Import Views.Setof.
Require Import Views.Tactics.
Require Import Views.Structures.

Section BasicDisjointPartialMaps.
  Variables Dom Codom : Type.
  Let PartialMap := Dom -> option Codom.
  Program Instance Map_Extensional_Setoid : Setoid PartialMap :=
    {| equiv := fun m m' => forall d, m d = m' d |}.
  Obligation 1.
   split; try firstorder.
   repeat intro.
   use_foralls; rewr auto.
  Qed.
