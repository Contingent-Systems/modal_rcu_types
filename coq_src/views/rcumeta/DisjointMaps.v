Require Import SetoidClass.
Require Import BasicSetoids.
Require Import Setof.
Require Import Tactics.
Require Import Structures.

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
