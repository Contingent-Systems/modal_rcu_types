(* A typeclass for types that are inhabited *)

Class Inhabited (A : Type) : Prop :=
  {
    inhabitant : A
  }.

(* Inhabited provides a witness that can only be
   used when proving something in Prop -- it does
   not have computational content.
   StronglyInhabited provides a witness that can
   be used computationally.
*)

Class StronglyInhabited (A : Type) :=
  {
    strong_inhabitant : A
  }.

Instance StronglyInhabitedIsInhabited (A : Type) `{StronglyInhabited A} :
  Inhabited A :=
   { inhabitant := strong_inhabitant }.

(* Setof *)

Require Import SetoidClass SetOf.

(* Sets over any type are (strongly) inhabited
   by the empty set. *)
Section SetofInhabited.
  Context A `{A_Setoid : Setoid A}.

  Instance Setof_StronglyInhabited :
      StronglyInhabited (Setof A) :=
   { strong_inhabitant := mkSetof (fun a => False) }.
End SetofInhabited.
Existing Instance Setof_StronglyInhabited.

(* Equivalence classes *)
Require Import EquivalenceClasses.

(* Equivalence classes on an inhabited type
   are inhabited. *)

Section ECInhabited.
  Context A `{A_Setoid : Setoid A}.
  Context `{A_Inhabited : Inhabited A}.
  
  (* The inhabitant of EC A is the equivalence
     class of the inhabitant of A. *)
  Instance EC_Inhabited :
     Inhabited (EC A).
   destruct A_Inhabited.
   constructor.
   apply make_EC; trivial.
  Qed.
End ECInhabited.
Existing Instance EC_Inhabited.

(* Equivalence classes on an strongly inhabited type
   are strongly inhabited. *)
Section ECStronglyInhabited.
  Context A `{A_Setoid : Setoid A}.
  Context `{A_SInhabited : StronglyInhabited A}.

  Instance EC_StronglyInhabited :
     StronglyInhabited (EC A) :=
        { strong_inhabitant := make_EC strong_inhabitant }.
End ECStronglyInhabited.
Existing Instance EC_StronglyInhabited.
