Require Export Relations Morphisms Setoid Equalities SetoidClass.
Require Import Basics.
Require Import Setof. 

Class SemiGroup {A} `{A_setoid : Setoid A} (op : A -> A -> A) :=
  {
     op_morphism :> Proper (equiv ==> equiv ==> equiv) op;
     op_assoc : forall a1 a2 a3, op (op a1 a2) a3 == op a1 (op a2 a3)
}.

Class Monoid {A} `{A_setoid : Setoid A} (op : A -> A -> A) :=
    {
     wm :> SemiGroup op;
     unit : A;
     unit_lunit : forall a, op unit a == a;
     unit_runit : forall a, op a unit == a
}.

Class Commutative {A} `{A_setoid : Setoid A} (op : A -> A -> A) :=
  { op_commut : forall a1 a2, op a1 a2 == op a2 a1 }.

Class Zero {A} `{A_setoid : Setoid A} (op : A -> A -> A) :=
  { zero : A;
    op_zero : forall a1, op a1 zero == zero }.

Class Zeros {A} `{A_setoid : Setoid A} (op : A -> A -> A) :=
  { zeros : Setof (A:=A) ;
    op_zeros : forall zero, zeros zero -> forall a1, zeros (op a1 zero);
    exist_zero : exists zero, zeros zero}.


Class ManyUnits {A} `{A_setoid : Setoid A} (op : A -> A -> A)
	`{A_zero : Zeros A op} :=
  { 
	many_units : 
	   forall x, exists u, op x u == x 
	                       /\ (forall y, op y u == y \/ zeros (op y u)) 
}.

Program Instance zeros_zero {A} `{A_setoid : Setoid A} (op : A -> A -> A) 
    { _ : Zero op} {_ : Proper (equiv ==> equiv ==> equiv) op}
    : Zeros op := { zeros := singleton zero }.
Next Obligation.
exists zero.   split; try reflexivity. 
rewrite H3. rewrite H2.
apply op_zero.
Qed.
Next Obligation.
exists zero. exists zero. split; reflexivity.
Qed.