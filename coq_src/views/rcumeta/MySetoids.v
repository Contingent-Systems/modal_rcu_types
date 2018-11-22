
Require Import SetoidClass.

Definition prod_equiv {A} {B} { _ : Setoid A } { _ : Setoid B } 
  := (fun (x : prod A B) (y : prod A B) => fst x == fst y /\ snd x == snd y).

Instance prod_equiv_Equiv A B ( s : Setoid A ) ( t : Setoid B ) 
  : Equivalence (prod_equiv (A:=A) (B:=B)).
unfold prod_equiv. split.
  (* Refl *) intuition. 
  (* Sym *)  intros x y; destruct x; destruct y; intuition.
  (* Trans *) intros x y z; destruct x; destruct y; destruct z; simpl; 
              split; intuition; etransitivity; eauto.
Qed.

Instance setoid_prod A B ( _ : Setoid A ) ( _ : Setoid B ) : Setoid (prod A B)
  := { equiv := prod_equiv }.

Program Instance setoid_arrow S T (s : Setoid S) (t : Setoid T) : Setoid (T -> S). 

Definition option_equiv {A} {_ : Setoid A} : option A -> option A -> Prop :=  
     fun x y => 
	match x,y with
	| None, None => True
	| Some x,Some y => x==y
	| _,_ => False end.
Instance eq_opt {A} {_ : Setoid A} : Equivalence option_equiv. 
split;
compute -[equiv];
intros;
repeat match goal with | H : option _ |- _ => destruct H end;
intuition. 
etransitivity; eauto.
Qed.

Instance setoid_option S (s : Setoid S) : Setoid (option S)
  := {equiv := option_equiv}.

Program Instance lift_setoid T : Setoid (T -> Prop).