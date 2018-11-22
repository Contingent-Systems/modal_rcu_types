Require Import SetoidClass.

Module Type Atomics.
  Parameter Atomic : Set.
End Atomics.

Module Type BasicSyntaxT (Import ats : Atomics).
Inductive Syntax : Set :=
  | atom :> Atomic -> Syntax
  | skip : Syntax
  | sequence : Syntax -> Syntax -> Syntax
  | choice : Syntax -> Syntax -> Syntax
  | parallel : Syntax -> Syntax -> Syntax
  | loop : Syntax -> Syntax.
Infix ";;" := sequence (at level 30, right associativity)
        : bsyntax_scope.
Infix "||" := parallel 
        : bsyntax_scope.
Infix "+" := choice 
        : bsyntax_scope.
Notation "(  x )*" := (loop x) : bsyntax_scope.
Open Scope bsyntax_scope.
End BasicSyntaxT.

Module BasicSyntax (Import ats : Atomics) : BasicSyntaxT ats.
Inductive Syntax : Set :=
  | atom :> Atomic -> Syntax
  | skip : Syntax
  | sequence : Syntax -> Syntax -> Syntax
  | choice : Syntax -> Syntax -> Syntax
  | parallel : Syntax -> Syntax -> Syntax
  | loop : Syntax -> Syntax.
Infix ";;" := sequence (at level 30, right associativity)
        : bsyntax_scope.
Infix "||" := parallel 
        : bsyntax_scope.
Infix "+" := choice 
        : bsyntax_scope.
Notation "(  x )*" := (loop x) : bsyntax_scope.
Open Scope bsyntax_scope.
End BasicSyntax.

(* A state transformer is a relation on states that respects
   the setoid equivalence *)
Record ST {A} `{Setoid A} :=
  { st_trans :> A -> A -> Prop;
     st_morph : Proper (equiv ==> equiv ==> iff) st_trans
  }.

Instance st_trans_morph (st : ST) :
    Proper (equiv ==> equiv ==> iff) st.
apply st_morph.
Qed.

Module Type StateTransformers (Import ats : Atomics).
(* Set of states to interpret commands over *)
Parameter State : Set.
Declare Instance state_setoid : Setoid State.

(* Interpretation of atomic commands *)
Parameter interp : Atomic -> ST (A:=State).
Local Coercion interp : Atomic >-> ST.

End StateTransformers.

Module OperationalSemantics (Import ats : Atomics) (Import bs : BasicSyntaxT ats)
        (Import sts : StateTransformers ats).

Inductive Label := 
	| atm : Atomic -> Label 
	| id : Label.

Local Coercion atm : Atomic >-> Label.
 
Definition st_equiv : ST:= {| st_trans := equiv |}.

Instance st_equiv_equiv : Equivalence st_equiv.
 unfold st_equiv.
 intuition.
  repeat intro.
  simpl in *.
  (*rewrite H;trivial.*)
Admitted.

Local Coercion interp : Atomic >-> ST.
 
Definition lifted_interp l : ST :=
   match l with 
   | id => st_equiv
   | atm a => a
   end.

Coercion lifted_interp : Label >-> ST.

(* Milner-style labelled operational semantics *)

Inductive los : Label -> Syntax -> Syntax -> Prop :=
  | los_atom : forall (a : Atomic), los a a skip
  | los_seq_left : forall a C1 C1' C2, los a C1 C1' ->
                 los a (C1 ;; C2) (C1' ;; C2)
  | los_seq_skip : forall C2, los id (skip ;; C2) C2
  | los_choice_left : forall C1 C2, los id (C1 + C2) C1
  | los_choice_right : forall C1 C2, los id (C1 + C2) C2
  | los_par_left : forall a C1 C1' C2, los a C1 C1' ->
                 los a (C1 || C2) (C1' || C2)
  | los_par_right : forall a C1 C2 C2', los a C2 C2' ->
                 los a (C1 || C2) (C1 || C2')
  | los_par_lskip : forall C, los id (skip || C) C
  | los_par_rskip : forall C, los id (C || skip) C
  | los_loop_loop : forall C, los id (C)* (C ;; (C)*)
  | los_loop_skip : forall C, los id (C)* skip.

Notation "x -[ a ]-> y" := (los a x y) (at level 70).


(* Stateful semantics *)

(*Definition ProgState := (Syntax * State)%type.*)

Inductive osms : Syntax -> State ->
        Syntax -> State -> Prop :=
  | osms_refl : forall C s, osms C s C s
  | osms_step : forall C1 s1 C2 s2 C3 s3 a,
          C1 -[ a ]-> C2 -> a s1 s2 -> 
          osms C2 s2 C3 s3 ->
              osms C1 s1 C3 s3.

(*Infix "~>*" := osms (at level 75).*)
Notation "[ C , s ] ~>* [ D , t ]" :=
          (osms C s D t) (at level 75).

End OperationalSemantics.

(* It's nice to know that your module types are inhabited *)

Module TrivialAtomics <: Atomics.
  Definition Atomic := unit.
End TrivialAtomics.

Module TrivialSTs <: (StateTransformers TrivialAtomics).
  Import TrivialAtomics.
  Definition idat := tt.
  Definition State := unit.
  Instance state_setoid : Setoid State := {equiv:=eq}.
  Definition interp (a:Atomic) : ST (A:=State).
    apply Build_ST with equiv.
    repeat intro.
    rewrite H, H0; reflexivity.
  Defined.
  Proposition idat_id : st_trans (interp idat) = equiv.
    cbv; reflexivity.
  Qed.
End TrivialSTs.

Module TrivialSyntax := BasicSyntax TrivialAtomics.
Module TrivialOpSem := OperationalSemantics TrivialAtomics TrivialSyntax TrivialSTs.
(* Import TrivialOpSem. *)