Require Import Language  StateTransformerConstructions.
Require Import Tactics.
Require Import Relations SetoidClass.
Require Import Bool Permut.

Module Type StateTypes.
  Parameter Var Other : Set.
  Axiom Var_eq_dec : forall (x y : Var), {x = y} + {x <> y}.
End StateTypes.

(* A basic instance of HeapTypes with only one
   non-location value (effectively null)
 *)
Module BasicStateTypes <: StateTypes.
  Definition Var := nat.
  Proposition Var_eq_dec : forall (x y : Var), {x = y} + {x <> y}.
   decide equality.
  Qed.
  Definition Other := unit.
End BasicStateTypes.


Module MStates (Import ht : StateTypes).

  Variable T := .

  
Hypothesis eq_dec : forall x y:nat, {x = y} + {x <> y}.

Inductive uniset : Set :=
    Charac : (nat -> bool) -> uniset.

Definition charac (s:uniset) (a:nat) : bool := let (f) := s in f a.

Definition Emptyset := Charac (fun a:nat => false).

Definition Fullset := Charac (fun a:nat => true).

Definition Singleton (a:nat) :=
  Charac
    (fun a':nat =>
       match eq_dec a a' with
       | left h => true
       | right h => false
       end).

Definition In (s:uniset) (a:nat) : Prop := charac s a = true.
Hint Unfold In.

Definition Threads := nat.
Variable l:nat.
Definition writer(l:nat) := Singleton(l:nat).

Definition Setminus(B  C:Threads): Threads :=  fun x:Threads => In x /\ ~ In C x.
Definition readers: nat := Threads  writer.


  Definition Loc := nat.
  Lemma Loc_eq_dec : forall (x y : Loc), {x = y} + {x <> y}.
   decide equality.
  Qed.
  (* Values are locations or others *)
  Inductive Val : Type :=
    | loc_val : Loc -> Val
    | oth_val : Other -> Val
  .
  (* Stores consist of finite partial heap and
     a variable environment.  We use an explicit
     bound to ensure finiteness.
   *)
  Record store := {
    heap : Loc -> option Val;
    stack : Var -> option Val;
    lock : 
    heapBound : nat;
    heapFree : forall m, heapBound <= m -> heap m = None
  }.


Lemma eq_dec : forall x y:RVars, {x = y} + {x <> y}.
decide equality.
Qed.

  Inductive Field : Set :=
    | single : Field
    | alternate : nat -> Field.

  Definition hfield := Field.

Definition fmapping := hfield -> Var.
