Require Import Heaps.
Require Import String.
Require Import MSets.
Require Import SetoidClass.
Require Import Tactics.
Require Import Setof.


  (*Variables*)
  Definition Var := nat.
  Proposition Var_eq_dec : forall (x y : Var), {x = y} + {x <> y}.
   decide equality.
  Qed.
  Definition Other := unit.

  (*Locations*)
  Definition Loc:= nat.
  Lemma Loc_eq_dec : forall (x y: Loc), {x=y}+{x <> y}.
  Proof.
    decide equality.
  Qed.
  
 (*Values are locations or others*)
  Inductive Val : Type :=
  |loc_val : Loc -> Val
  |oth_val : Other -> Val.

  Inductive  FName : Type:=
  |det : nat -> FName
  |alt: list nat -> FName
  .

  Lemma FName_eq_dec: forall (f1 f2: FName),  {f1=f2}+{f1 <> f2}.
  Proof.
    induction f1;decide equality.
    decide equality.
    decide equality.
    decide equality.
    decide equality.
    decide equality.
    decide equality.
  Qed.

  
  Definition TID:=nat.
  Inductive Thread : Type:=
  |reader |writer.

  (*Stores consist of finite partial heap.
    Finiteness is enforced via a explicit bound.
    There is also a stack in the store.
   *)
  
  Record store:=
    {
      heap : Loc * FName -> option Val;
      stack : Var * TID -> option Loc;
      heapBound:nat;
      heapFree: forall (h:Loc*FName) , heapBound <= (fst h) -> heap h  = None
    }.

  Instance store_equivalence : Equivalence 
    (fun s1 s2 => heap s1 == heap s2 /\ stack s1 == stack s2).
  Admitted.

  (* Stores form a setoid *)
  Instance store_setoid : Setoid store :=
   { equiv := fun s1 s2 => heap s1 == heap s2 /\ stack s1 == stack s2 }.

  (* The projections are morphisms *)
  Instance heap_morphism : Proper (equiv ==> equiv) heap.
   repeat intro.
   destruct H.
   rewr trivial.
  Qed.

    Instance heap_morphism2 : Proper (equiv ==> eq ==> eq) heap.
   repeat intro; subst.
   exact (heap_morphism _ _ H y0).
  Qed.

  Instance stack_morphism : Proper (equiv ==> equiv) stack.
   repeat intro.
   destruct H.
   rewr trivial.
  Qed.
  
    Instance stack_morphism2 : Proper (equiv ==> eq ==> eq) stack.
   repeat intro; subst.
   exact (stack_morphism _ _ H y0).
  Qed.

  (* Defining overwriting: use the max of the
     bounds as the new bound.
   *)
  Require Import Arith.
  Import Max. 
  Lemma max_over_bound (s1 s2 : store) :
      forall (m:Loc*FName), max (heapBound s1) (heapBound s2) <= (fst m) ->
          (pw_over (heap s1) (heap s2)) m = None.
   intros.
   assert (heap s1 m = None).    
    apply heapFree; eapply max_lub_l; eauto.
   unfold pw_over.
   rewrite H0.
   apply heapFree; eapply max_lub_r; eauto.
  Qed.

  Definition overwrite (s1 s2 : store) :=
   {|
      heap := pw_over (heap s1) (heap s2);
      stack := pw_over (stack s1) (stack s2);
      heapBound := max (heapBound s1) (heapBound s2);
      heapFree := max_over_bound s1 s2
   |}.

  (* A store with a single heap cell *)
  Definition sngloc (h:Loc*FName) (v:Val) : Loc*FName  -> option Val :=
    fun h' => if Loc_eq_dec  (fst h) (fst h')  then Some v else None.

  (* Bound will be location plus one *)
  Lemma sngloc_bound (h:Loc*FName) (v:Val) : forall (h':Loc*FName), S (fst h)  <= (fst h') -> sngloc h v h' = None.
   intros.
   cbv.
   destruct (Loc_eq_dec (fst h)  (fst h')).
   subst.
   set (Le.le_Sn_n (fst h')).
(*
   contradiction.
   trivial.*)
Admitted.

  Definition slstore h v : store :=
    {| heap :=  sngloc h v;
       stack := fun _ => None;
       heapBound := S (fst h);
       heapFree := sngloc_bound h v
    |}.
  
    (* A store with just a single stack variable *) 
  Definition sngvar (x : Var * TID) (v : Loc) : Var*TID -> option Loc :=
    fun x' => if Var_eq_dec (fst x) (fst x') then Some v else None.

  Definition svstore x v : store :=
   {|
     heap := fun _ => None;
     stack := sngvar x v;
     heapBound := 0;
     heapFree := fun (m : Loc*FName) (_ : 0 <= (fst m)) => eq_refl
   |}.


  