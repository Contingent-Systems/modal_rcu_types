Require Import Language StateTransformerConstructions.
Require Import Tactics.
Require Import Relations SetoidClass.

(* Setoid with extensional equivalence *)
Program Instance extensional_setoid {A B} : Setoid (A -> B).

Lemma fun_equiv {A B} (x y : A -> B) (a : A) : x == y -> x a = y a.
 firstorder.
Qed.

(* pointwise partial function overwriting *)
Definition pw_over {A B} (f1 f2 : A -> option B) (a : A) :=
  match f1 a with
  | Some b => Some b
  | None => f2 a
  end.

Instance pw_over_morphism {A B} : Proper (equiv ==> equiv ==> equiv) (pw_over (A:=A) (B:=B)).
 repeat intro.
 cbv.
 rewrite (H a), (H0 a).
 destruct (y a); reflexivity.
Qed.


(* Heaps -- well actually stores -- are parametrised
   by two types: the type of variables and the type
   of non-address values.  Equality for the former
   must be decidable.
 *)
Module Type HeapTypes.
  Parameter Var Other : Set.
  Axiom Var_eq_dec : forall (x y : Var), {x = y} + {x <> y}.
End HeapTypes.

(* A basic instance of HeapTypes with only one
   non-location value (effectively null)
 *)
Module BasicHeapTypes <: HeapTypes.
  Definition Var := nat.
  Proposition Var_eq_dec : forall (x y : Var), {x = y} + {x <> y}.
   decide equality.
  Qed.
  Definition Other := unit.
End BasicHeapTypes.


Module MHeaps (Import ht : HeapTypes).
  (* Locations are the naturals *)
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
    vars : Var -> option Val;
    heapBound : nat;
    heapFree : forall m, heapBound <= m -> heap m = None
  }.

  Instance store_equivalence : Equivalence 
                                 (fun s1 s2 => heap s1 == heap s2 /\ vars s1 == vars s2).
  intuition; repeat intro. (*rewr.  intuition.*)
  Admitted.

  (* Stores form a setoid *)
  Instance store_setoid : Setoid store :=
   { equiv := fun s1 s2 => heap s1 == heap s2 /\ vars s1 == vars s2 }.

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

  Instance vars_morphism : Proper (equiv ==> equiv) vars.
   repeat intro.
   destruct H.
   rewr trivial.
  Qed.

  Instance vars_morphism2 : Proper (equiv ==> eq ==> eq) vars.
   repeat intro; subst.
   exact (vars_morphism _ _ H y0).
  Qed.

  (* Defining overwriting: use the max of the
     bounds as the new bound.
   *)
  Require Import Arith Max.
(*  Import Max. *)
  Lemma max_over_bound (s1 s2 : store) :
      forall m, max (heapBound s1) (heapBound s2) <= m ->
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
      vars := pw_over (vars s1) (vars s2);
      heapBound := max (heapBound s1) (heapBound s2);
      heapFree := max_over_bound s1 s2
   |}.

  (* A store with just a single variable *)
  Definition sngvar (x : Var) (v : Val) : Var -> option Val :=
    fun x' => if Var_eq_dec x x' then Some v else None.

  Definition svstore x v : store :=
   {|
     heap := fun _ => None;
     vars := sngvar x v;
     heapBound := 0;
     heapFree := fun (m : nat) (_ : 0 <= m) => eq_refl
   |}.

  (* A store with a single heap cell *)
  Definition sngloc (l : Loc) (v : Val) : Loc -> option Val :=
    fun l' => if Loc_eq_dec l l' then Some v else None.

  (* Bound will be location plus one *)
  Lemma sngloc_bound l v : forall l', S l <= l' -> sngloc l v l' = None.
   intros.
   cbv.
   destruct (Loc_eq_dec l l').
   subst.
   set (Le.le_Sn_n l').
   contradiction.
   trivial.
  Qed.

  Definition slstore l v : store :=
    {| heap := sngloc l v;
       vars := fun _ => None;
       heapBound := S l;
       heapFree := sngloc_bound l v |}.

End MHeaps.

(* So we can define functors, we want a type for the
   Heaps module.
 *)
Module Type THeaps (ht : HeapTypes).
  Include (MHeaps ht).
End THeaps.

(* The atomic commands for heap update *)
Module HeapAtomics (Import ht : HeapTypes) (Import hp : THeaps ht) .
  Inductive hAtomic : Set :=
   | hidat : hAtomic
   | assn : Var -> Var -> hAtomic
   | mut_val : Var -> Val -> hAtomic
   | mut_var : Var -> Var -> hAtomic
   | lu_var : Var -> Var -> hAtomic
   | mkref : Var -> Var -> hAtomic.
  Definition Atomic := hAtomic.
End HeapAtomics.

(* Module type for HeapAtomics *)
Module Type THeapAtomics 
    (Import ht : HeapTypes)
    (Import hp : THeaps ht) <: Atomics.
  Include (HeapAtomics ht hp).
End THeapAtomics.

(* StateTransformers instance for the heap commands. *)
Module HeapStateTransformers 
    (Import ht : HeapTypes)
    (Import hp : THeaps ht)
    (Import ha : THeapAtomics ht hp) <: StateTransformers ha.

  Definition idat := hidat.

  (* States are stores or fault *)
  Inductive state : Set :=
    | sOK : store -> state
    | sFAULT : state.

  Definition State := state.

  Definition state_equiv : relation State :=
    fun s1 s2 : state =>
      match s1 with
        | sOK s => match s2 with
           | sOK s0 => s == s0
           | sFAULT => False
           end
        | sFAULT => match s2 with
            | sOK _ => False
            | sFAULT => True
            end
      end.

  Instance state_setoid : Setoid State :=
    {| equiv := state_equiv |}.
   split; repeat intro; unfold state_equiv;
    repeat (match goal with [x : State |- _] => destruct x; simpl in *; intuition end);
    rewr intuition.
  Defined.


  Definition makefp_trans (t : ST (A:=State)) : relation state :=
    fun s s' => match s with
      | sFAULT => s' = sFAULT
      | _ => st_trans t s s'
     end.

  Existing Instance st_morph.

  Instance makefp_morph t : Proper (equiv ==> equiv ==> iff) (makefp_trans t).
   repeat intro.
   destruct x; destruct y; simpl; try rewr intuition.
   destruct x0; destruct y0; intuition; inversion H1.
  Qed.

  Definition STmakefp (t : ST (A:=State)) : ST (A:=State) :=
    {| st_trans := makefp_trans t |}.

  (* Interpretation of atomic commands *)
  Definition interp (a : Atomic) : ST (A:=State) :=
    match a with
    | hidat => stid
    | assn x y => STmakefp (STchoice (fun v => STgchoice (fun s =>
        (vars s y = v, STseq (STeguard (sOK s))
             (STmp match v with
                    | Some vv => sOK (overwrite (svstore x vv) s)
                    | _ => sFAULT
                   end)))))
    | mut_val x v =>
        STmakefp (STchoice (fun l => STgchoice (fun s =>
        (vars s x = l, STseq (STeguard (sOK s))
             (STmp match l with
                    | Some (loc_val ll) =>
                       match heap s ll with
                       | Some _ => sOK (overwrite (slstore ll v) s)
                       | _ => sFAULT end
                    | _ => sFAULT end)))))
    | mut_var x y =>
        STmakefp (STchoice (fun l => STchoice (fun v => (STgchoice (fun s =>
        (vars s x = l /\ vars s y = v, STseq (STeguard (sOK s))
             (STmp match l with
                    | Some (loc_val ll) =>
                       match heap s ll with
                       | Some _ => 
                        match v with
                        | Some vv => sOK (overwrite (slstore ll vv) s)
                        | _ => sFAULT end
                       | _ => sFAULT end
                    | _ => sFAULT end)))))))
    | lu_var y x =>
       STmakefp (STchoice (fun l => STgchoice (fun s =>
        (vars s x = l, STseq (STeguard (sOK s))
            (STmp match l with
                   | Some (loc_val ll) =>
                      match heap s ll with
                      | Some vl => sOK (overwrite (svstore y vl) s)
                      | _ => sFAULT end
                   | _ => sFAULT end)))))
    | mkref x y =>
       STmakefp (STchoice (fun v => STgchoice (fun s =>
        (vars s y = v, STseq (STeguard (sOK s))
            match v with
                   | Some vv => STgchoice (fun l =>
                     (heap s l = None, STmp (sOK
             (overwrite (svstore x (loc_val l)) (overwrite (slstore l vv) s)))))
                   | _ => STmp sFAULT
            end))))
    end.

  (* Identity atomic must have the identity interpretation *)
  Lemma idat_id : st_trans (interp idat) = equiv.
   reflexivity.
  Qed.

End HeapStateTransformers.

Module Type THeapStateTransformers
    (Import ht : HeapTypes)
    (Import hp : THeaps ht)
    (Import ha : THeapAtomics ht hp) <: StateTransformers ha.
Include (HeapStateTransformers ht hp ha).
End THeapStateTransformers.