Require Import SetoidClass.
Require Import MySetoids.

Section Countable.

  Context (A : Type) {A_Setoid : Setoid A}.
  Class Countable := {
    cnt_count :> A -> nat;
    cnt_choose :> nat -> A;
    cnt_inverse1 : forall a, a == cnt_choose (cnt_count a);
    cnt_inverse2 : forall n, n = cnt_count (cnt_choose n)
  }.
  Coercion cnt_count : Countable >-> Funclass.
End Countable.


(*
Program Instance nat_setoid : Setoid nat.
Program Instance nat_count : Countable nat.
*)
Section NatFMap.
  Set Implicit Arguments.
  Context (Codom : Type).
  Record NatFMap := {
    nfm :> nat -> option Codom;
    nfm_bound : nat;
    nfm_bounded : forall a, a > nfm_bound -> nfm a = None
  }.

Require Import Max.


  Program Definition nfm_set (n : nat) (v : Codom) (m : NatFMap) : NatFMap :=
   {| nfm x := if Peano_dec.eq_nat_dec x n then Some v else nfm m x;
      nfm_bound := max n (nfm_bound m) |}.
   Obligation 1.
    remember (Peano_dec.eq_nat_dec a n) as s.
    destruct s; subst.
     contradict H.
     generalize (le_max_l n (nfm_bound m)); intro.
     auto with *.
    
     apply nfm_bounded.
     generalize (le_max_r n (nfm_bound m)); intro.
     unfold gt in *.
     unfold lt in *.
     generalize (Le.le_n_S _ _ H0); intro.
     rewrite H1.
     trivial.
  Qed.
  Definition nfm_fresh (m : NatFMap) := S (nfm_bound m).
  Hint Resolve nfm_bounded.
  Lemma nfm_fresh_is_fresh (m : NatFMap) : nfm m (nfm_fresh m) = None.
   auto.
  Qed.
  Unset Implicit Arguments.
End NatFMap.


Definition CFMap A `{Countable A} codom := NatFMap codom.

Section CountableFiniteMaps.

  Context (A : Type) {A_Setoid : Setoid A} {A_Countable : Countable A}.
  Variable R : Type.
  Set Implicit Arguments.
  Definition cfm : CFMap A R -> A -> option R :=
      fun m a => m (A_Countable a).
  Definition cfm_set (a : A) (v : R) (m : CFMap A R) : CFMap A R :=
      nfm_set (A_Countable a) v m.
  Definition cfm_fresh (m : CFMap A R) : A :=
      (cnt_choose _ (nfm_fresh m)).
  Lemma cfm_fresh_is_fresh (m : CFMap A R) : cfm m (cfm_fresh m) = None.
   cbv [cfm_fresh cfm].
   rewrite <- cnt_inverse2.
   apply nfm_fresh_is_fresh.
  Qed.
  Inductive cfm_def_at (m : CFMap A R) : A -> Prop :=
    | cfm_def_witness : forall a v, Some v = cfm m a -> cfm_def_at m a.
  Definition cfm_make_def_at (m : CFMap A R) (a : A) : option (cfm_def_at m a) :=
   match (cfm m a) as o return (o = cfm m a -> option (cfm_def_at m a)) with
   | Some r => fun H : Some r = cfm m a => Some (cfm_def_witness m a H)
   | None => fun _ => None
   end eq_refl.
  Fixpoint cfm_dom_fold_to
     (m : CFMap A R) (T : Type) (f : T -> forall a, cfm_def_at m a -> T) (o : T) (n : nat) : T :=
    match n with 
    | O => o
    | S n' => let t' := (cfm_dom_fold_to f o n') in
            match (cfm_make_def_at m (cnt_choose A n)) with
            | Some da => f t' (cnt_choose A n) da
            | _ => t' end
            end.
            
  Definition cfm_dom_fold (m : CFMap A R) (T : Type)
     (f : T -> forall a, cfm_def_at m a -> T) (o : T) : T :=
        cfm_dom_fold_to f o (nfm_bound m).
  Definition cfm_def_get (m : CFMap A R) (a : A) (P : cfm_def_at m a) : R.
   remember (cfm m a).
   destruct (o).
    exact r.
    contradict P.
    intro.
    destruct H.
    rewrite <- Heqo in H.
     inversion H.
  Defined.
  
  Section CFMSetoid.
    Context `{R_Setoid : Setoid R}.
    Program Instance cfm_setoid : Setoid (CFMap A R) :=
      {| equiv := fun x y => forall v, cfm x v == cfm y v |}.
    Require Import Tactics.
    Obligation 1.
    (* split; repeat intro;
     use_foralls; rewr auto.*)
    Admitted.
  End CFMSetoid.

End CountableFiniteMaps.