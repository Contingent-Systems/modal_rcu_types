(** * Reclamation, abstracted: is any of this RCU-specific?

    Milestone 6, and it is an experiment rather than a repair.

    [Oiter t] means ``thread [t] has announced it may access [o]''.  That is
    what a hazard pointer *is*, and the question this file settles is whether
    the memory-safety argument built on it knows anything about grace periods.

    The prior was strong and is worth stating, because it makes the experiment
    cheap to evaluate: the whole safety argument in [Denotations.v] ---
    [freeable_is_unobserved] and [no_live_reference_to_a_freeable_node] --- uses
    exactly two of the twenty invariants, IFL and RWOW, and neither of those two
    theorems mentions a grace period.  RWOW does not mention reclamation at all.
    IFL does, and only through the free list: it says a thread that has
    announced a node is in that node's entry.

    So the experiment is to replace ``is in that node's free-list entry'' with
    an abstract ``has announced that node'' and see what breaks.  Nothing does.
    What comes out is that the safety argument is *parametric in the
    reclamation discipline*: it needs an announcement relation, an invariant
    saying observations are announced, and a guard meaning nothing is announced
    --- three lines --- and RCU and hazard pointers are two instances of it.

    That is a result about scope.  It says the twenty invariants are not
    twenty facts about RCU; they are facts about an announce-then-reclaim
    structure, of which RCU's grace period is one way to decide the guard.

    Checked with Rocq 9.2, axiom-free. *)

From stdpp Require Import gmap sets.
From RCU Require Import WellFormed HeapPaths Denotations.

(** ** How much of the invariant is about reclamation at all

    Before abstracting the discipline it is worth knowing how much of the
    system it touches, and the sharpest way to say that is mechanically: change
    the free list to *anything* and see which invariants survive.  An invariant
    that survives an arbitrary rewrite of [flist] does not constrain the free
    list, and so cannot be about the grace period.

    Twenty-one of the twenty-six conjuncts survive, and the proof of each is
    [exact].  That is the point: they are not preserved by an argument, they
    are unchanged, because the free list does not occur in them. *)

Definition swap_flist (s : LState) (fl : Loc -> option (TID -> Prop)) : LState :=
  {| ms := ms s; obsv := obsv s; undf := undf s; thrd := thrd s; flist := fl |}.

Theorem free_list_is_local FType s fl :
  (OW FType s -> OW FType (swap_flist s fl))
  /\ (RWOW s -> RWOW (swap_flist s fl))
  /\ (AWRT s -> AWRT (swap_flist s fl))
  /\ (ULKR s -> ULKR (swap_flist s fl))
  /\ (WULK s -> WULK (swap_flist s fl))
  /\ (FR s -> FR (swap_flist s fl))
  /\ (WFresh s -> WFresh (swap_flist s fl))
  /\ (FNR s -> FNR (swap_flist s fl))
  /\ (FPI FType s -> FPI FType (swap_flist s fl))
  /\ (WNR s -> WNR (swap_flist s fl))
  /\ (RITR s -> RITR (swap_flist s fl))
  /\ (HD s -> HD (swap_flist s fl))
  /\ (UNQRT_a s -> UNQRT_a (swap_flist s fl))
  /\ (UNQRT_b s -> UNQRT_b (swap_flist s fl))
  /\ (WUNLK s -> WUNLK (swap_flist s fl))
  /\ (WITR s -> WITR (swap_flist s fl))
  /\ (UNQR s -> UNQR (swap_flist s fl))
  (* and four of the six this development added *)
  /\ (BR s -> BR (swap_flist s fl))
  /\ (WUNLKW s -> WUNLKW (swap_flist s fl))
  /\ (WFreshW s -> WFreshW (swap_flist s fl))
  /\ (FRW s -> FRW (swap_flist s fl)).
Proof. repeat apply conj; intros H; exact H. Qed.

Print Assumptions free_list_is_local.

(** And the five that do not survive are exactly the five that mention the free
    list: IFL, FLR, RINFL, and the added FLD and SameSnap.  One witness does for
    all five --- a state with an announced node, one edge, and no entries at
    all, in which every one of them holds vacuously, together with a rewrite of
    the free list that breaks each. *)

Definition ann_ms : MState :=
  {| stk := fun _ _ => None;
     hp  := fun o _ => if Nat.eqb o 3 then Some (VLoc 0%nat) else None;
     lk  := None;
     rt  := 0%nat;
     rds := fun t => t = 1%nat;
     bnd := fun _ => False |}.

Definition ann_s : LState :=
  {| ms    := ann_ms;
     obsv  := fun o ob => o = 0%nat /\ ob = Oiter 1%nat;
     undf  := fun _ _ => True;
     thrd  := fun _ => True;
     flist := fun _ => None |}.

(* the rewrite: the announced node gets an entry that does not contain the
   thread that announced it, a second node gets a different entry, and the node
   pointing at the first gets none *)
Definition ann_fl (o : Loc) : option (TID -> Prop) :=
  if Nat.eqb o 0 then Some (fun t => t = 2%nat)
  else if Nat.eqb o 1 then Some (fun _ => False)
  else None.

Definition ann_s' : LState := swap_flist ann_s ann_fl.

Theorem free_list_is_not_local :
  (IFL ann_s /\ ~ IFL ann_s')
  /\ (FLR ann_s /\ ~ FLR ann_s')
  /\ (RINFL ann_s /\ ~ RINFL ann_s')
  /\ (FLD ann_s /\ ~ FLD ann_s')
  /\ (SameSnap ann_s /\ ~ SameSnap ann_s').
Proof.
  assert (Hfl : forall o, flist ann_s o = None) by reflexivity.
  assert (H0 : flist ann_s' 0%nat = Some (fun t => t = 2%nat)) by reflexivity.
  assert (H1 : flist ann_s' 1%nat = Some (fun _ : TID => False))
    by reflexivity.
  assert (H3 : flist ann_s' 3%nat = None) by reflexivity.
  assert (He : Edge ann_s' 3%nat 0%nat 0%nat) by reflexivity.
  assert (Hob : obsv ann_s' 0%nat (Oiter 1%nat)) by (by split).
  repeat apply conj.
  - intros t o Tr _ Hc. by rewrite Hfl in Hc.
  - intros H. pose proof (H 1%nat 0%nat _ Hob H0) as Hc. discriminate.
  - intros o o' f' Tr Hc. by rewrite Hfl in Hc.
  - intros H. destruct (H 0%nat 3%nat 0%nat _ H0 He) as [Tr' [Hc _]].
    by rewrite H3 in Hc.
  - intros o Tr t Hc. by rewrite Hfl in Hc.
  - intros H. exact (H 0%nat _ 2%nat H0 eq_refl).
  - intros o Tr Hc. by rewrite Hfl in Hc.
  - intros H. destruct (H 0%nat _ H0) as [t [Hc | Hc]];
      by destruct Hc as [_ Hc].
  - intros a b Ta Tb Hc. by rewrite Hfl in Hc.
  - intros H. exact (proj1 (H 0%nat 1%nat _ _ H0 H1 2%nat) eq_refl).
Qed.

Print Assumptions free_list_is_not_local.

(** ** The discipline, abstracted

    Three components and two conditions.  [d_ann] is ``thread [t] has announced
    it may access [o]'' and [d_free] is ``[o] may be reclaimed''; the two
    conditions are that an observation is announced, and that the guard means
    nothing is announced.  That is the entire interface the safety argument
    uses. *)

Record Discipline := {
  d_ann  : LState -> Loc -> TID -> Prop;
  d_free : LState -> Loc -> Prop;
}.

Definition Announced (D : Discipline) (s : LState) : Prop :=
  forall t o, obsv s o (Oiter t) -> d_ann D s o t.

Definition Retires (D : Discipline) (s : LState) : Prop :=
  forall o, d_free D s o -> forall t, ~ d_ann D s o t.

(** \frbl{}'s denotation with the grace period abstracted away.  Everything but
    the last conjunct is unchanged from [D_freeable]; the last conjunct is the
    discipline's guard in place of ``the free-list entry is empty''. *)
Definition D_freeable_at (D : Discipline) (s : LState) (t : TID) (x : Var)
  : Prop :=
  exists o,
    stk (ms s) x t = Some o
    /\ obsv s o (Ofree t)
    /\ lk (ms s) = Some t
    /\ ~ undf s x t
    /\ d_free D s o.

(** ** The safety argument, re-proved against it

    These are [freeable_is_unobserved] and
    [no_live_reference_to_a_freeable_node] with IFL replaced by [Announced] and
    the free-list conjunct replaced by [Retires].  The proofs are the same
    proofs; what has gone is every mention of a free list. *)

Theorem reclaim_unobserved D s t x o :
  Announced D s -> Retires D s -> D_freeable_at D s t x ->
  stk (ms s) x t = Some o ->
  forall t', ~ obsv s o (Oiter t').
Proof.
  intros Hann Hret (o0 & Hstk & _ & _ & _ & Hfree) Hd t' Hit.
  rewrite Hd in Hstk. injection Hstk as <-.
  exact (Hret o Hfree t' (Hann t' o Hit)).
Qed.

Theorem reclaim_no_live_reference D s tw x o :
  Announced D s -> Retires D s -> RWOW s ->
  D_freeable_at D s tw x -> stk (ms s) x tw = Some o ->
  forall y t', t' <> tw -> stk (ms s) y t' = Some o -> ~ undf s y t' -> False.
Proof.
  intros Hann Hret HRWOW Hfree Hd y t' Hne Hy Hnu.
  destruct (HRWOW y t' o Hy Hnu) as [Hit | [Hlk' _]].
  - exact (reclaim_unobserved D s tw x o Hann Hret Hfree Hd t' Hit).
  - apply Hne.
    destruct Hfree as (o0 & _ & _ & Hlk & _). rewrite Hlk in Hlk'.
    by injection Hlk' as <-.
Qed.

Print Assumptions reclaim_unobserved.
Print Assumptions reclaim_no_live_reference.

(** ** RCU is one instance

    The announcement relation is ``[t] is in [o]'s free-list entry'' and the
    guard is ``[o]'s entry is empty''.  [Announced] at this instance is
    IFL, and [Retires] needs nothing at all: the free list is a function, so an
    entry cannot be both empty and contain someone. *)

Definition RCU : Discipline :=
  {| d_ann  := fun s o t => forall Tr, flist s o = Some Tr -> Tr t;
     d_free := fun s o => exists Tr, flist s o = Some Tr /\ forall t, ~ Tr t |}.

(** The vacuous case is the right one and worth a word: a node with no entry is
    not being reclaimed, so the discipline owes every thread a wait for it, and
    [d_ann] is trivially true there.  With that, [Announced] at this instance is
    IFL, up to the order of its arguments. *)
Lemma rcu_Announced s : IFL s <-> Announced RCU s.
Proof.
  split.
  - intros HIFL t o Hit Tr Hfl. exact (HIFL t o Tr Hit Hfl).
  - intros Hann t o Tr Hit Hfl. exact (Hann t o Hit Tr Hfl).
Qed.

Lemma rcu_Retires s : Retires RCU s.
Proof.
  intros o [Tr [Hfl Hemp]] t Hann. exact (Hemp t (Hann Tr Hfl)).
Qed.

Lemma rcu_freeable s t x : D_freeable s t x <-> D_freeable_at RCU s t x.
Proof.
  split; intros (o & Hstk & Hfr & Hlk & Hnu & Hrest); exists o;
    repeat apply conj; assumption.
Qed.

(** And the original theorem falls out, which is the check that the abstraction
    did not weaken anything. *)
Corollary rcu_no_live_reference s tw x o :
  IFL s -> RWOW s -> D_freeable s tw x -> stk (ms s) x tw = Some o ->
  forall y t', t' <> tw -> stk (ms s) y t' = Some o -> ~ undf s y t' -> False.
Proof.
  intros HIFL HRWOW Hfree Hd.
  exact (reclaim_no_live_reference RCU s tw x o
           (proj1 (rcu_Announced s) HIFL) (rcu_Retires s) HRWOW
           (proj1 (rcu_freeable s tw x) Hfree) Hd).
Qed.

Print Assumptions rcu_Announced.
Print Assumptions rcu_no_live_reference.

(** ** Hazard pointers are the other

    A hazard-pointer scheme gives each thread a set of announced locations, and
    reclaims a node when no thread's set contains it.  The announcement
    relation is set membership and the guard is its negation, so [Retires]
    holds by construction; [Announced] is the invariant the scheme maintains by
    publishing before dereferencing, and it is IFL's exact analogue with the
    indices swapped --- IFL puts the *thread* in the node's entry, this puts
    the *node* in the thread's set.

    Nothing here mentions a grace period, an epoch, a bounding set or a
    quiescent state. *)

Definition HP (ann : TID -> gset Loc) : Discipline :=
  {| d_ann  := fun _ o t => o ∈ ann t;
     d_free := fun _ o => forall t, o ∉ ann t |}.

Lemma hp_Retires ann s : Retires (HP ann) s.
Proof. intros o Hfree t Hin. exact (Hfree t Hin). Qed.

(** The announcement invariant, written out: what a thread observes, it has
    published. *)
Definition Publishes (ann : TID -> gset Loc) (s : LState) : Prop :=
  forall t o, obsv s o (Oiter t) -> o ∈ ann t.

Lemma hp_Announced ann s : Publishes ann s <-> Announced (HP ann) s.
Proof. reflexivity. Qed.

Theorem hp_no_live_reference ann s tw x o :
  Publishes ann s -> RWOW s ->
  D_freeable_at (HP ann) s tw x -> stk (ms s) x tw = Some o ->
  forall y t', t' <> tw -> stk (ms s) y t' = Some o -> ~ undf s y t' -> False.
Proof.
  intros Hpub HRWOW Hfree Hd.
  exact (reclaim_no_live_reference (HP ann) s tw x o Hpub (hp_Retires ann s)
           HRWOW Hfree Hd).
Qed.

Print Assumptions hp_Retires.
Print Assumptions hp_no_live_reference.

(** ** What the experiment settled

    The safety argument is reclamation-agnostic.  It needs an announcement
    relation, the invariant that observations are announced, and a guard
    meaning nothing is announced; RCU decides that guard with a grace period
    and hazard pointers decide it with a scan, and the argument does not know
    which.  Of the twenty-six conjuncts the development carries, twenty-one do
    not constrain the free list at all --- [free_list_is_local], whose proof is
    twenty-one [exact]s --- and of the five that do, the safety argument uses
    one, IFL, and uses it only through the announcement interface.

    Two cautions, because the result is easy to overstate.

    First, this is the *safety* argument, not the whole system.  The five
    free-list invariants are doing real work elsewhere: FLR and SameSnap are
    what discharge the reader's read (\texttt{read\_bound}), FLD is what
    SyncStart needs, and RINFL ties the entries to the bounding set.  A
    hazard-pointer system would need analogues of those or would have to do
    without the rules that use them.

    Second, what carries over is the argument, not the implementation.  Hazard
    pointers have their own hard part --- the announcement has to be published
    before the dereference and re-validated after, which is a memory-ordering
    obligation this development does not model, being sequentially consistent.
    [Publishes] is stated as an invariant of the logical state and is therefore
    exactly the thing a weak-memory account would have to earn.  That is the
    next file, not this one. *)
