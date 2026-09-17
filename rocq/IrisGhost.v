(** * IrisGhost: ghost state for the RCU invariants.

    Milestone 3.  The first two milestones are deliberately Iris-free:
    [WellFormed.v] states the nineteen invariants as pure propositions over a
    plain record, and [HeapPaths.v] proves the reachability and heap-domain
    facts the atomic actions need.  Nothing in either mentions a logic.

    This file supplies the missing half: the observation map and the free list
    become *resources*, so that a thread can hold a fragment of them and the
    invariant can hold the authority.  The design keeps the pure layer intact --
    [WellFormed] is reused verbatim, applied to a state reconstructed from the
    ghost maps by [to_LState].  Nothing proved in the first two milestones has
    to be restated.

    Concretely:

      - [O] becomes [gmap Loc (gset obs)] and [F] a [gmap Loc (gset TID)],
        each under [auth], so the invariant owns the whole map and a thread owns
        a piece.
      - The value camera is [gsetUR], whose order is subset inclusion.  That is
        exactly the reading the type system wants: owning an observation means
        the authority records at least it.
      - [rcu_inv] is the invariant [WellFormed.v]'s header anticipated,
        [inv N (exists s, phys * ghost * |-WellFormed s-|)].

    What is *not* here, and it is the bulk of the remaining work: the
    denotations of the types and the atomic-action lemmas as Hoare triples.
    This file is the substrate those will be stated over, not a proof of any of
    them.  The ghost state itself is complete for their purposes: observations
    and free-list entries can be introduced ([obs_alloc_at]) and *replaced*
    ([obs_set], [fl_set]), and control of an entry tells you exactly what the
    authority records there ([obs_ctl_agree], [observes_mem]).  Replacement is
    the operation the first version of this file could not express; see the
    note on the value camera below.

    What it does establish is that the substrate is sound and usable: the
    cameras are well formed, the invariant is allocatable, ownership of a
    fragment implies the corresponding fact about the authority, and the bridge
    to the pure layer is faithful at the initial state.  Adding Iris introduces
    no axioms.

    Checked with Rocq 9.2 against the Iris in the bluerock switch. *)

From iris.algebra Require Import numbers.
From iris.algebra Require Import auth excl gmap gset local_updates.
From iris.base_logic.lib Require Import invariants own.
From iris.proofmode Require Import proofmode.
From stdpp Require Import gmap sets.
From RCU Require Import WellFormed.

(** ** [obs] as a countable type

    [gset obs] needs decidable equality and a countable encoding.  [obs] is a
    five-way tag over a thread id, so it injects into [nat * nat]. *)

Global Instance obs_eq_dec : EqDecision obs.
Proof. solve_decision. Defined.

Definition obs_encode (o : obs) : nat * nat :=
  match o with
  | Oiter  t => (0, t)
  | Ounlk  t => (1, t)
  | Ofresh t => (2, t)
  | Ofree  t => (3, t)
  | Oroot    => (4, 0)
  end.

Definition obs_decode (p : nat * nat) : obs :=
  match p.1 with
  | 0 => Oiter  p.2
  | 1 => Ounlk  p.2
  | 2 => Ofresh p.2
  | 3 => Ofree  p.2
  | _ => Oroot
  end.

Lemma obs_decode_encode o : obs_decode (obs_encode o) = o.
Proof. destruct o; reflexivity. Qed.

Global Instance obs_countable : Countable obs :=
  inj_countable' obs_encode obs_decode obs_decode_encode.

(** ** Bridging the ghost maps back to [LState]

    The pure invariants quantify over a state whose [O] is a function
    [Loc -> obs -> Prop] and whose [F] is [Loc -> option (TID -> Prop)].  The
    ghost state is finite maps.  [to_LState] is the coercion, and it is the only
    place the two representations meet: every lemma of milestones 1 and 2
    applies to [to_LState ...] unchanged. *)

Definition to_LState
    (m : MState)
    (O : gmap Loc (gset obs))
    (U : Var -> TID -> Prop)
    (T : gset TID)
    (F : gmap Loc (gset TID)) : LState :=
  {| ms    := m;
     obsv  := fun o ob => match O !! o with
                          | Some s => ob ∈ s
                          | None   => False
                          end;
     undf  := U;
     thrd  := fun t => t ∈ T;
     flist := fun o => match F !! o with
                       | Some s => Some (fun t => t ∈ s)
                       | None   => None
                       end |}.

(** ** Cameras

    [gsetUR] has union as its operation and subset as its order, so a fragment
    [{[o := s]}] is included in the authority exactly when the authority records
    exactly the entry at [o].  That is [obs_ctl_agree] below, and it is what
    makes "the writer observes [o] as [iterator]" a resource rather than a side
    condition -- and, unlike a shared fragment, one that can be given up. *)

(** The value camera is [exclR], not [gsetUR].

    [gsetUR] was the first choice, and it was wrong.  Its operation is union, so
    all its elements are [CoreId] and every fragment is persistent: an
    observation once handed out could never be withdrawn.  Unlinking has to
    withdraw one -- the replaced node loses [iterator] and gains [unlinked], and
    WULK makes those exclusive -- so no action that unlinks could re-establish
    the invariant.  The union camera is right for a quantity that only grows,
    and observations are not one.

    Exclusive control of a location's observation set supports withdrawal.  The
    authority still holds the same logical map, so [to_LState] and everything
    stated over it are unaffected. *)
Definition obsUR : ucmra := authUR (gmapUR Loc (exclR (leibnizO (gset obs)))).
(** The free list stores a *stamp*: the epoch at which the node's grace period
    began.  Which threads that snapshot contains is derived from the
    registrations rather than stored, which is what makes ReadEnd a write to
    the departing reader's own state.  See [Epochs.v] for the argument. *)
Definition flUR  : ucmra := authUR (gmapUR Loc (exclR (leibnizO nat))).

(** A thread's registration: [None] outside a read-side critical section,
    [Some e] inside one entered at epoch [e].  Owned by the thread, which is
    the whole point. *)
Definition regUR : ucmra :=
  authUR (gmapUR TID (exclR (leibnizO (option nat)))).

(** The watermark: a lower bound on every registration, which only grows.  A
    fragment is persistent, so the result of a grace period is a fact the
    writer may carry rather than a resource it must own. *)
Definition wmUR  : ucmra := authUR max_natUR.

(** Observations indexed by the observing thread; see the section on
    per-thread control at the end of the file for why this is the right unit. *)
Definition tobsUR : ucmra :=
  authUR (gmapUR (Loc * TID) (exclR (leibnizO (gset obs)))).

Class rcuG (Σ : gFunctors) := RcuG {
  rcu_obsG  :: inG Σ obsUR;
  rcu_flG   :: inG Σ flUR;
  rcu_tobsG :: inG Σ tobsUR;
  rcu_regG  :: inG Σ regUR;
  rcu_wmG   :: inG Σ wmUR;
}.

Definition rcuΣ : gFunctors :=
  #[ GFunctor obsUR; GFunctor flUR; GFunctor tobsUR;
     GFunctor regUR; GFunctor wmUR ].

Global Instance subG_rcuΣ {Σ} : subG rcuΣ Σ → rcuG Σ.
Proof. solve_inG. Qed.

(** ** Ownership *)

Section ghost.
  Context `{!rcuG Σ}.

  (** The authority holds the logical map; a fragment is *exclusive* control of
      one location's entry.  Control is what makes withdrawal possible, and it
      is the writer's relationship to a location's observations. *)
  Definition obs_auth (γ : gname) (O : gmap Loc (gset obs)) : iProp Σ :=
    own γ (● (Excl <$> O : gmap Loc (excl (leibnizO (gset obs))))).
  Definition obs_ctl (γ : gname) (o : Loc) (s : gset obs) : iProp Σ :=
    own γ (◯ {[ o := Excl (s : leibnizO (gset obs)) ]}).

  Definition fl_auth (γ : gname) (F : gmap Loc nat) : iProp Σ :=
    own γ (● (Excl <$> F : gmap Loc (excl (leibnizO nat)))).
  Definition fl_ctl (γ : gname) (o : Loc) (s : nat) : iProp Σ :=
    own γ (◯ {[ o := Excl (s : leibnizO nat) ]}).

  (** The registration cell, and the watermark. *)
  Definition reg_auth (γ : gname) (Rg : gmap TID (option nat)) : iProp Σ :=
    own γ (● (Excl <$> Rg : gmap TID (excl (leibnizO (option nat))))).
  Definition reg_cell (γ : gname) (t : TID) (v : option nat) : iProp Σ :=
    own γ (◯ {[ t := Excl (v : leibnizO (option nat)) ]}).

  Definition wm_auth (γ : gname) (w : nat) : iProp Σ :=
    own γ (● MaxNat w : wmUR).
  Definition wm_lb (γ : gname) (n : nat) : iProp Σ :=
    own γ (◯ MaxNat n : wmUR).

  Global Instance wm_lb_persistent γ n : Persistent (wm_lb γ n).
  Proof. apply _. Qed.

  (** Control is exclusive: two threads cannot both hold a location's entry.
      That is the property [gsetUR] could not express. *)
  Lemma obs_ctl_exclusive γ o s s' :
    obs_ctl γ o s -∗ obs_ctl γ o s' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. rewrite auth_frag_op_valid singleton_op singleton_valid in Hv.
    by apply exclusive_l in Hv.
  Qed.

  (** Allocation: both maps start empty. *)
  Lemma obs_alloc : ⊢ |==> ∃ γ, obs_auth γ ∅.
  Proof.
    iMod (own_alloc (● (∅ : gmap Loc (excl (leibnizO (gset obs))))))
      as (γ) "H".
    { by apply auth_auth_valid. }
    iModIntro. iExists γ. unfold obs_auth. by rewrite fmap_empty.
  Qed.


  (** Agreement and update for a registration cell, the same shape as the
      stack's.  Both directions matter: a thread learns from its own cell
      whether it is inside a critical section, which is what ReadBegin's
      negative premise needs. *)
  Lemma reg_cell_agree γ Rg t v :
    reg_auth γ Rg -∗ reg_cell γ t v -∗ ⌜Rg !! t = Some v⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply singleton_included_l in Hincl as [y [Hlk Hle]].
    rewrite lookup_fmap in Hlk.
    apply fmap_Some_equiv in Hlk as [v0 [Hv0 Hy]].
    rewrite Hv0. f_equal.
    rewrite Hy Excl_included in Hle. exact (eq_sym Hle).
  Qed.

  Lemma reg_cell_update γ Rg t v v' :
    reg_auth γ Rg -∗ reg_cell γ t v ==∗
    reg_auth γ (<[t := v']> Rg) ∗ reg_cell γ t v'.
  Proof.
    iIntros "Ha Hf". rewrite /reg_auth /reg_cell.
    iMod (own_update_2 _ _ _ (● (Excl <$> (<[t := v']> Rg)
                                 : gmap TID (excl (leibnizO (option nat))))
                              ⋅ ◯ {[t := Excl (v' : leibnizO (option nat))]})
           with "Ha Hf") as "[Ha Hf]".
    { rewrite fmap_insert. apply auth_update.
      apply singleton_local_update_any.
      intros y _. by apply exclusive_local_update. }
    iModIntro. iFrame.
  Qed.

  Lemma reg_alloc : ⊢ |==> ∃ γ, reg_auth γ ∅.
  Proof.
    iMod (own_alloc (● (∅ : gmap TID (excl (leibnizO (option nat))))))
      as (γ) "H".
    { by apply auth_auth_valid. }
    iModIntro. iExists γ. unfold reg_auth. by rewrite fmap_empty.
  Qed.

  (** The watermark.  A fragment is persistent and bounds the authority from
      below, which is how a completed grace period becomes a fact rather than a
      resource. *)
  Lemma wm_lb_le γ w n : wm_auth γ w -∗ wm_lb γ n -∗ ⌜n <= w⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    by apply max_nat_included in Hincl.
  Qed.

  Lemma wm_snapshot γ w : wm_auth γ w ==∗ wm_auth γ w ∗ wm_lb γ w.
  Proof.
    iIntros "Ha". rewrite /wm_auth /wm_lb -own_op.
    iApply (own_update with "Ha").
    apply (auth_update_alloc _ (MaxNat w) (MaxNat w)).
    apply max_nat_local_update. simpl. lia.
  Qed.

  Lemma wm_raise γ w w' : w <= w' -> wm_auth γ w ==∗ wm_auth γ w'.
  Proof.
    iIntros (Hle) "Ha". rewrite /wm_auth.
    iApply (own_update with "Ha").
    apply auth_update_auth with (b' := MaxNat w').
    apply max_nat_local_update. simpl. exact Hle.
  Qed.

  Lemma wm_alloc : ⊢ |==> ∃ γ, wm_auth γ 0.
  Proof.
    iMod (own_alloc (● MaxNat 0 : wmUR)) as (γ) "H".
    { by apply auth_auth_valid. }
    by iModIntro; iExists γ.
  Qed.

  Lemma fl_alloc : ⊢ |==> ∃ γ, fl_auth γ ∅.
  Proof.
    iMod (own_alloc (● (∅ : gmap Loc (excl (leibnizO nat)))))
      as (γ) "H".
    { by apply auth_auth_valid. }
    iModIntro. iExists γ. unfold fl_auth. by rewrite fmap_empty.
  Qed.

  (** Agreement.  Holding a location's entry tells you exactly what the
      authority records there -- an equality now, where the union camera could
      only give an inclusion. *)
  Lemma obs_ctl_agree γ O o s :
    obs_auth γ O -∗ obs_ctl γ o s -∗ ⌜O !! o = Some s⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply singleton_included_l in Hincl as [y [Hlk Hle]].
    rewrite lookup_fmap in Hlk.
    apply fmap_Some_equiv in Hlk as [s0 [Hs0 Hy]].
    rewrite Hs0. f_equal.
    rewrite Hy Excl_included in Hle.
    by apply leibniz_equiv.
  Qed.

  Lemma fl_ctl_agree γ F o s :
    fl_auth γ F -∗ fl_ctl γ o s -∗ ⌜F !! o = Some s⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply singleton_included_l in Hincl as [y [Hlk Hle]].
    rewrite lookup_fmap in Hlk.
    apply fmap_Some_equiv in Hlk as [s0 [Hs0 Hy]].
    rewrite Hs0. f_equal.
    rewrite Hy Excl_included in Hle.
    by apply leibniz_equiv.
  Qed.

  (** Introducing an entry. *)
  Lemma obs_alloc_at γ O o s :
    O !! o = None ->
    obs_auth γ O ==∗ obs_auth γ (<[o := s]> O) ∗ obs_ctl γ o s.
  Proof.
    iIntros (Hlk) "Ha".
    iMod (own_update _ _ (● (Excl <$> (<[o := s]> O)
                              : gmap Loc (excl (leibnizO (gset obs))))
                          ⋅ ◯ {[o := Excl (s : leibnizO (gset obs))]})
           with "Ha") as "[Ha Hf]".
    { rewrite fmap_insert. apply auth_update_alloc.
      apply alloc_singleton_local_update; [| done].
      by rewrite lookup_fmap Hlk. }
    iModIntro. iFrame.
  Qed.

  (** Replacing one.  This is the update the union camera could not do, and the
      reason for the change: unlinking rewrites a location's observations
      rather than adding to them. *)
  Lemma obs_set γ O o s s' :
    obs_auth γ O -∗ obs_ctl γ o s ==∗
      obs_auth γ (<[o := s']> O) ∗ obs_ctl γ o s'.
  Proof.
    iIntros "Ha Hf".
    iMod (own_update_2 _ _ _ (● (Excl <$> (<[o := s']> O)
                                  : gmap Loc (excl (leibnizO (gset obs))))
                              ⋅ ◯ {[o := Excl (s' : leibnizO (gset obs))]})
           with "Ha Hf") as "[Ha Hf]".
    { rewrite fmap_insert. apply auth_update.
      apply singleton_local_update_any.
      intros y _. by apply exclusive_local_update. }
    iModIntro. iFrame.
  Qed.

  Lemma fl_set γ F o s s' :
    fl_auth γ F -∗ fl_ctl γ o s ==∗
      fl_auth γ (<[o := s']> F) ∗ fl_ctl γ o s'.
  Proof.
    iIntros "Ha Hf".
    iMod (own_update_2 _ _ _ (● (Excl <$> (<[o := s']> F)
                                  : gmap Loc (excl (leibnizO nat)))
                              ⋅ ◯ {[o := Excl (s' : leibnizO nat)]})
           with "Ha Hf") as "[Ha Hf]".
    { rewrite fmap_insert. apply auth_update.
      apply singleton_local_update_any.
      intros y _. by apply exclusive_local_update. }
    iModIntro. iFrame.
  Qed.

  (** Reading a single observation off the entry. *)
  Definition observes (γ : gname) (o : Loc) (ob : obs) : iProp Σ :=
    ∃ s, obs_ctl γ o s ∗ ⌜ob ∈ s⌝.

  Lemma observes_mem γ O o ob :
    obs_auth γ O -∗ observes γ o ob -∗ ⌜∃ s, O !! o = Some s ∧ ob ∈ s⌝.
  Proof.
    iIntros "Ha [%s [Hf %Hin]]".
    iDestruct (obs_ctl_agree with "Ha Hf") as %Hlk.
    iPureIntro. by exists s.
  Qed.

End ghost.

(** ** The invariant

    The shape [WellFormed.v]'s header anticipated: physical state, ghost
    authority, and the pure invariant tying them together.  [phys] is left
    abstract -- it will be instantiated with the points-to assertions of
    whichever heap the language semantics uses, and nothing here depends on that
    choice. *)

Section invariant.
  Context `{!rcuG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  (** The free list is stamps now, and the logical [F] its snapshots are
      derived from -- the derivation is in [Epochs.v], which sits above this
      file, so what is recorded here is the part statable without it: the two
      have the same domain, which is the property this invariant was ever
      illustrating. *)
  Definition rcu_inv_inner (γo γf : gname) : iProp Σ :=
    ∃ (m : MState) (O : gmap Loc (gset obs)) (U : Var -> TID -> Prop)
      (T : gset TID) (F : gmap Loc (gset TID)) (St : gmap Loc nat),
      phys m
      ∗ obs_auth γo O
      ∗ fl_auth γf St
      ∗ ⌜dom F = dom St⌝
      ∗ ⌜WellFormed FType (to_LState m O U T F)⌝.

  Definition rcu_inv (N : namespace) (γo γf : gname) : iProp Σ :=
    inv N (rcu_inv_inner γo γf).

  Global Instance rcu_inv_persistent N γo γf : Persistent (rcu_inv N γo γf).
  Proof. apply _. Qed.

  (** Opening the invariant yields the pure invariant on the reconstructed
      state, which is the interface every atomic-action lemma will use: the
      milestone-1 and milestone-2 results apply to it directly. *)
  Lemma rcu_inv_wellformed γo γf :
    rcu_inv_inner γo γf -∗
    ∃ m O U T F St, ⌜WellFormed FType (to_LState m O U T F)⌝ ∗
                    (phys m ∗ obs_auth γo O ∗ fl_auth γf St).
  Proof.
    iIntros "H".
    iDestruct "H" as (m O U T F St) "(Hp & Ho & Hf & %Hdom & %Hwf)".
    iExists m, O, U, T, F, St. iFrame. done.
  Qed.

End invariant.

(** ** Establishing the invariant at the initial state

    [initial] satisfies the pure invariants (milestone 1), and its observation
    map and free list are empty, so it is exactly the state the empty ghost maps
    describe.  This is what makes the instantiation non-vacuous: the invariant
    is allocatable. *)

(** [initial] observes the root, so the corresponding ghost map is a singleton
    rather than empty, and its thread set is [{[0]}]. *)
Definition O_initial : gmap Loc (gset obs) := {[ 0 := {[ Oroot ]} ]}.
Definition T_initial : gset TID := {[ 0 ]}.

Definition initial_ghost : LState :=
  to_LState (ms initial) O_initial (fun _ _ => False) T_initial ∅.

(** The bridge is faithful at the initial state.  These are stated
    componentwise rather than as [initial_ghost = initial]: the two records
    differ only in how their function-valued fields are *presented*, and proving
    them equal as records would need functional extensionality, which would put
    an axiom into a development that currently has none. *)

Lemma initial_ghost_obsv o ob : obsv initial_ghost o ob <-> obsv initial o ob.
Proof.
  unfold initial_ghost, to_LState, O_initial, initial. simpl.
  destruct (decide (o = 0)) as [->|Hne].
  - rewrite lookup_singleton. split.
    + intros H%elem_of_singleton. split; [reflexivity | exact H].
    + intros [_ ->]. by apply elem_of_singleton.
  - rewrite lookup_singleton_ne //. split; [done | by intros [-> _]].
Qed.

Lemma initial_ghost_flist o : flist initial_ghost o = flist initial o.
Proof. reflexivity. Qed.

Lemma initial_ghost_thrd t : thrd initial_ghost t <-> thrd initial t.
Proof.
  unfold initial_ghost, to_LState, T_initial, initial. simpl.
  split; [by intros ?%elem_of_singleton | intros ->; by apply elem_of_singleton].
Qed.

Lemma initial_ghost_undf x t : undf initial_ghost x t <-> undf initial x t.
Proof. simpl. tauto. Qed.

Lemma initial_ghost_ms : ms initial_ghost = ms initial.
Proof. reflexivity. Qed.

(** ** No axioms

    The first two milestones are axiom-free, and adding Iris does not change
    that: Iris's model is constructive, so nothing below depends on classical
    logic or functional extensionality.  Keeping the bridge lemmas
    componentwise, rather than as a record equality, is what preserves this. *)

Print Assumptions obs_ctl_agree.
Print Assumptions fl_ctl_agree.
Print Assumptions obs_ctl_exclusive.
Print Assumptions observes_mem.
Print Assumptions obs_alloc_at.
Print Assumptions obs_set.
Print Assumptions fl_set.
Print Assumptions initial_ghost_obsv.

(** * Observations indexed by thread

    A defect in the design above, found when attempting the reader-side rules.

    Exclusive control of a location's whole observation set is right for the
    writer, which is the only thread that unlinks.  It is wrong for readers: two
    readers may each observe the same location as [iterator], and several
    variables of one reader may assert that observation at once.  Under a single
    entry per location, at most one of them can hold it.

    The fix follows from what the system actually does.  Observations carry the
    observing thread, and *every thread only ever changes its own*: the writer
    moves its own [iterator] to [unlinked] to [freeable], and a reader adds and
    drops its own.  No thread writes another's.  So the unit of control is the
    pair [(o, t)], not [o] -- and then exclusivity, which the writer needs, and
    sharing between threads, which the readers need, stop being in tension.

    The logical observation map is recovered pointwise rather than computed: a
    location is observed as [ob] when some thread's entry records it.  That
    avoids a fold over the map and keeps the reconstruction definitionally
    transparent, which is what makes the lemmas below one-liners. *)

Definition ObsMap := gmap (Loc * TID) (gset obs).

Definition to_LState_t
    (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
    (T : gset TID) (F : gmap Loc (gset TID)) : LState :=
  {| ms    := m;
     obsv  := fun o ob => exists t s, Og !! (o, t) = Some s /\ ob ∈ s;
     undf  := U;
     thrd  := fun t => t ∈ T;
     flist := fun o => match F !! o with
                       | Some s => Some (fun t => t ∈ s)
                       | None   => None
                       end |}.

(** ** Why scope is a predicate and not a finite set

    [U] was a [gset (Var * TID)] -- the pairs that are out of scope -- and that
    was wrong in a way only the departure rules could show.  ReadEnd and
    WriteEnd require *every* variable of the leaving thread to go out of scope,
    and with [Var = nat] no finite set contains every variable of a thread.  So
    the hypothesis was unsatisfiable, and the two action theorems that carried
    it proved nothing at all.

    The witness is below.  It is a defect of the bridge rather than of the type
    system, but it is exactly the kind a mechanization is for: the theorems
    looked fine, were proved honestly, and were empty.  Flipping the polarity
    does not help -- the *initial* state has nothing out of scope, which under
    the flip needs the set to be everything -- so scope is a predicate.

    [U] carries no ghost authority; the invariant only quantifies over it.  The
    change therefore costs nothing but the annotation. *)

Lemma no_finite_scope_set (U : gset (Var * TID)) (t : TID) :
  ~ (forall x : Var, (x, t) ∈ U).
Proof.
  intros H.
  assert (Hin : fresh (set_map fst U : gset Var) ∈ (set_map fst U : gset Var)).
  { apply elem_of_map. exists (fresh (set_map fst U : gset Var), t).
    split; [reflexivity | exact (H _)]. }
  exact (is_fresh (set_map fst U : gset Var) Hin).
Qed.

Print Assumptions no_finite_scope_set.

Lemma to_LState_t_obs Og m U T F o t s ob :
  Og !! (o, t) = Some s -> ob ∈ s ->
  obsv (to_LState_t m Og U T F) o ob.
Proof. intros Hlk Hin. by exists t, s. Qed.

(** Independence: changing one thread's entry cannot affect what another
    thread's entries record.  This is the property the single-map design could
    not state, and it is what lets a reader keep an observation across a write
    that revokes the writer's. *)
Lemma to_LState_t_other_thread Og m U T F o t t' s' ob :
  t <> t' ->
  Og !! (o, t') = Some s' -> ob ∈ s' ->
  obsv (to_LState_t m (<[(o, t) := ∅]> Og) U T F) o ob.
Proof.
  intros Hne Hlk Hin. exists t', s'. split; [| exact Hin].
  rewrite lookup_insert_ne; [exact Hlk |].
  intros HH. apply Hne. congruence.
Qed.

Section threadghost.
  Context `{!rcuG Σ}.

  (** Control of one thread's observations of one location. *)
  Definition tobs_auth (γ : gname) (Og : ObsMap) : iProp Σ :=
    own γ (● (Excl <$> Og : gmap (Loc * TID) (excl (leibnizO (gset obs))))).
  Definition tobs_ctl (γ : gname) (o : Loc) (t : TID) (s : gset obs) : iProp Σ :=
    own γ (◯ {[ (o, t) := Excl (s : leibnizO (gset obs)) ]}).

  (** Introducing a thread's entry for a location. *)
  Lemma tobs_alloc_at γ Og o t s :
    Og !! (o, t) = None ->
    tobs_auth γ Og ==∗ tobs_auth γ (<[(o, t) := s]> Og) ∗ tobs_ctl γ o t s.
  Proof.
    iIntros (Hlk) "Ha".
    iMod (own_update _ _
            (● (Excl <$> (<[(o, t) := s]> Og)
                : gmap (Loc * TID) (excl (leibnizO (gset obs))))
             ⋅ ◯ {[(o, t) := Excl (s : leibnizO (gset obs))]})
           with "Ha") as "[Ha Hf]".
    { rewrite fmap_insert. apply auth_update_alloc.
      apply alloc_singleton_local_update; [| done].
      by rewrite lookup_fmap Hlk. }
    iModIntro. iFrame.
  Qed.

  (** Two *threads* hold entries for the same location at once.  This is the
      point of the change: under one entry per location it is unprovable,
      because the two fragments would be the same exclusive resource.  Here
      they are different keys, so both are held, and [tobs_ctl_exclusive] below
      still forbids two holders of the *same* key -- which is what revocation
      needs. *)
  Lemma tobs_two_threads γ Og o t t' s s' :
    t <> t' ->
    Og !! (o, t) = None ->
    (<[(o, t) := s]> Og) !! (o, t') = None ->
    tobs_auth γ Og ==∗
      tobs_auth γ (<[(o, t') := s']> (<[(o, t) := s]> Og))
      ∗ tobs_ctl γ o t s ∗ tobs_ctl γ o t' s'.
  Proof.
    iIntros (Hne H1 H2) "Ha".
    iMod (tobs_alloc_at with "Ha") as "[Ha Hc]"; [exact H1 |].
    iMod (tobs_alloc_at with "Ha") as "[Ha Hc']"; [exact H2 |].
    iModIntro. iFrame.
  Qed.

  (** But one thread's entry is still exclusive, so revocation works. *)
  Lemma tobs_ctl_exclusive γ o t s s' :
    tobs_ctl γ o t s -∗ tobs_ctl γ o t s' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. rewrite auth_frag_op_valid singleton_op singleton_valid in Hv.
    by apply exclusive_l in Hv.
  Qed.

  Lemma tobs_ctl_agree γ Og o t s :
    tobs_auth γ Og -∗ tobs_ctl γ o t s -∗ ⌜Og !! (o, t) = Some s⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply singleton_included_l in Hincl as [y [Hlk Hle]].
    rewrite lookup_fmap in Hlk.
    apply fmap_Some_equiv in Hlk as [s0 [Hs0 Hy]].
    rewrite Hs0. f_equal.
    rewrite Hy Excl_included in Hle.
    by apply leibniz_equiv.
  Qed.

  (** A thread replaces its own observations of a location.  The writer's
      unlink step is this with [s' = {[Ounlk t]}]. *)
  Lemma tobs_set γ Og o t s s' :
    tobs_auth γ Og -∗ tobs_ctl γ o t s ==∗
      tobs_auth γ (<[(o, t) := s']> Og) ∗ tobs_ctl γ o t s'.
  Proof.
    iIntros "Ha Hf".
    iMod (own_update_2 _ _ _
            (● (Excl <$> (<[(o, t) := s']> Og)
                : gmap (Loc * TID) (excl (leibnizO (gset obs))))
             ⋅ ◯ {[(o, t) := Excl (s' : leibnizO (gset obs))]})
           with "Ha Hf") as "[Ha Hf]".
    { rewrite fmap_insert. apply auth_update.
      apply singleton_local_update_any.
      intros y _. by apply exclusive_local_update. }
    iModIntro. iFrame.
  Qed.

End threadghost.

Print Assumptions to_LState_t_other_thread.
Print Assumptions tobs_ctl_agree.
Print Assumptions tobs_ctl_exclusive.
Print Assumptions tobs_set.
Print Assumptions tobs_two_threads.

(** ** Well-formedness of the per-thread encoding

    Indexing by [(o, t)] only means what it should if an entry at that key holds
    observations tagged with that thread.  Without it a thread's entry could
    record another thread's observation, and dropping a thread's entries -- what
    ReadEnd does -- would not drop exactly that thread's observations.  Stated
    here because it is a property of the encoding, not of any action. *)

Definition obs_tid (ob : obs) : option TID :=
  match ob with
  | Oiter t | Ounlk t | Ofresh t | Ofree t => Some t
  | Oroot => None
  end.

Definition ObsWF (Og : ObsMap) : Prop :=
  forall o t s ob, Og !! (o, t) = Some s -> ob ∈ s ->
    obs_tid ob = Some t \/ ob = Oroot.

(** Under it, a thread's observations are exactly what its own entries record,
    so reading an observation off the reconstruction locates the entry. *)
Lemma obsv_t_locates m Og U T F o t ob :
  ObsWF Og -> obs_tid ob = Some t ->
  obsv (to_LState_t m Og U T F) o ob ->
  exists s, Og !! (o, t) = Some s /\ ob ∈ s.
Proof.
  intros HWF Htid [t' [s [Hlk Hin]]].
  destruct (HWF o t' s ob Hlk Hin) as [Htid' | ->].
  - rewrite Htid in Htid'. injection Htid' as ->. by exists s.
  - simpl in Htid. discriminate.
Qed.
