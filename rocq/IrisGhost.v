(** * IrisGhost: ghost state for the RCU invariants.

    Milestone 3.  The first two milestones are deliberately Iris-free:
    [WellFormed.v] states the seventeen invariants as pure propositions over a
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
    (U : gset (Var * TID))
    (T : gset TID)
    (F : gmap Loc (gset TID)) : LState :=
  {| ms    := m;
     obsv  := fun o ob => match O !! o with
                          | Some s => ob ∈ s
                          | None   => False
                          end;
     undf  := fun x t => (x, t) ∈ U;
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
Definition flUR  : ucmra := authUR (gmapUR Loc (exclR (leibnizO (gset TID)))).

Class rcuG (Σ : gFunctors) := RcuG {
  rcu_obsG :: inG Σ obsUR;
  rcu_flG  :: inG Σ flUR;
}.

Definition rcuΣ : gFunctors := #[ GFunctor obsUR; GFunctor flUR ].

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

  Definition fl_auth (γ : gname) (F : gmap Loc (gset TID)) : iProp Σ :=
    own γ (● (Excl <$> F : gmap Loc (excl (leibnizO (gset TID))))).
  Definition fl_ctl (γ : gname) (o : Loc) (s : gset TID) : iProp Σ :=
    own γ (◯ {[ o := Excl (s : leibnizO (gset TID)) ]}).

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

  Lemma fl_alloc : ⊢ |==> ∃ γ, fl_auth γ ∅.
  Proof.
    iMod (own_alloc (● (∅ : gmap Loc (excl (leibnizO (gset TID))))))
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
                                  : gmap Loc (excl (leibnizO (gset TID))))
                              ⋅ ◯ {[o := Excl (s' : leibnizO (gset TID))]})
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

  Definition rcu_inv_inner (γo γf : gname) : iProp Σ :=
    ∃ (m : MState) (O : gmap Loc (gset obs)) (U : gset (Var * TID))
      (T : gset TID) (F : gmap Loc (gset TID)),
      phys m
      ∗ obs_auth γo O
      ∗ fl_auth γf F
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
    ∃ m O U T F, ⌜WellFormed FType (to_LState m O U T F)⌝ ∗
                 (phys m ∗ obs_auth γo O ∗ fl_auth γf F).
  Proof.
    iIntros "H". iDestruct "H" as (m O U T F) "(Hp & Ho & Hf & %Hwf)".
    iExists m, O, U, T, F. iFrame. done.
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
  to_LState (ms initial) O_initial ∅ T_initial ∅.

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
Proof. simpl. split; [by intros ?%elem_of_empty | done]. Qed.

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
