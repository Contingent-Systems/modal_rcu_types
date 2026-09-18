(** * Triples: the heap in the invariant.

    An experiment, and a small one on purpose.

    [Compose.v] shows that the published composition operator does not preserve
    WellFormed, and the reason is that every view carries a copy of the whole
    heap.  Patching the operator and the rely gives a single-writer proof whose
    structure does not survive more than one writer: with several mutators, every
    write must be absorbed by every frame, and the rely degenerates to "somebody
    did something that preserved the invariants".

    The alternative this file tests is the one [IrisGhost.v] was already built
    for: put the heap in the invariant rather than in the views.  Then

      - composition is on the ghost state only -- observations and the free
        list -- which is genuinely separating, so the counterexample cannot be
        written down;
      - framing is Iris framing, with no bespoke partial commutative monoid and
        no hand-rolled interference relation;
      - and the atomic-action lemmas are exactly the obligation to re-establish
        the invariant before closing it.

    The last point is what is being tested.  If the action lemmas plug in, the
    architecture carries them; if they need reshaping, better to find out on one
    action than on fifteen.  Free is the one to try: it has no type denotations,
    so nothing outside this file is assumed.

    Checked with Rocq 9.2, axiom-free. *)

From iris.algebra Require Import auth gmap gset excl local_updates.
From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants own.
From iris.proofmode Require Import proofmode.
From stdpp Require Import gmap sets.
From RCU Require Import WellFormed HeapPaths IrisGhost Denotations Actions
                        Epochs.

(** ** Deleting a free-list entry

    Free removes the reclaimed node's entry, which the ghost layer could not
    previously express: [fl_set] replaces an entry, and there was no way to drop
    one.  Exclusive control of the entry is what makes the deletion legal. *)

Section ghost_delete.
  Context `{!rcuG Σ}.

  Lemma fl_delete γ F d s :
    fl_auth γ F -∗ fl_ctl γ d s ==∗ fl_auth γ (delete d F).
  Proof.
    iIntros "Ha Hc". unfold fl_auth, fl_ctl. rewrite fmap_delete.
    iMod (own_update_2 with "Ha Hc") as "Hr".
    { apply auth_update.
      apply (delete_local_update _ _ d (Excl (s : leibnizO nat))).
      by rewrite lookup_singleton_eq. }
    iDestruct "Hr" as "[Hr _]". by iModIntro.
  Qed.

End ghost_delete.

(** ** The invariant, in the per-thread encoding

    [rcu_inv] of [IrisGhost.v] uses the location-keyed observation map.  The
    per-thread one is the right encoding, for the reason the mutation rules
    exposed: unlinking revokes *the writer's* iterator observation and must
    leave a reader's alone, which a location-keyed map cannot express.  So the
    invariant here holds [tobs_auth].

    It also carries [ObsWF], that an entry at [(o,t)] records only observations
    of [t] or the anonymous [root].  That is a property of the encoding rather
    than of the structure, and the unlink step needs it: to know that revoking
    the writer's entry leaves no iterator of the writer's anywhere else.

    And it carries [FLD], that a free-list entry implies the node is detached.
    That is not a property of the encoding but a missing invariant -- see
    [free_list_domain_is_unconstrained] -- and it is carried here rather than
    inside [WellFormed] for the reason given there.  It earns its place twice:
    \textsc{SyncStart} cannot re-establish "exactly the detached nodes" without
    it, and it is what lets a thread holding an iterator on a node conclude the
    node has no free-list entry, which is a premise of the unlinking rules and
    the only *negative* fact about shared state any of them needs.

    And it carries [WFreshW], that a [fresh] observation belongs to the lock
    holder.  That is what WFresh was supposed to say and does not -- see
    [fresh_observations_need_not_be_the_writers] -- and the linking rules need
    it, to know that the fresh node they are about to publish is observed by
    nobody else.  Like FLD it is carried here rather than inside [WellFormed],
    for the same reason.

    The last conjunct is the type environment showing up as an invariant.  The
    unlinking rules need to know that no \frsh{} reference anywhere points at
    the node being unlinked, and no fragment can say that: it is a statement
    about every fresh node in the system, and a fragment says what is, never
    what is absent everywhere.  What the invariant records instead is that the
    fresh nodes are *enumerated* -- every location observed fresh is in the set
    [Fr], whose authority the invariant holds.  A thread holding the matching
    fragment then knows the enumeration, and if it also holds those nodes'
    cells, it knows their contents.  The premise becomes a property of resources
    the thread owns, which is what translating a type environment into
    separation logic means. *)

(** The fresh set: an exclusive authoritative [gset Loc].  The invariant holds
    the authority, the writer the fragment, so the writer *knows* the set. *)
Definition frUR : cmra := excl_authR (leibnizO (gset Loc)).

Class freshG (Σ : gFunctors) := FreshG { fresh_inG :: inG Σ frUR }.
Definition freshΣ : gFunctors := #[ GFunctor frUR ].
Global Instance subG_freshΣ {Σ} : subG freshΣ Σ -> freshG Σ.
Proof. solve_inG. Qed.

Section freshghost.
  Context `{!freshG Σ}.

  Definition fr_auth (γ : gname) (Fr : gset Loc) : iProp Σ :=
    own γ (●E (Fr : leibnizO (gset Loc))).
  Definition fr_frag (γ : gname) (Fr : gset Loc) : iProp Σ :=
    own γ (◯E (Fr : leibnizO (gset Loc))).

  Global Instance fr_auth_timeless γ Fr : Timeless (fr_auth γ Fr).
  Proof. apply _. Qed.
  Global Instance fr_frag_timeless γ Fr : Timeless (fr_frag γ Fr).
  Proof. apply _. Qed.

  Lemma fr_agree γ Fr Fr' :
    fr_auth γ Fr -∗ fr_frag γ Fr' -∗ ⌜Fr = Fr'⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro. exact (excl_auth_agree _ _ Hv).
  Qed.

  Lemma fr_update γ Fr Fr' Fr'' :
    fr_auth γ Fr -∗ fr_frag γ Fr' ==∗ fr_auth γ Fr'' ∗ fr_frag γ Fr''.
  Proof.
    iIntros "Ha Hf". rewrite /fr_auth /fr_frag.
    iMod (own_update_2 with "Ha Hf") as "[$ $]"; [| done].
    by apply excl_auth_update.
  Qed.

End freshghost.

Print Assumptions fr_agree.

(** ** Readers

    The reader state is a per-thread registration cell, [reg_cell] in
    [IrisGhost.v]: [None] outside a read-side critical section, [Some e] inside
    one entered at epoch [e].  It replaces an earlier two-valued cell, for the
    reason [Epochs.v] gives -- the epoch is what distinguishes a reader's new
    critical section from its old one, and without it ReadEnd cannot be a
    thread-local step.

    [RepresentsR] ties the machine state's reader set to the registrations.
    [R] is a finite map as a result, for the reason the heap and the stack are
    finite: a fragment is an element of a camera.  The thread set was already
    finite, so this is the model catching up with itself. *)

Definition RepresentsR (r : TID -> Prop)
    (Rg : gmap TID (option (nat * gset Loc))) : Prop :=
  forall t, r t <-> (exists e D, Rg !! t = Some (Some (e, D))).

(** The epoch state the invariant's bookkeeping is read from. *)
Definition mkE (g : nat) (Rg : gmap TID (option (nat * gset Loc)))
    (St : gmap Loc nat) : EState :=
  {| egen := g; ereg := omap (fun v => fst <$> v) Rg; estamp := St |}.

(** Clearing a registration is exactly the epoch layer's ReadEnd, so
    [e_end_is_read_end] applies to it. *)
Lemma mkE_end g Rg St t :
  mkE g (<[t := None]> Rg) St = e_end (mkE g Rg St) t.
Proof.
  unfold mkE, e_end. simpl. f_equal.
  apply map_eq. intros t'. rewrite lookup_omap.
  destruct (decide (t' = t)) as [-> | Hne].
  - by rewrite lookup_insert_eq lookup_delete_eq.
  - rewrite lookup_insert_ne; [| exact (fun Hc => Hne (eq_sym Hc))].
    rewrite lookup_delete_ne; [| exact (fun Hc => Hne (eq_sym Hc))].
    by rewrite lookup_omap.
Qed.

(** Registering is the epoch layer's ReadBegin. *)
Lemma mkE_begin g Rg St t D :
  mkE g (<[t := Some (g, D)]> Rg) St = e_begin (mkE g Rg St) t.
Proof.
  unfold mkE, e_begin. simpl. f_equal.
  apply map_eq. intros t'. rewrite lookup_omap.
  destruct (decide (t' = t)) as [-> | Hne].
  - by rewrite lookup_insert_eq lookup_insert_eq.
  - rewrite lookup_insert_ne; [| exact (fun Hc => Hne (eq_sym Hc))].
    rewrite lookup_insert_ne; [| exact (fun Hc => Hne (eq_sym Hc))].
    by rewrite lookup_omap.
Qed.

Lemma mkE_F_free g Rg St d :
  e_F (mkE g Rg (delete d St)) = delete d (e_F (mkE g Rg St)).
Proof. exact (e_F_free (mkE g Rg St) d). Qed.

Lemma EWF_del g Rg St d : EWF (mkE g Rg St) -> EWF (mkE g Rg (delete d St)).
Proof.
  intros [Hs Hr]. split; [| exact Hr].
  intros o e H. simpl in H.
  destruct (decide (o = d)) as [-> | Hne]; [by rewrite lookup_delete_eq in H |].
  rewrite lookup_delete_ne in H; [| exact (fun Hc => Hne (eq_sym Hc))].
  exact (Hs o e H).
Qed.

Lemma mkE_F_end g Rg St t :
  e_F (mkE g (<[t := None]> Rg) St) = read_end_F (e_F (mkE g Rg St)) t.
Proof.
  rewrite mkE_end. exact (proj2 (proj2 (e_end_is_read_end (mkE g Rg St) t))).
Qed.

Lemma mkE_reg g Rg St t e :
  ereg (mkE g Rg St) !! t = Some e <-> (exists D, Rg !! t = Some (Some (e, D))).
Proof.
  simpl. rewrite lookup_omap. split.
  - destruct (Rg !! t) as [[[e0 D0]|]|] eqn:E; simpl;
      [| discriminate | discriminate].
    intros H. injection H as <-. by exists D0.
  - intros [D H]. by rewrite H.
Qed.

(** References live in RCU fields.  This is what the mutation rules actually
    need, and it replaces the published proofs' assumption that *every* field is
    an RCU field -- which a class declaration forbids, and which [BST.v] shows
    stops the worked example from being typed.  It is a property of the physical
    state, like the shape condition, so it is carried where that is. *)
Definition RefsRCU (FType : FName -> FieldKind) (h : Heap) : Prop :=
  forall o g o', h o g = Some (VLoc o') -> FType g = RCUField.

Lemma RefsRCU_upd FType h o f o' :
  RefsRCU FType h -> FType f = RCUField -> RefsRCU FType (upd h o f (VLoc o')).
Proof.
  intros HR Hf q g y Hq. destruct (decide ((q, g) = (o, f))) as [Heq | Hne].
  - injection Heq as -> ->. exact Hf.
  - rewrite (upd_other h o f (VLoc o') q g Hne) in Hq. exact (HR q g y Hq).
Qed.

Lemma RefsRCU_free FType h d :
  RefsRCU FType h -> RefsRCU FType (free h d).
Proof.
  intros HR o g y Ho. destruct (Nat.eq_dec o d) as [->|Hne].
  - by rewrite free_same in Ho.
  - rewrite (free_other h d o g Hne) in Ho. exact (HR o g y Ho).
Qed.

Lemma RefsRCU_alloc FType h n fs :
  RefsRCU FType h -> RefsRCU FType (alloc h n fs).
Proof.
  intros HR o g y Ho. destruct (Nat.eq_dec o n) as [->|Hne].
  - destruct (in_dec Nat.eq_dec g fs) as [Hin | Hni].
    + by rewrite (alloc_same h n fs g Hin) in Ho.
    + rewrite (alloc_miss h n fs g Hni) in Ho. exact (HR n g y Ho).
  - rewrite (alloc_other h n fs o g Hne) in Ho. exact (HR o g y Ho).
Qed.

(** ** The shape of the heap

    What the class declaration buys, stated as a property of the physical
    state: every allocated cell is at a declared field.  It is what lets a
    thread holding all of a node's declared cells conclude that it holds all of
    the node's cells, which is what reclamation needs. *)

Definition HeapShape (fs : list FName) (h : Heap) : Prop :=
  forall o f v, h o f = Some v -> In f fs.

Lemma HeapShape_upd fs h o f v :
  HeapShape fs h -> In f fs -> HeapShape fs (upd h o f v).
Proof.
  intros HS Hin q g w Hlk.
  destruct (decide ((q, g) = (o, f))) as [Heq | Hne].
  - injection Heq as -> ->. exact Hin.
  - rewrite (upd_other h o f v q g Hne) in Hlk. exact (HS q g w Hlk).
Qed.

Lemma HeapShape_free fs h d :
  HeapShape fs h -> HeapShape fs (free h d).
Proof.
  intros HS o f v Hlk. destruct (Nat.eq_dec o d) as [->|Hne].
  - by rewrite free_same in Hlk.
  - rewrite (free_other h d o f Hne) in Hlk. exact (HS o f v Hlk).
Qed.

Lemma HeapShape_alloc fs h n :
  HeapShape fs h -> HeapShape fs (alloc h n fs).
Proof.
  intros HS o f v Hlk. destruct (Nat.eq_dec o n) as [->|Hne].
  - destruct (in_dec Nat.eq_dec f fs) as [Hin | Hni]; [exact Hin |].
    rewrite (alloc_miss h n fs f Hni) in Hlk. exact (HS n f v Hlk).
  - rewrite (alloc_other h n fs o f Hne) in Hlk. exact (HS o f v Hlk).
Qed.

Section invariantT.
  Context `{!rcuG Σ, !freshG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  (** The free list is no longer a map of snapshots that somebody owns.  It is
      stamps, owned by the writer, and registrations, owned one cell each by
      the readers; the snapshots are derived.  [Epochs.v] is the argument that
      this is the same system, and it is what makes ReadEnd a write to the
      departing reader's own cell.

      [w] is the watermark: every registration is at least [w], and [w] only
      grows, so a fragment of it is the persistent certificate a completed
      grace period leaves behind. *)
  Definition rcu_invT_inner (γo γf γr γe γq : gname) : iProp Σ :=
    ∃ (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
      (T : gset TID) (F : gmap Loc (gset TID)) (St : gmap Loc nat)
      (Rg : gmap TID (option (nat * gset Loc))) (g w : nat) (Fr : gset Loc),
      phys m
      ∗ tobs_auth γo Og
      ∗ fl_auth γf St
      ∗ reg_auth γe Rg
      ∗ wm_auth γq w
      ∗ fr_auth γr Fr
      ∗ ⌜ObsWF Og⌝
      ∗ ⌜FLD (to_LState_t m Og U T F)⌝
      ∗ ⌜WFreshW (to_LState_t m Og U T F)⌝
      ∗ ⌜RefsRCU FType (hp m)⌝
      ∗ ⌜forall q t, obsv (to_LState_t m Og U T F) q (Ofresh t) -> q ∈ Fr⌝
      ∗ ⌜WellFormed FType (to_LState_t m Og U T F)⌝
      ∗ ⌜WUNLKW (to_LState_t m Og U T F)⌝
      (* the free list is derived, not owned: stamps are the writer's and
         registrations are the readers' own, and [F] is what they say *)
      ∗ ⌜F = e_F (mkE g Rg St)⌝
      ∗ ⌜EWF (mkE g Rg St)⌝
      ∗ ⌜RepresentsR (rds m) Rg⌝
      ∗ ⌜forall t, bnd m t <-> e_bnd (mkE g Rg St) t⌝
      ∗ ⌜forall t, lk m = Some t -> Rg !! t = None⌝
      ∗ ⌜w <= g /\ forall t e D, Rg !! t = Some (Some (e, D)) -> w <= e⌝
      (* a registered thread's own observations are enumerated by its cell,
         which is what makes ReadEnd's enumeration the thread's business *)
      ∗ ⌜forall t e D o sg ob,
           Rg !! t = Some (Some (e, D)) -> Og !! (o, t) = Some sg ->
           ob ∈ sg -> obs_tid ob = Some t -> o ∈ D⌝.

  Definition rcu_invT (N : namespace) (γo γf γr γe γq : gname) : iProp Σ :=
    inv N (rcu_invT_inner γo γf γr γe γq).

  Global Instance rcu_invT_persistent N γo γf γr γe γq :
    Persistent (rcu_invT N γo γf γr γe γq).
  Proof. apply _. Qed.

End invariantT.

(** ** Free, as a step on the invariant's contents

    The shape an atomic action takes once the heap is in the invariant: the
    contents go in, the physical step happens, the contents come back out with
    the invariant re-established.  The pure work is [free_preserves_WellFormed]
    and nothing else -- which is the result the experiment was after.

    [Hstep] is where the language's own [free] would go.  It stays a hypothesis
    because [phys] is still a parameter; choosing it is the only thing between
    this and a Hoare triple. *)

Section free_step.
  Context `{!rcuG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  Lemma free_update γo γf g Rg m Og U T St d t e :
    (* the rule's premise: the variable freed is typed [freeable] *)
    obsv (to_LState_t m Og U T (e_F (mkE g Rg St))) d (Ofree t) ->
    WellFormed FType (to_LState_t m Og U T (e_F (mkE g Rg St))) ->
    (* the thread holds the node's stamp, which is the writer's to hold *)
    fl_ctl γf d e -∗
    (* the invariant's contents *)
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (* the physical step *)
    (phys m ==∗ phys (free_ms m d)) -∗
    (* ... and the contents come back, re-established *)
    |==> phys (free_ms m d)
         ∗ tobs_auth γo Og
         ∗ fl_auth γf (delete d St)
         ∗ ⌜WellFormed FType
              (to_LState_t (free_ms m d) Og U T
                 (e_F (mkE g Rg (delete d St))))⌝.
  Proof.
    iIntros (Hfree Hwf) "Hctl Hp Ho Hf Hstep".
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (fl_delete with "Hf Hctl") as "Hf".
    iModIntro. iFrame. iPureIntro.
    rewrite (e_F_free (mkE g Rg St) d).
    exact (free_preserves_WellFormed FType m Og U T _ d t Hwf Hfree).
  Qed.

End free_step.

Print Assumptions fl_delete.
Print Assumptions free_update.

(** ** A mutation: T-UnlinkH

    Free was the easy case: no denotations and no observation change.  The
    mutation rules are the real test of the encoding, because they change the
    observations as well as the heap, and because what they change is *one
    thread's* view of one location -- the writer's iterator on the node being
    unlinked -- while a reader's iterator on the same node must survive
    untouched.  That is what the per-thread ghost state is for, and this is
    where it is exercised.

    The four abstract properties [unlink_preserves_WellFormed] takes of the
    observation change are discharged here from the concrete update, and each
    needs something.  Two are immediate.  The third, that no iterator of the
    writer's survives at the unlinked node, needs [ObsWF]: without it a reader's
    entry could in principle record an observation tagged with the writer.  The
    fourth, that everything else survives, needs the writer to hold *exactly*
    its iterator observation there -- which is what owning [tobs_ctl] with that
    singleton says, and what makes the revocation legal in the first place. *)

Lemma ObsWF_unlink Og oz lw :
  ObsWF Og -> ObsWF (<[(oz, lw) := {[Ounlk lw]}]> Og).
Proof.
  intros H o t sg ob Hl Hin.
  destruct (decide ((o, t) = (oz, lw))) as [Heq | Hne].
  - injection Heq as -> ->. rewrite lookup_insert_eq in Hl.
    injection Hl as <-. apply elem_of_singleton in Hin. subst ob.
    left. reflexivity.
  - rewrite lookup_insert_ne // in Hl. exact (H o t sg ob Hl Hin).
Qed.

Section unlink_obs.
  Variables (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)) (St : gmap Loc nat).
  Variables (lw : TID) (ox : Loc) (f1 : FName) (oz ow : Loc).
  Hypothesis Hwf  : ObsWF Og.
  Hypothesis Hctl : Og !! (oz, lw) = Some {[Oiter lw]}.

  Lemma uo_demote : obsv (to_LState_t (write_ms m ox f1 (VLoc ow))
                     (<[(oz, lw) := {[Ounlk lw]}]> Og) U T F) oz (Ounlk lw).
  Proof.
    exists lw, {[Ounlk lw]}.
    split; [by rewrite lookup_insert_eq | set_solver].
  Qed.

  Lemma uo_noiter : ~ obsv (to_LState_t (write_ms m ox f1 (VLoc ow))
                       (<[(oz, lw) := {[Ounlk lw]}]> Og) U T F) oz (Oiter lw).
  Proof.
    intros [t [sg [Hl Hin]]].
    destruct (decide ((oz, t) = (oz, lw))) as [Heq | Hne].
    - injection Heq as ->. rewrite lookup_insert_eq in Hl.
      injection Hl as <-. set_solver.
    - rewrite lookup_insert_ne // in Hl.
      destruct (Hwf oz t sg (Oiter lw) Hl Hin) as [Htid | Hc]; [| discriminate].
      simpl in Htid. injection Htid as ->. by apply Hne.
  Qed.

  Lemma uo_new o ob :
    obsv (to_LState_t (write_ms m ox f1 (VLoc ow))
            (<[(oz, lw) := {[Ounlk lw]}]> Og) U T F) o ob ->
    obsv (to_LState_t m Og U T F) o ob \/ (o = oz /\ ob = Ounlk lw).
  Proof.
    intros [t [sg [Hl Hin]]].
    destruct (decide ((o, t) = (oz, lw))) as [Heq | Hne].
    - injection Heq as -> ->. rewrite lookup_insert_eq in Hl.
      injection Hl as <-. apply elem_of_singleton in Hin.
      right. by split.
    - rewrite lookup_insert_ne // in Hl. left. by exists t, sg.
  Qed.

  Lemma uo_keep o ob :
    obsv (to_LState_t m Og U T F) o ob -> (o, ob) <> (oz, Oiter lw) ->
    obsv (to_LState_t (write_ms m ox f1 (VLoc ow))
            (<[(oz, lw) := {[Ounlk lw]}]> Og) U T F) o ob.
  Proof.
    intros [t [sg [Hl Hin]]] Hne.
    destruct (decide ((o, t) = (oz, lw))) as [Heq | Hno].
    - exfalso. injection Heq as -> ->. rewrite Hctl in Hl.
      injection Hl as <-. apply elem_of_singleton in Hin. subst ob.
      by apply Hne.
    - exists t, sg. rewrite lookup_insert_ne //.
  Qed.

End unlink_obs.

Section unlink_step.
  Context `{!rcuG Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  (** The pure content of T-UnlinkH, separated out so the atomic version can
      use it without going through the ghost plumbing twice. *)
  Lemma unlink_pure m Og U T F lw ox f1 oz f2 ow rho :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    Og !! (oz, lw) = Some {[Oiter lw]} ->
    (forall o g o', hp m o g = Some (VLoc o') -> FType g = RCUField) ->
    lk m = Some lw ->
    hp m ox f1 = Some (VLoc oz) ->
    hp m oz f2 = Some (VLoc ow) ->
    obsv (to_LState_t m Og U T F) ox (Oiter lw) ->
    obsv (to_LState_t m Og U T F) oz (Oiter lw) ->
    obsv (to_LState_t m Og U T F) ow (Oiter lw) ->
    flist (to_LState_t m Og U T F) ow = None ->
    hstar (hp m) (rt m) rho = Some ox ->
    UNQR_h (hp m) (rt m) ->
    (forall q t g, obsv (to_LState_t m Og U T F) q (Ofresh t) ->
       hp m q g <> Some (VLoc oz)) ->
    ObsWF (<[(oz, lw) := {[Ounlk lw]}]> Og)
    /\ WellFormed FType
         (to_LState_t (write_ms m ox f1 (VLoc ow))
            (<[(oz, lw) := {[Ounlk lw]}]> Og) U T F).
  Proof.
    intros Hwf Hinv Hlook Hall Hlk He1 He2 Hix Hiz Hiw Hfw Hrho HU Hnf. split.
    - exact (ObsWF_unlink Og oz lw Hwf).
    - apply (unlink_preserves_WellFormed FType m Og
               (<[(oz, lw) := {[Ounlk lw]}]> Og) U T F lw ox f1 oz f2 ow rho).
      all: try assumption.
      + eapply uo_demote; eauto.
      + eapply uo_noiter; eauto.
      + intros o ob Hx. eapply uo_new; eauto.
      + intros o ob Hx Hy. eapply uo_keep; eauto.
  Qed.

  Lemma unlink_update γo γf m Og U T F St lw ox f1 oz f2 ow rho :
    (* the encoding's well-formedness, carried by the invariant *)
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    (* the rule's premises *)
    (forall o g o', hp m o g = Some (VLoc o') -> FType g = RCUField) ->
    lk m = Some lw ->
    hp m ox f1 = Some (VLoc oz) ->
    hp m oz f2 = Some (VLoc ow) ->
    obsv (to_LState_t m Og U T F) ox (Oiter lw) ->
    obsv (to_LState_t m Og U T F) oz (Oiter lw) ->
    obsv (to_LState_t m Og U T F) ow (Oiter lw) ->
    flist (to_LState_t m Og U T F) ow = None ->
    hstar (hp m) (rt m) rho = Some ox ->
    UNQR_h (hp m) (rt m) ->
    (forall q t g, obsv (to_LState_t m Og U T F) q (Ofresh t) ->
       hp m q g <> Some (VLoc oz)) ->
    (* the writer holds exactly its iterator observation on the node *)
    tobs_ctl γo oz lw {[Oiter lw]} -∗
    (* the invariant's contents *)
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (* the physical step *)
    (phys m ==∗ phys (write_ms m ox f1 (VLoc ow))) -∗
    |==> phys (write_ms m ox f1 (VLoc ow))
         ∗ tobs_auth γo (<[(oz, lw) := {[Ounlk lw]}]> Og)
         ∗ tobs_ctl γo oz lw {[Ounlk lw]}
         ∗ fl_auth γf St
         ∗ ⌜ObsWF (<[(oz, lw) := {[Ounlk lw]}]> Og)⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (write_ms m ox f1 (VLoc ow))
                 (<[(oz, lw) := {[Ounlk lw]}]> Og) U T F)⌝.
  Proof.
    iIntros (Hwf Hinv Hall Hlk He1 He2 Hix Hiz Hiw Hfw Hrho HU Hnf)
            "Hctl Hp Ho Hf Hstep".
    iDestruct (tobs_ctl_agree with "Ho Hctl") as %Hlook.
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (tobs_set with "Ho Hctl") as "[Ho Hctl]".
    iModIntro. iFrame. iPureIntro.
    exact (unlink_pure m Og U T F lw ox f1 oz f2 ow rho
             Hwf Hinv Hlook Hall Hlk He1 He2 Hix Hiz Hiw Hfw Hrho HU Hnf).
  Qed.

End unlink_step.

Print Assumptions ObsWF_unlink.
Print Assumptions unlink_update.

(** ** The shape, factored

    Both steps so far update the observation map at a single key, and so do most
    of the remaining actions.  Three lemmas about [<[(o,t) := s]>] cover all of
    them, and each action's step is then the action lemma plus a line per
    property. *)

Lemma tobs_ins_at m Og U T F o t s' ob :
  ob ∈ s' -> obsv (to_LState_t m (<[(o, t) := s']> Og) U T F) o ob.
Proof. intros H. exists t, s'. split; [by rewrite lookup_insert_eq | exact H]. Qed.

Lemma tobs_ins_new m Og U T F o t s' q ob :
  obsv (to_LState_t m (<[(o, t) := s']> Og) U T F) q ob ->
  (q = o /\ ob ∈ s') \/ obsv (to_LState_t m Og U T F) q ob.
Proof.
  intros [t' [sg [Hl Hin]]].
  destruct (decide ((q, t') = (o, t))) as [Heq | Hne].
  - injection Heq as -> ->. rewrite lookup_insert_eq in Hl.
    injection Hl as <-. left. by split.
  - rewrite lookup_insert_ne // in Hl. right. by exists t', sg.
Qed.

(** Carrying WUNLKW across an observation insert.  Every rule that inserts is
    the writer's, so the only way the inserted set may carry a detaching
    observation is for it to be the lock holder's -- which is what the unlinking
    rules supply and the others discharge vacuously. *)
Lemma WUNLKW_ins m m' Og U T F o t s' lw :
  WUNLKW (to_LState_t m Og U T F) ->
  lk m' = lk m -> lk m = Some lw ->
  (forall t0, Ounlk t0 ∈ s' \/ Ofree t0 ∈ s' -> t0 = lw) ->
  WUNLKW (to_LState_t m' (<[(o, t) := s']> Og) U T F).
Proof.
  intros HW Hlk' Hlk Hs q t0 Hq. simpl. rewrite Hlk'.
  destruct Hq as [Hq | Hq];
    [ destruct (tobs_ins_new m Og U T F o t s' q (Ounlk t0) Hq)
        as [[-> Hin] | Hy];
      [ rewrite (Hs t0 (or_introl Hin)); exact Hlk
      | exact (HW q t0 (or_introl Hy)) ]
    | destruct (tobs_ins_new m Og U T F o t s' q (Ofree t0) Hq)
        as [[-> Hin] | Hy];
      [ rewrite (Hs t0 (or_intror Hin)); exact Hlk
      | exact (HW q t0 (or_intror Hy)) ] ].
Qed.

Lemma tobs_ins_keep m Og U T F o t sold s' q ob :
  Og !! (o, t) = Some sold ->
  obsv (to_LState_t m Og U T F) q ob ->
  (q = o -> ob ∈ sold -> ob ∈ s') ->
  obsv (to_LState_t m (<[(o, t) := s']> Og) U T F) q ob.
Proof.
  intros Hold [t' [sg [Hl Hin]]] Hsub.
  destruct (decide ((q, t') = (o, t))) as [Heq | Hne].
  - injection Heq as -> ->. rewrite Hold in Hl. injection Hl as <-.
    exists t, s'. split;
      [by rewrite lookup_insert_eq | exact (Hsub eq_refl Hin)].
  - exists t', sg. rewrite lookup_insert_ne //.
Qed.

(** At a key with no prior entry nothing can be lost. *)
Lemma tobs_ins_fresh m Og U T F o t s' q ob :
  Og !! (o, t) = None ->
  obsv (to_LState_t m Og U T F) q ob ->
  obsv (to_LState_t m (<[(o, t) := s']> Og) U T F) q ob.
Proof.
  intros Hnone [t' [sg [Hl Hin]]].
  destruct (decide ((q, t') = (o, t))) as [Heq | Hne].
  - exfalso. injection Heq as -> ->. rewrite Hnone in Hl. discriminate.
  - exists t', sg. rewrite lookup_insert_ne //.
Qed.

Lemma ObsWF_ins Og o t s' :
  ObsWF Og -> (forall ob, ob ∈ s' -> obs_tid ob = Some t \/ ob = Oroot) ->
  ObsWF (<[(o, t) := s']> Og).
Proof.
  intros H Hs q t' sg ob Hl Hin.
  destruct (decide ((q, t') = (o, t))) as [Heq | Hne].
  - injection Heq as -> ->. rewrite lookup_insert_eq in Hl.
    injection Hl as <-. exact (Hs ob Hin).
  - rewrite lookup_insert_ne // in Hl. exact (H q t' sg ob Hl Hin).
Qed.

(** ** The actions that touch no observation at all

    T-WriteFH writes a field of a fresh node and ReadBegin adds a thread to the
    reader set; neither moves the ghost state, so the step is the action lemma
    and nothing else. *)

Section quiet_steps.
  Context `{!rcuG Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  Lemma write_fresh_update γo γf m Og U T F St lw on f oy :
    WellFormed FType (to_LState_t m Og U T F) ->
    lk m = Some lw ->
    obsv (to_LState_t m Og U T F) on (Ofresh lw) ->
    obsv (to_LState_t m Og U T F) oy (Oiter lw) ->
    (forall p, hstar (hp m) (rt m) p <> Some on) ->
    InHeap (to_LState_t m Og U T F) oy ->
    flist (to_LState_t m Og U T F) oy = None ->
    oy <> rt m ->
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (write_ms m on f (VLoc oy))) -∗
    |==> phys (write_ms m on f (VLoc oy))
         ∗ tobs_auth γo Og ∗ fl_auth γf St
         ∗ ⌜WellFormed FType (to_LState_t (write_ms m on f (VLoc oy)) Og U T F)⌝.
  Proof.
    iIntros (Hinv Hlk Hfr Hit Hun Hin Hfl Hrt) "Hp Ho Hf Hstep".
    iMod ("Hstep" with "Hp") as "Hp". iModIntro. iFrame. iPureIntro.
    exact (write_fresh_preserves_WellFormed FType m Og U T F lw on f oy
             Hlk Hfr Hit Hun Hin Hfl Hrt Hinv).
  Qed.

  Lemma read_begin_update γo γf m Og U T F St t :
    WellFormed FType (to_LState_t m Og U T F) ->
    (forall lw, lk m = Some lw -> lw <> t) ->
    (forall o, ~ obsv (to_LState_t m Og U T F) o (Ounlk t)
            /\ ~ obsv (to_LState_t m Og U T F) o (Ofree t)
            /\ ~ obsv (to_LState_t m Og U T F) o (Ofresh t)) ->
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (read_begin_ms m t)) -∗
    |==> phys (read_begin_ms m t)
         ∗ tobs_auth γo Og ∗ fl_auth γf St
         ∗ ⌜WellFormed FType (to_LState_t (read_begin_ms m t) Og U T F)⌝.
  Proof.
    iIntros (Hinv Hnw Hcl) "Hp Ho Hf Hstep".
    iMod ("Hstep" with "Hp") as "Hp". iModIntro. iFrame. iPureIntro.
    exact (read_begin_preserves_WellFormed FType m Og U T F t Hnw Hcl Hinv).
  Qed.

End quiet_steps.

Print Assumptions tobs_ins_keep.
Print Assumptions write_fresh_update.
Print Assumptions read_begin_update.

(** ** Granting at one key: T-Alloc, the binding rules, and a reader's read

    Three actions whose whole effect on the ghost state is an entry at one key.
    T-Alloc creates the entry, the binding rules and a reader's read extend an
    existing one, and in each case the action lemma's observation hypotheses are
    the three lemmas above applied once. *)

Section grant_steps.
  Context `{!rcuG Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  (** T-Alloc.  The node is new, so no thread has an entry for it, and the
      ghost step is an allocation rather than an update. *)
  (** The pure content of T-Alloc, separated out like the others. *)
  Lemma alloc_pure m Og U U' T F lw n x fs :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    (forall t, Og !! (n, t) = None) ->
    lk m = Some lw ->
    ~ undf (to_LState_t m (<[(n, lw) := {[Ofresh lw]}]> Og) U' T F) x lw ->
    (forall y t, (y, t) <> (x, lw) ->
       (undf (to_LState_t m (<[(n, lw) := {[Ofresh lw]}]> Og) U' T F) y t
        <-> undf (to_LState_t m Og U T F) y t)) ->
    (forall g, hp m n g = None) ->
    (forall o g, hp m o g <> Some (VLoc n)) ->
    (forall y t, stk m y t <> Some n) ->
    n <> rt m ->
    flist (to_LState_t m Og U T F) n = None ->
    (* the class declaration: the node's field list holds every RCU field *)
    (forall g, FType g = RCUField -> In g fs) ->
    ObsWF (<[(n, lw) := {[Ofresh lw]}]> Og)
    /\ WellFormed FType
         (to_LState_t (alloc_ms m n fs x lw)
            (<[(n, lw) := {[Ofresh lw]}]> Og) U' T F).
  Proof.
    intros Hwf Hinv Hnone Hlk Hdef Hundf Hun Hni Hnr Hrt Hfl Hrcu. split.
    - apply ObsWF_ins; [exact Hwf |].
      intros ob Hin. apply elem_of_singleton in Hin. subst ob. by left.
    - apply (alloc_preserves_WellFormed FType m Og
               (<[(n, lw) := {[Ofresh lw]}]> Og) U U' T F lw n x fs);
        try assumption.
      + apply tobs_ins_at. set_solver.
      + intros o ob Hx. destruct (tobs_ins_new m Og U T F n lw _ o ob Hx)
          as [[-> Hin] | Hy]; [| by left].
        apply elem_of_singleton in Hin. right. by split.
      + intros o ob Hx.
        exact (tobs_ins_fresh m Og U T F n lw _ o ob (Hnone lw) Hx).
      + intros ob [t [sg [Hl _]]]. rewrite Hnone in Hl. discriminate.
  Qed.

  Lemma alloc_update γo γf m Og U U' T F St lw n x fs :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    (forall t, Og !! (n, t) = None) ->
    lk m = Some lw ->
    ~ undf (to_LState_t m (<[(n, lw) := {[Ofresh lw]}]> Og) U' T F) x lw ->
    (forall y t, (y, t) <> (x, lw) ->
       (undf (to_LState_t m (<[(n, lw) := {[Ofresh lw]}]> Og) U' T F) y t
        <-> undf (to_LState_t m Og U T F) y t)) ->
    (forall g, hp m n g = None) ->
    (forall o g, hp m o g <> Some (VLoc n)) ->
    (forall y t, stk m y t <> Some n) ->
    n <> rt m ->
    flist (to_LState_t m Og U T F) n = None ->
    (* the class declaration: the node's field list holds every RCU field *)
    (forall g, FType g = RCUField -> In g fs) ->
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (alloc_ms m n fs x lw)) -∗
    |==> phys (alloc_ms m n fs x lw)
         ∗ tobs_auth γo (<[(n, lw) := {[Ofresh lw]}]> Og)
         ∗ tobs_ctl γo n lw {[Ofresh lw]}
         ∗ fl_auth γf St
         ∗ ⌜ObsWF (<[(n, lw) := {[Ofresh lw]}]> Og)⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (alloc_ms m n fs x lw)
                 (<[(n, lw) := {[Ofresh lw]}]> Og) U' T F)⌝.
  Proof.
    iIntros (Hwf Hinv Hnone Hlk Hdef Hundf Hun Hni Hnr Hrt Hfl Hrcu)
            "Hp Ho Hf Hstep".
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (tobs_alloc_at with "Ho") as "[Ho Hctl]"; [exact (Hnone lw) |].
    iModIntro. iFrame. iPureIntro.
    exact (alloc_pure m Og U U' T F lw n x fs
             Hwf Hinv Hnone Hlk Hdef Hundf Hun Hni Hnr Hrt Hfl Hrcu).
  Qed.

End grant_steps.

Print Assumptions alloc_update.

Section grant_steps2.
  Context `{!rcuG Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  (** A reader's read: the observation is added to the reader's own entry, which
      is why a concurrent writer's entry for the same node is untouched. *)
  Lemma reader_acquire_update γo γf m Og U T F St t z sz :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    rds m t ->
    (forall Tr, flist (to_LState_t m Og U T F) z = Some Tr -> Tr t) ->
    (forall t0, ~ obsv (to_LState_t m Og U T F) z (Ofresh t0)) ->
    tobs_ctl γo z t sz -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    |==> phys m
         ∗ tobs_auth γo (<[(z, t) := sz ∪ {[Oiter t]}]> Og)
         ∗ tobs_ctl γo z t (sz ∪ {[Oiter t]})
         ∗ fl_auth γf St
         ∗ ⌜ObsWF (<[(z, t) := sz ∪ {[Oiter t]}]> Og)⌝
         ∗ ⌜WellFormed FType
              (to_LState_t m (<[(z, t) := sz ∪ {[Oiter t]}]> Og) U T F)⌝.
  Proof.
    iIntros (Hwf Hinv Hrd Hbnd Hnf) "Hctl Hp Ho Hf".
    iDestruct (tobs_ctl_agree with "Ho Hctl") as %Hlook.
    iMod (tobs_set with "Ho Hctl") as "[Ho Hctl]".
    iModIntro. iFrame. iPureIntro. split.
    - apply ObsWF_ins; [exact Hwf |].
      intros ob Hin. apply elem_of_union in Hin as [Hin | Hin].
      + exact (Hwf z t sz ob Hlook Hin).
      + apply elem_of_singleton in Hin. subst ob. by left.
    - exact (reader_acquire_preserves_WellFormed FType m Og U T F t z sz
               Hlook Hrd Hbnd Hnf Hinv).
  Qed.

  (** T-Root, T-ReadS and T-ReadH: the binder's entry gains an iterator and
      keeps whatever it had. *)
  (** The pure content of the binding rules, separated out like the others. *)
  Lemma bind_pure m Og U U' T F tb y o sold :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    (lk m = Some tb \/ rds m tb) ->
    (forall z t, (z, t) <> (y, tb) ->
       (undf (to_LState_t (bind_ms m y tb o)
                (<[(o, tb) := sold ∪ {[Oiter tb]}]> Og) U' T F) z t
        <-> undf (to_LState_t m Og U T F) z t)) ->
    ~ Detached (to_LState_t m Og U T F) o ->
    flist (to_LState_t m Og U T F) o = None ->
    Og !! (o, tb) = Some sold ->
    ObsWF (<[(o, tb) := sold ∪ {[Oiter tb]}]> Og)
    /\ WellFormed FType
         (to_LState_t (bind_ms m y tb o)
            (<[(o, tb) := sold ∪ {[Oiter tb]}]> Og) U' T F).
  Proof.
    intros Hwf Hinv Hact Hundf Hdet Hfl Hlook. split.
    - apply ObsWF_ins; [exact Hwf |].
      intros ob Hin. apply elem_of_union in Hin as [Hin | Hin].
      + exact (Hwf o tb sold ob Hlook Hin).
      + apply elem_of_singleton in Hin. subst ob. by left.
    - apply (bind_preserves_WellFormed FType m Og
               (<[(o, tb) := sold ∪ {[Oiter tb]}]> Og) U U' T F tb y o);
        try assumption.
      + apply tobs_ins_at. set_solver.
      + intros q ob Hx.
        destruct (tobs_ins_new m Og U T F o tb _ q ob Hx) as [[-> Hin] | Hy];
          [| by left].
        apply elem_of_union in Hin as [Hin | Hin].
        * left. by exists tb, sold.
        * apply elem_of_singleton in Hin. right. by split.
      + intros q ob Hx.
        exact (tobs_ins_keep m Og U T F o tb sold _ q ob Hlook Hx
                 (fun _ Hin => elem_of_union_l _ _ _ Hin)).
  Qed.

  Lemma bind_update γo γf m Og U U' T F St tb y o sold :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    (lk m = Some tb \/ rds m tb) ->
    (forall z t, (z, t) <> (y, tb) ->
       (undf (to_LState_t (bind_ms m y tb o)
                (<[(o, tb) := sold ∪ {[Oiter tb]}]> Og) U' T F) z t
        <-> undf (to_LState_t m Og U T F) z t)) ->
    ~ Detached (to_LState_t m Og U T F) o ->
    flist (to_LState_t m Og U T F) o = None ->
    tobs_ctl γo o tb sold -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (bind_ms m y tb o)) -∗
    |==> phys (bind_ms m y tb o)
         ∗ tobs_auth γo (<[(o, tb) := sold ∪ {[Oiter tb]}]> Og)
         ∗ tobs_ctl γo o tb (sold ∪ {[Oiter tb]})
         ∗ fl_auth γf St
         ∗ ⌜ObsWF (<[(o, tb) := sold ∪ {[Oiter tb]}]> Og)⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (bind_ms m y tb o)
                 (<[(o, tb) := sold ∪ {[Oiter tb]}]> Og) U' T F)⌝.
  Proof.
    iIntros (Hwf Hinv Hown Hundf Hlive Hfl) "Hctl Hp Ho Hf Hstep".
    iDestruct (tobs_ctl_agree with "Ho Hctl") as %Hlook.
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (tobs_set with "Ho Hctl") as "[Ho Hctl]".
    iModIntro. iFrame. iPureIntro.
    exact (bind_pure m Og U U' T F tb y o sold
             Hwf Hinv Hown Hundf Hlive Hfl Hlook).
  Qed.

End grant_steps2.

Print Assumptions reader_acquire_update.
Print Assumptions bind_update.

(** ** Promotion: T-Insert and T-LinkF-Null

    The linking rules turn the fresh node's entry from a freshness into the
    writer's iterator.  The only new hypothesis is that no other thread has an
    entry for the node -- which is what being fresh means, and what makes the
    replacement of the entry, rather than an extension of it, the right ghost
    move. *)

Section promote_steps.
  Context `{!rcuG Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  (** The observational form of "no other thread has an entry here", which is
      what the promotion actually needs and what [WFreshW] can supply.  The
      entry form cannot be derived from any resource: a thread's fragment says
      nothing about whether another key exists, and an *empty* entry at another
      key is invisible to every invariant. *)
  Lemma promote_nofresh' Og on lw m U T F :
    (forall t t' sg, Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw) ->
    forall t, ~ obsv (to_LState_t m (<[(on, lw) := {[Oiter lw]}]> Og) U T F)
                on (Ofresh t).
  Proof.
    intros Hsole t [t' [sg [Hl Hin]]].
    destruct (decide (t' = lw)) as [-> | Hne].
    - rewrite lookup_insert_eq in Hl. injection Hl as <-. set_solver.
    - rewrite lookup_insert_ne in Hl; [| by injection 1].
      exact (Hne (Hsole t t' sg Hl Hin)).
  Qed.

  Lemma promote_nofresh Og on lw m U T F :
    (forall t sg, Og !! (on, t) = Some sg -> t = lw) ->
    forall t, ~ obsv (to_LState_t m (<[(on, lw) := {[Oiter lw]}]> Og) U T F)
                on (Ofresh t).
  Proof.
    intros Hsole t [t' [sg [Hl Hin]]].
    destruct (decide (t' = lw)) as [-> | Hne].
    - rewrite lookup_insert_eq in Hl. injection Hl as <-. set_solver.
    - rewrite lookup_insert_ne in Hl; [| by injection 1].
      exact (Hne (Hsole t' sg Hl)).
  Qed.

  (** The pure content of T-Insert, separated out for the same reason as
      T-LinkF-Null's. *)
  Lemma insert_pure m Og U T F lw op f on oo f4 rho :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    (forall t t' sg, Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw) ->
    Og !! (on, lw) = Some {[Ofresh lw]} ->
    lk m = Some lw ->
    (forall o g o', hp m o g = Some (VLoc o') -> FType g = RCUField) ->
    hp m op f = Some (VLoc oo) ->
    obsv (to_LState_t m Og U T F) op (Oiter lw) ->
    PointsOnlyAt (hp m) on f4 oo ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    InHeap (to_LState_t m Og U T F) on ->
    on <> rt m ->
    flist (to_LState_t m Og U T F) on = None ->
    hstar (hp m) (rt m) rho = Some op ->
    UNQR_h (hp m) (rt m) ->
    ObsWF (<[(on, lw) := {[Oiter lw]}]> Og)
    /\ WellFormed FType
         (to_LState_t (write_ms m op f (VLoc on))
            (<[(on, lw) := {[Oiter lw]}]> Og) U T F).
  Proof.
    intros Hwf Hinv Hsole Hlook Hlk Hall Hedge Hitr Hpo Hni Hin Hrt Hfl
           Hrho HU. split.
    - apply ObsWF_ins; [exact Hwf |].
      intros ob Hin'. apply elem_of_singleton in Hin'. subst ob. by left.
    - apply (insert_preserves_WellFormed FType m Og
               (<[(on, lw) := {[Oiter lw]}]> Og) U T F lw op f on oo f4 rho);
        try assumption.
      + apply tobs_ins_at. set_solver.
      + exact (promote_nofresh' Og on lw m U T F Hsole).
      + intros o ob Hx.
        destruct (tobs_ins_new m Og U T F on lw _ o ob Hx) as [[-> Hin'] | Hy];
          [| by left].
        apply elem_of_singleton in Hin'. right. by split.
      + intros o ob Hx Hne.
        apply (tobs_ins_keep m Og U T F on lw {[Ofresh lw]} _ o ob Hlook Hx).
        intros -> Hin'. apply elem_of_singleton in Hin'. subst ob.
        by destruct (Hne eq_refl).
      + exists lw, {[Ofresh lw]}. split; [exact Hlook | set_solver].
  Qed.

  Lemma insert_update γo γf m Og U T F St lw op f on oo f4 rho :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    (forall t t' sg, Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw) ->
    lk m = Some lw ->
    (forall o g o', hp m o g = Some (VLoc o') -> FType g = RCUField) ->
    hp m op f = Some (VLoc oo) ->
    obsv (to_LState_t m Og U T F) op (Oiter lw) ->
    PointsOnlyAt (hp m) on f4 oo ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    InHeap (to_LState_t m Og U T F) on ->
    on <> rt m ->
    flist (to_LState_t m Og U T F) on = None ->
    hstar (hp m) (rt m) rho = Some op ->
    UNQR_h (hp m) (rt m) ->
    tobs_ctl γo on lw {[Ofresh lw]} -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (write_ms m op f (VLoc on))) -∗
    |==> phys (write_ms m op f (VLoc on))
         ∗ tobs_auth γo (<[(on, lw) := {[Oiter lw]}]> Og)
         ∗ tobs_ctl γo on lw {[Oiter lw]}
         ∗ fl_auth γf St
         ∗ ⌜ObsWF (<[(on, lw) := {[Oiter lw]}]> Og)⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (write_ms m op f (VLoc on))
                 (<[(on, lw) := {[Oiter lw]}]> Og) U T F)⌝.
  Proof.
    iIntros (Hwf Hinv Hsole Hlk Hall Hedge Hitr Hpo Hni Hin Hrt Hfl Hrho HU)
            "Hctl Hp Ho Hf Hstep".
    iDestruct (tobs_ctl_agree with "Ho Hctl") as %Hlook.
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (tobs_set with "Ho Hctl") as "[Ho Hctl]".
    iModIntro. iFrame. iPureIntro.
    exact (insert_pure m Og U T F lw op f on oo f4 rho
             Hwf Hinv Hsole Hlook Hlk Hall Hedge Hitr Hpo Hni Hin Hrt Hfl
             Hrho HU).
  Qed.

  (** The pure content of T-LinkF-Null, separated out so that the atomic
      version can use it without going through the ghost plumbing twice. *)
  Lemma link_null_pure m Og U T F lw op f on rho :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    (forall t t' sg, Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw) ->
    Og !! (on, lw) = Some {[Ofresh lw]} ->
    lk m = Some lw ->
    obsv (to_LState_t m Og U T F) op (Oiter lw) ->
    PointsNowhere (hp m) on ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    InHeap (to_LState_t m Og U T F) on ->
    on <> rt m ->
    flist (to_LState_t m Og U T F) on = None ->
    hstar (hp m) (rt m) rho = Some op ->
    UNQR_h (hp m) (rt m) ->
    ObsWF (<[(on, lw) := {[Oiter lw]}]> Og)
    /\ WellFormed FType
         (to_LState_t (write_ms m op f (VLoc on))
            (<[(on, lw) := {[Oiter lw]}]> Og) U T F).
  Proof.
    intros Hwf Hinv Hsole Hlook Hlk Hitr Hpn Hni Hin Hrt Hfl Hrho HU. split.
    - apply ObsWF_ins; [exact Hwf |].
      intros ob Hin'. apply elem_of_singleton in Hin'. subst ob. by left.
    - apply (link_null_preserves_WellFormed FType m Og
               (<[(on, lw) := {[Oiter lw]}]> Og) U T F lw op f on rho);
        try assumption.
      + apply tobs_ins_at. set_solver.
      + exact (promote_nofresh' Og on lw m U T F Hsole).
      + intros o ob Hx.
        destruct (tobs_ins_new m Og U T F on lw _ o ob Hx) as [[-> Hin'] | Hy];
          [| by left].
        apply elem_of_singleton in Hin'. right. by split.
      + intros o ob Hx Hne.
        apply (tobs_ins_keep m Og U T F on lw {[Ofresh lw]} _ o ob Hlook Hx).
        intros -> Hin'. apply elem_of_singleton in Hin'. subst ob.
        by destruct (Hne eq_refl).
      + exists lw, {[Ofresh lw]}. split; [exact Hlook | set_solver].
  Qed.

  Lemma link_null_update γo γf m Og U T F St lw op f on rho :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    (* the observational form: any entry here holding a [fresh] observation is
       the writer's.  The entry form this had before is not derivable from any
       resource -- an empty entry at another key is invisible -- and it is not
       what the promotion needs. *)
    (forall t t' sg, Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw) ->
    lk m = Some lw ->
    obsv (to_LState_t m Og U T F) op (Oiter lw) ->
    PointsNowhere (hp m) on ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    InHeap (to_LState_t m Og U T F) on ->
    on <> rt m ->
    flist (to_LState_t m Og U T F) on = None ->
    hstar (hp m) (rt m) rho = Some op ->
    UNQR_h (hp m) (rt m) ->
    tobs_ctl γo on lw {[Ofresh lw]} -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (write_ms m op f (VLoc on))) -∗
    |==> phys (write_ms m op f (VLoc on))
         ∗ tobs_auth γo (<[(on, lw) := {[Oiter lw]}]> Og)
         ∗ tobs_ctl γo on lw {[Oiter lw]}
         ∗ fl_auth γf St
         ∗ ⌜ObsWF (<[(on, lw) := {[Oiter lw]}]> Og)⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (write_ms m op f (VLoc on))
                 (<[(on, lw) := {[Oiter lw]}]> Og) U T F)⌝.
  Proof.
    iIntros (Hwf Hinv Hsole Hlk Hitr Hpn Hni Hin Hrt Hfl Hrho HU)
            "Hctl Hp Ho Hf Hstep".
    iDestruct (tobs_ctl_agree with "Ho Hctl") as %Hlook.
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (tobs_set with "Ho Hctl") as "[Ho Hctl]".
    iModIntro. iFrame. iPureIntro.
    exact (link_null_pure m Og U T F lw op f on rho
             Hwf Hinv Hsole Hlook Hlk Hitr Hpn Hni Hin Hrt Hfl Hrho HU).
  Qed.

End promote_steps.

Print Assumptions insert_update.
Print Assumptions link_null_update.

(** ** Both at once: T-Replace

    The only action that promotes and demotes in the same step, so its ghost
    update is two entries rather than one and the five observation properties
    have to be read off a nested insert.  [on <> oo] is what keeps the two keys
    apart, and it is the fact the pure layer already needed. *)

Section replace_obs.
  Variables (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)) (St : gmap Loc nat).
  Variables (lw : TID) (op : Loc) (f : FName) (oo on : Loc).
  Hypothesis Hne   : on <> oo.
  Hypothesis Hwf   : ObsWF Og.
  Hypothesis Hon   : Og !! (on, lw) = Some {[Ofresh lw]}.
  Hypothesis Hoo   : Og !! (oo, lw) = Some {[Oiter lw]}.
  (** The observational form, as in the two linking rules: what the promotion
      needs, and what a resource can supply. *)
  Hypothesis Hsole : forall t t' sg,
    Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw.

  Lemma rp_at_on :
    (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
      !! (on, lw) = Some {[Oiter lw]}.
  Proof. by rewrite lookup_insert_eq. Qed.

  Lemma rp_at_oo :
    (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
      !! (oo, lw) = Some {[Ounlk lw]}.
  Proof.
    rewrite lookup_insert_ne; [by rewrite lookup_insert_eq |].
    by injection 1.
  Qed.

  Lemma rp_other q t :
    (q, t) <> (on, lw) -> (q, t) <> (oo, lw) ->
    (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
      !! (q, t) = Og !! (q, t).
  Proof.
    intros H1 H2. rewrite lookup_insert_ne; [| by intros Hc; apply H1].
    rewrite lookup_insert_ne; [reflexivity | by intros Hc; apply H2].
  Qed.

  Lemma rp_promote :
    obsv (to_LState_t (write_ms m op f (VLoc on))
            (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
            U T F) on (Oiter lw).
  Proof. exists lw, {[Oiter lw]}. split; [exact rp_at_on | set_solver]. Qed.

  Lemma rp_demote :
    obsv (to_LState_t (write_ms m op f (VLoc on))
            (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
            U T F) oo (Ounlk lw).
  Proof. exists lw, {[Ounlk lw]}. split; [exact rp_at_oo | set_solver]. Qed.

  Lemma rp_nofresh t :
    ~ obsv (to_LState_t (write_ms m op f (VLoc on))
              (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
              U T F) on (Ofresh t).
  Proof.
    intros [t' [sg [Hl Hin]]].
    destruct (decide (t' = lw)) as [-> | Hnt].
    - rewrite rp_at_on in Hl. injection Hl as <-. set_solver.
    - rewrite rp_other in Hl; [| by injection 1 | by injection 1; intros ->].
      exact (Hnt (Hsole t t' sg Hl Hin)).
  Qed.

  Lemma rp_noiter :
    ~ obsv (to_LState_t (write_ms m op f (VLoc on))
              (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
              U T F) oo (Oiter lw).
  Proof.
    intros [t' [sg [Hl Hin]]].
    destruct (decide (t' = lw)) as [-> | Hnt].
    - rewrite rp_at_oo in Hl. injection Hl as <-. set_solver.
    - rewrite rp_other in Hl;
        [| by injection 1; intros -> | by injection 1; intros ->].
      destruct (Hwf oo t' sg (Oiter lw) Hl Hin) as [Htid | Hc]; [| discriminate].
      simpl in Htid. injection Htid as ->. by apply Hnt.
  Qed.

  Lemma rp_new o ob :
    obsv (to_LState_t (write_ms m op f (VLoc on))
            (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
            U T F) o ob ->
    obsv (to_LState_t m Og U T F) o ob
    \/ (o = on /\ ob = Oiter lw) \/ (o = oo /\ ob = Ounlk lw).
  Proof.
    intros [t' [sg [Hl Hin]]].
    destruct (decide ((o, t') = (on, lw))) as [Heq | H1].
    - injection Heq as -> ->. rewrite rp_at_on in Hl. injection Hl as <-.
      apply elem_of_singleton in Hin. right; left. by split.
    - destruct (decide ((o, t') = (oo, lw))) as [Heq | H2].
      + injection Heq as -> ->. rewrite rp_at_oo in Hl. injection Hl as <-.
        apply elem_of_singleton in Hin. right; right. by split.
      + rewrite (rp_other o t' H1 H2) in Hl. left. by exists t', sg.
  Qed.

  Lemma rp_keep o ob :
    obsv (to_LState_t m Og U T F) o ob ->
    (o, ob) <> (on, Ofresh lw) -> (o, ob) <> (oo, Oiter lw) ->
    obsv (to_LState_t (write_ms m op f (VLoc on))
            (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
            U T F) o ob.
  Proof.
    intros [t' [sg [Hl Hin]]] Hn1 Hn2.
    destruct (decide ((o, t') = (on, lw))) as [Heq | H1].
    - exfalso. injection Heq as -> ->. rewrite Hon in Hl. injection Hl as <-.
      apply elem_of_singleton in Hin. subst ob. by apply Hn1.
    - destruct (decide ((o, t') = (oo, lw))) as [Heq | H2].
      + exfalso. injection Heq as -> ->. rewrite Hoo in Hl. injection Hl as <-.
        apply elem_of_singleton in Hin. subst ob. by apply Hn2.
      + exists t', sg. rewrite (rp_other o t' H1 H2). by split.
  Qed.

  Lemma rp_ObsWF :
    ObsWF (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og)).
  Proof.
    apply ObsWF_ins; [apply ObsWF_ins; [exact Hwf |] |];
      intros ob Hin; apply elem_of_singleton in Hin; subst ob; by left.
  Qed.

End replace_obs.

Section replace_step.
  Context `{!rcuG Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  (** The pure content of T-Replace, separated out like the others. *)
  Lemma replace_pure m Og U T F lw op f oo on rho :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    on <> oo ->
    (forall t t' sg, Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw) ->
    Og !! (on, lw) = Some {[Ofresh lw]} ->
    Og !! (oo, lw) = Some {[Oiter lw]} ->
    lk m = Some lw ->
    (forall o g o', hp m o g = Some (VLoc o') -> FType g = RCUField) ->
    hp m op f = Some (VLoc oo) ->
    Mirrors (hp m) on oo ->
    obsv (to_LState_t m Og U T F) op (Oiter lw) ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    InHeap (to_LState_t m Og U T F) on ->
    on <> rt m ->
    flist (to_LState_t m Og U T F) on = None ->
    hstar (hp m) (rt m) rho = Some op ->
    UNQR_h (hp m) (rt m) ->
    (forall q t g, obsv (to_LState_t m Og U T F) q (Ofresh t) ->
       hp m q g <> Some (VLoc oo)) ->
    (forall q t0, obsv (to_LState_t m Og U T F) q (Ounlk t0)
               \/ obsv (to_LState_t m Og U T F) q (Ofree t0) -> t0 = lw) ->
    ObsWF (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
    /\ WellFormed FType
         (to_LState_t (write_ms m op f (VLoc on))
            (<[(on, lw) := {[Oiter lw]}]>
               (<[(oo, lw) := {[Ounlk lw]}]> Og)) U T F).
  Proof.
    intros Hwf Hinv Hno Hsole Hon Hoo Hlk Hall Hedge Hmir Hitr Hni Hin
           Hrt Hfl Hrho HU Hnfp Huw. split.
    - eapply rp_ObsWF; eauto.
    - apply (replace_preserves_WellFormed FType m Og
               (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og))
               U T F lw op f oo on rho); try assumption.
      + eapply rp_promote; eauto.
      + intros t. eapply rp_nofresh; eauto.
      + eapply rp_demote; eauto.
      + eapply rp_noiter; eauto.
      + intros o ob Hx. eapply rp_new; eauto.
      + intros o ob Hx H1 H2. eapply rp_keep; eauto.
      + exists lw, {[Ofresh lw]}. split; [exact Hon | set_solver].
      + exists lw, {[Oiter lw]}. split; [exact Hoo | set_solver].
  Qed.

  Lemma replace_update γo γf m Og U T F St lw op f oo on rho :
    ObsWF Og ->
    WellFormed FType (to_LState_t m Og U T F) ->
    on <> oo ->
    (forall t t' sg, Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw) ->
    Og !! (on, lw) = Some {[Ofresh lw]} ->
    Og !! (oo, lw) = Some {[Oiter lw]} ->
    lk m = Some lw ->
    (forall o g o', hp m o g = Some (VLoc o') -> FType g = RCUField) ->
    hp m op f = Some (VLoc oo) ->
    Mirrors (hp m) on oo ->
    obsv (to_LState_t m Og U T F) op (Oiter lw) ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    InHeap (to_LState_t m Og U T F) on ->
    on <> rt m ->
    flist (to_LState_t m Og U T F) on = None ->
    hstar (hp m) (rt m) rho = Some op ->
    UNQR_h (hp m) (rt m) ->
    (forall q t g, obsv (to_LState_t m Og U T F) q (Ofresh t) ->
       hp m q g <> Some (VLoc oo)) ->
    (forall q t0, obsv (to_LState_t m Og U T F) q (Ounlk t0)
               \/ obsv (to_LState_t m Og U T F) q (Ofree t0) -> t0 = lw) ->
    tobs_ctl γo on lw {[Ofresh lw]} -∗ tobs_ctl γo oo lw {[Oiter lw]} -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (write_ms m op f (VLoc on))) -∗
    |==> phys (write_ms m op f (VLoc on))
         ∗ tobs_auth γo (<[(on, lw) := {[Oiter lw]}]>
                           (<[(oo, lw) := {[Ounlk lw]}]> Og))
         ∗ tobs_ctl γo on lw {[Oiter lw]} ∗ tobs_ctl γo oo lw {[Ounlk lw]}
         ∗ fl_auth γf St
         ∗ ⌜ObsWF (<[(on, lw) := {[Oiter lw]}]>
                     (<[(oo, lw) := {[Ounlk lw]}]> Og))⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (write_ms m op f (VLoc on))
                 (<[(on, lw) := {[Oiter lw]}]>
                    (<[(oo, lw) := {[Ounlk lw]}]> Og)) U T F)⌝.
  Proof.
    iIntros (Hwf Hinv Hno Hsole Hon Hoo Hlk Hall Hedge Hmir Hitr Hni Hin
             Hrt Hfl Hrho HU Hnfp Huw)
            "Hcn Hco Hp Ho Hf Hstep".
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (tobs_set with "Ho Hco") as "[Ho Hco]".
    iMod (tobs_set with "Ho Hcn") as "[Ho Hcn]".
    iModIntro. iFrame. iPureIntro.
    exact (replace_pure m Og U T F lw op f oo on rho
             Hwf Hinv Hno Hsole Hon Hoo Hlk Hall Hedge Hmir Hitr Hni Hin
             Hrt Hfl Hrho HU Hnfp Huw).
  Qed.

End replace_step.


Print Assumptions replace_update.

(** * Bulk updates

    The five remaining actions change the ghost state at many keys at once:
    SyncStart gives every detached node a free-list entry, SyncStop turns every
    [unlinked] observation into a [freeable] one, ReadEnd and WriteEnd retire a
    thread's entries, and WriteBegin grants the incoming writer an iterator on
    everything reachable.  The ghost layer had only single-key operations, so
    none of them could be stated.

    What is needed is not a new camera and not a new frame-preserving update.  A
    map-wide change is an iterated single-key change, and what makes it legal is
    owning every fragment it touches -- or the key being absent, which is the
    other way to earn the right to write there.  The induction is the whole
    content, and it is short.

    Worth noticing what this does *not* require: that the intermediate maps
    satisfy WellFormed.  The fold happens inside one opening of the invariant,
    so the half-finished states never appear in it and only the endpoint has to
    be well formed.  That is what lets SyncStop recolour every observation in a
    single step. *)

(** ** The fold, and what it looks up to *)

Section inslist.
  Context {K A : Type} `{EqDecision K, !Countable K}.

  Definition ins_list (M : gmap K A) (l : list (K * A)) : gmap K A :=
    foldl (fun M p => <[p.1 := p.2]> M) M l.

  Lemma ins_list_Some M l k v :
    M !! k = Some v -> exists v', ins_list M l !! k = Some v'.
  Proof.
    revert M v. induction l as [|p l IH]; intros M v Hl.
    - by exists v.
    - simpl. destruct (decide (k = p.1)) as [->|Hne].
      + apply (IH _ p.2). by rewrite lookup_insert_eq.
      + apply (IH _ v). by rewrite lookup_insert_ne.
  Qed.

  Lemma ins_list_in M l k v :
    (k, v) ∈ l -> exists v', ins_list M l !! k = Some v'.
  Proof.
    revert M. induction l as [|p l IH]; intros M Hin.
    - by apply not_elem_of_nil in Hin.
    - apply elem_of_cons in Hin. destruct Hin as [<- | Hin].
      + simpl. apply (ins_list_Some _ _ _ v). by rewrite lookup_insert_eq.
      + by apply IH.
  Qed.

  Lemma ins_list_notin M l k : k ∉ l.*1 -> ins_list M l !! k = M !! k.
  Proof.
    revert M. induction l as [|p l IH]; intros M Hni; [reflexivity |].
    rewrite fmap_cons in Hni.
    assert (Hne : p.1 <> k).
    { intros <-. apply Hni. apply elem_of_cons. by left. }
    assert (Hsub : k ∉ l.*1).
    { intros Hc. apply Hni. apply elem_of_cons. by right. }
    simpl. rewrite (IH _ Hsub). by rewrite lookup_insert_ne.
  Qed.

  (** With distinct keys the fold is a lookup table. *)
  Lemma ins_list_nodup M l k v :
    NoDup l.*1 -> (k, v) ∈ l -> ins_list M l !! k = Some v.
  Proof.
    revert M. induction l as [|p l IH]; intros M Hnd Hin.
    - by apply not_elem_of_nil in Hin.
    - rewrite fmap_cons in Hnd. apply NoDup_cons in Hnd.
      destruct Hnd as [Hni Hnd].
      apply elem_of_cons in Hin. destruct Hin as [<- | Hin].
      + simpl in Hni. simpl. rewrite (ins_list_notin _ _ _ Hni).
        by rewrite lookup_insert_eq.
      + simpl. by apply IH.
  Qed.

  (** The inversion.  No [NoDup] is needed: a later write simply wins. *)
  Lemma ins_list_inv M l k v :
    ins_list M l !! k = Some v -> (k, v) ∈ l \/ ((k ∉ l.*1) /\ M !! k = Some v).
  Proof.
    revert M. induction l as [|p l IH]; intros M Hl.
    - right. split; [by apply not_elem_of_nil | exact Hl].
    - destruct (IH _ Hl) as [Hin | [Hni Hlk]].
      + left. apply elem_of_cons. by right.
      + destruct (decide (k = p.1)) as [Heq | Hne].
        * rewrite Heq in Hlk. rewrite lookup_insert_eq in Hlk.
          injection Hlk as <-. left. apply elem_of_cons. left.
          rewrite Heq. by destruct p.
        * rewrite lookup_insert_ne in Hlk; [| intros Hc; by apply Hne].
          right. split; [| exact Hlk]. rewrite fmap_cons.
          intros Hc. apply elem_of_cons in Hc.
          destruct Hc as [-> | Hc]; [by apply Hne | by apply Hni].
  Qed.

  (** When every entry carries the same value, the last write wins trivially
      and no [NoDup] is needed. *)
  Lemma ins_list_const M l k v :
    (k, v) ∈ l -> (forall p, p ∈ l -> p.2 = v) -> ins_list M l !! k = Some v.
  Proof.
    intros Hin Hval.
    destruct (ins_list_in M l k v Hin) as [v' Hlk].
    destruct (ins_list_inv _ _ _ _ Hlk) as [Hp | [Hni _]].
    - assert (Hv : v' = v) by exact (Hval (k, v') Hp). by rewrite Hv in Hlk.
    - exfalso. apply Hni. exact (list_elem_of_fmap_2 fst l (k, v) Hin).
  Qed.

End inslist.

(** ** The two bulk operations

    Each key of the list is written either because the thread holds its
    fragment or because the key is free.  [NoDup] on the keys is what carries
    "free" past the earlier writes in the fold. *)

Section ghost_bulk.
  Context `{!rcuG Σ}.

  (** The free-list counterpart of [obs_alloc_at], which the layer was missing
      for the same reason it was missing [fl_delete]. *)
  Lemma fl_alloc_at γ F o s :
    F !! o = None ->
    fl_auth γ F ==∗ fl_auth γ (<[o := s]> F) ∗ fl_ctl γ o s.
  Proof.
    iIntros (Hlk) "Ha".
    iMod (own_update _ _ (● (Excl <$> (<[o := s]> F)
                              : gmap Loc (excl (leibnizO nat)))
                          ⋅ ◯ {[o := Excl (s : leibnizO nat)]})
           with "Ha") as "[Ha Hf]".
    { rewrite fmap_insert. apply auth_update_alloc.
      apply alloc_singleton_local_update; [| done].
      by rewrite lookup_fmap Hlk. }
    iModIntro. iFrame.
  Qed.

  Lemma fl_upd_list γ (l : list (Loc * nat)) F :
    NoDup l.*1 ->
    ([∗ list] p ∈ l, (∃ s, fl_ctl γ p.1 s) ∨ ⌜F !! p.1 = None⌝) -∗
    fl_auth γ F ==∗
    fl_auth γ (ins_list F l) ∗ ([∗ list] p ∈ l, fl_ctl γ p.1 p.2).
  Proof.
    revert F. induction l as [|p l IH]; intros F Hnd.
    - iIntros "_ Ha". rewrite /ins_list /=. iModIntro. iFrame.
    - rewrite fmap_cons in Hnd. apply NoDup_cons in Hnd.
      destruct Hnd as [Hni Hnd].
      iIntros "[Hp Hl] Ha".
      iAssert (|==> fl_auth γ (<[p.1 := p.2]> F) ∗ fl_ctl γ p.1 p.2)%I
        with "[Hp Ha]" as ">[Ha Hc]".
      { iDestruct "Hp" as "[Hp | %Hn]".
        - iDestruct "Hp" as (s) "Hf". by iMod (fl_set with "Ha Hf") as "[$ $]".
        - by iMod (fl_alloc_at with "Ha") as "[$ $]". }
      iAssert ([∗ list] q ∈ l,
                 (∃ s, fl_ctl γ q.1 s) ∨ ⌜(<[p.1 := p.2]> F) !! q.1 = None⌝)%I
        with "[Hl]" as "Hl".
      { iApply (big_sepL_impl with "Hl"). iIntros "!>" (i q Hi) "Hq".
        iDestruct "Hq" as "[Hq | %Hn]"; [by iLeft |].
        iRight. iPureIntro.
        assert (Hin : q.1 ∈ l.*1).
        { apply (list_elem_of_fmap_2 fst).
          exact (list_elem_of_lookup_2 _ _ _ Hi). }
        rewrite lookup_insert_ne; [exact Hn |].
        intros Heq. apply Hni. rewrite Heq. exact Hin. }
      iMod (IH _ Hnd with "Hl Ha") as "[Ha Hl]".
      iModIntro. iFrame.
  Qed.

  Lemma tobs_upd_list γ (l : list ((Loc * TID) * gset obs)) Og :
    NoDup l.*1 ->
    ([∗ list] p ∈ l,
       (∃ s, tobs_ctl γ p.1.1 p.1.2 s) ∨ ⌜Og !! p.1 = None⌝) -∗
    tobs_auth γ Og ==∗
    tobs_auth γ (ins_list Og l)
    ∗ ([∗ list] p ∈ l, tobs_ctl γ p.1.1 p.1.2 p.2).
  Proof.
    revert Og. induction l as [|p l IH]; intros Og Hnd.
    - iIntros "_ Ha". rewrite /ins_list /=. iModIntro. iFrame.
    - rewrite fmap_cons in Hnd. apply NoDup_cons in Hnd.
      destruct Hnd as [Hni Hnd].
      iIntros "[Hp Hl] Ha".
      iAssert (|==> tobs_auth γ (<[p.1 := p.2]> Og)
                    ∗ tobs_ctl γ p.1.1 p.1.2 p.2)%I with "[Hp Ha]" as ">[Ha Hc]".
      { iDestruct "Hp" as "[Hp | %Hn]".
        - iDestruct "Hp" as (s) "Hf".
          destruct p as [[o t] sn]. simpl.
          by iMod (tobs_set with "Ha Hf") as "[$ $]".
        - destruct p as [[o t] sn]. simpl. simpl in Hn.
          by iMod (tobs_alloc_at with "Ha") as "[$ $]". }
      iAssert ([∗ list] q ∈ l,
                 (∃ s, tobs_ctl γ q.1.1 q.1.2 s)
                 ∨ ⌜(<[p.1 := p.2]> Og) !! q.1 = None⌝)%I
        with "[Hl]" as "Hl".
      { iApply (big_sepL_impl with "Hl"). iIntros "!>" (i q Hi) "Hq".
        iDestruct "Hq" as "[Hq | %Hn]"; [by iLeft |].
        iRight. iPureIntro.
        assert (Hin : q.1 ∈ l.*1).
        { apply (list_elem_of_fmap_2 fst).
          exact (list_elem_of_lookup_2 _ _ _ Hi). }
        rewrite lookup_insert_ne; [exact Hn |].
        intros Heq. apply Hni. rewrite Heq. exact Hin. }
      iMod (IH _ Hnd with "Hl Ha") as "[Ha Hl]".
      iModIntro. iFrame.
  Qed.

End ghost_bulk.

Print Assumptions fl_alloc_at.
Print Assumptions fl_upd_list.
Print Assumptions tobs_upd_list.

(** [ObsWF] survives a bulk write on the same condition a single one needs: the
    entries written record only their own thread's observations. *)
Lemma ObsWF_ins_list Og (l : list ((Loc * TID) * gset obs)) :
  ObsWF Og ->
  (forall p ob, p ∈ l -> ob ∈ p.2 -> obs_tid ob = Some p.1.2 \/ ob = Oroot) ->
  ObsWF (ins_list Og l).
Proof.
  intros HWF Hl o t s ob Hlk Hin.
  destruct (ins_list_inv _ _ _ _ Hlk) as [Hp | [_ Hold]].
  - exact (Hl ((o, t), s) ob Hp Hin).
  - exact (HWF o t s ob Hold Hin).
Qed.

(** * SyncStart, as a step on the invariant's contents

    The first of the five.  Its ghost update is a bulk write on the free list:
    every detached node gets an entry holding the snapshot of current readers,
    and nothing else has one.

    The list is a parameter rather than something computed, for the same reason
    [Og'] is a parameter in [Actions.v]: what matters is what the snapshot
    *is*, not how the implementation enumerates it.  What is no longer a
    parameter is the resulting map, which is now the fold, and the update that
    produces it, which is now a frame-preserving update rather than an
    assumption.

    [FLD] appears as a hypothesis because it is not a consequence of the
    nineteen -- see [free_list_domain_is_unconstrained].  Without it the step
    cannot re-establish "*exactly* the detached nodes have entries", because a
    stray entry inherited from the pre-state would survive the fold. *)

Section sync_start_step.
  Context `{!rcuG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  (** SyncStart in epoch terms, which is simpler than the snapshot version it
      replaces: there is no set to write, only a stamp, and the snapshot the
      published rule stores is what the registrations already say.  The bump of
      the counter is what separates the readers this grace period waits for
      from the ones that start after it. *)
  Lemma sync_start_update γo γf g Rg m Og U T St (l : list (Loc * nat)) :
    WellFormed FType (to_LState_t m Og U T (e_F (mkE g Rg St))) ->
    FLD (to_LState_t m Og U T (e_F (mkE g Rg St))) ->
    EWF (mkE g Rg St) ->
    RepresentsR (rds m) Rg ->
    NoDup l.*1 ->
    (* every node stamped is stamped with the current epoch *)
    (forall p, p ∈ l -> p.2 = g) ->
    (* every detached node is stamped *)
    (forall o t, (obsv (to_LState_t m Og U T (e_F (mkE g Rg St))) o (Ounlk t)
                  \/ obsv (to_LState_t m Og U T (e_F (mkE g Rg St))) o (Ofree t))
                 -> (o, g) ∈ l) ->
    (* and nothing else is *)
    (forall p, p ∈ l -> exists t,
        obsv (to_LState_t m Og U T (e_F (mkE g Rg St))) p.1 (Ounlk t)
        \/ obsv (to_LState_t m Og U T (e_F (mkE g Rg St))) p.1 (Ofree t)) ->
    ([∗ list] p ∈ l, (∃ s, fl_ctl γf p.1 s) ∨ ⌜St !! p.1 = None⌝) -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (sync_start_ms m)) -∗
    |==> phys (sync_start_ms m)
         ∗ tobs_auth γo Og
         ∗ fl_auth γf (ins_list St l)
         ∗ ([∗ list] p ∈ l, fl_ctl γf p.1 p.2)
         ∗ ⌜WellFormed FType
              (to_LState_t (sync_start_ms m) Og U T
                 (e_F (mkE (S g) Rg (ins_list St l))))⌝.
  Proof.
    iIntros (Hwf Hfld HEWF HRR Hnd Hval Hcov Hon) "Hfrags Hp Ho Hf Hstep".
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (fl_upd_list with "Hfrags Hf") as "[Hf Hfrags]"; [exact Hnd |].
    iModIntro. iFrame. iPureIntro.
    (* every stamp in the new map is the current epoch: the ones written are,
       and the ones already there were at detached nodes, so they were
       rewritten *)
    assert (Hallg : forall o e, ins_list St l !! o = Some e -> e = g).
    { intros o e Hlk.
      destruct (ins_list_inv _ _ _ _ Hlk) as [Hin | [Hni Hold]].
      - exact (Hval (o, e) Hin).
      - exfalso. apply Hni.
        assert (Hfl : flist (to_LState_t m Og U T (e_F (mkE g Rg St))) o
                      = Some (fun t => t ∈ e_snapshot (mkE g Rg St) e)).
        { simpl. unfold e_F. by rewrite lookup_fmap Hold. }
        destruct (Hfld o _ Hfl) as [t Hdet].
        exact (list_elem_of_fmap_2 fst l (o, g) (Hcov o t Hdet)). }
    (* and the snapshot at the current epoch is every registered reader *)
    assert (Hsnapg : e_snapshot (mkE (S g) Rg (ins_list St l)) g
                     = dom (ereg (mkE g Rg St))).
    { apply set_eq. intros t. rewrite e_snapshot_elem elem_of_dom. simpl.
      split; [by intros [e' [H _]] | intros [e' H]; exists e'; split;
        [exact H | exact (proj2 HEWF t e' H)]]. }
    eapply (sync_start_preserves_WellFormed FType m Og U T
              (e_F (mkE g Rg St)) (e_F (mkE (S g) Rg (ins_list St l)))
              (dom (ereg (mkE g Rg St))));
      [| | | | exact Hwf].
    - intros t. rewrite elem_of_dom. split.
      + intros [e' H]. apply HRR. exists e'. by apply (mkE_reg g Rg St t e').
      + intros Hrd. destruct (proj1 (HRR t) Hrd) as [e' H].
        exists e'. by apply (mkE_reg g Rg St t e').
    - intros o s0 Hlk. unfold e_F in Hlk. rewrite lookup_fmap in Hlk.
      apply fmap_Some in Hlk as [e [E Hq]].
      rewrite Hq (Hallg o e E). exact Hsnapg.
    - intros o t Hdet.
      assert (Hin : (o, g) ∈ l) by exact (Hcov o t Hdet).
      destruct (ins_list_in St l o g Hin) as [v' Hv'].
      exists (e_snapshot (mkE (S g) Rg (ins_list St l)) v').
      unfold e_F. by rewrite lookup_fmap Hv'.
    - intros o s0 Hlk. unfold e_F in Hlk. rewrite lookup_fmap in Hlk.
      apply fmap_Some in Hlk as [e [E Hq]].
      destruct (ins_list_inv _ _ _ _ E) as [Hin | [_ Hold]].
      + exact (Hon (o, e) Hin).
      + assert (Hfl : flist (to_LState_t m Og U T (e_F (mkE g Rg St))) o
                      = Some (fun t => t ∈ e_snapshot (mkE g Rg St) e)).
        { simpl. unfold e_F. by rewrite lookup_fmap Hold. }
        exact (Hfld o _ Hfl).
  Qed.

End sync_start_step.

Print Assumptions sync_start_update.

(** * SyncStop, as a step on the invariant's contents

    The grace period has elapsed and every [unlinked] observation becomes
    [freeable].  Stated that way it reads as a change to every thread's
    entries, which would make it the one action that is not thread-local -- a
    reader would have to surrender its fragments for the writer to recolour
    them.

    It is not.  WUNLK says only the writer holds a detaching observation, and
    [ObsWF] says an entry records only its own thread's, so the keys whose
    contents actually change are exactly the writer's.  Everywhere else
    [sync_obs] is the identity and no update is needed at all.  That is the
    step's real content, and it is where the invariant added in this
    development earns its place: without WUNLK the recolouring is global. *)

Lemma obs_tid_sync ob : obs_tid (sync_obs ob) = obs_tid ob.
Proof. by destruct ob. Qed.

Section sync_stop_step.
  Context `{!rcuG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  Lemma sync_stop_update γo γf m Og U T F St lw
        (l : list ((Loc * TID) * gset obs)) :
    WellFormed FType (to_LState_t m Og U T F) ->
    ObsWF Og ->
    lk m = Some lw ->
    (* SyncStop returns only once the grace period has completed *)
    (forall t, ~ bnd m t) ->
    NoDup l.*1 ->
    (* every key written is one of the writer's, and is recoloured *)
    (forall p, p ∈ l -> exists sg,
        Og !! p.1 = Some sg /\ p.1.2 = lw /\ p.2 = set_map sync_obs sg) ->
    (* and every one of the writer's keys is written *)
    (forall o sg, Og !! (o, lw) = Some sg ->
        ((o, lw), set_map sync_obs sg) ∈ l) ->
    ([∗ list] p ∈ l, (∃ s, tobs_ctl γo p.1.1 p.1.2 s) ∨ ⌜Og !! p.1 = None⌝) -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (sync_stop_ms m)) -∗
    |==> phys (sync_stop_ms m)
         ∗ tobs_auth γo (ins_list Og l)
         ∗ fl_auth γf St
         ∗ ([∗ list] p ∈ l, tobs_ctl γo p.1.1 p.1.2 p.2)
         ∗ ⌜ObsWF (ins_list Og l)⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (sync_stop_ms m) (ins_list Og l) U T F)⌝.
  Proof.
    iIntros (Hwf Hobs Hlk Hquiet Hnd Hval Hkeys) "Hfrags Hp Ho Hf Hstep".
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (tobs_upd_list with "Hfrags Ho") as "[Ho Hfrags]"; [exact Hnd |].
    iModIntro. iFrame. iPureIntro.
    (* [ObsWF] first: the recolouring keeps every tag where it was *)
    assert (HobsWF' : ObsWF (ins_list Og l)).
    { apply ObsWF_ins_list; [exact Hobs |].
      intros p ob Hp Hin. destruct p as [[o t] v]. simpl in *.
      destruct (Hval _ Hp) as [sg [Hog [Ht Hv]]]. simpl in Hog, Ht, Hv.
      rewrite Hv in Hin. apply elem_of_map in Hin.
      destruct Hin as [ob0 [-> Hin0]].
      destruct (Hobs o t sg ob0 Hog Hin0) as [Htid | ->].
      - left. by rewrite obs_tid_sync.
      - by right. }
    split; [exact HobsWF' |].
    apply (sync_stop_preserves_WellFormed FType m Og (ins_list Og l) U T F);
      [| | exact Hquiet | exact Hwf].
    - (* Hfwd: nothing appears that was not there, except [freeable] *)
      intros o ob H. destruct H as [t [sg' [Hlk' Hin]]].
      destruct (ins_list_inv _ _ _ _ Hlk') as [Hp | [_ Hold]].
      + destruct (Hval _ Hp) as [sg [Hog [Ht Hv]]]. simpl in Hog, Hv.
        rewrite Hv in Hin. apply elem_of_map in Hin.
        destruct Hin as [ob0 [-> Hin0]].
        destruct ob0 as [t0|t0|t0|t0|]; simpl.
        * left. by exists t, sg.
        * right. exists t0. split; [reflexivity | by exists t, sg].
        * left. by exists t, sg.
        * left. by exists t, sg.
        * left. by exists t, sg.
      + left. by exists t, sg'.
    - (* Hmap: everything survives, [unlinked] as [freeable] *)
      intros o ob H. destruct H as [t [sg [Hog Hin]]].
      destruct (decide ((o, t) ∈ l.*1)) as [Hinl | Hnil].
      + apply list_elem_of_fmap_1 in Hinl.
        destruct Hinl as [p [Hp1 Hpin]]. destruct p as [k v]. simpl in Hp1.
        subst k.
        destruct (Hval _ Hpin) as [sg0 [Hog0 [_ Hv]]]. simpl in Hog0, Hv.
        rewrite Hog in Hog0. injection Hog0 as <-.
        exists t, v. split.
        * exact (ins_list_nodup Og l (o, t) v Hnd Hpin).
        * rewrite Hv. apply elem_of_map. by exists ob.
      + (* an unwritten key: [sync_obs] is the identity there *)
        assert (Hid : sync_obs ob = ob).
        { destruct ob as [t0|t0|t0|t0|]; try reflexivity. exfalso.
          destruct (Hobs o t sg (Ounlk t0) Hog Hin) as [Htid | Hc];
            [| discriminate].
          simpl in Htid. injection Htid as Heq. subst t0.
          assert (Ht : t = lw).
          { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                             _ & _ & _ & _ & _ & HWU & _).
            apply (HWU o t lw Hlk). left. by exists t, sg. }
          subst t. apply Hnil.
          exact (list_elem_of_fmap_2 fst l ((o, lw), set_map sync_obs sg)
                   (Hkeys o sg Hog)). }
        rewrite Hid. exists t, sg. split; [| exact Hin].
        by rewrite (ins_list_notin Og l (o, t) Hnil).
  Qed.

End sync_stop_step.

Print Assumptions sync_stop_update.

(** * WriteBegin, as a step on the invariant's contents

    The incoming writer takes an iterator on everything reachable.  Its ghost
    update is a bulk write at the writer's own keys: at a node it already has
    an entry for, the entry grows by [iterator]; at one it does not, an entry
    is created.  The mixed form is why [fl_upd_list] and [tobs_upd_list] take
    "the thread holds the fragment, or the key is free" rather than insisting
    on ownership.

    The UNQRT-b obligation recorded with the mutation rules is untouched here:
    it is discharged upstream, by whatever shows the grant is legitimate, and
    the two directions of the observation change are hypotheses of the action
    lemma exactly as they were. *)

Section write_begin_step.
  Context `{!rcuG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  Lemma write_begin_update γo γf m Og U T F St lw
        (l : list ((Loc * TID) * gset obs)) :
    WellFormed FType (to_LState_t m Og U T F) ->
    ObsWF Og ->
    lk m = None ->
    ~ rds m lw ->
    (* the state the previous WriteEnd left behind *)
    (forall o, ~ Detached (to_LState_t m Og U T F) o) ->
    (forall q o, Reaches (to_LState_t m Og U T F) q o ->
        flist (to_LState_t m Og U T F) o = None) ->
    NoDup l.*1 ->
    (* every key written is the writer's own, at a reachable node *)
    (forall p, p ∈ l -> p.1.2 = lw) ->
    (forall p, p ∈ l ->
        exists q, Reaches (to_LState_t m Og U T F) q p.1.1) ->
    (* every reachable node is written *)
    (forall q o, Reaches (to_LState_t m Og U T F) q o ->
        exists v, ((o, lw), v) ∈ l) ->
    (* and each entry written is the old one plus [iterator] *)
    (forall p, p ∈ l -> Oiter lw ∈ p.2) ->
    (forall p ob, p ∈ l ->
        (exists sg, Og !! p.1 = Some sg /\ ob ∈ sg) -> ob ∈ p.2) ->
    (forall p ob, p ∈ l -> ob ∈ p.2 ->
        ob = Oiter lw \/ (exists sg, Og !! p.1 = Some sg /\ ob ∈ sg)) ->
    ([∗ list] p ∈ l, (∃ s, tobs_ctl γo p.1.1 p.1.2 s) ∨ ⌜Og !! p.1 = None⌝) -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (write_begin_ms m lw)) -∗
    |==> phys (write_begin_ms m lw)
         ∗ tobs_auth γo (ins_list Og l)
         ∗ fl_auth γf St
         ∗ ([∗ list] p ∈ l, tobs_ctl γo p.1.1 p.1.2 p.2)
         ∗ ⌜ObsWF (ins_list Og l)⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (write_begin_ms m lw) (ins_list Og l) U T F)⌝.
  Proof.
    iIntros (Hwf Hobs Hlk Hnotrd Hclean Hrfl Hnd Hkey Hreach Hcovers
             Hiter Hgrow Hcontent) "Hfrags Hp Ho Hf Hstep".
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (tobs_upd_list with "Hfrags Ho") as "[Ho Hfrags]"; [exact Hnd |].
    iModIntro. iFrame. iPureIntro.
    assert (HobsWF' : ObsWF (ins_list Og l)).
    { apply ObsWF_ins_list; [exact Hobs |].
      intros p ob Hp Hin. destruct p as [[o t] v]. simpl in *.
      assert (Ht : t = lw) by exact (Hkey ((o, t), v) Hp). subst t.
      destruct (Hcontent ((o, lw), v) ob Hp Hin) as [-> | [sg [Hog Hin0]]].
      - by left.
      - simpl in Hog. exact (Hobs o lw sg ob Hog Hin0). }
    split; [exact HobsWF' |].
    apply (write_begin_preserves_WellFormed FType m Og (ins_list Og l)
             U T F lw Hlk Hnotrd); [| | | exact Hclean | exact Hrfl | exact Hwf].
    - (* Hcover *)
      intros q o Hr. destruct (Hcovers q o Hr) as [v Hv].
      left. exists lw, v. split.
      + exact (ins_list_nodup Og l (o, lw) v Hnd Hv).
      + exact (Hiter ((o, lw), v) Hv).
    - (* Hnew *)
      intros o ob H. destruct H as [t [sg' [Hlk' Hin]]].
      destruct (ins_list_inv _ _ _ _ Hlk') as [Hp | [_ Hold]].
      + destruct (Hcontent _ ob Hp Hin) as [-> | [sg [Hog Hin0]]].
        * right. split; [reflexivity |].
          destruct (Hreach _ Hp) as [q Hr]. by exists q.
        * left. by exists t, sg.
      + left. by exists t, sg'.
    - (* Hkeep *)
      intros o ob H. destruct H as [t [sg [Hog Hin]]].
      destruct (decide ((o, t) ∈ l.*1)) as [Hi | Hn].
      + apply list_elem_of_fmap_1 in Hi.
        destruct Hi as [p [Hp1 Hpin]]. destruct p as [k v]. simpl in Hp1.
        subst k. exists t, v. split.
        * exact (ins_list_nodup Og l (o, t) v Hnd Hpin).
        * apply (Hgrow ((o, t), v) ob Hpin). by exists sg.
      + exists t, sg. split; [| exact Hin].
        by rewrite (ins_list_notin Og l (o, t) Hn).
  Qed.

End write_begin_step.

Print Assumptions write_begin_update.

(** * Retiring a thread's entries

    ReadEnd and WriteEnd are the same ghost step with different physical ones:
    a thread's observations go away.  "Go away" is not quite right, and the
    difference matters.  The anonymous root observation can be filed under any
    thread -- [ObsWF] permits it, and [ce_Og] in [Actions.v] is a state where
    it is filed under a reader -- and the action lemmas require it to survive a
    departure.  So the retirement keeps [Oroot] and drops everything else,
    which is what makes [Hkeep] provable rather than an extra assumption about
    where the root lives.

    The three pure lemmas below are shared; only the physical step and the free
    list differ between the two actions. *)

Lemma retire_ObsWF Og (l : list ((Loc * TID) * gset obs)) :
  ObsWF Og ->
  (forall p, p ∈ l -> exists sg, Og !! p.1 = Some sg
      /\ (forall ob, ob ∈ p.2 <-> (ob = Oroot /\ Oroot ∈ sg))) ->
  ObsWF (ins_list Og l).
Proof.
  intros Hobs Hval. apply ObsWF_ins_list; [exact Hobs |].
  intros p ob Hp Hin. destruct (Hval _ Hp) as [sg [_ Hch]].
  right. exact (proj1 (proj1 (Hch ob) Hin)).
Qed.

Lemma retire_self Og l t m U T F o ob :
  ObsWF Og -> NoDup l.*1 ->
  (forall p, p ∈ l -> exists sg, Og !! p.1 = Some sg
      /\ (forall ob, ob ∈ p.2 <-> (ob = Oroot /\ Oroot ∈ sg))) ->
  (forall o' sg ob', Og !! (o', t) = Some sg -> ob' ∈ sg ->
     obs_tid ob' = Some t -> exists v, ((o', t), v) ∈ l) ->
  obs_tid ob = Some t ->
  ~ obsv (to_LState_t m (ins_list Og l) U T F) o ob.
Proof.
  intros Hobs Hnd Hval Hcov Htid [t' [sg' [Hlk Hin]]].
  destruct (ins_list_inv _ _ _ _ Hlk) as [Hp | [Hni Hold]].
  - destruct (Hval _ Hp) as [sg [_ Hch]].
    rewrite (proj1 (proj1 (Hch ob) Hin)) in Htid. discriminate.
  - assert (Ht : t' = t).
    { destruct (Hobs o t' sg' ob Hold Hin) as [Hx | Hy].
      - rewrite Htid in Hx. injection Hx as Hq. by rewrite Hq.
      - rewrite Hy in Htid. discriminate. }
    subst t'. destruct (Hcov o sg' ob Hold Hin Htid) as [v Hv].
    apply Hni. exact (list_elem_of_fmap_2 fst l ((o, t), v) Hv).
Qed.

Lemma retire_keep Og l t m U T F m' U' T' F' o ob :
  ObsWF Og -> NoDup l.*1 ->
  (forall p, p ∈ l -> p.1.2 = t) ->
  (forall p, p ∈ l -> exists sg, Og !! p.1 = Some sg
      /\ (forall ob, ob ∈ p.2 <-> (ob = Oroot /\ Oroot ∈ sg))) ->
  obsv (to_LState_t m Og U T F) o ob ->
  obs_tid ob <> Some t ->
  obsv (to_LState_t m' (ins_list Og l) U' T' F') o ob.
Proof.
  intros Hobs Hnd Hkey Hval [t' [sg [Hold Hin]]] Htid.
  destruct (decide ((o, t') ∈ l.*1)) as [Hi | Hn].
  - apply list_elem_of_fmap_1 in Hi. destruct Hi as [p [Hp1 Hpin]].
    destruct p as [k v]. simpl in Hp1. subst k.
    destruct (Hval _ Hpin) as [sg0 [Hog Hch]]. simpl in Hog.
    rewrite Hold in Hog. injection Hog as <-.
    assert (Hroot : ob = Oroot).
    { destruct (Hobs o t' sg ob Hold Hin) as [Hx | Hy]; [| exact Hy].
      exfalso. apply Htid. rewrite Hx.
      assert (Ht' : t' = t) by exact (Hkey ((o, t'), v) Hpin).
      by rewrite Ht'. }
    exists t', v. split.
    + exact (ins_list_nodup Og l (o, t') v Hnd Hpin).
    + apply Hch. split; [exact Hroot | rewrite -Hroot; exact Hin].
  - exists t', sg. split; [| exact Hin].
    by rewrite (ins_list_notin Og l (o, t') Hn).
Qed.

Lemma retire_shrink Og l m U T F m' U' T' F' o ob :
  (forall p, p ∈ l -> exists sg, Og !! p.1 = Some sg
      /\ (forall ob, ob ∈ p.2 <-> (ob = Oroot /\ Oroot ∈ sg))) ->
  obsv (to_LState_t m (ins_list Og l) U T F) o ob ->
  obsv (to_LState_t m' Og U' T' F') o ob.
Proof.
  intros Hval [t' [sg' [Hlk Hin]]].
  destruct (ins_list_inv _ _ _ _ Hlk) as [Hp | [_ Hold]].
  - destruct (Hval _ Hp) as [sg [Hog Hch]]. simpl in Hog.
    destruct (proj1 (Hch ob) Hin) as [Hr Hin0].
    rewrite Hr. by exists t', sg.
  - by exists t', sg'.
Qed.

(** The free list under ReadEnd is a map over every entry, and the fold
    reproduces it. *)
Lemma ins_list_read_end F t lF :
  NoDup lF.*1 ->
  (forall p, p ∈ lF -> exists s, F !! p.1 = Some s /\ p.2 = s ∖ {[t]}) ->
  (forall o s, F !! o = Some s -> (o, s ∖ {[t]}) ∈ lF) ->
  ins_list F lF = read_end_F F t.
Proof.
  intros Hnd Hval Hcov. apply map_eq. intros k.
  unfold read_end_F. rewrite lookup_fmap.
  destruct (F !! k) as [s|] eqn:Hs; simpl.
  - by rewrite (ins_list_nodup F lF k (s ∖ {[t]}) Hnd (Hcov k s Hs)).
  - rewrite -Hs. apply ins_list_notin. intros Hi.
    apply list_elem_of_fmap_1 in Hi. destruct Hi as [p [Hp1 Hpin]].
    destruct (Hval _ Hpin) as [s [Hlk _]].
    rewrite -Hp1 in Hlk. rewrite Hs in Hlk. discriminate.
Qed.

(** * ReadEnd, as a step on the invariant's contents

    Two bulk updates: the departing reader's observations are retired, and the
    free list loses it from every snapshot it appears in.

    The second is where the encoding pushes back.  [flUR] gives each node's
    snapshot as one exclusive entry, so a reader that wants to remove itself
    from a snapshot must hold the whole entry -- which is the precondition
    below, and which is wrong in the same way the location-keyed observation
    map was wrong: it makes a per-thread act require a whole-structure
    resource.  The repair is the same one, a step further down: the free-list
    value should be a [gset_disj] of tickets so that a reader owns its own
    membership and deallocates that, rather than rewriting the set.  It is
    recorded here rather than done because it changes the camera under all of
    SyncStart, Free and IFL, and that is a change to make deliberately.

    One cheaper repair suggests itself and does not work, and the development
    now records why: leave the entries alone and read a snapshot against the
    threads still running.  That would make ReadEnd touch nothing but its own
    reader cell, and it is unsound, because a thread that leaves its read
    section and enters a new one is a reader again and rejoins every snapshot it
    was ever in.  [reentry_breaks_the_intersected_reading] in [Actions.v] is the
    witness, and the failure appears at ReadBegin rather than at ReadEnd, which
    is why it is worth having tried. *)

Section read_end_step.
  Context `{!rcuG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  (** ReadEnd, and it is now a thread-local step.  The departing reader clears
      its own registration; the free list is not touched, because the snapshots
      it appears in are derived from that registration.  [mkE_F_end] is the
      equation -- what the clearing does to the derived free list is exactly
      the published rule's [read_end_F]. *)
  Lemma read_end_update γo γe g Rg m Og U T St t e
        (l : list ((Loc * TID) * gset obs)) :
    WellFormed FType (to_LState_t m Og U T (e_F (mkE g Rg St))) ->
    ObsWF Og ->
    rds m t ->
    (* the observation retirement, unchanged from the snapshot version *)
    NoDup l.*1 ->
    (forall p, p ∈ l -> p.1.2 = t) ->
    (forall p, p ∈ l -> exists sg, Og !! p.1 = Some sg
        /\ (forall ob, ob ∈ p.2 <-> (ob = Oroot /\ Oroot ∈ sg))) ->
    (forall o sg ob, Og !! (o, t) = Some sg -> ob ∈ sg ->
       obs_tid ob = Some t -> exists v, ((o, t), v) ∈ l) ->
    ([∗ list] p ∈ l, (∃ s, tobs_ctl γo p.1.1 p.1.2 s) ∨ ⌜Og !! p.1 = None⌝) -∗
    (* and the reader's own cell, which is the whole of the free-list half *)
    reg_cell γe t (Some e) -∗
    phys m -∗ tobs_auth γo Og -∗ reg_auth γe Rg -∗
    (phys m ==∗ phys (read_end_ms m t)) -∗
    |==> phys (read_end_ms m t)
         ∗ tobs_auth γo (ins_list Og l)
         ∗ reg_auth γe (<[t := None]> Rg)
         ∗ reg_cell γe t None
         ∗ ([∗ list] p ∈ l, tobs_ctl γo p.1.1 p.1.2 p.2)
         ∗ ⌜ObsWF (ins_list Og l)⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (read_end_ms m t) (ins_list Og l)
                 (fun x t' => U x t' \/ t' = t) T
                 (e_F (mkE g (<[t := None]> Rg) St)))⌝.
  Proof.
    iIntros (Hwf Hobs Hrd Hnd Hkey Hval Hcov) "Hog Hcell Hp Ho Hr Hstep".
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (tobs_upd_list with "Hog Ho") as "[Ho Hog]"; [exact Hnd |].
    iMod (reg_cell_update _ _ _ _ None with "Hr Hcell") as "[Hr Hcell]".
    iModIntro. iFrame. iPureIntro. split.
    - exact (retire_ObsWF Og l Hobs Hval).
    - rewrite mkE_F_end.
      apply (read_end_preserves_WellFormed FType m Og (ins_list Og l)
               U (fun x t' => U x t' \/ t' = t) T (e_F (mkE g Rg St)) t);
        [| | | | | exact Hrd | exact Hwf].
      + intros o ob Htid. exact (retire_self Og l t _ _ _ _ o ob
                                   Hobs Hnd Hval Hcov Htid).
      + intros o ob H Htid. exact (retire_keep Og l t _ _ _ _ _ _ _ _ o ob
                                     Hobs Hnd Hkey Hval H Htid).
      + intros o ob H. exact (retire_shrink Og l _ _ _ _ _ _ _ _ o ob Hval H).
      + intros x. simpl. by right.
      + intros x t' H. simpl. by left.
  Qed.

End read_end_step.

Print Assumptions read_end_update.

(** * WriteEnd, as a step on the invariant's contents

    The writer's turn, and the shorter of the two: the free list is untouched,
    because the rule requires nothing to be detached when the lock is released.
    Only the writer's observations are retired. *)

Section write_end_step.
  Context `{!rcuG Σ, !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (phys : MState -> iProp Σ).

  Lemma write_end_update γo γf m Og U T F St lw
        (l : list ((Loc * TID) * gset obs)) :
    WellFormed FType (to_LState_t m Og U T F) ->
    ObsWF Og ->
    lk m = Some lw ->
    (forall o, ~ Detached (to_LState_t m Og U T F) o) ->
    NoDup l.*1 ->
    (forall p, p ∈ l -> p.1.2 = lw) ->
    (forall p, p ∈ l -> exists sg, Og !! p.1 = Some sg
        /\ (forall ob, ob ∈ p.2 <-> (ob = Oroot /\ Oroot ∈ sg))) ->
    (forall o sg, Og !! (o, lw) = Some sg -> exists v, ((o, lw), v) ∈ l) ->
    ([∗ list] p ∈ l, (∃ s, tobs_ctl γo p.1.1 p.1.2 s) ∨ ⌜Og !! p.1 = None⌝) -∗
    phys m -∗ tobs_auth γo Og -∗ fl_auth γf St -∗
    (phys m ==∗ phys (write_end_ms m)) -∗
    |==> phys (write_end_ms m)
         ∗ tobs_auth γo (ins_list Og l)
         ∗ fl_auth γf St
         ∗ ([∗ list] p ∈ l, tobs_ctl γo p.1.1 p.1.2 p.2)
         ∗ ⌜ObsWF (ins_list Og l)⌝
         ∗ ⌜WellFormed FType
              (to_LState_t (write_end_ms m) (ins_list Og l)
                 (fun x t' => U x t' \/ t' = lw) T F)⌝.
  Proof.
    iIntros (Hwf Hobs Hlk Hclean Hnd Hkey Hval Hcov) "Hog Hp Ho Hf Hstep".
    iMod ("Hstep" with "Hp") as "Hp".
    iMod (tobs_upd_list with "Hog Ho") as "[Ho Hog]"; [exact Hnd |].
    iModIntro. iFrame. iPureIntro. split.
    - exact (retire_ObsWF Og l Hobs Hval).
    - apply (write_end_preserves_WellFormed FType m Og (ins_list Og l)
               U (fun x t' => U x t' \/ t' = lw) T F lw Hlk);
        [| | | | | exact Hclean | exact Hwf].
      + intros o ob Htid. exact (retire_self Og l lw _ _ _ _ o ob
                                   Hobs Hnd Hval
                                   (fun o' sg ob' H _ _ => Hcov o' sg H) Htid).
      + intros o ob H Htid. exact (retire_keep Og l lw _ _ _ _ _ _ _ _ o ob
                                     Hobs Hnd Hkey Hval H Htid).
      + intros o ob H. exact (retire_shrink Og l _ _ _ _ _ _ _ _ o ob Hval H).
      + intros x. simpl. by right.
      + intros x t' H. simpl. by left.
  Qed.

End write_end_step.

Print Assumptions write_end_update.

(** * The heap, finite

    Everything above leaves the physical state a parameter and the physical step
    a hypothesis.  Choosing [phys] is what turns a step on the invariant's
    contents into a Hoare triple, and attempting it is what found the last
    defect.

    The standard choice is a heap of points-to assertions, so that a thread's
    right to write a field is a resource and the physical step is licensed by
    holding it.  That choice was not available.  Allocation as originally
    written gave the new node *every* field name, and field names are drawn from
    an infinite supply, so one allocation put infinitely many cells in the heap.
    No finite map represents such a heap, so there is no [gen_heap] over it and
    no camera of the usual shape either: they are all built on finite maps.  And
    without points-to, a rule whose premise mentions the heap -- every mutation
    rule -- cannot be stated outside the invariant at all, because the heap is
    bound inside it.

    [alloc_all] below is the original, kept so the defect can be stated, and
    [no_finite_heap_map] is the proof.  [alloc] now takes the node's field list,
    and the rest of this section is the consequence: a finite heap, a points-to
    assertion, and the mutation rules stated with their premises carried by
    resources rather than assumed. *)

Definition alloc_all (h : Heap) (n : Loc) : Heap :=
  fun o f => if Nat.eq_dec o n then Some VNull else h o f.

Lemma alloc_all_same h n f : alloc_all h n n f = Some VNull.
Proof. unfold alloc_all. destruct (Nat.eq_dec n n); congruence. Qed.

(** The defect: no finite map represents the heap after one allocation. *)
Lemma no_finite_heap_map (h : Heap) (n : Loc) (H : gmap (Loc * FName) Val) :
  ~ (forall o f, alloc_all h n o f = H !! (o, f)).
Proof.
  intros Hrep.
  assert (Hall : forall f, H !! (n, f) = Some VNull).
  { intros f. rewrite -Hrep. by rewrite alloc_all_same. }
  assert (Hin : fresh (set_map snd (dom H) : gset FName)
                  ∈ (set_map snd (dom H) : gset FName)).
  { apply elem_of_map.
    exists (n, fresh (set_map snd (dom H) : gset FName)).
    split; [reflexivity |]. apply elem_of_dom. exists VNull. exact (Hall _). }
  exact (is_fresh (set_map snd (dom H) : gset FName) Hin).
Qed.

Print Assumptions no_finite_heap_map.

(** ** Representation

    [Represents h H] says the finite map [H] is the heap [h].  The three
    heap-changing operations preserve it, which is the repair's payoff: the
    heap is finite if it starts finite, so it has a camera. *)

Definition Represents (h : Heap) (H : gmap (Loc * FName) Val) : Prop :=
  forall o f, h o f = H !! (o, f).

Lemma Represents_empty : Represents (fun _ _ => None) ∅.
Proof. intros o f. by rewrite lookup_empty. Qed.

Lemma Represents_upd h H o f v :
  Represents h H -> Represents (upd h o f v) (<[(o, f) := v]> H).
Proof.
  intros HR q g. destruct (decide ((q, g) = (o, f))) as [Heq | Hne].
  - injection Heq as -> ->. rewrite lookup_insert_eq. by rewrite upd_same.
  - rewrite lookup_insert_ne; [| intros Hc; apply Hne; by rewrite Hc].
    rewrite -HR. by apply upd_other.
Qed.

Lemma Represents_free h H d :
  Represents h H -> Represents (free h d) (filter (fun kv => kv.1.1 <> d) H).
Proof.
  intros HR o f. destruct (Nat.eq_dec o d) as [->|Hne].
  - rewrite free_same. symmetry. apply map_lookup_filter_None. right.
    intros v _ Hc. exact (Hc eq_refl).
  - rewrite (free_other h d o f Hne) HR.
    destruct (H !! (o, f)) as [v|] eqn:E.
    + symmetry. apply map_lookup_filter_Some. split; [exact E | by simpl].
    + symmetry. apply map_lookup_filter_None. by left.
Qed.

Lemma Represents_alloc h H n fs :
  Represents h H ->
  Represents (alloc h n fs)
             (ins_list H ((fun f => ((n, f), VNull)) <$> fs)).
Proof.
  intros HR o f.
  destruct (Nat.eq_dec o n) as [->|Hne].
  - destruct (in_dec Nat.eq_dec f fs) as [Hin | Hni].
    + rewrite (alloc_same h n fs f Hin). symmetry.
      apply ins_list_const.
      * apply (list_elem_of_fmap_2 (fun g => ((n, g), VNull)) fs f).
        by apply list_elem_of_In.
      * intros p Hp. apply list_elem_of_fmap_1 in Hp.
        destruct Hp as [g [-> _]]. reflexivity.
    + rewrite (alloc_miss h n fs f Hni) HR. symmetry.
      apply ins_list_notin. intros Hc.
      apply list_elem_of_fmap_1 in Hc. destruct Hc as [p [Hp1 Hpin]].
      apply list_elem_of_fmap_1 in Hpin. destruct Hpin as [g [-> Hg]].
      simpl in Hp1. injection Hp1 as Hp1. apply Hni.
      apply list_elem_of_In. by rewrite Hp1.
  - rewrite (alloc_other h n fs o f Hne) HR. symmetry.
    apply ins_list_notin. intros Hc.
    apply list_elem_of_fmap_1 in Hc. destruct Hc as [p [Hp1 Hpin]].
    apply list_elem_of_fmap_1 in Hpin. destruct Hpin as [g [-> Hg]].
    simpl in Hp1. by injection Hp1 as Hp1.
Qed.

(** ** The heap as ghost state

    With a finite heap there is a camera of the usual shape, and a points-to
    assertion.  This is the same construction as the free list's, one key per
    cell, and exclusive because a writer that holds a cell is the only thread
    that may change it. *)

Definition hpUR : ucmra :=
  authUR (gmapUR (Loc * FName) (exclR (leibnizO Val))).

Class heapG (Σ : gFunctors) := HeapG { heap_inG :: inG Σ hpUR }.
Definition heapΣ : gFunctors := #[ GFunctor hpUR ].
Global Instance subG_heapΣ {Σ} : subG heapΣ Σ -> heapG Σ.
Proof. solve_inG. Qed.

(** Deleting a list of keys, for reclamation. *)
Definition del_list {K A} `{EqDecision K, !Countable K}
    (M : gmap K A) (ks : list K) : gmap K A :=
  foldl (fun M k => delete k M) M ks.

Section dellist.
  Context {K A : Type} `{EqDecision K, !Countable K}.

  Lemma del_list_notin (M : gmap K A) ks k :
    k ∉ ks -> del_list M ks !! k = M !! k.
  Proof.
    revert M. induction ks as [|k0 ks IH]; intros M Hni; [reflexivity |].
    assert (Hne : k0 <> k).
    { intros <-. apply Hni. apply elem_of_cons. by left. }
    assert (Hsub : k ∉ ks).
    { intros Hc. apply Hni. apply elem_of_cons. by right. }
    simpl. rewrite (IH _ Hsub). by rewrite lookup_delete_ne.
  Qed.

  Lemma del_list_in (M : gmap K A) ks k : k ∈ ks -> del_list M ks !! k = None.
  Proof.
    revert M. induction ks as [|k0 ks IH]; intros M Hin.
    - by apply not_elem_of_nil in Hin.
    - apply elem_of_cons in Hin. simpl.
      destruct (decide (k ∈ ks)) as [Hi | Hni]; [by apply IH |].
      destruct Hin as [Heq | Hc]; [| by contradiction].
      rewrite (del_list_notin (delete k0 M) ks k Hni).
      rewrite Heq. by rewrite lookup_delete_eq.
  Qed.

End dellist.

Section heapghost.
  Context `{!heapG Σ}.

  Definition hp_auth (γ : gname) (H : gmap (Loc * FName) Val) : iProp Σ :=
    own γ (● (Excl <$> H : gmap (Loc * FName) (excl (leibnizO Val)))).
  Definition pt (γ : gname) (o : Loc) (f : FName) (v : Val) : iProp Σ :=
    own γ (◯ {[ (o, f) := Excl (v : leibnizO Val) ]}).

  Global Instance hp_auth_timeless γ H : Timeless (hp_auth γ H).
  Proof. apply _. Qed.
  Global Instance pt_timeless γ o f v : Timeless (pt γ o f v).
  Proof. apply _. Qed.

  Lemma hp_alloc : ⊢ |==> ∃ γ, hp_auth γ ∅.
  Proof.
    iMod (own_alloc (● (Excl <$> (∅ : gmap (Loc * FName) Val)
                        : gmap (Loc * FName) (excl (leibnizO Val))))) as (γ) "H".
    { rewrite fmap_empty. by apply auth_auth_valid. }
    iModIntro. by iExists γ.
  Qed.

  (** A held cell says what the heap holds.  This is what carries a mutation
      rule's premise across the invariant boundary. *)
  Lemma pt_agree γ H o f v :
    hp_auth γ H -∗ pt γ o f v -∗ ⌜H !! (o, f) = Some v⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply singleton_included_l in Hincl as [y [Hlk Hle]].
    rewrite lookup_fmap in Hlk.
    apply fmap_Some_equiv in Hlk as [v0 [Hv0 Hy]].
    rewrite Hv0. f_equal.
    rewrite Hy Excl_included in Hle.
    exact (eq_sym Hle).
  Qed.

  Lemma pt_update γ H o f v v' :
    hp_auth γ H -∗ pt γ o f v ==∗ hp_auth γ (<[(o, f) := v']> H) ∗ pt γ o f v'.
  Proof.
    iIntros "Ha Hf". rewrite /hp_auth /pt.
    iMod (own_update_2 _ _ _ (● (Excl <$> (<[(o, f) := v']> H)
                                 : gmap (Loc * FName) (excl (leibnizO Val)))
                              ⋅ ◯ {[(o, f) := Excl (v' : leibnizO Val)]})
           with "Ha Hf") as "[Ha Hf]".
    { rewrite fmap_insert. apply auth_update.
      apply singleton_local_update_any.
      intros y _. by apply exclusive_local_update. }
    iModIntro. iFrame.
  Qed.

  Lemma pt_alloc_at γ H o f v :
    H !! (o, f) = None ->
    hp_auth γ H ==∗ hp_auth γ (<[(o, f) := v]> H) ∗ pt γ o f v.
  Proof.
    iIntros (Hlk) "Ha". rewrite /hp_auth /pt.
    iMod (own_update _ _ (● (Excl <$> (<[(o, f) := v]> H)
                             : gmap (Loc * FName) (excl (leibnizO Val)))
                          ⋅ ◯ {[(o, f) := Excl (v : leibnizO Val)]})
           with "Ha") as "[Ha Hf]".
    { rewrite fmap_insert. apply auth_update_alloc.
      apply alloc_singleton_local_update; [| done].
      by rewrite lookup_fmap Hlk. }
    iModIntro. iFrame.
  Qed.

  Lemma pt_delete γ H o f v :
    hp_auth γ H -∗ pt γ o f v ==∗ hp_auth γ (delete (o, f) H).
  Proof.
    iIntros "Ha Hc". rewrite /hp_auth /pt. rewrite fmap_delete.
    iMod (own_update_2 with "Ha Hc") as "Hr".
    { apply auth_update.
      apply (delete_local_update _ _ (o, f) (Excl (v : leibnizO Val))).
      by rewrite lookup_singleton_eq. }
    iDestruct "Hr" as "[Hr _]". by iModIntro.
  Qed.

  (** Bulk versions, for allocation and reclamation. *)
  Lemma pt_alloc_list γ (l : list ((Loc * FName) * Val)) H :
    NoDup l.*1 ->
    (forall p, p ∈ l -> H !! p.1 = None) ->
    hp_auth γ H ==∗
    hp_auth γ (ins_list H l) ∗ ([∗ list] p ∈ l, pt γ p.1.1 p.1.2 p.2).
  Proof.
    revert H. induction l as [|p l IH]; intros H Hnd Hfree.
    - iIntros "Ha". rewrite /ins_list /=. iModIntro. iFrame.
    - rewrite fmap_cons in Hnd. apply NoDup_cons in Hnd.
      destruct Hnd as [Hni Hnd].
      iIntros "Ha". destruct p as [[o f] v]. simpl.
      iMod (pt_alloc_at with "Ha") as "[Ha Hc]".
      { apply (Hfree ((o, f), v)). apply elem_of_cons. by left. }
      iMod (IH (<[(o, f) := v]> H) Hnd with "Ha") as "[Ha Hl]".
      { intros q Hq. rewrite lookup_insert_ne.
        - apply Hfree. apply elem_of_cons. by right.
        - intros Heq. apply Hni.
          assert (Hq1 : q.1 ∈ l.*1) by exact (list_elem_of_fmap_2 fst l q Hq).
          by rewrite Heq. }
      iModIntro. iFrame.
  Qed.

  Lemma pt_delete_list γ (l : list ((Loc * FName) * Val)) H :
    ([∗ list] p ∈ l, pt γ p.1.1 p.1.2 p.2) -∗ hp_auth γ H ==∗
    hp_auth γ (del_list H l.*1).
  Proof.
    revert H. induction l as [|p l IH]; intros H.
    - iIntros "_ Ha". rewrite /del_list /=. by iModIntro.
    - iIntros "[Hp Hl] Ha". destruct p as [[o f] v]. simpl.
      iMod (pt_delete with "Ha Hp") as "Ha".
      by iMod (IH (delete (o, f) H) with "Hl Ha") as "Ha".
  Qed.

  Lemma pt_list_agree γ H (l : list ((Loc * FName) * Val)) :
    hp_auth γ H -∗ ([∗ list] p ∈ l, pt γ p.1.1 p.1.2 p.2) -∗
    ⌜forall p, p ∈ l -> H !! p.1 = Some p.2⌝.
  Proof.
    iIntros "Ha Hl". iInduction l as [|p l IH] "IH".
    - iPureIntro. intros q Hq. by apply not_elem_of_nil in Hq.
    - iDestruct "Hl" as "[Hp Hl]". destruct p as [[o f] v].
      iDestruct (pt_agree with "Ha Hp") as %Hp.
      iDestruct ("IH" with "Ha Hl") as %Hrest.
      iPureIntro. intros q Hq. apply elem_of_cons in Hq.
      destruct Hq as [Heq | Hq]; [| exact (Hrest q Hq)].
      rewrite Heq. exact Hp.
  Qed.

  (** A path was once a resource of its own here -- a fold of points-to along
      the path, [ppt].  It is gone, and its removal is the same lesson as
      [fresh_cells]': one assertion per iterator cannot be right, because two
      iterators' paths overlap in their prefix and a points-to is exclusive.
      What replaced it is [cells] with [hstarC]: the thread owns a cell *map*
      once, and a path is a pure fold of lookups in it.  Overlapping paths then
      share cells by being the same entry, which is also why the write side
      needs no fractional permissions. *)

End heapghost.

(** * The type environment as a resource

    The eight closed triples say the invariants survive and hand the thread its
    fragments back.  Axiom soundness asks for more: that the post-state
    satisfies the denotation of the post-type environment.  The pure half of
    that is already proved -- [Actions.v] has a [post_env] theorem for every
    write-side rule -- so what is missing is the bridge, a reading of a type
    environment as a resource from which the pure denotation follows.

    The obvious reading, one resource per variable, does not work, and the
    reason is worth stating because it is the same reason twice.  Two iterators
    may name the same node, and two paths overlap in their prefix; a per-
    variable reading would demand two exclusive fragments for one location and
    two owners for one cell.  The type system's aliasing side conditions are
    exactly what rules that out, but they are conditions on the environment, not
    on the individual variable, so a per-variable reading cannot see them.

    What works is to own the resources *once*, as maps, and make each variable's
    requirement a pure condition on those maps.  The thread holds its stack
    entries, its observations and a set of cells; a path is then a pure lookup
    in the cell map, an alias is two variables reading the same entry, and
    nothing is duplicated because a map has one entry per key.  It also means no
    fractions are needed on the write side -- overlapping paths share cells by
    being the same entry, not by splitting ownership. *)

Section cellmap.
  Context `{!heapG Σ}.

  Definition cells (γ : gname) (C : gmap (Loc * FName) Val) : iProp Σ :=
    [∗ map] k ↦ v ∈ C, pt γ k.1 k.2 v.

  Lemma cells_agree γ H C :
    hp_auth γ H -∗ cells γ C -∗
    ⌜forall k v, C !! k = Some v -> H !! k = Some v⌝.
  Proof.
    iIntros "Ha Hc". rewrite /cells.
    iInduction C as [|k v C Hk] "IH" using map_ind.
    - iPureIntro. intros k' v' Hlk. by rewrite lookup_empty in Hlk.
    - rewrite big_sepM_insert; [| exact Hk].
      iDestruct "Hc" as "[Hone Hrest]".
      iDestruct (pt_agree with "Ha Hone") as %Hag.
      iDestruct ("IH" with "Ha Hrest") as %Hrest.
      iPureIntro. intros k' v' Hlk.
      destruct (decide (k' = k)) as [-> | Hne].
      + rewrite lookup_insert_eq in Hlk. injection Hlk as <-.
        by destruct k.
      + rewrite lookup_insert_ne in Hlk; [| done]. exact (Hrest k' v' Hlk).
  Qed.

End cellmap.

(** A path is a lookup in the cell map: pure, and about the thread's own
    resources rather than about the heap. *)
Fixpoint hstarC (C : gmap (Loc * FName) Val) (o : Loc) (p : list FName)
  : option Loc :=
  match p with
  | []      => Some o
  | f :: p' => match C !! (o, f) with
               | Some (VLoc o') => hstarC C o' p'
               | _              => None
               end
  end.

Lemma hstarC_hstar (C : gmap (Loc * FName) Val) (h : Heap) o p q :
  (forall k v, C !! k = Some v -> h k.1 k.2 = Some v) ->
  hstarC C o p = Some q -> hstar h o p = Some q.
Proof.
  intros Hsub. revert o. induction p as [|f p IH]; intros o Hp; simpl in *.
  - exact Hp.
  - destruct (C !! (o, f)) as [[o1|]|] eqn:E; try discriminate.
    rewrite (Hsub (o, f) (VLoc o1) E). exact (IH o1 Hp).
Qed.

Print Assumptions hstarC_hstar.

Print Assumptions pt_agree.
Print Assumptions pt_alloc_list.
Print Assumptions pt_delete_list.

(** ** The lock

    The one other negative fact a rule needs about shared state is the writer's:
    the unlinking rules ask that the lock is held, and by whom.  An
    authoritative option makes that a resource -- the writer holds the token,
    the invariant holds the authority, and agreement gives the premise. *)

Definition lkUR : ucmra := authUR (optionUR (exclR (leibnizO TID))).

Class lockG (Σ : gFunctors) := LockG { lock_inG :: inG Σ lkUR }.
Definition lockΣ : gFunctors := #[ GFunctor lkUR ].
Global Instance subG_lockΣ {Σ} : subG lockΣ Σ -> lockG Σ.
Proof. solve_inG. Qed.

Section lockghost.
  Context `{!lockG Σ}.

  Definition lk_auth (γ : gname) (l : option TID) : iProp Σ :=
    own γ (● (match l with
              | Some t => Some (Excl (t : leibnizO TID))
              | None => None
              end : option (excl (leibnizO TID)))).
  Definition lk_tok (γ : gname) (t : TID) : iProp Σ :=
    own γ (◯ Some (Excl (t : leibnizO TID))).

  Global Instance lk_auth_timeless γ l : Timeless (lk_auth γ l).
  Proof. apply _. Qed.
  Global Instance lk_tok_timeless γ t : Timeless (lk_tok γ t).
  Proof. apply _. Qed.

  Lemma lk_agree γ l t : lk_auth γ l -∗ lk_tok γ t -∗ ⌜l = Some t⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    destruct l as [t0|]; simpl in Hincl.
    - apply Some_included_exclusive in Hincl; [| apply _ | done].
      by rewrite (leibniz_equiv _ _ (Excl_inj _ _ Hincl)).
    - apply option_included in Hincl.
      destruct Hincl as [Hc | (a & b & _ & Hc & _)]; discriminate.
  Qed.

  Lemma lk_acquire γ t : lk_auth γ None ==∗ lk_auth γ (Some t) ∗ lk_tok γ t.
  Proof.
    iIntros "Ha". rewrite /lk_auth /lk_tok /=.
    iMod (own_update _ _ (● Some (Excl (t : leibnizO TID))
                          ⋅ ◯ Some (Excl (t : leibnizO TID))) with "Ha")
      as "[Ha Hf]".
    { apply auth_update_alloc. by apply alloc_option_local_update. }
    iModIntro. iFrame.
  Qed.

  Lemma lk_release γ t : lk_auth γ (Some t) -∗ lk_tok γ t ==∗ lk_auth γ None.
  Proof.
    iIntros "Ha Hf". rewrite /lk_auth /lk_tok /=.
    iMod (own_update_2 _ _ _ (● (None : option (excl (leibnizO TID))))
           with "Ha Hf") as "Ha".
    { apply auth_update_dealloc.
      apply (delete_option_local_update _ (Excl (t : leibnizO TID))).
      apply _. }
    by iModIntro.
  Qed.

End lockghost.

Print Assumptions lk_agree.

(** ** The physical state

    Three pieces: the heap, which is now finite and so has a camera; the lock;
    and everything else -- the stack, the reader set, the bounding set -- as one
    exclusive resource, because no rule's premise asks anything about them that
    is not already an observation.  [Represents] ties the finite heap to the
    functional one the action lemmas are stated over. *)

Global Instance MState_inhabited : Inhabited MState :=
  populate {| stk := fun _ _ => None; hp := fun _ _ => None;
              lk := None; rt := 0; rds := fun _ => False;
              bnd := fun _ => False |}.

Definition mstateR : cmra := exclR (leibnizO MState).

Class physG (Σ : gFunctors) := PhysG { phys_inG :: inG Σ mstateR }.
Definition physΣ : gFunctors := #[ GFunctor mstateR ].
Global Instance subG_physΣ {Σ} : subG physΣ Σ -> physG Σ.
Proof. solve_inG. Qed.

(** The free operation, on the finite side. *)
Lemma Represents_free_del h H d (l : list ((Loc * FName) * Val)) :
  Represents h H ->
  (forall p, p ∈ l -> p.1.1 = d) ->
  (forall f v, h d f = Some v -> ((d, f), v) ∈ l) ->
  Represents (free h d) (del_list H l.*1).
Proof.
  intros HR Hd Hcov o f. destruct (Nat.eq_dec o d) as [->|Hne].
  - rewrite free_same. symmetry.
    destruct (decide ((d, f) ∈ l.*1)) as [Hi | Hni].
    + by apply del_list_in.
    + rewrite (del_list_notin H l.*1 (d, f) Hni) -HR.
      destruct (h d f) as [v|] eqn:E; [| reflexivity].
      exfalso. apply Hni.
      exact (list_elem_of_fmap_2 fst l ((d, f), v) (Hcov f v E)).
  - rewrite (free_other h d o f Hne) HR. symmetry.
    apply del_list_notin. intros Hi.
    apply list_elem_of_fmap_1 in Hi. destruct Hi as [p [Hp1 Hpin]].
    apply Hne.
    assert (Ho : o = p.1.1) by (rewrite -Hp1; reflexivity).
    by rewrite Ho (Hd p Hpin).
Qed.

(** ** The stack

    Same construction again.  The stack is finite for the same reason the heap
    now is: it starts empty and each binding adds one entry. *)

Definition stkUR : ucmra :=
  authUR (gmapUR (Var * TID) (exclR (leibnizO Loc))).

Class stackG (Σ : gFunctors) := StackG { stack_inG :: inG Σ stkUR }.
Definition stackΣ : gFunctors := #[ GFunctor stkUR ].
Global Instance subG_stackΣ {Σ} : subG stackΣ Σ -> stackG Σ.
Proof. solve_inG. Qed.

Definition RepresentsS (s : Var -> TID -> option Loc)
                       (S : gmap (Var * TID) Loc) : Prop :=
  forall x t, s x t = S !! (x, t).

Section stackghost.
  Context `{!stackG Σ}.

  Definition stk_auth (γ : gname) (S : gmap (Var * TID) Loc) : iProp Σ :=
    own γ (● (Excl <$> S : gmap (Var * TID) (excl (leibnizO Loc)))).
  Definition sv (γ : gname) (x : Var) (t : TID) (o : Loc) : iProp Σ :=
    own γ (◯ {[ (x, t) := Excl (o : leibnizO Loc) ]}).

  Global Instance stk_auth_timeless γ S : Timeless (stk_auth γ S).
  Proof. apply _. Qed.
  Global Instance sv_timeless γ x t o : Timeless (sv γ x t o).
  Proof. apply _. Qed.

  Lemma sv_agree γ S x t o :
    stk_auth γ S -∗ sv γ x t o -∗ ⌜S !! (x, t) = Some o⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply singleton_included_l in Hincl as [y [Hlk Hle]].
    rewrite lookup_fmap in Hlk.
    apply fmap_Some_equiv in Hlk as [o0 [Ho0 Hy]].
    rewrite Ho0. f_equal.
    rewrite Hy Excl_included in Hle. exact (eq_sym Hle).
  Qed.

  Lemma sv_update γ S x t o o' :
    stk_auth γ S -∗ sv γ x t o ==∗
    stk_auth γ (<[(x, t) := o']> S) ∗ sv γ x t o'.
  Proof.
    iIntros "Ha Hf". rewrite /stk_auth /sv.
    iMod (own_update_2 _ _ _ (● (Excl <$> (<[(x, t) := o']> S)
                                 : gmap (Var * TID) (excl (leibnizO Loc)))
                              ⋅ ◯ {[(x, t) := Excl (o' : leibnizO Loc)]})
           with "Ha Hf") as "[Ha Hf]".
    { rewrite fmap_insert. apply auth_update.
      apply singleton_local_update_any.
      intros y _. by apply exclusive_local_update. }
    iModIntro. iFrame.
  Qed.

  Lemma RepresentsS_upd s S x t o :
    RepresentsS s S ->
    RepresentsS (fun y t' => if decide ((y, t') = (x, t)) then Some o else s y t')
                (<[(x, t) := o]> S).
  Proof.
    intros HR y t'. destruct (decide ((y, t') = (x, t))) as [Heq | Hne].
    - injection Heq as -> ->. by rewrite lookup_insert_eq.
    - rewrite lookup_insert_ne; [exact (HR y t') |].
      intros Hc. apply Hne. by rewrite Hc.
  Qed.

End stackghost.

Print Assumptions sv_agree.

Section physical.
  Context `{!physG Σ, !heapG Σ, !lockG Σ, !stackG Σ}.

  (** The readers, as the physical state's own component: a finite set with
      the authority over the tokens.  Every action that does not touch [R]
      carries it across unchanged, which is what [rdown_same] says. *)
  Definition phys (γm γh γl γs : gname) (root : Loc) (fs : list FName)
      (m : MState) : iProp Σ :=
    own γm (Excl (m : leibnizO MState))
    ∗ lk_auth γl (lk m)
    ∗ ⌜rt m = root⌝
    ∗ (∃ H, ⌜Represents (hp m) H⌝ ∗ ⌜HeapShape fs (hp m)⌝ ∗ hp_auth γh H)
    ∗ (∃ S, ⌜RepresentsS (stk m) S⌝ ∗ stk_auth γs S).

  Lemma phys_rest γm m m' :
    own γm (Excl (m : leibnizO MState))
    ==∗ own γm (Excl (m' : leibnizO MState)).
  Proof.
    iIntros "H". iApply (own_update with "H").
    by apply cmra_update_exclusive.
  Qed.

  (** A step that leaves the heap, the stack, the lock and the root alone: the
      reader and bounding sets are not [phys]'s any more -- they are the
      invariant's registrations -- so the six control actions are this lemma
      plus a ghost step on those. *)
  Lemma phys_ctrl γm γh γl γs root fs m m' :
    hp m' = hp m -> stk m' = stk m -> lk m' = lk m -> rt m' = rt m ->
    phys γm γh γl γs root fs m ==∗ phys γm γh γl γs root fs m'.
  Proof.
    iIntros (Hh Hs Hl Hr) "(Hm & Hlk & %Hrt & Hhp & Hst)".
    iMod (phys_rest with "Hm") as "Hm".
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    iDestruct "Hst" as (S) "[%HRS Hb]".
    iModIntro. rewrite /phys Hl. iFrame "Hm Hlk".
    iSplitR; [iPureIntro; by rewrite Hr |].
    iSplitL "Ha".
    - iExists H. iFrame. iPureIntro. rewrite Hh. by split.
    - iExists S. iFrame. iPureIntro. by rewrite Hs.
  Qed.

  (** A field write: licensed by holding the cell, which is what carries the
      rule's premise about the heap out of the invariant in the first place. *)
  Lemma phys_write γm γh γl γs root fs m o f v v' :
    phys γm γh γl γs root fs m -∗ pt γh o f v ==∗
    phys γm γh γl γs root fs (write_ms m o f v') ∗ pt γh o f v'
    ∗ ⌜hp m o f = Some v⌝.
  Proof.
    iIntros "(Hm & Hlk & %Hrt & Hhp & Hst) Hpt".
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    iDestruct (pt_agree with "Ha Hpt") as %Hag.
    assert (Hcell : hp m o f = Some v) by (rewrite HR; exact Hag).
    iMod (phys_rest _ _ (write_ms m o f v') with "Hm") as "Hm".
    iMod (pt_update with "Ha Hpt") as "[Ha Hpt]".
    iModIntro. iSplitL "Hm Hlk Ha Hst"; last first.
    { iFrame "Hpt". by iPureIntro. }
    rewrite /phys /=. iFrame "Hm Hlk Hst".
    iSplitR; [by iPureIntro |].
    iExists (<[(o, f) := v']> H). iFrame. iPureIntro. split.
    - by apply Represents_upd.
    - apply HeapShape_upd; [exact HS | exact (HS o f v Hcell)].
  Qed.

  (** Allocation hands the new node's cells to the allocating thread, and
      rebinds the variable. *)
  Lemma phys_alloc_step γm γh γl γs root fs m n x t o0 :
    NoDup fs ->
    (forall g, hp m n g = None) ->
    phys γm γh γl γs root fs m -∗ sv γs x t o0 ==∗
    phys γm γh γl γs root fs (alloc_ms m n fs x t)
    ∗ sv γs x t n
    ∗ ([∗ list] p ∈ ((fun f => ((n, f), VNull)) <$> fs),
         pt γh p.1.1 p.1.2 p.2).
  Proof.
    iIntros (Hnd Hfresh) "(Hm & Hlk & %Hrt & Hhp & Hst) Hsv".
    iMod (phys_rest _ _ (alloc_ms m n fs x t) with "Hm") as "Hm".
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    iDestruct "Hst" as (S) "[%HRS Hb]".
    iMod (sv_update with "Hb Hsv") as "[Hb Hsv]".
    assert (Hkeys : ((fun f => ((n, f), VNull)) <$> fs).*1
                    = (fun f => (n, f)) <$> fs)
      by (rewrite -list_fmap_compose; reflexivity).
    iMod (pt_alloc_list γh ((fun f => ((n, f), VNull)) <$> fs) H
           with "Ha") as "[Ha Hl]".
    { unfold ins_list. rewrite Hkeys.
      assert (Hinj : Inj eq eq (fun f : FName => (n, f))).
      { intros a b Hc. by injection Hc. }
      by apply NoDup_fmap_2. }
    { intros p Hp. apply list_elem_of_fmap_1 in Hp.
      destruct Hp as [g [-> _]]. simpl. by rewrite -HR. }
    iModIntro. rewrite /phys /=. iFrame "Hm Hlk Hsv Hl".
    iSplitR; [by iPureIntro |].
    iSplitL "Ha".
    - iExists (ins_list H ((fun f => ((n, f), VNull)) <$> fs)). iFrame.
      iPureIntro. split; [by apply Represents_alloc | by apply HeapShape_alloc].
    - iExists (<[(x, t) := n]> S). iFrame. iPureIntro.
      by apply RepresentsS_upd.
  Qed.

  (** A binding: the stack changes, nothing else does. *)
  Lemma phys_bind γm γh γl γs root fs m y t o o0 :
    phys γm γh γl γs root fs m -∗ sv γs y t o0 ==∗
    phys γm γh γl γs root fs (bind_ms m y t o) ∗ sv γs y t o.
  Proof.
    iIntros "(Hm & Hlk & %Hrt & Hhp & Hst) Hsv".
    iMod (phys_rest _ _ (bind_ms m y t o) with "Hm") as "Hm".
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    iDestruct "Hst" as (S) "[%HRS Hb]".
    iMod (sv_update with "Hb Hsv") as "[Hb Hsv]".
    iModIntro. rewrite /phys /=. iFrame "Hm Hlk Hsv".
    iSplitR; [by iPureIntro |].
    iSplitL "Ha".
    - iExists H. iFrame. iPureIntro. by split.
    - iExists (<[(y, t) := o]> S). iFrame. iPureIntro.
      by apply RepresentsS_upd.
  Qed.

  (** Reclamation consumes them. *)
  Lemma phys_free_step γm γh γl γs root fs m d (l : list ((Loc * FName) * Val)) :
    (forall p, p ∈ l -> p.1.1 = d) ->
    (forall f, In f fs -> exists v, ((d, f), v) ∈ l) ->
    ([∗ list] p ∈ l, pt γh p.1.1 p.1.2 p.2) -∗
    phys γm γh γl γs root fs m ==∗ phys γm γh γl γs root fs (free_ms m d).
  Proof.
    iIntros (Hd Hfs) "Hpts (Hm & Hlk & %Hrt & Hhp & Hst)".
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    iDestruct (pt_list_agree with "Ha Hpts") as %Hag.
    (* the node's cells are exactly the declared ones, so [l] covers them *)
    assert (Hcov : forall f v, hp m d f = Some v -> ((d, f), v) ∈ l).
    { intros f v Hlk.
      destruct (Hfs f (HS d f v Hlk)) as [w Hw].
      assert (Hw' : H !! (d, f) = Some w) by exact (Hag ((d, f), w) Hw).
      rewrite HR Hw' in Hlk. by injection Hlk as <-. }
    iMod (phys_rest _ _ (free_ms m d) with "Hm") as "Hm".
    iMod (pt_delete_list with "Hpts Ha") as "Ha".
    iModIntro. rewrite /phys /=. iFrame "Hm Hlk Hst".
    iSplitR; [by iPureIntro |].
    iExists (del_list H l.*1). iFrame. iPureIntro. split.
    - by apply (Represents_free_del (hp m) H d l).
    - by apply HeapShape_free.
  Qed.

End physical.

Print Assumptions phys_write.
Print Assumptions phys_alloc_step.
Print Assumptions phys_free_step.

(** * Two steps with nothing left open

    The point of the repair.  With a finite heap there are points-to
    assertions, so a rule's premise about the heap is a resource the thread
    carries; with the lock and the stack the same, every premise of these two
    rules is either derived from a fragment the thread holds or from the
    invariant it opens.  Nothing about the shared state is assumed.

    The two negative premises are the interesting ones, since a fragment can
    only say what *is*.  "The node has no free-list entry" comes from FLD and
    WULK: a node the writer holds an iterator on is not detached, and only
    detached nodes have entries.  "The fresh node is unreachable" comes from FR
    and the pinned root: nothing points at a fresh node, and a non-empty path
    ends at an edge target.  Both are invariants doing the work a resource
    cannot. *)

Lemma iter_no_flist s lw o :
  FLD s -> WULK s -> lk (ms s) = Some lw -> obsv s o (Oiter lw) ->
  flist s o = None.
Proof.
  intros HF HW Hlk Hit. destruct (flist s o) as [Tr|] eqn:E; [| reflexivity].
  exfalso. destruct (HF o Tr E) as [t [Hu | Hf]];
    destruct (HW lw o t Hlk Hit) as [Hnu Hnf];
    [exact (Hnu Hu) | exact (Hnf Hf)].
Qed.

Lemma FLD_free m Og U T F d :
  FLD (to_LState_t m Og U T F) ->
  FLD (to_LState_t (free_ms m d) Og U T (delete d F)).
Proof.
  intros HF o Tr Hfl. simpl in Hfl.
  destruct (Nat.eq_dec o d) as [->|Hne].
  - by rewrite lookup_delete_eq in Hfl.
  - rewrite lookup_delete_ne in Hfl; [| intros Hc; by apply Hne].
    apply (HF o Tr). simpl. exact Hfl.
Qed.

Lemma FLD_same m m' Og U T F :
  FLD (to_LState_t m Og U T F) -> FLD (to_LState_t m' Og U T F).
Proof. intros HF o Tr Hfl. exact (HF o Tr Hfl). Qed.

(** The thread's own observation entries agree with the invariant's, one list
    at a time.  Same induction as [pt_list_agree]. *)
Section tobs_list.
  Context `{!rcuG Σ}.
  Lemma tobs_list_agree γo Og (lo : list ((Loc * TID) * gset obs)) :
    tobs_auth γo Og -∗ ([∗ list] p ∈ lo, tobs_ctl γo p.1.1 p.1.2 p.2) -∗
    ⌜forall p, p ∈ lo -> Og !! p.1 = Some p.2⌝.
  Proof.
    iIntros "Ha Hl". iInduction lo as [|p lo IH] "IH".
    - iPureIntro. intros q Hq. by apply not_elem_of_nil in Hq.
    - iDestruct "Hl" as "[Hp Hl]". destruct p as [[o t] sg].
      iDestruct (tobs_ctl_agree with "Ha Hp") as %Hp.
      iDestruct ("IH" with "Ha Hl") as %Hrest.
      iPureIntro. intros q Hq. apply elem_of_cons in Hq.
      destruct Hq as [Heq | Hq]; [| exact (Hrest q Hq)].
      rewrite Heq. exact Hp.
  Qed.
End tobs_list.

(** What ReadEnd leaves at one of its entries: the root observation, which is
    anonymous and is not the departing thread's to drop. *)
Definition retired (sg : gset obs) : gset obs :=
  if decide (Oroot ∈ sg) then {[Oroot]} else ∅.

Lemma retired_spec sg ob : ob ∈ retired sg <-> (ob = Oroot /\ Oroot ∈ sg).
Proof.
  unfold retired. destruct (decide (Oroot ∈ sg)) as [Hin | Hni].
  - rewrite elem_of_singleton. split; [by intros -> | by intros [-> _]].
  - rewrite elem_of_empty. split; [by intros [] | by intros [-> Hc]].
Qed.

(** ** The two points where the protocol tests shared state

    \textsc{WriteBegin} asks whether the lock is free, \textsc{SyncStop}
    whether every reader still running entered after the grace period began.
    Neither is a fact any thread holds, so neither can be a premise; they are
    what a compare-and-set and a wait loop are for.

    What can be mechanized is the body of each, and the reason it can is that
    both tests are over *finite* data -- the lock is an option and the
    registrations are a finite map -- so the test is decidable inside the proof
    and the attempt needs no oracle.  What is not mechanized, and needs a
    semantics, is that the loop goes round again. *)

Definition past (e : nat) (v : option (nat * gset Loc)) : Prop :=
  match v with None => True | Some (e', _) => e < e' end.

Global Instance past_dec e v : Decision (past e v).
Proof.
  destruct v as [[e' D]|]; simpl; [apply lt_dec | left; exact I].
Defined.

(** The domain clause across an observation insert.  Every rule that inserts
    is the writer's, and the writer holds no registration, so the inserted key
    belongs to no thread the clause speaks about. *)
Lemma dom_ins (Rg : gmap TID (option (nat * gset Loc))) (Og : ObsMap)
    (m : MState) o0 t0 s' :
  lk m = Some t0 ->
  (forall t, lk m = Some t -> Rg !! t = None) ->
  (forall t e D o sg ob, Rg !! t = Some (Some (e, D)) ->
     Og !! (o, t) = Some sg -> ob ∈ sg -> obs_tid ob = Some t -> o ∈ D) ->
  (forall t e D o sg ob, Rg !! t = Some (Some (e, D)) ->
     (<[(o0, t0) := s']> Og) !! (o, t) = Some sg ->
     ob ∈ sg -> obs_tid ob = Some t -> o ∈ D).
Proof.
  intros Hlk HLk Hdom t e D o sg ob Hreg Hlook Hin Htid.
  destruct (decide ((o, t) = (o0, t0))) as [Heq | Hne].
  - injection Heq as -> ->. by rewrite (HLk t0 Hlk) in Hreg.
  - rewrite lookup_insert_ne in Hlook; [| exact (fun Hc => Hne (eq_sym Hc))].
    exact (Hdom t e D o sg ob Hreg Hlook Hin Htid).
Qed.

Section atomic.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (root : Loc) (fs : list FName).

  (** ** T-Free *)
  Lemma free_atomic N γm γh γl γs γo γf γr γe γq E d t (sd : nat)
        (l : list ((Loc * FName) * Val)) :
    ↑N ⊆ E ->
    (forall p, p ∈ l -> p.1.1 = d) ->
    (forall f, In f fs -> exists v, ((d, f), v) ∈ l) ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    tobs_ctl γo d t {[Ofree t]} -∗
    fl_ctl γf d sd -∗
    ([∗ list] p ∈ l, pt γh p.1.1 p.1.2 p.2)
    ={E}=∗ tobs_ctl γo d t {[Ofree t]}.
  Proof.
    iIntros (HN Hd Hfs) "#Hinv Hobs Hfl Hpts".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)" "Hclose".
    iDestruct (tobs_ctl_agree with "Ho Hobs") as %Hlk.
    assert (Hfree : obsv (to_LState_t m Og U T F) d (Ofree t)).
    { exists t, {[Ofree t]}. split; [exact Hlk | by apply elem_of_singleton]. }
    subst F.
    iMod (free_update FType (phys γm γh γl γs root fs) γo γf gg Rg m Og U T St
            d t sd Hfree Hwf with "Hfl Hp Ho Hf [Hpts]")
      as "(Hp & Ho & Hf & %Hwf')".
    { iIntros "Hp". by iMod (phys_free_step with "Hpts Hp") as "$". }
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext.
      iExists (free_ms m d), Og, U, T, (e_F (mkE gg Rg (delete d St))),
              (delete d St), Rg, gg, ww, Fr. iFrame.
      iPureIntro. split; [exact HWF | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - rewrite mkE_F_free. by apply FLD_free.
      - rewrite mkE_F_free. intros o0 t0 Hf0. exact (HWFW o0 t0 Hf0).
      - apply RefsRCU_free. exact HRefs.
      - rewrite mkE_F_free. intros q t0 Hq. exact (HFrc q t0 Hq).
      - exact Hwf'.
      - rewrite mkE_F_free. exact HWUW.
      - reflexivity.
      - by apply EWF_del.
      - exact HRR.
      - exact HBnd.
      - exact HLk.
      - exact HWm.
      - first [ exact Hdom
              | by apply (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)
              | by apply (dom_ins Rg _ m _ lw _ Hlkm HLk
                            (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)) ]. }
    by iModIntro.
  Qed.

  (** ** T-ReadBegin, and the first closed triple on the read side

      A thread holding its own registration, outside a critical section, enters
      one -- registering at the current epoch, which is what distinguishes this
      section from any it ran before.  Nothing else is required of it: both
      premises the action lemma carries as hypotheses are discharged here.  The
      first, that the thread is not the writer, comes from the registration
      itself, since the invariant says the lock holder has none; the second,
      that it holds no detaching observation, from WFreshW and WUNLKW together
      with the first. *)
  Lemma read_begin_atomic N γm γh γl γs γo γf γr γe γq E t :
    ↑N ⊆ E ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    reg_cell γe t None
    ={E}=∗ ∃ e, reg_cell γe t (Some (e, ∅)).
  Proof.
    iIntros (HN) "#Hinv Hcell".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)"
      "Hclose".
    iDestruct (reg_cell_agree with "Hreg Hcell") as %Hcell.
    (* the thread is not the writer, because the lock holder has no cell *)
    assert (Hnw : forall lw, lk m = Some lw -> lw <> t).
    { intros lw Hlw Heq. subst lw. by rewrite (HLk t Hlw) in Hcell. }
    assert (Hclean : forall o,
              ~ obsv (to_LState_t m Og U T F) o (Ounlk t)
              /\ ~ obsv (to_LState_t m Og U T F) o (Ofree t)
              /\ ~ obsv (to_LState_t m Og U T F) o (Ofresh t)).
    { intros o. repeat apply conj; intros Hbad;
        [ pose proof (HWUW o t (or_introl Hbad)) as Hlk
        | pose proof (HWUW o t (or_intror Hbad)) as Hlk
        | pose proof (HWFW o t Hbad) as Hlk ];
        exact (Hnw t Hlk eq_refl). }
    (* the thread is not a reader, so it bounds nothing *)
    assert (Hnrd : ~ rds m t).
    { intros Hrd. destruct (proj1 (HRR t) Hrd) as [e' [D' He']].
      by rewrite Hcell in He'. }
    (* and it holds no observation of its own: the three detaching kinds by
       WFreshW and WUNLKW, the iterator by WITR, which is what says an
       iterator belongs to the writer or to a reader *)
    assert (Hnoobs : forall o ob, obsv (to_LState_t m Og U T F) o ob ->
                       obs_tid ob <> Some t).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                       & _ & _ & _ & _ & HWITR & _).
      intros o ob Hob Htid. destruct ob as [t0|t0|t0|t0|]; simpl in Htid;
        try discriminate; injection Htid as <-.
      - destruct (HWITR o t0 Hob) as [Hlk | Hrd];
          [exact (Hnw t0 Hlk eq_refl) | exact (Hnrd Hrd)].
      - exact (proj1 (Hclean o) Hob).
      - exact (proj2 (proj2 (Hclean o)) Hob).
      - exact (proj1 (proj2 (Hclean o)) Hob). }
    iMod (phys_ctrl _ _ _ _ _ _ m (read_begin_ms m t)
            eq_refl eq_refl eq_refl eq_refl with "Hp") as "Hp".
    iMod (reg_cell_update _ _ _ _ (Some (gg, ∅)) with "Hreg Hcell")
      as "[Hreg Hcell]".
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext. iExists (read_begin_ms m t), Og, U, T, F, St,
                     (<[t := Some (gg, ∅)]> Rg), gg, ww, Fr. iFrame.
      iPureIntro.
      split; [exact HWF | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - exact HFLD.
      - exact HWFW.
      - exact HRefs.
      - exact HFrc.
      - exact (read_begin_preserves_WellFormed FType m Og U T F t
                 Hnw Hclean Hwf).
      - exact HWUW.
      - assert (Hnone : ereg (mkE gg Rg St) !! t = None)
          by (simpl; by rewrite lookup_omap Hcell).
        rewrite (mkE_begin gg Rg St t ∅)
          (e_begin_keeps_the_free_list (mkE gg Rg St) t HEWF Hnone).
        exact HFeq.
      - rewrite (mkE_begin gg Rg St t ∅). by apply EWF_begin.
      - intros t'. simpl. destruct (decide (t' = t)) as [-> | Hne].
        + rewrite lookup_insert_eq. split.
          * intros _. by exists gg, ∅.
          * intros _. by right.
        + rewrite lookup_insert_ne; [| exact (fun Hc => Hne (eq_sym Hc))].
          split.
          * intros [Hrd | Hc]; [exact (proj1 (HRR t') Hrd) | by destruct (Hne Hc)].
          * intros H. left. exact (proj2 (HRR t') H).
      - intros t'. simpl. destruct (decide (t' = t)) as [-> | Hne].
        + split.
          * intros Hb. exfalso.
            destruct (proj1 (HBnd t) Hb) as [e' [He' _]].
            simpl in He'. rewrite lookup_omap Hcell in He'. discriminate He'.
          * intros [e' [He' Hlt]]. exfalso.
            simpl in He'. rewrite lookup_omap lookup_insert_eq in He'.
            simpl in He'. injection He' as <-. exact (Nat.lt_irrefl gg Hlt).
        + split.
          * intros Hb. destruct (proj1 (HBnd t') Hb) as [e' [He' Hlt]].
            exists e'. split; [| exact Hlt]. simpl in He' |- *.
            rewrite lookup_omap lookup_insert_ne;
              [| exact (fun Hc => Hne (eq_sym Hc))].
            by rewrite lookup_omap in He'.
          * intros [e' [He' Hlt]]. apply (HBnd t'). exists e'.
            split; [| exact Hlt]. simpl in He' |- *.
            rewrite lookup_omap lookup_insert_ne in He';
              [| exact (fun Hc => Hne (eq_sym Hc))].
            by rewrite lookup_omap.
      - intros t0 Hlk0. rewrite lookup_insert_ne;
          [exact (HLk t0 Hlk0) | intros ->; exact (Hnw t0 Hlk0 eq_refl)].
      - split; [exact (proj1 HWm) |].
        intros t0 e0 D0 H. destruct (decide (t0 = t)) as [-> | Hne].
        + rewrite lookup_insert_eq in H. injection H as <- <-.
          exact (proj1 HWm).
        + rewrite lookup_insert_ne in H;
            [exact (proj2 HWm t0 e0 D0 H) | exact (fun Hc => Hne (eq_sym Hc))].
      - intros t0 e0 D0 o0 sg0 ob0 Hreg0 Hlk0 Hin0 Htid0.
        destruct (decide (t0 = t)) as [-> | Hne].
        + exfalso. apply (Hnoobs o0 ob0); [by exists t, sg0 | exact Htid0].
        + rewrite lookup_insert_ne in Hreg0;
            [| exact (fun Hc => Hne (eq_sym Hc))].
          exact (Hdom t0 e0 D0 o0 sg0 ob0 Hreg0 Hlk0 Hin0 Htid0). }
    iModIntro. by iExists gg.
  Qed.


  (** ** T-ReadEnd, closed

      The departing reader hands in its registration and the observation
      entries its own cell enumerates, and gets its registration back empty.
      Nothing about the shared state is assumed: the list is the thread's, the
      domain is the thread's, and the free list is not mentioned at all --
      which is the whole of what the epoch representation was for.

      The three conditions are about the thread's own data: the enumeration has
      no repeats, every entry in it is the thread's, and it covers the domain
      the cell records.  The invariant supplies the converse -- that the domain
      covers every entry of the thread's that carries an observation of its own
      -- so between them the retirement is complete. *)
  Lemma read_end_atomic N γm γh γl γs γo γf γr γe γq E t e D
        (lo : list ((Loc * TID) * gset obs)) :
    ↑N ⊆ E ->
    NoDup lo.*1 ->
    (forall p, p ∈ lo -> p.1.2 = t) ->
    (forall o, o ∈ D -> exists v, ((o, t), v) ∈ lo) ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    reg_cell γe t (Some (e, D)) -∗
    ([∗ list] p ∈ lo, tobs_ctl γo p.1.1 p.1.2 p.2)
    ={E}=∗ reg_cell γe t None
           ∗ ([∗ list] p ∈ lo, tobs_ctl γo p.1.1 p.1.2 (retired p.2)).
  Proof.
    iIntros (HN Hnd Hkey HcovD) "#Hinv Hcell Hfrags".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)"
      "Hclose".
    iDestruct (reg_cell_agree with "Hreg Hcell") as %Hcell.
    iDestruct (tobs_list_agree with "Ho Hfrags") as %Hag.
    subst F.
    (* the thread is a reader, which is what the retirement needs *)
    assert (Hrd : rds m t) by (apply HRR; by exists e, D).
    (* the retired list, and the three conditions read_end_update asks of it *)
    set (l := (fun p => (p.1, retired p.2)) <$> lo).
    assert (Hkeys : l.*1 = lo.*1)
      by (subst l; rewrite -list_fmap_compose; by apply list_fmap_ext).
    assert (Hnd' : NoDup l.*1) by (rewrite Hkeys; exact Hnd).
    assert (Hval : forall p, p ∈ l -> exists sg, Og !! p.1 = Some sg
             /\ (forall ob, ob ∈ p.2 <-> (ob = Oroot /\ Oroot ∈ sg))).
    { intros p Hp. subst l. apply list_elem_of_fmap_1 in Hp as [q [-> Hq]].
      exists q.2. split; [exact (Hag q Hq) | simpl; exact (retired_spec q.2)]. }
    assert (Hkey' : forall p, p ∈ l -> p.1.2 = t).
    { intros p Hp. subst l. apply list_elem_of_fmap_1 in Hp as [q [-> Hq]].
      simpl. exact (Hkey q Hq). }
    assert (Hcov : forall o sg ob, Og !! (o, t) = Some sg -> ob ∈ sg ->
             obs_tid ob = Some t -> exists v, ((o, t), v) ∈ l).
    { intros o sg ob Hlk Hin Htid.
      destruct (HcovD o (Hdom t e D o sg ob Hcell Hlk Hin Htid)) as [v Hv].
      exists (retired v). subst l.
      exact (list_elem_of_fmap_2 _ lo ((o, t), v) Hv). }
    iMod (read_end_update FType (phys γm γh γl γs root fs) γo γe gg Rg m Og U T
            St t (e, D) l Hwf HWF Hrd Hnd' Hkey' Hval Hcov
            with "[Hfrags] Hcell Hp Ho Hreg []")
      as "(Hp & Ho & Hreg & Hcell & Hfrags & %HWF' & %Hwf')".
    { subst l. rewrite big_sepL_fmap. iApply (big_sepL_mono with "Hfrags").
      intros k p _. simpl. iIntros "H". iLeft. by iExists p.2. }
    { iIntros "Hp". iApply (phys_ctrl _ _ _ _ _ _ m (read_end_ms m t)
        eq_refl eq_refl eq_refl eq_refl with "Hp"). }
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext.
      iExists (read_end_ms m t), (ins_list Og l),
              (fun x t' => U x t' \/ t' = t), T,
              (e_F (mkE gg (<[t := None]> Rg) St)), St,
              (<[t := None]> Rg), gg, ww, Fr. iFrame.
      iPureIntro.
      (* observations only shrink, so every conjunct whose hypothesis is an
         observation transfers *)
      assert (Hshr : forall o ob,
                obsv (to_LState_t (read_end_ms m t) (ins_list Og l)
                        (fun x t' => U x t' \/ t' = t) T
                        (e_F (mkE gg (<[t := None]> Rg) St))) o ob ->
                obsv (to_LState_t m Og U T (e_F (mkE gg Rg St))) o ob)
        by (intros o ob H; exact (retire_shrink Og l _ _ _ _ _ _ _ _ o ob
                                    Hval H)).
      split; [exact HWF' | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - (* FLD: the entries are the same, and a detached node stays detached
           because a reader holds no detaching observation *)
        destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRITR
                         & _).
        intros o Tr Hfl. rewrite mkE_F_end in Hfl.
        assert (Hfl0 : exists Tr0, flist (to_LState_t m Og U T (e_F (mkE gg Rg St))) o = Some Tr0).
        { simpl in Hfl |- *. rewrite /read_end_F lookup_fmap in Hfl.
          destruct (e_F (mkE gg Rg St) !! o) as [s0|]; [by exists (fun t' => t' ∈ s0)
                                      | discriminate]. }
        destruct Hfl0 as [Tr0 Hfl0].
        destruct (HFLD o Tr0 Hfl0) as [t0 Hdet].
        exists t0.
        assert (Hkeepfn : forall o' ob',
                  obsv (to_LState_t m Og U T (e_F (mkE gg Rg St))) o' ob' ->
                  obs_tid ob' <> Some t ->
                  obsv (to_LState_t (read_end_ms m t) (ins_list Og l)
                          (fun x t' => U x t' \/ t' = t) T
                          (read_end_F (e_F (mkE gg Rg St)) t)) o' ob')
          by (intros o' ob' H Htid; exact (retire_keep Og l t _ _ _ _ _ _ _ _
                                             o' ob' HWF Hnd' Hkey' Hval H Htid)).
        destruct Hdet as [Hd | Hd].
        + left. exact (re_detach_kept m Og (ins_list Og l) U
                         (fun x t' => U x t' \/ t' = t) T (e_F (mkE gg Rg St))
                         t Hkeepfn Hrd o (Ounlk t0) HRITR Hd
                         (ex_intro _ t0 (or_introl eq_refl))).
        + right. exact (re_detach_kept m Og (ins_list Og l) U
                          (fun x t' => U x t' \/ t' = t) T (e_F (mkE gg Rg St))
                          t Hkeepfn Hrd o (Ofree t0) HRITR Hd
                          (ex_intro _ t0 (or_intror (or_introl eq_refl)))).
      - intros o t0 H. exact (HWFW o t0 (Hshr o _ H)).
      - exact HRefs.
      - intros q t0 H. exact (HFrc q t0 (Hshr q _ H)).
      - exact Hwf'.
      - intros o t0 [H | H];
          [exact (HWUW o t0 (or_introl (Hshr o _ H)))
          | exact (HWUW o t0 (or_intror (Hshr o _ H)))].
      - reflexivity.
      - rewrite mkE_end. by apply EWF_end.
      - intros t'. simpl. destruct (decide (t' = t)) as [-> | Hne].
        + rewrite lookup_insert_eq. split.
          * by intros [_ Hc].
          * by intros [e' [D' Hc]].
        + rewrite lookup_insert_ne; [| exact (fun Hc => Hne (eq_sym Hc))].
          split.
          * intros [Hrd' _]. exact (proj1 (HRR t') Hrd').
          * intros H. split; [exact (proj2 (HRR t') H) | exact Hne].
      - intros t'. simpl. destruct (decide (t' = t)) as [-> | Hne].
        + split.
          * by intros [_ Hc].
          * intros [e' [He' _]]. exfalso. simpl in He'.
            by rewrite lookup_omap lookup_insert_eq in He'.
        + split.
          * intros [Hb _]. destruct (proj1 (HBnd t') Hb) as [e' [He' Hlt]].
            exists e'. split; [| exact Hlt]. simpl in He' |- *.
            rewrite lookup_omap lookup_insert_ne;
              [| exact (fun Hc => Hne (eq_sym Hc))].
            by rewrite lookup_omap in He'.
          * intros [e' [He' Hlt]]. split; [| exact Hne].
            apply (HBnd t'). exists e'. split; [| exact Hlt].
            simpl in He' |- *.
            rewrite lookup_omap lookup_insert_ne in He';
              [| exact (fun Hc => Hne (eq_sym Hc))].
            by rewrite lookup_omap.
      - intros t0 Hlk0. simpl in Hlk0.
        destruct (decide (t0 = t)) as [-> | Hne].
        + exfalso. by rewrite (HLk t Hlk0) in Hcell.
        + rewrite lookup_insert_ne; [exact (HLk t0 Hlk0)
                                    | exact (fun Hc => Hne (eq_sym Hc))].
      - split; [exact (proj1 HWm) |].
        intros t0 e0 D0 H. destruct (decide (t0 = t)) as [-> | Hne].
        + by rewrite lookup_insert_eq in H.
        + rewrite lookup_insert_ne in H;
            [exact (proj2 HWm t0 e0 D0 H) | exact (fun Hc => Hne (eq_sym Hc))].
      - intros t0 e0 D0 o0 sg0 ob0 Hreg0 Hlk0 Hin0 Htid0.
        destruct (decide (t0 = t)) as [-> | Hne].
        + by rewrite lookup_insert_eq in Hreg0.
        + rewrite lookup_insert_ne in Hreg0;
            [| exact (fun Hc => Hne (eq_sym Hc))].
          apply (Hdom t0 e0 D0 o0 sg0 ob0 Hreg0); [| exact Hin0 | exact Htid0].
          destruct (ins_list_inv _ _ _ _ Hlk0) as [Hin | [_ Hold]];
            [| exact Hold].
          exfalso. apply Hne. exact (Hkey' _ Hin). }
    iModIntro. iFrame. subst l. by rewrite big_sepL_fmap.
  Qed.



  (** ** T-WriteFH: a field of a fresh node.  A mutation, with the heap premise
      carried by the cell being written and the unreachability of the fresh
      node derived rather than assumed. *)
  Lemma write_fresh_atomic N γm γh γl γs γo γf γr γe γq E lw on f oy x g
        sn sy v vy C :
    ↑N ⊆ E ->
    (* the field written is an RCU field: the rules write the structure, and
       the invariant that references live in RCU fields has to survive *)
    FType f = RCUField ->
    on <> root -> oy <> root ->
    Ofresh lw ∈ sn -> Oiter lw ∈ sy ->
    (* the witness that the target is in the heap is a condition on the cell
       map, since the rule only reads it *)
    C !! (oy, g) = Some vy ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    lk_tok γl lw -∗
    tobs_ctl γo on lw sn -∗
    tobs_ctl γo oy lw sy -∗
    sv γs x lw on -∗
    cells γh C -∗
    pt γh on f v
    ={E}=∗ lk_tok γl lw ∗ tobs_ctl γo on lw sn ∗ tobs_ctl γo oy lw sy
           ∗ sv γs x lw on ∗ cells γh C ∗ pt γh on f (VLoc oy).
  Proof.
    iIntros (HN Hfrcu Hnr Hyr Hin Hiy Hcy)
            "#Hinv Hlk Hon Hoy Hsv Hcells Hptn".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)" "Hclose".
    (* the premises, one resource at a time *)
    iDestruct (tobs_ctl_agree with "Ho Hon") as %Hlon.
    iDestruct (tobs_ctl_agree with "Ho Hoy") as %Hloy.
    assert (Hfr : obsv (to_LState_t m Og U T F) on (Ofresh lw))
      by (by exists lw, sn).
    assert (Hit : obsv (to_LState_t m Og U T F) oy (Oiter lw))
      by (by exists lw, sy).
    iDestruct "Hp" as "(Hm & Hlka & %Hrt & Hhp & Hst)".
    iDestruct (lk_agree with "Hlka Hlk") as %Hlkm.
    iDestruct "Hst" as (S) "[%HRS Hb]".
    iDestruct (sv_agree with "Hb Hsv") as %Hsvag.
    assert (Hstk : stk m x lw = Some on) by (rewrite HRS; exact Hsvag).
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    iDestruct (cells_agree with "Ha Hcells") as %Hcellag.
    assert (Hcelly : hp m oy g = Some vy)
      by (rewrite HR; exact (Hcellag (oy, g) vy Hcy)).
    (* the two negative premises *)
    assert (Hno_in : forall o' f', ~ Edge (to_LState_t m Og U T F) o' f' on).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & HFR & _).
      exact (proj1 (HFR lw x on Hstk Hfr)). }
    assert (Hunr : forall p, hstar (hp m) (rt m) p <> Some on).
    { apply no_incoming_unreachable.
      - intros o' f' Hc. exact (Hno_in o' f' Hc).
      - rewrite Hrt. intros Hc. apply Hnr. by rewrite Hc. }
    assert (Hfl : flist (to_LState_t m Og U T F) oy = None).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & HWU & _).
      exact (iter_no_flist _ lw oy HFLD HWU Hlkm Hit). }
    assert (Hheap : InHeap (to_LState_t m Og U T F) oy) by (by exists g, vy).
    assert (Hne : oy <> rt m) by (rewrite Hrt; exact Hyr).
    (* reassemble [phys] and take the step *)
    iAssert (phys γm γh γl γs root fs m) with "[Hm Hlka Ha Hb]" as "Hp".
    { rewrite /phys. iFrame "Hm Hlka". iSplitR; [by iPureIntro |].
      iSplitL "Ha"; [iExists H; by iFrame | iExists S; by iFrame]. }
    iMod (phys_write with "Hp Hptn") as "(Hp & Hptn & _)".
    (* the ghost state does not move: the pure action lemma is the whole step *)
    assert (Hwf' : WellFormed FType
                     (to_LState_t (write_ms m on f (VLoc oy)) Og U T F))
      by exact (write_fresh_preserves_WellFormed FType m Og U T F lw on f oy
                  Hlkm Hfr Hit Hunr Hheap Hfl Hne Hwf).
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext. iExists (write_ms m on f (VLoc oy)), Og, U, T, F, St, Rg, gg, ww, Fr. iFrame.
      iPureIntro. split; [exact HWF | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - by apply (FLD_same m).
      - intros o0 t0 Hf0. exact (HWFW o0 t0 Hf0).
      - apply RefsRCU_upd; [exact HRefs | exact Hfrcu].
      - intros q t0 Hq. exact (HFrc q t0 Hq).
      - exact Hwf'.
      - exact HWUW.
      - exact HFeq.
      - exact HEWF.
      - exact HRR.
      - exact HBnd.
      - exact HLk.
      - exact HWm.
      - first [ exact Hdom
              | by apply (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)
              | by apply (dom_ins Rg _ m _ lw _ Hlkm HLk
                            (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)) ]. }
    iModIntro. iFrame.
  Qed.

  (** ** SyncStop, one attempt

      The grace period for a node stamped at [e] is complete when every
      registration still standing is later than [e].  That is a [map_Forall]
      over the registrations, so the attempt decides it and either takes the
      certificate or does not.  The certificate is a watermark fragment, which
      is persistent -- quiescence past an epoch is stable
      (\texttt{quiescence\_is\_stable}), so once the wait has succeeded the
      writer carries a fact rather than holding a resource.

      The disjunction is the loop body.  Which branch is taken is the
      implementation's scan; that the left one is eventually taken is the part
      that needs a semantics, and it is the only part. *)
  Lemma sync_stop_attempt N γm γh γl γs γo γf γr γe γq E d e :
    ↑N ⊆ E ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    fl_ctl γf d e
    ={E}=∗ fl_ctl γf d e ∗ (wm_lb γq (S e) ∨ True).
  Proof.
    iIntros (HN) "#Hinv Hst".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)"
      "Hclose".
    iDestruct (fl_ctl_agree with "Hf Hst") as %Hstamp.
    destruct (decide (map_Forall (fun _ v => past e v) Rg)) as [Hq | Hnq];
      last first.
    { (* some reader is still inside a section it entered no later than [e] *)
      iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_";
        [iNext; iExists m, Og, U, T, F, St, Rg, gg, ww, Fr; by iFrame |].
      iModIntro. iFrame. by iRight. }
    (* the wait has succeeded: raise the watermark and keep a fragment *)
    assert (Hle : S e <= gg) by exact (proj1 HEWF d e Hstamp).
    (* raise to the later of the two: the watermark never goes backwards, and
       the certificate we want is the weaker of the two bounds *)
    iMod (wm_raise _ _ (Nat.max ww (S e)) (Nat.le_max_l _ _) with "Hwm")
      as "Hwm".
    iMod (wm_snapshot with "Hwm") as "[Hwm Hlb0]".
    iDestruct (wm_lb_weaken _ (S e) _ (Nat.le_max_r _ _) with "Hlb0") as "#Hlb".
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext. iExists m, Og, U, T, F, St, Rg, gg, (Nat.max ww (S e)), Fr. iFrame.
      iPureIntro.
      split; [exact HWF | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - exact HFLD.
      - exact HWFW.
      - exact HRefs.
      - exact HFrc.
      - exact Hwf.
      - exact HWUW.
      - exact HFeq.
      - exact HEWF.
      - exact HRR.
      - exact HBnd.
      - exact HLk.
      - split; [apply Nat.max_lub; [exact (proj1 HWm) | exact Hle] |].
        intros t0 e0 D0 H. apply Nat.max_lub;
          [exact (proj2 HWm t0 e0 D0 H) | exact (Hq t0 _ H)].
      - exact Hdom. }
    iModIntro. iFrame. by iLeft.
  Qed.

  (** What the certificate licenses, read inside the invariant: a node stamped
      no later than the watermark has an empty snapshot, which is the conjunct
      \frbl{}'s denotation asks for.  The writer reads this off a fact it
      carries rather than an entry it owns. *)
  Lemma wm_lb_entry_empty N γm γh γl γs γo γf γr γe γq E d e n :
    ↑N ⊆ E -> e < n ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    fl_ctl γf d e -∗ wm_lb γq n
    ={E}=∗ fl_ctl γf d e.
  Proof.
    iIntros (HN Hlt) "#Hinv Hst Hlb".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)"
      "Hclose".
    iDestruct (fl_ctl_agree with "Hf Hst") as %Hstamp.
    iDestruct (wm_lb_le with "Hwm Hlb") as %Hn.
    (* every registration is at least the watermark, which is past [e] *)
    assert (Hquiet : e_quiescent (mkE gg Rg St) e).
    { intros t0 e0 H0. apply mkE_reg in H0 as [D0 H0].
      exact (Nat.lt_le_trans _ _ _ (Nat.lt_le_trans _ _ _ Hlt Hn)
               (proj2 HWm t0 e0 D0 H0)). }
    assert (Hempty : F !! d = Some ∅)
      by (rewrite HFeq; exact (e_free_premise (mkE gg Rg St) d e Hstamp Hquiet)).
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_";
      [iNext; iExists m, Og, U, T, F, St, Rg, gg, ww, Fr; by iFrame |].
    by iModIntro.
  Qed.

  (** ** WriteBegin's test, and why it is not here

      The lock is an option, so its test is decidable in exactly the way
      \textsc{SyncStop}'s is, and the acquisition is [lk_acquire].  What stops
      it being a triple of the same shape is not the test at all:
      \textsc{WriteBegin} also takes an \itr{} observation on *every reachable
      node*, which \texttt{write\_begin\_preserves\_WellFormed} requires and
      which \textbf{UNQRT-b} is the reason for.  That is a bulk ghost update
      over the reachable set, and it needs the set enumerated -- the same
      premise \texttt{sync\_start\_update} carries, for the same reason.  We
      record that rather than state a lemma whose name would claim more than it
      proves: the lock test is not the obstacle, and saying so is the useful
      part. *)

End atomic.

Print Assumptions read_begin_atomic.
Print Assumptions read_end_atomic.
Print Assumptions sync_stop_attempt.
Print Assumptions wm_lb_entry_empty.

Print Assumptions free_atomic.
Print Assumptions write_fresh_atomic.

Section atomic_link.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (root : Loc) (fs : list FName).

  Lemma link_null_atomic N γm γh γl γs γo γf γr γe γq E lw op f on rho x f0 sp v
        C :
    ↑N ⊆ E ->
    FType f = RCUField ->
    on <> root -> In f0 fs ->
    Oiter lw ∈ sp ->
    (* the path and the fresh node's fields, as facts about the writer's own
       cell map rather than as separate resources *)
    hstarC C root rho = Some op ->
    (forall g, In g fs -> C !! (on, g) = Some VNull) ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    lk_tok γl lw -∗
    tobs_ctl γo op lw sp -∗
    tobs_ctl γo on lw {[Ofresh lw]} -∗
    sv γs x lw on -∗
    cells γh C -∗
    pt γh op f v
    ={E}=∗ lk_tok γl lw ∗ tobs_ctl γo op lw sp
           ∗ tobs_ctl γo on lw {[Oiter lw]} ∗ sv γs x lw on
           ∗ cells γh C ∗ pt γh op f (VLoc on).
  Proof.
    iIntros (HN Hfrcu Hnr Hf0 Hip HpathC Hnull)
            "#Hinv Hlk Hop Hon Hsv Hcells Hptf".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)" "Hclose".
    iDestruct (tobs_ctl_agree with "Ho Hop") as %Hlop.
    iDestruct (tobs_ctl_agree with "Ho Hon") as %Hlon.
    assert (Hitr : obsv (to_LState_t m Og U T F) op (Oiter lw))
      by (by exists lw, sp).
    assert (Hfr : obsv (to_LState_t m Og U T F) on (Ofresh lw))
      by (exists lw, {[Ofresh lw]}; split;
          [exact Hlon | by apply elem_of_singleton]).
    iDestruct "Hp" as "(Hm & Hlka & %Hrt & Hhp & Hst)".
    iDestruct (lk_agree with "Hlka Hlk") as %Hlkm.
    iDestruct "Hst" as (S) "[%HRS Hb]".
    iDestruct (sv_agree with "Hb Hsv") as %Hsvag.
    assert (Hstk : stk m x lw = Some on) by (rewrite HRS; exact Hsvag).
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    (* the path premise, carried by the spine *)
    iDestruct (cells_agree with "Ha Hcells") as %Hcellag.
    assert (Hsub : forall k v', C !! k = Some v' -> hp m k.1 k.2 = Some v')
      by (intros k v' Hk; rewrite HR; exact (Hcellag k v' Hk)).
    assert (Hrho : hstar (hp m) root rho = Some op)
      by exact (hstarC_hstar C (hp m) root rho op Hsub HpathC).
    (* the fresh node's cells: all null, and there are no others *)
    assert (Hpn : PointsNowhere (hp m) on).
    { intros g y. destruct (in_dec Nat.eq_dec g fs) as [Hin | Hni].
      - rewrite (Hsub (on, g) VNull (Hnull g Hin)). discriminate.
      - destruct (hp m on g) as [w|] eqn:Eg; [| discriminate].
        exfalso. exact (Hni (HS on g w Eg)). }
    assert (Hin : InHeap (to_LState_t m Og U T F) on).
    { exists f0, VNull. exact (Hsub (on, f0) VNull (Hnull f0 Hf0)). }
    (* nothing points at a fresh node *)
    assert (Hni : forall o g, hp m o g <> Some (VLoc on)).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & HFR & _).
      intros o g. exact (proj1 (HFR lw x on Hstk Hfr) o g). }
    (* a fresh node has no free-list entry *)
    assert (Hfl : flist (to_LState_t m Og U T F) on = None).
    { destruct (flist (to_LState_t m Og U T F) on) as [Tr|] eqn:Ef;
        [| reflexivity].
      exfalso. destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HFNR & _).
      destruct (HFLD on Tr Ef) as [t0 [Hu | Hd]];
        destruct (HFNR on lw t0 Hfr) as (_ & Hnu & Hnf);
        [exact (Hnu Hu) | exact (Hnf Hd)]. }
    (* no other thread observes the node as fresh *)
    assert (Hsole : forall t t' sg,
              Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw).
    { intros t t' sg Hlk' Hin'.
      assert (Ht : t = t').
      { destruct (HWF on t' sg (Ofresh t) Hlk' Hin') as [Htid | Hc];
          [| discriminate]. simpl in Htid. by injection Htid. }
      assert (Hlw : lk m = Some t).
      { apply (HWFW on t). by exists t', sg. }
      rewrite Hlkm in Hlw. injection Hlw as <-. exact (eq_sym Ht). }
    assert (HU : UNQR_h (hp m) (rt m)).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                       _ & _ & _ & _ & _ & HUq).
      exact HUq. }
    assert (Hrt' : on <> rt m) by (rewrite Hrt; exact Hnr).
    assert (Hrho' : hstar (hp m) (rt m) rho = Some op)
      by (rewrite Hrt; exact Hrho).
    (* reassemble, write, and take the ghost step *)
    iAssert (phys γm γh γl γs root fs m) with "[Hm Hlka Ha Hb]" as "Hp".
    { rewrite /phys. iFrame "Hm Hlka". iSplitR; [by iPureIntro |].
      iSplitL "Ha"; [iExists H; by iFrame | iExists S; by iFrame]. }
    destruct (link_null_pure FType m Og U T F lw op f on rho
                HWF Hwf Hsole Hlon Hlkm Hitr Hpn Hni Hin Hrt' Hfl Hrho' HU)
      as [HWF' Hwf'].
    iMod (phys_write with "Hp Hptf") as "(Hp & Hptf & _)".
    iMod (tobs_set with "Ho Hon") as "[Ho Hon]".
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext.
      iExists (write_ms m op f (VLoc on)),
              (<[(on, lw) := {[Oiter lw]}]> Og), U, T, F, St, Rg, gg, ww, Fr.
      iFrame. iPureIntro. split; [exact HWF' | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - intros o Tr Hfl'. destruct (HFLD o Tr Hfl') as [t0 Hdet].
        exists t0. destruct Hdet as [Hd | Hd];
          [left | right];
          (destruct Hd as [t' [sg [Hl Hin']]];
           destruct (decide ((o, t') = (on, lw))) as [Heq | Hne];
           [ injection Heq as -> ->; rewrite Hlon in Hl; injection Hl as <-;
             apply elem_of_singleton in Hin'; discriminate
           | exists t', sg; split; [by rewrite lookup_insert_ne | exact Hin']]).
      - intros o t0 Hf0'.
        destruct (tobs_ins_new m Og U T F on lw _ o (Ofresh t0) Hf0')
          as [[-> Hin'] | Hy].
        + apply elem_of_singleton in Hin'. discriminate.
        + exact (HWFW o t0 Hy).
      - apply RefsRCU_upd; [exact HRefs | exact Hfrcu].
      - intros q t0 Hq.
        destruct (tobs_ins_new m Og U T F on lw _ q (Ofresh t0) Hq)
          as [[-> Hin'] | Hy].
        + apply elem_of_singleton in Hin'. discriminate.
        + exact (HFrc q t0 Hy).
      - exact Hwf'.
      - apply (WUNLKW_ins m _ _ _ _ _ _ _ _ lw);
          [ exact HWUW | reflexivity | exact Hlkm
          | intros t0 [Hz | Hz]; apply elem_of_singleton in Hz;
            discriminate ].
      - exact HFeq.
      - exact HEWF.
      - exact HRR.
      - exact HBnd.
      - exact HLk.
      - exact HWm.
      - first [ exact Hdom
              | by apply (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)
              | by apply (dom_ins Rg _ m _ lw _ Hlkm HLk
                            (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)) ]. }
    iModIntro. iFrame.
  Qed.


  (** ** T-Insert: the same, with the fresh node already pointing somewhere

      The fresh node carries one edge, to the node it is being inserted above,
      and its other fields are null.  That is [PointsOnlyAt], and it is the same
      resource as before read differently: the thread holds all of the node's
      declared cells, one of them a pointer and the rest null, and the class
      declaration says there are no others. *)
  Lemma insert_atomic N γm γh γl γs γo γf γr γe γq E lw op f on oo f4 rho x sp C :
    ↑N ⊆ E ->
    on <> root -> In f4 fs ->
    Oiter lw ∈ sp ->
    hstarC C root rho = Some op ->
    (forall g, In g fs ->
       C !! (on, g) = Some (if decide (g = f4) then VLoc oo else VNull)) ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    lk_tok γl lw -∗
    tobs_ctl γo op lw sp -∗
    tobs_ctl γo on lw {[Ofresh lw]} -∗
    sv γs x lw on -∗
    cells γh C -∗
    pt γh op f (VLoc oo)
    ={E}=∗ lk_tok γl lw ∗ tobs_ctl γo op lw sp
           ∗ tobs_ctl γo on lw {[Oiter lw]} ∗ sv γs x lw on
           ∗ cells γh C ∗ pt γh op f (VLoc on).
  Proof.
    iIntros (HN Hnr Hf4 Hip HpathC Hcell0)
            "#Hinv Hlk Hop Hon Hsv Hcells Hptf".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)" "Hclose".
    iDestruct (tobs_ctl_agree with "Ho Hop") as %Hlop.
    iDestruct (tobs_ctl_agree with "Ho Hon") as %Hlon.
    assert (Hitr : obsv (to_LState_t m Og U T F) op (Oiter lw))
      by (by exists lw, sp).
    assert (Hfr : obsv (to_LState_t m Og U T F) on (Ofresh lw))
      by (exists lw, {[Ofresh lw]}; split;
          [exact Hlon | by apply elem_of_singleton]).
    iDestruct "Hp" as "(Hm & Hlka & %Hrt & Hhp & Hst)".
    iDestruct (lk_agree with "Hlka Hlk") as %Hlkm.
    iDestruct "Hst" as (S) "[%HRS Hb]".
    iDestruct (sv_agree with "Hb Hsv") as %Hsvag.
    assert (Hstk : stk m x lw = Some on) by (rewrite HRS; exact Hsvag).
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    iDestruct (cells_agree with "Ha Hcells") as %Hcellag.
    assert (Hsub : forall k v', C !! k = Some v' -> hp m k.1 k.2 = Some v')
      by (intros k v' Hk; rewrite HR; exact (Hcellag k v' Hk)).
    assert (Hrho : hstar (hp m) root rho = Some op)
      by exact (hstarC_hstar C (hp m) root rho op Hsub HpathC).
    iDestruct (pt_agree with "Ha Hptf") as %Hagf.
    assert (Hedge : hp m op f = Some (VLoc oo)) by (rewrite HR; exact Hagf).
    assert (Hcell : forall g, In g fs ->
              hp m on g = Some (if decide (g = f4) then VLoc oo else VNull)).
    { intros g Hg. exact (Hsub (on, g) _ (Hcell0 g Hg)). }
    assert (Hpo : PointsOnlyAt (hp m) on f4 oo).
    { split.
      - rewrite (Hcell f4 Hf4). by rewrite decide_True.
      - intros g y Hne. destruct (in_dec Nat.eq_dec g fs) as [Hg | Hg].
        + rewrite (Hcell g Hg). rewrite decide_False; [discriminate | exact Hne].
        + destruct (hp m on g) as [w|] eqn:Eg; [| discriminate].
          exfalso. exact (Hg (HS on g w Eg)). }
    assert (Hin : InHeap (to_LState_t m Og U T F) on).
    { exists f4, (VLoc oo). simpl. rewrite (Hcell f4 Hf4).
      by rewrite decide_True. }
    assert (Hni : forall o g, hp m o g <> Some (VLoc on)).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & HFR & _).
      intros o g. exact (proj1 (HFR lw x on Hstk Hfr) o g). }
    assert (Hfl : flist (to_LState_t m Og U T F) on = None).
    { destruct (flist (to_LState_t m Og U T F) on) as [Tr|] eqn:Ef;
        [| reflexivity].
      exfalso. destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HFNR & _).
      destruct (HFLD on Tr Ef) as [t0 [Hu | Hd]];
        destruct (HFNR on lw t0 Hfr) as (_ & Hnu & Hnf);
        [exact (Hnu Hu) | exact (Hnf Hd)]. }
    assert (Hsole : forall t t' sg,
              Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw).
    { intros t t' sg Hlk' Hin'.
      assert (Ht : t = t').
      { destruct (HWF on t' sg (Ofresh t) Hlk' Hin') as [Htid | Hc];
          [| discriminate]. simpl in Htid. by injection Htid. }
      assert (Hlw : lk m = Some t).
      { apply (HWFW on t). by exists t', sg. }
      rewrite Hlkm in Hlw. injection Hlw as <-. exact (eq_sym Ht). }
    assert (HU : UNQR_h (hp m) (rt m)).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                       _ & _ & _ & _ & _ & HUq).
      exact HUq. }
    assert (Hrt' : on <> rt m) by (rewrite Hrt; exact Hnr).
    assert (Hrho' : hstar (hp m) (rt m) rho = Some op)
      by (rewrite Hrt; exact Hrho).
    iAssert (phys γm γh γl γs root fs m) with "[Hm Hlka Ha Hb]" as "Hp".
    { rewrite /phys. iFrame "Hm Hlka". iSplitR; [by iPureIntro |].
      iSplitL "Ha"; [iExists H; by iFrame | iExists S; by iFrame]. }
    destruct (insert_pure FType m Og U T F lw op f on oo f4 rho
                HWF Hwf Hsole Hlon Hlkm HRefs Hedge Hitr Hpo Hni Hin Hrt' Hfl
                Hrho' HU) as [HWF' Hwf'].
    iMod (phys_write with "Hp Hptf") as "(Hp & Hptf & _)".
    iMod (tobs_set with "Ho Hon") as "[Ho Hon]".
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext.
      iExists (write_ms m op f (VLoc on)),
              (<[(on, lw) := {[Oiter lw]}]> Og), U, T, F, St, Rg, gg, ww, Fr.
      iFrame. iPureIntro. split; [exact HWF' | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - intros o Tr Hfl'. destruct (HFLD o Tr Hfl') as [t0 Hdet].
        exists t0. destruct Hdet as [Hd | Hd];
          [left | right];
          (destruct Hd as [t' [sg [Hl Hin']]];
           destruct (decide ((o, t') = (on, lw))) as [Heq | Hne];
           [ injection Heq as -> ->; rewrite Hlon in Hl; injection Hl as <-;
             apply elem_of_singleton in Hin'; discriminate
           | exists t', sg; split; [by rewrite lookup_insert_ne | exact Hin']]).
      - intros o t0 Hf0'.
        destruct (tobs_ins_new m Og U T F on lw _ o (Ofresh t0) Hf0')
          as [[-> Hin'] | Hy].
        + apply elem_of_singleton in Hin'. discriminate.
        + exact (HWFW o t0 Hy).
      - apply RefsRCU_upd; [exact HRefs | exact (HRefs op f oo Hedge)].
      - intros q t0 Hq.
        destruct (tobs_ins_new m Og U T F on lw _ q (Ofresh t0) Hq)
          as [[-> Hin'] | Hy].
        + apply elem_of_singleton in Hin'. discriminate.
        + exact (HFrc q t0 Hy).
      - exact Hwf'.
      - apply (WUNLKW_ins m _ _ _ _ _ _ _ _ lw);
          [ exact HWUW | reflexivity | exact Hlkm
          | intros t0 [Hz | Hz]; apply elem_of_singleton in Hz;
            discriminate ].
      - exact HFeq.
      - exact HEWF.
      - exact HRR.
      - exact HBnd.
      - exact HLk.
      - exact HWm.
      - first [ exact Hdom
              | by apply (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)
              | by apply (dom_ins Rg _ m _ lw _ Hlkm HLk
                            (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)) ]. }
    iModIntro. iFrame.
  Qed.

End atomic_link.

Print Assumptions link_null_atomic.
Print Assumptions insert_atomic.


(** * The premise no fragment can state

    \textsc{T-UnlinkH} and \textsc{T-Replace} carry the repair for the aliasing
    defect: no \frsh{} reference anywhere may point at the node being unlinked.
    Every other premise of every rule is either a fact about a cell, an
    observation, the lock or a path -- things a thread can hold.  This one is
    not.  It quantifies over every fresh node in the system, and a fragment says
    what is, never what is absent everywhere.

    What discharges it in the type system is the environment: the denotation of
    a type environment is an intersection over all of it, so a rule may read off
    a property of every \texttt{rcuFresh} reference at once.  Translating that
    into separation logic is the last thing this development needs, and it comes
    out as two pieces.

    The invariant records that the fresh nodes are *enumerated*: every location
    observed \frsh{} lies in a set whose authority the invariant holds.  The
    thread holds the matching exclusive fragment, so inside the invariant it
    learns the enumeration, and it holds those nodes' cells, so it knows their
    contents.  The rule's premise is then a property of values the thread owns
    -- [forall q g, val q g <> VLoc oz] -- which mentions no shared state at
    all, and which is exactly what the checker's [noFreshPointsAt] decides by
    walking the environment.

    The universal quantifier does not disappear; it moves from the shared state,
    where nothing could discharge it, to the thread's own resources, where the
    type system already had it. *)

Section fresh_env.
  Context `{!heapG Σ}.

  (** The writer's fresh nodes are cells in the one cell map it owns, picked
      out by the enumeration [Fr].  An earlier version made them a separate
      resource; folding them into the cell map is the same move as everywhere
      else in this section, and it means a fresh node's cells and a path's cells
      are the same kind of thing. *)
  Definition FrCells (Fr : gset Loc) (fs : list FName)
      (C : gmap (Loc * FName) Val) (val : Loc -> FName -> Val) : Prop :=
    forall q g, q ∈ Fr -> In g fs -> C !! (q, g) = Some (val q g).

  (** The cells a freshly allocated node contributes. *)
  Definition newcells (fs : list FName) (n : Loc) : gmap (Loc * FName) Val :=
    list_to_map ((fun g => ((n, g), VNull)) <$> fs).

  Lemma newcells_keys (fs : list FName) (n : Loc) : NoDup fs ->
    NoDup (((fun g => ((n, g), VNull)) <$> fs).*1).
  Proof.
    intros Hnd.
    assert (Hkeys : ((fun g => ((n, g), VNull)) <$> fs).*1
                    = (fun g => (n, g)) <$> fs)
      by (rewrite -list_fmap_compose; reflexivity).
    rewrite Hkeys.
    assert (Hinj : Inj eq eq (fun g : FName => (n, g))).
    { intros a b Hc. by injection Hc. }
    by apply NoDup_fmap_2.
  Qed.

  Lemma newcells_at (fs : list FName) (n : Loc) (g : FName) :
    NoDup fs -> In g fs -> newcells fs n !! (n, g) = Some VNull.
  Proof.
    intros Hnd Hg. rewrite /newcells. apply elem_of_list_to_map.
    - exact (newcells_keys fs n Hnd).
    - apply (list_elem_of_fmap_2 (fun g' => ((n, g'), VNull)) fs g).
      by apply list_elem_of_In.
  Qed.

  Lemma newcells_other (fs : list FName) (n : Loc) (k : Loc * FName) :
    k.1 <> n -> newcells fs n !! k = None.
  Proof.
    intros Hk. rewrite /newcells. apply not_elem_of_list_to_map_1.
    intros Hc. apply list_elem_of_fmap_1 in Hc. destruct Hc as [p [Hp1 Hpin]].
    apply list_elem_of_fmap_1 in Hpin. destruct Hpin as [g [-> Hg]].
    simpl in Hp1. apply Hk. by rewrite Hp1.
  Qed.

  Lemma cells_new γh (fs : list FName) (n : Loc) :
    NoDup fs ->
    ([∗ list] p ∈ ((fun g => ((n, g), VNull)) <$> fs),
       pt γh p.1.1 p.1.2 p.2) -∗ cells γh (newcells fs n).
  Proof.
    iIntros (Hnd) "Hl". rewrite /cells /newcells.
    rewrite big_sepM_list_to_map; [| exact (newcells_keys fs n Hnd)].
    iApply (big_sepL_mono with "Hl"). iIntros (k p _) "Hc".
    by destruct p as [[o g] v].
  Qed.

  Lemma cells_agree_one γh fs val H q :
    hp_auth γh H -∗ ([∗ list] g ∈ fs, pt γh q g (val q g)) -∗
    ⌜forall g, In g fs -> H !! (q, g) = Some (val q g)⌝.
  Proof.
    iIntros "Ha Hc". iInduction fs as [|g gs IH] "IH".
    - iPureIntro. intros g Hg. destruct Hg.
    - iDestruct "Hc" as "[Hg Hgs]".
      iDestruct (pt_agree with "Ha Hg") as %Hag.
      iDestruct ("IH" with "Ha Hgs") as %Hrest.
      iPureIntro. intros g' Hg'. destruct Hg' as [-> | Hg'];
        [exact Hag | exact (Hrest g' Hg')].
  Qed.

End fresh_env.

Section atomic_unlink.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (root : Loc) (fs : list FName).

  Lemma unlink_atomic N γm γh γl γs γo γf γr γe γq E lw ox f1 oz f2 ow rho
        sx sw Fr val C :
    ↑N ⊆ E ->
    Oiter lw ∈ sx -> Oiter lw ∈ sw ->
    (* the aliasing premise, now about the thread's own resources *)
    FrCells Fr fs C val ->
    hstarC C root rho = Some ox ->
    (* the child's field is only read, so it is a condition on the cell map
       rather than a resource taken apart from it *)
    C !! (oz, f2) = Some (VLoc ow) ->
    (forall q g, val q g <> VLoc oz) ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    lk_tok γl lw -∗
    tobs_ctl γo ox lw sx -∗
    tobs_ctl γo oz lw {[Oiter lw]} -∗
    tobs_ctl γo ow lw sw -∗
    cells γh C -∗
    pt γh ox f1 (VLoc oz) -∗
    fr_frag γr Fr
    ={E}=∗ lk_tok γl lw ∗ tobs_ctl γo ox lw sx
           ∗ tobs_ctl γo oz lw {[Ounlk lw]} ∗ tobs_ctl γo ow lw sw
           ∗ cells γh C ∗ pt γh ox f1 (VLoc ow)
           ∗ fr_frag γr Fr.
  Proof.
    iIntros (HN Hix Hiw HFrC HpathC Hcell2 Hnf)
            "#Hinv Hlk Hox Hoz How Hcells Hpt1 Hfrg".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr0)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)" "Hclose".
    iDestruct (fr_agree with "Hfr Hfrg") as %->.
    iDestruct (tobs_ctl_agree with "Ho Hox") as %Hlox.
    iDestruct (tobs_ctl_agree with "Ho Hoz") as %Hloz.
    iDestruct (tobs_ctl_agree with "Ho How") as %Hlow.
    assert (Hitx : obsv (to_LState_t m Og U T F) ox (Oiter lw))
      by (by exists lw, sx).
    assert (Hitz : obsv (to_LState_t m Og U T F) oz (Oiter lw))
      by (exists lw, {[Oiter lw]}; split;
          [exact Hloz | by apply elem_of_singleton]).
    assert (Hitw : obsv (to_LState_t m Og U T F) ow (Oiter lw))
      by (by exists lw, sw).
    iDestruct "Hp" as "(Hm & Hlka & %Hrt & Hhp & Hst)".
    iDestruct (lk_agree with "Hlka Hlk") as %Hlkm.
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    iDestruct (cells_agree with "Ha Hcells") as %Hcellag.
    assert (Hsub : forall k v', C !! k = Some v' -> hp m k.1 k.2 = Some v')
      by (intros k v' Hk; rewrite HR; exact (Hcellag k v' Hk)).
    assert (Hrho : hstar (hp m) root rho = Some ox)
      by exact (hstarC_hstar C (hp m) root rho ox Hsub HpathC).
    iDestruct (pt_agree with "Ha Hpt1") as %Hag1.
    assert (He1 : hp m ox f1 = Some (VLoc oz)) by (rewrite HR; exact Hag1).
    assert (He2 : hp m oz f2 = Some (VLoc ow))
      by exact (Hsub (oz, f2) (VLoc ow) Hcell2).
    (* the free-list premise, from FLD and WULK *)
    assert (Hfl : flist (to_LState_t m Og U T F) ow = None).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & HWU & _).
      exact (iter_no_flist _ lw ow HFLD HWU Hlkm Hitw). }
    (* the aliasing premise: the fresh nodes are enumerated, and the thread
       holds their cells *)
    assert (Hnofresh : forall q t g,
              obsv (to_LState_t m Og U T F) q (Ofresh t) ->
              hp m q g <> Some (VLoc oz)).
    { intros q t g Hfr.
      assert (Hq : q ∈ Fr) by exact (HFrc q t Hfr).
      destruct (in_dec Nat.eq_dec g fs) as [Hg | Hg].
      - rewrite HR (Hcellag (q, g) (val q g) (HFrC q g Hq Hg)).
        intros Hc. injection Hc as Hc. exact (Hnf q g Hc).
      - destruct (hp m q g) as [w|] eqn:Eq; [| discriminate].
        exfalso. exact (Hg (HS q g w Eq)). }
    assert (HU : UNQR_h (hp m) (rt m)).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                       _ & _ & _ & _ & _ & HUq).
      exact HUq. }
    assert (Hrho' : hstar (hp m) (rt m) rho = Some ox)
      by (rewrite Hrt; exact Hrho).
    iAssert (phys γm γh γl γs root fs m) with "[Hm Hlka Ha Hst]" as "Hp".
    { rewrite /phys. iFrame "Hm Hlka Hst". iSplitR; [by iPureIntro |].
      iExists H. by iFrame. }
    destruct (unlink_pure FType m Og U T F lw ox f1 oz f2 ow rho
                HWF Hwf Hloz HRefs Hlkm He1 He2 Hitx Hitz Hitw Hfl Hrho' HU
                Hnofresh) as [HWF' Hwf'].
    iMod (phys_write with "Hp Hpt1") as "(Hp & Hpt1 & _)".
    iMod (tobs_set with "Ho Hoz") as "[Ho Hoz]".
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext.
      iExists (write_ms m ox f1 (VLoc ow)),
              (<[(oz, lw) := {[Ounlk lw]}]> Og), U, T, F, St, Rg, gg, ww, Fr.
      iFrame. iPureIntro. split; [exact HWF' | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - intros o Tr Hfl'. destruct (HFLD o Tr Hfl') as [t0 Hdet].
        exists t0. destruct Hdet as [Hd | Hd];
          [left | right];
          (destruct Hd as [t' [sg [Hl Hin']]];
           destruct (decide ((o, t') = (oz, lw))) as [Heq | Hne];
           [ injection Heq as -> ->; rewrite Hloz in Hl; injection Hl as <-;
             apply elem_of_singleton in Hin'; discriminate
           | exists t', sg; split; [by rewrite lookup_insert_ne | exact Hin']]).
      - intros o t0 Hf0'.
        destruct (tobs_ins_new m Og U T F oz lw _ o (Ofresh t0) Hf0')
          as [[-> Hin'] | Hy].
        + apply elem_of_singleton in Hin'. discriminate.
        + exact (HWFW o t0 Hy).
      - apply RefsRCU_upd; [exact HRefs | exact (HRefs ox f1 oz He1)].
      - intros q t0 Hq.
        destruct (tobs_ins_new m Og U T F oz lw _ q (Ofresh t0) Hq)
          as [[-> Hin'] | Hy].
        + apply elem_of_singleton in Hin'. discriminate.
        + exact (HFrc q t0 Hy).
      - exact Hwf'.
      - apply (WUNLKW_ins m _ _ _ _ _ _ _ _ lw);
          [ exact HWUW | reflexivity | exact Hlkm
          | intros t0 [Hz | Hz]; apply elem_of_singleton in Hz;
            [ by injection Hz | discriminate ] ].
      - exact HFeq.
      - exact HEWF.
      - exact HRR.
      - exact HBnd.
      - exact HLk.
      - exact HWm.
      - first [ exact Hdom
              | by apply (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)
              | by apply (dom_ins Rg _ m _ lw _ Hlkm HLk
                            (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)) ]. }
    iModIntro. iFrame.
  Qed.

  (** ** T-Replace: the last one

      Replace promotes and demotes in the same step, so its ghost update is two
      entries, and it needs both aliasing premises at once -- no fresh reference
      pointing at the node it unlinks, which the enumerated fresh set supplies,
      and that every detaching observation in the system is the writer's, which
      is WUNLK read directly off the invariant.

      [Mirrors] is the last premise to be carried by a resource: the fresh node
      and the node it replaces agree on every field, which is the thread holding
      both nodes' cells with the same values.  Under the class declaration the
      declared fields are all there are, so agreeing on those is agreeing. *)
  Lemma replace_atomic N γm γh γl γs γo γf γr γe γq E lw op f oo on rho x f0 sp Fr
        val valo C :
    ↑N ⊆ E ->
    on <> oo -> on <> root -> In f0 fs ->
    Oiter lw ∈ sp ->
    FrCells Fr fs C val ->
    hstarC C root rho = Some op ->
    (forall g, In g fs -> C !! (on, g) = Some (valo g)) ->
    (forall g, In g fs -> C !! (oo, g) = Some (valo g)) ->
    (forall q g, val q g <> VLoc oo) ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    lk_tok γl lw -∗
    tobs_ctl γo op lw sp -∗
    tobs_ctl γo on lw {[Ofresh lw]} -∗
    tobs_ctl γo oo lw {[Oiter lw]} -∗
    sv γs x lw on -∗
    cells γh C -∗
    pt γh op f (VLoc oo) -∗
    fr_frag γr Fr
    ={E}=∗ lk_tok γl lw ∗ tobs_ctl γo op lw sp
           ∗ tobs_ctl γo on lw {[Oiter lw]} ∗ tobs_ctl γo oo lw {[Ounlk lw]}
           ∗ sv γs x lw on ∗ cells γh C ∗ pt γh op f (VLoc on)
           ∗ fr_frag γr Fr.
  Proof.
    iIntros (HN Hno Hnr Hf0 Hip HFrC HpathC Hcn0 Hco0 Hnf)
            "#Hinv Hlk Hop Hon Hoo Hsv Hcells Hptf Hfrg".
    iInv "Hinv" as (m Og U T F St Rg gg ww Fr0)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)" "Hclose".
    iDestruct (fr_agree with "Hfr Hfrg") as %->.
    iDestruct (tobs_ctl_agree with "Ho Hop") as %Hlop.
    iDestruct (tobs_ctl_agree with "Ho Hon") as %Hlon.
    iDestruct (tobs_ctl_agree with "Ho Hoo") as %Hloo.
    assert (Hitr : obsv (to_LState_t m Og U T F) op (Oiter lw))
      by (by exists lw, sp).
    assert (Hfr : obsv (to_LState_t m Og U T F) on (Ofresh lw))
      by (exists lw, {[Ofresh lw]}; split;
          [exact Hlon | by apply elem_of_singleton]).
    iDestruct "Hp" as "(Hm & Hlka & %Hrt & Hhp & Hst)".
    iDestruct (lk_agree with "Hlka Hlk") as %Hlkm.
    iDestruct "Hst" as (S) "[%HRS Hb]".
    iDestruct (sv_agree with "Hb Hsv") as %Hsvag.
    assert (Hstk : stk m x lw = Some on) by (rewrite HRS; exact Hsvag).
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    iDestruct (cells_agree with "Ha Hcells") as %Hcellag.
    assert (Hsub : forall k v', C !! k = Some v' -> hp m k.1 k.2 = Some v')
      by (intros k v' Hk; rewrite HR; exact (Hcellag k v' Hk)).
    assert (Hrho : hstar (hp m) root rho = Some op)
      by exact (hstarC_hstar C (hp m) root rho op Hsub HpathC).
    iDestruct (pt_agree with "Ha Hptf") as %Hagf.
    assert (Hedge : hp m op f = Some (VLoc oo)) by (rewrite HR; exact Hagf).
    assert (Hcn : forall g, In g fs -> H !! (on, g) = Some (valo g))
      by (intros g Hg; exact (Hcellag (on, g) _ (Hcn0 g Hg))).
    assert (Hco : forall g, In g fs -> H !! (oo, g) = Some (valo g))
      by (intros g Hg; exact (Hcellag (oo, g) _ (Hco0 g Hg))).
    (* the two nodes agree on every field: on the declared ones because the
       thread holds both with the same value, elsewhere because there are no
       others *)
    assert (Hmir : Mirrors (hp m) on oo).
    { intros g. destruct (in_dec Nat.eq_dec g fs) as [Hg | Hg].
      - rewrite !HR (Hcn g Hg) (Hco g Hg). reflexivity.
      - destruct (hp m on g) as [w|] eqn:E1;
          [exfalso; exact (Hg (HS on g w E1)) |].
        destruct (hp m oo g) as [w|] eqn:E2;
          [exfalso; exact (Hg (HS oo g w E2)) | reflexivity]. }
    assert (Hin : InHeap (to_LState_t m Og U T F) on).
    { exists f0, (valo f0). simpl. rewrite HR. exact (Hcn f0 Hf0). }
    assert (Hni : forall o g, hp m o g <> Some (VLoc on)).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & HFR & _).
      intros o g. exact (proj1 (HFR lw x on Hstk Hfr) o g). }
    assert (Hfl : flist (to_LState_t m Og U T F) on = None).
    { destruct (flist (to_LState_t m Og U T F) on) as [Tr|] eqn:Ef;
        [| reflexivity].
      exfalso. destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HFNR & _).
      destruct (HFLD on Tr Ef) as [t0 [Hu | Hd]];
        destruct (HFNR on lw t0 Hfr) as (_ & Hnu & Hnfe);
        [exact (Hnu Hu) | exact (Hnfe Hd)]. }
    assert (Hsole : forall t t' sg,
              Og !! (on, t') = Some sg -> Ofresh t ∈ sg -> t' = lw).
    { intros t t' sg Hlk' Hin'.
      assert (Ht : t = t').
      { destruct (HWF on t' sg (Ofresh t) Hlk' Hin') as [Htid | Hc];
          [| discriminate]. simpl in Htid. by injection Htid. }
      assert (Hlw : lk m = Some t).
      { apply (HWFW on t). by exists t', sg. }
      rewrite Hlkm in Hlw. injection Hlw as <-. exact (eq_sym Ht). }
    (* no fresh node points at the node being replaced *)
    assert (Hnofresh : forall q t g,
              obsv (to_LState_t m Og U T F) q (Ofresh t) ->
              hp m q g <> Some (VLoc oo)).
    { intros q t g Hfq.
      assert (Hq : q ∈ Fr) by exact (HFrc q t Hfq).
      destruct (in_dec Nat.eq_dec g fs) as [Hg | Hg].
      - rewrite HR (Hcellag (q, g) (val q g) (HFrC q g Hq Hg)).
        intros Hc. injection Hc as Hc. exact (Hnf q g Hc).
      - destruct (hp m q g) as [w|] eqn:Eq; [| discriminate].
        exfalso. exact (Hg (HS q g w Eq)). }
    (* and every detaching observation is the writer's: that is WUNLK *)
    assert (Huw : forall q t0,
              obsv (to_LState_t m Og U T F) q (Ounlk t0)
              \/ obsv (to_LState_t m Og U T F) q (Ofree t0) -> t0 = lw).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                       _ & _ & _ & HWU & _).
      intros q t0 Hd. exact (HWU q t0 lw Hlkm Hd). }
    assert (HU : UNQR_h (hp m) (rt m)).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                       _ & _ & _ & _ & _ & HUq).
      exact HUq. }
    assert (Hrt' : on <> rt m) by (rewrite Hrt; exact Hnr).
    assert (Hrho' : hstar (hp m) (rt m) rho = Some op)
      by (rewrite Hrt; exact Hrho).
    iAssert (phys γm γh γl γs root fs m) with "[Hm Hlka Ha Hb]" as "Hp".
    { rewrite /phys. iFrame "Hm Hlka". iSplitR; [by iPureIntro |].
      iSplitL "Ha"; [iExists H; by iFrame | iExists S; by iFrame]. }
    destruct (replace_pure FType m Og U T F lw op f oo on rho
                HWF Hwf Hno Hsole Hlon Hloo Hlkm HRefs Hedge Hmir Hitr Hni Hin
                Hrt' Hfl Hrho' HU Hnofresh Huw) as [HWF' Hwf'].
    iMod (phys_write with "Hp Hptf") as "(Hp & Hptf & _)".
    iMod (tobs_set with "Ho Hoo") as "[Ho Hoo]".
    iMod (tobs_set with "Ho Hon") as "[Ho Hon]".
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext.
      iExists (write_ms m op f (VLoc on)),
              (<[(on, lw) := {[Oiter lw]}]> (<[(oo, lw) := {[Ounlk lw]}]> Og)),
              U, T, F, St, Rg, gg, ww, Fr.
      iFrame. iPureIntro. split; [exact HWF' | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - intros o Tr Hfl'. destruct (HFLD o Tr Hfl') as [t0 Hdet].
        exists t0. destruct Hdet as [Hd | Hd];
          [left | right];
          (destruct Hd as [t' [sg [Hl Hin']]];
           destruct (decide ((o, t') = (on, lw))) as [Heq1 | Hne1];
           [ injection Heq1 as -> ->; rewrite Hlon in Hl; injection Hl as <-;
             apply elem_of_singleton in Hin'; discriminate
           | destruct (decide ((o, t') = (oo, lw))) as [Heq2 | Hne2];
             [ injection Heq2 as -> ->; rewrite Hloo in Hl; injection Hl as <-;
               apply elem_of_singleton in Hin'; discriminate
             | exists t', sg; split;
               [ rewrite lookup_insert_ne; [| done];
                 rewrite lookup_insert_ne; [exact Hl | done]
               | exact Hin'] ]]).
      - intros o t0 Hf0'.
        destruct Hf0' as [t' [sg [Hl Hin']]].
        destruct (decide ((o, t') = (on, lw))) as [Heq1 | Hne1].
        + injection Heq1 as -> ->. rewrite lookup_insert_eq in Hl.
          injection Hl as <-. apply elem_of_singleton in Hin'. discriminate.
        + rewrite lookup_insert_ne in Hl; [| done].
          destruct (decide ((o, t') = (oo, lw))) as [Heq2 | Hne2].
          * injection Heq2 as -> ->. rewrite lookup_insert_eq in Hl.
            injection Hl as <-. apply elem_of_singleton in Hin'. discriminate.
          * rewrite lookup_insert_ne in Hl; [| done].
            apply (HWFW o t0). by exists t', sg.
      - apply RefsRCU_upd; [exact HRefs | exact (HRefs op f oo Hedge)].
      - intros q t0 Hq.
        destruct Hq as [t' [sg [Hl Hin']]].
        destruct (decide ((q, t') = (on, lw))) as [Heq1 | Hne1].
        + injection Heq1 as -> ->. rewrite lookup_insert_eq in Hl.
          injection Hl as <-. apply elem_of_singleton in Hin'. discriminate.
        + rewrite lookup_insert_ne in Hl; [| done].
          destruct (decide ((q, t') = (oo, lw))) as [Heq2 | Hne2].
          * injection Heq2 as -> ->. rewrite lookup_insert_eq in Hl.
            injection Hl as <-. apply elem_of_singleton in Hin'. discriminate.
          * rewrite lookup_insert_ne in Hl; [| done].
            apply (HFrc q t0). by exists t', sg.
      - exact Hwf'.
      - apply (WUNLKW_ins m _ _ _ _ _ _ _ _ lw);
          [ apply (WUNLKW_ins m m _ _ _ _ _ _ _ lw);
            [ exact HWUW | reflexivity | exact Hlkm
            | intros t0 [Hz | Hz]; apply elem_of_singleton in Hz;
              [ by injection Hz | discriminate ] ]
          | reflexivity | exact Hlkm
          | intros t0 [Hz | Hz]; apply elem_of_singleton in Hz;
            discriminate ].
      - exact HFeq.
      - exact HEWF.
      - exact HRR.
      - exact HBnd.
      - exact HLk.
      - exact HWm.
      - first [ exact Hdom
              | by apply (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)
              | by apply (dom_ins Rg _ m _ lw _ Hlkm HLk
                            (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)) ]. }
    iModIntro. iFrame.
  Qed.

End atomic_unlink.

Print Assumptions unlink_atomic.
Print Assumptions replace_atomic.

(** * The allocator

    The last thing.  \textsc{T-Alloc}'s premises say the new location is
    unallocated, unreferenced, pointed at by nothing, unobserved, not on the
    free list and not the root.  Those are six negative facts about shared
    state, and no thread can hold a resource saying any of them -- which is why
    allocation was the one action that looked to need an operational semantics
    before it could be a triple.

    It does not.  What it needs is an allocator, and an allocator is a function
    of the state, which is now finite in every component: a finite heap, a
    finite stack, a finite observation map, a finite free list.  So the set of
    locations that are used for anything is a finite set, and a location outside
    it satisfies all six conditions at once.  [stdpp]'s [fresh] produces one.

    That is the whole of it.  The reason allocation could not close was never
    the absence of a language; it was that the state model made the used set
    infinite, and the field-list repair is what made it finite.  The same repair
    pays twice. *)

Definition val_loc (v : Val) : option Loc :=
  match v with VLoc o => Some o | VNull => None end.

(** Every location the state mentions: as a node, as an edge target, as a
    reference, as an observed location, or on the free list. *)
Definition used (r : Loc) (H : gmap (Loc * FName) Val)
    (S : gmap (Var * TID) Loc) (Og : ObsMap) (F : gmap Loc (gset TID))
    (Fr : gset Loc) : gset Loc :=
  {[ r ]}
  ∪ set_map (fun k => k.1) (dom H)
  ∪ list_to_set (omap val_loc (map_to_list H).*2)
  ∪ list_to_set (map_to_list S).*2
  ∪ set_map (fun k => k.1) (dom Og)
  ∪ dom F
  ∪ Fr.

Section allocator.
  Variables (r : Loc) (H : gmap (Loc * FName) Val) (S : gmap (Var * TID) Loc)
            (Og : ObsMap) (F : gmap Loc (gset TID)) (Fr : gset Loc).
  Variable n : Loc.
  Hypothesis Hn : n ∉ used r H S Og F Fr.

  Lemma fresh_not_fresh : n ∉ Fr.
  Proof. intros Hc. apply Hn. rewrite /used. set_solver. Qed.

  Lemma fresh_not_root : n <> r.
  Proof. intros ->. apply Hn. rewrite /used. set_solver. Qed.

  Lemma fresh_unallocated g : H !! (n, g) = None.
  Proof.
    destruct (H !! (n, g)) as [v|] eqn:E; [| reflexivity]. exfalso.
    assert (Hin : n ∈ (set_map (fun k => k.1) (dom H) : gset Loc)).
    { apply elem_of_map. exists (n, g). split; [reflexivity |].
      apply elem_of_dom. by exists v. }
    apply Hn. rewrite /used. set_solver.
  Qed.

  Lemma fresh_unpointed k v : H !! k = Some v -> v <> VLoc n.
  Proof.
    intros Hlk ->.
    assert (Hin : n ∈ (list_to_set (omap val_loc (map_to_list H).*2)
                       : gset Loc)).
    { apply elem_of_list_to_set. apply list_elem_of_omap.
      exists (VLoc n). split; [| reflexivity].
      apply (list_elem_of_fmap_2 snd (map_to_list H) (k, VLoc n)).
      by apply elem_of_map_to_list. }
    apply Hn. rewrite /used. set_solver.
  Qed.

  Lemma fresh_unreferenced k : S !! k <> Some n.
  Proof.
    intros Hlk.
    assert (Hin : n ∈ (list_to_set (map_to_list S).*2 : gset Loc)).
    { apply elem_of_list_to_set.
      apply (list_elem_of_fmap_2 snd (map_to_list S) (k, n)).
      by apply elem_of_map_to_list. }
    apply Hn. rewrite /used. set_solver.
  Qed.

  Lemma fresh_unobserved t : Og !! (n, t) = None.
  Proof.
    destruct (Og !! (n, t)) as [sg|] eqn:E; [| reflexivity]. exfalso.
    assert (Hin : n ∈ (set_map (fun k => k.1) (dom Og) : gset Loc)).
    { apply elem_of_map. exists (n, t). split; [reflexivity |].
      apply elem_of_dom. by exists sg. }
    apply Hn. rewrite /used. set_solver.
  Qed.

  Lemma fresh_unlisted : F !! n = None.
  Proof.
    destruct (F !! n) as [sg|] eqn:E; [| reflexivity]. exfalso.
    assert (Hin : n ∈ dom F) by (apply elem_of_dom; by exists sg).
    apply Hn. rewrite /used. set_solver.
  Qed.

End allocator.

Print Assumptions fresh_unallocated.
Print Assumptions fresh_unpointed.

(** ** What the writer holds

    Three maps and the lock: its stack entries, its observations, and the cells
    it has read.  Everything a type environment asserts is a pure condition on
    these. *)

Section writerstate.
  Context `{!rcuG Σ, !heapG Σ, !stackG Σ, !lockG Σ}.

  Definition obs_own (γo : gname) (t : TID) (Ob : gmap Loc (gset obs))
    : iProp Σ := [∗ map] o ↦ sg ∈ Ob, tobs_ctl γo o t sg.

  Definition stk_own (γs : gname) (Sm : gmap (Var * TID) Loc) : iProp Σ :=
    [∗ map] k ↦ o ∈ Sm, sv γs k.1 k.2 o.

  Lemma obs_own_agree γo t Og Ob :
    tobs_auth γo Og -∗ obs_own γo t Ob -∗
    ⌜forall o sg, Ob !! o = Some sg -> Og !! (o, t) = Some sg⌝.
  Proof.
    iIntros "Ha Hc". rewrite /obs_own.
    iInduction Ob as [|o sg Ob Ho] "IH" using map_ind.
    - iPureIntro. intros o sg Hlk. by rewrite lookup_empty in Hlk.
    - rewrite big_sepM_insert; [| exact Ho].
      iDestruct "Hc" as "[Hone Hrest]".
      iDestruct (tobs_ctl_agree with "Ha Hone") as %Hag.
      iDestruct ("IH" with "Ha Hrest") as %Hrest.
      iPureIntro. intros o' sg' Hlk.
      destruct (decide (o' = o)) as [-> | Hne].
      + rewrite lookup_insert_eq in Hlk. by injection Hlk as <-.
      + rewrite lookup_insert_ne in Hlk; [| done]. exact (Hrest o' sg' Hlk).
  Qed.

  Lemma stk_own_agree γs S Sm :
    stk_auth γs S -∗ stk_own γs Sm -∗
    ⌜forall k o, Sm !! k = Some o -> S !! k = Some o⌝.
  Proof.
    iIntros "Ha Hc". rewrite /stk_own.
    iInduction Sm as [|k o Sm Hk] "IH" using map_ind.
    - iPureIntro. intros k o Hlk. by rewrite lookup_empty in Hlk.
    - rewrite big_sepM_insert; [| exact Hk].
      iDestruct "Hc" as "[Hone Hrest]".
      iDestruct (sv_agree with "Ha Hone") as %Hag.
      iDestruct ("IH" with "Ha Hrest") as %Hrest.
      iPureIntro. intros k' o' Hlk.
      destruct (decide (k' = k)) as [-> | Hne].
      + rewrite lookup_insert_eq in Hlk. injection Hlk as <-. by destruct k.
      + rewrite lookup_insert_ne in Hlk; [| done]. exact (Hrest k' o' Hlk).
  Qed.

  (** The writer's free list is stamps now: which threads a snapshot contains
      is the readers' business, and the writer holding the stamp is what lets
      it free the node once the grace period past that stamp is complete. *)
  Definition fl_own (γf : gname) (Fl : gmap Loc nat) : iProp Σ :=
    [∗ map] o ↦ sg ∈ Fl, fl_ctl γf o sg.

  Lemma fl_own_agree γf St Fl :
    fl_auth γf St -∗ fl_own γf Fl -∗
    ⌜forall o sg, Fl !! o = Some sg -> St !! o = Some sg⌝.
  Proof.
    iIntros "Ha Hc". rewrite /fl_own.
    iInduction Fl as [|o sg Fl Ho] "IH" using map_ind.
    - iPureIntro. intros o sg Hlk. by rewrite lookup_empty in Hlk.
    - rewrite big_sepM_insert; [| exact Ho].
      iDestruct "Hc" as "[Hone Hrest]".
      iDestruct (fl_ctl_agree with "Ha Hone") as %Hag.
      iDestruct ("IH" with "Ha Hrest") as %Hrest.
      iPureIntro. intros o' sg' Hlk.
      destruct (decide (o' = o)) as [-> | Hne].
      + rewrite lookup_insert_eq in Hlk. by injection Hlk as <-.
      + rewrite lookup_insert_ne in Hlk; [| done]. exact (Hrest o' sg' Hlk).
  Qed.

  (** A fragment the thread receives cannot already be in its own map: the
      entries are exclusive, so holding two would be a contradiction.  That is
      how a rebundling learns the new key was free. *)
  Lemma obs_own_fresh γo t Ob n sg :
    obs_own γo t Ob -∗ tobs_ctl γo n t sg -∗ ⌜Ob !! n = None⌝.
  Proof.
    iIntros "Hm Hc". rewrite /obs_own.
    destruct (Ob !! n) as [sg'|] eqn:E; [| by iPureIntro].
    iDestruct (big_sepM_lookup _ _ n sg' E with "Hm") as "Hc'".
    by iDestruct (tobs_ctl_exclusive with "Hc Hc'") as %[].
  Qed.

  Definition writer (γo γs γh γl γf : gname) (t : TID)
      (Sm : gmap (Var * TID) Loc) (Ob : gmap Loc (gset obs))
      (C : gmap (Loc * FName) Val) (Fl : gmap Loc nat) : iProp Σ :=
    lk_tok γl t ∗ stk_own γs Sm ∗ obs_own γo t Ob ∗ cells γh C
    ∗ fl_own γf Fl.

End writerstate.

(** ** The environment, as a condition on those maps

    [ItrOK] is [D_rcuItr] with every mention of the shared state replaced by a
    lookup in the thread's own maps.  The scope condition is the one thing that
    is not a map lookup, because scope is a predicate rather than ghost state;
    it is carried as a parameter, exactly as [U] is in the invariant. *)

(** A field map, read on the thread's own maps.  This is what lets a type carry
    a field map at all: [FVar y] is a lookup in the cell map whose target is a
    variable the environment also names. *)
Definition FieldOK (t : TID) (Sm : gmap (Var * TID) Loc)
    (Ob : gmap Loc (gset obs)) (C : gmap (Loc * FName) Val)
    (o : Loc) (N : FieldMap) : Prop :=
  forall f v, N f = Some v ->
    match v with
    | FVar y => exists oy sg, Sm !! (y, t) = Some oy
                           /\ C !! (o, f) = Some (VLoc oy)
                           /\ Ob !! oy = Some sg /\ Oiter t ∈ sg
    | FNull  => C !! (o, f) = Some VNull
    end.

Definition ItrOK (root : Loc) (t : TID) (U : Var -> TID -> Prop)
    (Sm : gmap (Var * TID) Loc) (Ob : gmap Loc (gset obs))
    (C : gmap (Loc * FName) Val)
    (x : Var) (rho : list FName) (N : FieldMap) : Prop :=
  exists o sg,
    Sm !! (x, t) = Some o
    /\ Ob !! o = Some sg /\ Oiter t ∈ sg
    /\ ~ U x t
    /\ FieldOK t Sm Ob C o N
    /\ hstarC C root rho = Some o
    /\ (forall rho1 rho2, rho1 ++ rho2 = rho ->
          exists o' sg', hstarC C root rho1 = Some o'
                      /\ Ob !! o' = Some sg' /\ Oiter t ∈ sg').

(** And the transfer: what the thread holds implies what the type says, once
    the invariant is open.  The free-list condition is the only one that is
    neither a fragment nor a map lookup -- it is negative -- and it comes from
    FLD and WULK, as it has throughout. *)

(** The other four the write side produces, each a condition on the same
    maps. *)

Definition FreshOK (t : TID) (U : Var -> TID -> Prop) (fs : list FName)
    (Sm : gmap (Var * TID) Loc) (Ob : gmap Loc (gset obs))
    (C : gmap (Loc * FName) Val) (x : Var) (N : FieldMap) : Prop :=
  exists o sg,
    Sm !! (x, t) = Some o
    /\ Ob !! o = Some sg /\ Ofresh t ∈ sg
    /\ ~ U x t
    /\ FieldOK t Sm Ob C o N
    /\ (forall g, In g fs -> N g = None -> C !! (o, g) = Some VNull).

Definition DetOK (t : TID) (U : Var -> TID -> Prop) (ob : obs)
    (Sm : gmap (Var * TID) Loc) (Ob : gmap Loc (gset obs))
    (x : Var) : Prop :=
  exists o sg,
    Sm !! (x, t) = Some o /\ Ob !! o = Some sg /\ ob ∈ sg /\ ~ U x t.

Definition RootOK (root : Loc) (t : TID)
    (Sm : gmap (Var * TID) Loc) (Ob : gmap Loc (gset obs))
    (x : Var) : Prop :=
  exists sg, Sm !! (x, t) = Some root
          /\ Ob !! root = Some sg /\ Oroot ∈ sg.

(** The thread's maps agree with the invariant's, and that is all the pure
    reasoning below needs: five submap facts, extracted once. *)

Record Agrees (t : TID) (S : gmap (Var * TID) Loc) (Og : ObsMap)
    (H : gmap (Loc * FName) Val) (St : gmap Loc nat) (lkm : option TID)
    (Sm : gmap (Var * TID) Loc) (Ob : gmap Loc (gset obs))
    (C : gmap (Loc * FName) Val) (Fl : gmap Loc nat) : Prop := {
  ag_stk : forall k o, Sm !! k = Some o -> S !! k = Some o;
  ag_obs : forall o sg, Ob !! o = Some sg -> Og !! (o, t) = Some sg;
  ag_cell : forall k v, C !! k = Some v -> H !! k = Some v;
  ag_fl : forall o e, Fl !! o = Some e -> St !! o = Some e;
  ag_lk : lkm = Some t;
}.

Section transfer_pure.
  Variable FType : FName -> FieldKind.
  Variables (root : Loc) (t : TID) (fs : list FName).
  Variables (U : Var -> TID -> Prop).
  Variables (m : MState) (Og : ObsMap) (T : gset TID)
            (F : gmap Loc (gset TID)) (St : gmap Loc nat).
  Variables (Qc : nat -> Prop).
  Variables (H : gmap (Loc * FName) Val) (S : gmap (Var * TID) Loc).
  Variables (Sm : gmap (Var * TID) Loc) (Ob : gmap Loc (gset obs))
            (C : gmap (Loc * FName) Val) (Fl : gmap Loc nat).
  Hypothesis Hag : Agrees t S Og H St (lk m) Sm Ob C Fl.
  (** A stamp the thread holds a certificate for names a completed grace
      period, so its snapshot is empty.  This is the writer's half of the
      ownership story in [Epochs.v]: the emptiness is a fact it carries, not an
      entry it owns. *)
  Hypothesis HQ : forall o e, St !! o = Some e -> Qc e -> F !! o = Some ∅.
  Hypothesis HR  : Represents (hp m) H.
  Hypothesis HRS : RepresentsS (stk m) S.
  Hypothesis Hrt : rt m = root.
  Hypothesis Hwf : WellFormed FType (to_LState_t m Og U T F).
  Hypothesis HFLD : FLD (to_LState_t m Og U T F).

  Let s := to_LState_t m Og U T F.

  Lemma tr_cell_heap : forall k v, C !! k = Some v -> hp m k.1 k.2 = Some v.
  Proof. intros k v Hk. rewrite HR. exact (ag_cell _ _ _ _ _ _ _ _ _ _ Hag k v Hk). Qed.

  Lemma tr_stk x o : Sm !! (x, t) = Some o -> stk (ms s) x t = Some o.
  Proof.
    intros Hk. simpl. rewrite HRS.
    exact (ag_stk _ _ _ _ _ _ _ _ _ _ Hag (x, t) o Hk).
  Qed.

  Lemma tr_obs o sg ob : Ob !! o = Some sg -> ob ∈ sg -> obsv s o ob.
  Proof.
    intros Hk Hin. exists t, sg.
    split; [exact (ag_obs _ _ _ _ _ _ _ _ _ _ Hag o sg Hk) | exact Hin].
  Qed.

  Lemma tr_itr x rho N :
    ItrOK root t U Sm Ob C x rho N -> D_rcuItr s t x rho N.
  Proof.
    intros (o & sg & Hstk & Hob & Hit & Hundf & Hfld & Hpath & Hpre).
    assert (Hit' : obsv s o (Oiter t)) by exact (tr_obs o sg _ Hob Hit).
    exists o. repeat apply conj.
    - exact (tr_stk x o Hstk).
    - exact Hit'.
    - simpl. exact Hundf.
    - intros f v Hc. specialize (Hfld f v Hc). destruct v as [y | ].
      + destruct Hfld as (oy & sgy & Hsy & Hcy & Hoy & Hity).
        exists oy. repeat apply conj.
        * exact (tr_stk y oy Hsy).
        * exact (tr_cell_heap (o, f) (VLoc oy) Hcy).
        * exact (tr_obs oy sgy _ Hoy Hity).
        * destruct Hwf as (_ & _ & _ & _ & _ & _ & HWU & _).
          exact (iter_no_flist _ t oy HFLD HWU
                   (ag_lk _ _ _ _ _ _ _ _ _ _ Hag) (tr_obs oy sgy _ Hoy Hity)).
      + exact (tr_cell_heap (o, f) VNull Hfld).
    - intros rho1 rho2 Happ.
      destruct (Hpre rho1 rho2 Happ) as (o' & sg' & Hp' & Hob' & Hit'').
      exists o'. split.
      + simpl. rewrite Hrt.
        exact (hstarC_hstar C (hp m) root rho1 o' tr_cell_heap Hp').
      + exact (tr_obs o' sg' _ Hob' Hit'').
    - simpl. rewrite Hrt.
      exact (hstarC_hstar C (hp m) root rho o tr_cell_heap Hpath).
    - exact (ag_lk _ _ _ _ _ _ _ _ _ _ Hag).
    - destruct Hwf as (_ & _ & _ & _ & _ & _ & HWU & _).
      exact (iter_no_flist _ t o HFLD HWU
               (ag_lk _ _ _ _ _ _ _ _ _ _ Hag) Hit').
  Qed.

  Lemma tr_fresh x N :
    HeapShape fs (hp m) ->
    (forall g, FType g = RCUField -> In g fs) ->
    FreshOK t U fs Sm Ob C x N -> D_rcuFresh FType s t x N.
  Proof.
    intros HS Hrcu (o & sg & Hstk & Hob & Hfr & Hundf & Hfld & Hnull).
    assert (Hfr' : obsv s o (Ofresh t)) by exact (tr_obs o sg _ Hob Hfr).
    exists o. repeat apply conj.
    - exact (tr_stk x o Hstk).
    - exact Hfr'.
    - simpl. exact Hundf.
    - destruct (flist s o) as [Tr|] eqn:E; [| reflexivity].
      exfalso. destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HFNR & _).
      destruct (HFLD o Tr E) as [t0 [Hu | Hd]];
        destruct (HFNR o t t0 Hfr') as (_ & Hnu & Hnf);
        [exact (Hnu Hu) | exact (Hnf Hd)].
    - intros f v Hc. specialize (Hfld f v Hc). destruct v as [y | ].
      + destruct Hfld as (oy & sgy & Hsy & Hcy & Hoy & Hity).
        exists oy. repeat apply conj.
        * exact (tr_stk y oy Hsy).
        * exact (tr_cell_heap (o, f) (VLoc oy) Hcy).
        * exact (tr_obs oy sgy _ Hoy Hity).
        * destruct Hwf as (_ & _ & _ & _ & _ & _ & HWU & _).
          exact (iter_no_flist _ t oy HFLD HWU
                   (ag_lk _ _ _ _ _ _ _ _ _ _ Hag) (tr_obs oy sgy _ Hoy Hity)).
      + exact (tr_cell_heap (o, f) VNull Hfld).
    - intros g Hg HNg.
      exact (tr_cell_heap (o, g) VNull (Hnull g (Hrcu g Hg) HNg)).
  Qed.

  Lemma tr_unlinked x :
    DetOK t U (Ounlk t) Sm Ob x -> D_unlinked s t x.
  Proof.
    intros (o & sg & Hstk & Hob & Hin & Hundf). exists o. repeat apply conj.
    - exact (tr_stk x o Hstk).
    - exact (tr_obs o sg _ Hob Hin).
    - exact (ag_lk _ _ _ _ _ _ _ _ _ _ Hag).
    - simpl. exact Hundf.
  Qed.

  Lemma tr_freeable x :
    DetOK t U (Ofree t) Sm Ob x ->
    (forall o, Sm !! (x, t) = Some o -> exists e, Fl !! o = Some e /\ Qc e) ->
    D_freeable s t x.
  Proof.
    intros (o & sg & Hstk & Hob & Hin & Hundf) Hfle. exists o.
    destruct (Hfle o Hstk) as [e [Hfl Hq]].
    repeat apply conj.
    - exact (tr_stk x o Hstk).
    - exact (tr_obs o sg _ Hob Hin).
    - exact (ag_lk _ _ _ _ _ _ _ _ _ _ Hag).
    - simpl. exact Hundf.
    - simpl.
      rewrite (HQ o e (ag_fl _ _ _ _ _ _ _ _ _ _ Hag o e Hfl) Hq).
      exists (fun t' => t' ∈ (∅ : gset TID)). split; [reflexivity |].
      intros t'. by apply not_elem_of_empty.
  Qed.

  Lemma tr_root x :
    RootOK root t Sm Ob x -> D_rcuRoot s t x.
  Proof.
    intros (sg & Hstk & Hob & Hin). split.
    - simpl. rewrite Hrt. exact (tr_stk x root Hstk).
    - simpl in *. rewrite Hrt. exact (tr_obs root sg Oroot Hob Hin).
  Qed.

End transfer_pure.

(** ** The environment

    [TyOK] is the type read as a condition on the thread's maps.  [TUndef] is
    the one entry with no reading: its denotation says the variable is out of
    scope *and* that whatever the stack still maps it to has no free-list entry
    -- a fact about a node the thread no longer references, and so about state
    it does not own.  That is a defect of the same family as the others: the
    second conjunct belongs in an invariant, not in a type. *)

Definition TyOK (root : Loc) (t : TID) (U : Var -> TID -> Prop)
    (Qc : nat -> Prop)
    (FType : FName -> FieldKind) (fs : list FName)
    (Sm : gmap (Var * TID) Loc) (Ob : gmap Loc (gset obs))
    (C : gmap (Loc * FName) Val) (Fl : gmap Loc nat)
    (x : Var) (ty : Ty) : Prop :=
  match ty with
  | TItr rho N => ItrOK root t U Sm Ob C x rho N
  | TFresh N   => FreshOK t U fs Sm Ob C x N
  | TUnlinked  => DetOK t U (Ounlk t) Sm Ob x
  | TFreeable  => DetOK t U (Ofree t) Sm Ob x
                  /\ (forall o, Sm !! (x, t) = Some o ->
                        exists e, Fl !! o = Some e /\ Qc e)
  | TRoot      => RootOK root t Sm Ob x
  | TUndef     => False
  end.

Definition tyN (ty : Ty) : FieldMap :=
  match ty with
  | TItr _ N => N
  | TFresh N => N
  | _        => fun _ => None
  end.

Definition EnvOK (root : Loc) (t : TID) (U : Var -> TID -> Prop)
    (Qc : nat -> Prop)
    (FType : FName -> FieldKind) (fs : list FName)
    (Sm : gmap (Var * TID) Loc) (Ob : gmap Loc (gset obs))
    (C : gmap (Loc * FName) Val) (Fl : gmap Loc nat)
    (G : Env) : Prop :=
  forall x ty, In (x, ty) G -> TyOK root t U Qc FType fs Sm Ob C Fl x ty.

Section transfer.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ}.
  Context (FType : FName -> FieldKind).

  (** What the writer holds implies what its type environment says.  This is the
      statement the eight triples were missing: their preconditions are
      resources, and this is the reading under which those resources *are* the
      typing judgement's environment. *)
  Lemma writer_env γo γs γh γl γf root t fs U Qc Sm Ob C Fl G
        m Og T F St H S :
    WellFormed FType (to_LState_t m Og U T F) ->
    FLD (to_LState_t m Og U T F) ->
    Represents (hp m) H ->
    RepresentsS (stk m) S ->
    HeapShape fs (hp m) ->
    rt m = root ->
    (forall g, FType g = RCUField -> In g fs) ->
    (forall o e, St !! o = Some e -> Qc e -> F !! o = Some ∅) ->
    EnvOK root t U Qc FType fs Sm Ob C Fl G ->
    hp_auth γh H -∗ stk_auth γs S -∗ tobs_auth γo Og -∗ lk_auth γl (lk m) -∗
    fl_auth γf St -∗
    writer γo γs γh γl γf t Sm Ob C Fl -∗
    ⌜D_env FType (to_LState_t m Og U T F) t G⌝.
  Proof.
    iIntros (Hwf HFLD HR HRS HS Hrt Hrcu HQ Hok)
            "Hh Hs Ho Hl Hfa (Hlkt & Hsm & Hob & Hc & Hfl)".
    iDestruct (lk_agree with "Hl Hlkt") as %Hlkm.
    iDestruct (cells_agree with "Hh Hc") as %Hcsub.
    iDestruct (stk_own_agree with "Hs Hsm") as %Hssub.
    iDestruct (obs_own_agree with "Ho Hob") as %Hosub.
    iDestruct (fl_own_agree with "Hfa Hfl") as %Hflsub.
    iPureIntro.
    assert (Hag : Agrees t S Og H St (lk m) Sm Ob C Fl)
      by (constructor; assumption).
    intros x ty Hin. destruct ty; simpl.
    - eapply tr_itr; eauto. exact (Hok x _ Hin).
    - eapply tr_fresh; eauto. exact (Hok x _ Hin).
    - eapply tr_unlinked; eauto. exact (Hok x _ Hin).
    - destruct (Hok x _ Hin) as [Hdet Hfle]. eapply tr_freeable; eauto.
    - destruct (Hok x _ Hin).
    - eapply tr_root; eauto. exact (Hok x _ Hin).
  Qed.

  (** ** The reader's environment, and why it needs no fractions

      We said in an earlier draft that the reader's read could not be stated
      because the points-to assertion is exclusive.  That is wrong, and the
      shape of this lemma is why.  A reader's iterator is not a claim about the
      heap: [D_rcuItrR] is a stack binding, an \itr{} observation of the
      reader's own, and the bounding conjunct.  No path, no cell.  So the
      reader's environment follows from fragments of the stack and the
      observation map and nothing else -- there is no heap authority in the
      statement below, and none in [reader_acquire_update] either.

      What the reader's *read* does with the heap is read the authority inside
      the invariant to find the successor, and carry nothing out.  That needs no
      fragment, so it needs no fraction.  What the read does need is IFL's
      obligation, that a reader acquiring a reference to a node already on the
      free list is one of the threads its grace period waits for; that is a real
      obligation and it is not this one.

      The bounding conjunct is a hypothesis here for the reason recorded with
      [reader_post_env]: the reader's own rule does not establish it. *)
  Lemma reader_env γo γs t Sm Ob G m Og U T F S :
    RepresentsS (stk m) S ->
    (forall x, In x G -> exists o sg, Sm !! (x, t) = Some o
       /\ Ob !! o = Some sg /\ Oiter t ∈ sg /\ ~ U x t) ->
    (forall x o, In x G -> Sm !! (x, t) = Some o -> bnd m t ->
       exists Tr, flist (to_LState_t m Og U T F) o = Some Tr /\ Tr t
               /\ (forall t', Tr t' -> bnd m t')) ->
    stk_auth γs S -∗ tobs_auth γo Og -∗
    stk_own γs Sm -∗ obs_own γo t Ob -∗
    ⌜forall x, In x G -> D_rcuItrR (to_LState_t m Og U T F) t x⌝.
  Proof.
    iIntros (HRS Hitr Hbnd) "Hsa Hoa Hsm Hob".
    iDestruct (stk_own_agree with "Hsa Hsm") as %Hssub.
    iDestruct (obs_own_agree with "Hoa Hob") as %Hosub.
    iPureIntro. intros x Hin.
    destruct (Hitr x Hin) as (o & sg & Hstk & Hobk & Hit & Hundf).
    exists o. repeat apply conj.
    - simpl. rewrite HRS. exact (Hssub (x, t) o Hstk).
    - exists t, sg. split; [exact (Hosub o sg Hobk) | exact Hit].
    - simpl. exact Hundf.
    - intros Hb. exact (Hbnd x o Hin Hstk Hb).
  Qed.

End transfer.

Print Assumptions writer_env.
Print Assumptions reader_env.

(** ** The environment across a step

    [writer_env] reads a *state*.  To use it on both sides of a triple the
    reading has to survive the step, and for allocation that is a monotonicity
    property: the maps grow at a location nothing else mentions, and every
    entry already in the environment is untouched.

    The path case is the only one with content.  A path is a fold of lookups in
    the cell map, and extending the map at a node no value points at cannot
    change any fold that does not start there -- which is the allocator's
    "nothing points at the new node", used a second time. *)

Lemma hstarC_stable (C C' : gmap (Loc * FName) Val) n o p q :
  (forall k, k.1 <> n -> C' !! k = C !! k) ->
  (forall k v, C !! k = Some v -> v <> VLoc n) ->
  o <> n ->
  hstarC C o p = Some q -> hstarC C' o p = Some q.
Proof.
  intros Hsame Hno. revert o.
  induction p as [|f p IH]; intros o Hon Hp; simpl in *.
  - exact Hp.
  - rewrite (Hsame (o, f)); [| exact Hon].
    destruct (C !! (o, f)) as [[o1|]|] eqn:E; try discriminate.
    assert (Ho1 : o1 <> n)
      by (intros ->; exact (Hno (o, f) (VLoc n) E eq_refl)).
    exact (IH o1 Ho1 Hp).
Qed.

Lemma EnvOK_alloc root t U U2 Qc FType fs Sm Sm' Ob Ob' C C' Fl G x n :
  (* the scope condition may only shrink: a variable that was in scope stays so *)
  (forall y t', ~ U y t' -> ~ U2 y t') ->
  (* the new location is mentioned nowhere the environment can see *)
  (forall k o, Sm !! k = Some o -> o <> n) ->
  Ob !! n = None ->
  (forall k v, C !! k = Some v -> v <> VLoc n) ->
  n <> root ->
  (* and the maps grow only there *)
  (forall k, k <> (x, t) -> Sm' !! k = Sm !! k) ->
  (forall o, o <> n -> Ob' !! o = Ob !! o) ->
  (forall k, k.1 <> n -> C' !! k = C !! k) ->
  (* no field map in the environment names the variable being rebound *)
  (forall y ty f, In (y, ty) G -> tyN ty f <> Some (FVar x)) ->
  EnvOK root t U Qc FType fs Sm Ob C Fl G ->
  EnvOK root t U2 Qc FType fs Sm' Ob' C' Fl
    (List.filter (fun p => negb (Nat.eqb (fst p) x)) G).
Proof.
  intros HU2 HSn HOn HCn Hrn0 HS HO HC HNx Hok y ty Hin.
  assert (Hrn : root <> n) by (intros Hc; apply Hrn0; by rewrite Hc).
  apply List.filter_In in Hin. destruct Hin as [Hin Hne].
  assert (Hyx : y <> x).
  { intros ->. simpl in Hne. by rewrite Nat.eqb_refl in Hne. }
  assert (Hsm : Sm' !! (y, t) = Sm !! (y, t)).
  { apply HS. intros Hc. injection Hc as Hc. by apply Hyx. }
  pose proof (Hok y ty Hin) as Hty.
  destruct ty; simpl in Hty |- *.
  - destruct Hty as (o & sg & Hstk & Hob & Hit & Hundf & Hfld & Hpath & Hpre).
    exists o, sg.
    assert (Hon : o <> n) by exact (HSn (y, t) o Hstk).
    repeat apply conj.
    + by rewrite Hsm.
    + by rewrite (HO o Hon).
    + exact Hit.
    + exact (HU2 y t Hundf).
    + intros f v Hv. specialize (Hfld f v Hv). destruct v as [z | ].
      * destruct Hfld as (oy & sgy & Hsy & Hcy & Hoy & Hity).
        assert (Hzx : z <> x)
          by (intros ->; exact (HNx y (TItr rho N) f Hin Hv)).
        assert (Hoyn : oy <> n) by exact (HSn (z, t) oy Hsy).
        exists oy, sgy. repeat apply conj.
        -- rewrite HS; [exact Hsy | intros Hc; injection Hc as Hc; by apply Hzx].
        -- rewrite (HC (o, f)); [exact Hcy | exact Hon].
        -- by rewrite (HO oy Hoyn).
        -- exact Hity.
      * rewrite (HC (o, f)); [exact Hfld | exact Hon].
    + exact (hstarC_stable C C' n root rho o HC HCn Hrn Hpath).
    + intros rho1 rho2 Happ. destruct (Hpre rho1 rho2 Happ)
        as (o' & sg' & Hp' & Hob' & Hit').
      exists o', sg'. repeat apply conj.
      * exact (hstarC_stable C C' n root rho1 o' HC HCn Hrn Hp').
      * rewrite (HO o'); [exact Hob' |].
        intros ->. by rewrite HOn in Hob'.
      * exact Hit'.
  - destruct Hty as (o & sg & Hstk & Hob & Hfr & Hundf & Hfld & Hnull).
    exists o, sg.
    assert (Hon : o <> n) by exact (HSn (y, t) o Hstk).
    repeat apply conj.
    + by rewrite Hsm.
    + by rewrite (HO o Hon).
    + exact Hfr.
    + exact (HU2 y t Hundf).
    + intros f v Hv. specialize (Hfld f v Hv). destruct v as [z | ].
      * destruct Hfld as (oy & sgy & Hsy & Hcy & Hoy & Hity).
        assert (Hzx : z <> x)
          by (intros ->; exact (HNx y (TFresh N) f Hin Hv)).
        assert (Hoyn : oy <> n) by exact (HSn (z, t) oy Hsy).
        exists oy, sgy. repeat apply conj.
        -- rewrite HS; [exact Hsy | intros Hc; injection Hc as Hc; by apply Hzx].
        -- rewrite (HC (o, f)); [exact Hcy | exact Hon].
        -- by rewrite (HO oy Hoyn).
        -- exact Hity.
      * rewrite (HC (o, f)); [exact Hfld | exact Hon].
    + intros g Hg HNg.
      rewrite (HC (o, g)); [exact (Hnull g Hg HNg) | exact Hon].
  - destruct Hty as (o & sg & Hstk & Hob & Hin' & Hundf).
    exists o, sg. assert (Hon : o <> n) by exact (HSn (y, t) o Hstk).
    repeat apply conj; [by rewrite Hsm | by rewrite (HO o Hon)
                       | exact Hin' | exact (HU2 y t Hundf)].
  - destruct Hty as [(o & sg & Hstk & Hob & Hin' & Hundf) Hfle].
    assert (Hon : o <> n) by exact (HSn (y, t) o Hstk).
    split.
    + exists o, sg. repeat apply conj; [by rewrite Hsm | by rewrite (HO o Hon)
                                       | exact Hin' | exact (HU2 y t Hundf)].
    + intros o' Hstk'. rewrite Hsm in Hstk'. exact (Hfle o' Hstk').
  - exact Hty.
  - destruct Hty as (sg & Hstk & Hob & Hin').
    exists sg. repeat apply conj.
    + by rewrite Hsm.
    + rewrite (HO root); [exact Hob |]. intros ->. by apply Hrn.
    + exact Hin'.
Qed.

Print Assumptions EnvOK_alloc.

(** ** Framing: what a step must not touch

    The seven other closed triples do not grow the maps at a new location; they
    overwrite an entry.  So what they need is not monotonicity but *framing*:
    the environment survives a step whose footprint it does not read.  There are
    only three kinds of footprint -- a cell, a location's observations, a stack
    slot -- so there are three lemmas, not seven.

    The cell case is the one with content, and it is where the type rules'
    aliasing side conditions land.  A path is a fold of lookups, so the cells it
    reads are a concrete list; a write outside that list cannot change the fold.
    [MayAlias] is the checker's decision procedure for exactly this question. *)

Fixpoint pathcells (C : gmap (Loc * FName) Val) (o : Loc) (p : list FName)
  : list (Loc * FName) :=
  match p with
  | []      => []
  | f :: p' => match C !! (o, f) with
               | Some (VLoc o') => (o, f) :: pathcells C o' p'
               | _              => [(o, f)]
               end
  end.

Lemma hstarC_stable_cell C k v o p q :
  ~ In k (pathcells C o p) ->
  hstarC C o p = Some q -> hstarC (<[k := v]> C) o p = Some q.
Proof.
  revert o. induction p as [|f p IH]; intros o Hni Hp; simpl in *.
  - exact Hp.
  - destruct (C !! (o, f)) as [[o1|]|] eqn:E; try discriminate.
    assert (Hne : k <> (o, f)) by (intros ->; apply Hni; by left).
    rewrite lookup_insert_ne; [| intros Hc; by apply Hne].
    rewrite E. apply IH; [| exact Hp].
    intros Hc. apply Hni. by right.
Qed.

Lemma pathcells_prefix C o p1 p2 k :
  In k (pathcells C o p1) -> In k (pathcells C o (p1 ++ p2)).
Proof.
  revert o. induction p1 as [|f p1 IH]; intros o Hin; simpl in *; [destruct Hin |].
  destruct (C !! (o, f)) as [[o1|]|] eqn:E.
  - destruct Hin as [-> | Hin]; [by left | right; exact (IH o1 Hin)].
  - exact Hin.
  - exact Hin.
Qed.

(** The environment's footprint: the cells its paths read, and the locations its
    variables and path prefixes observe. *)

Definition ReadsCell (root : Loc) (C : gmap (Loc * FName) Val)
    (Sm : gmap (Var * TID) Loc) (t : TID) (G : Env) (k : Loc * FName) : Prop :=
  (forall x rho N, In (x, TItr rho N) G -> ~ In k (pathcells C root rho))
  /\ (forall x N o, In (x, TFresh N) G -> Sm !! (x, t) = Some o -> k.1 <> o)
  (* nor is it a tracked field of anything the environment names *)
  /\ (forall x ty o, In (x, ty) G -> Sm !! (x, t) = Some o ->
        k.1 = o -> tyN ty k.2 = None).

Definition ReadsObs (root : Loc) (C : gmap (Loc * FName) Val)
    (Sm : gmap (Var * TID) Loc) (t : TID) (G : Env) (o : Loc) : Prop :=
  (forall x ty, In (x, ty) G -> Sm !! (x, t) <> Some o)
  /\ (forall x rho N rho1 rho2, In (x, TItr rho N) G -> rho1 ++ rho2 = rho ->
        hstarC C root rho1 <> Some o)
  /\ (forall x, In (x, TRoot) G -> o <> root)
  (* nor is it the target of a tracked field *)
  /\ (forall x ty f z, In (x, ty) G -> tyN ty f = Some (FVar z) ->
        Sm !! (z, t) <> Some o).

Lemma EnvOK_cell root t U Qc FType fs Sm Ob C Fl G k v :
  ReadsCell root C Sm t G k ->
  EnvOK root t U Qc FType fs Sm Ob C Fl G ->
  EnvOK root t U Qc FType fs Sm Ob (<[k := v]> C) Fl G.
Proof.
  intros (HP & HF & HN) Hok y ty Hin. pose proof (Hok y ty Hin) as Hty.
  (* a tracked field of this variable is never the written cell *)
  assert (Hfld : forall o f, Sm !! (y, t) = Some o -> tyN ty f <> None ->
            k <> (o, f)).
  { intros o f Hstk Hsome ->. by apply Hsome, (HN y ty o Hin Hstk). }
  destruct ty; simpl in Hty |- *; simpl in Hfld.
  - destruct Hty as (o & sg & Hstk & Hob & Hit & Hundf & Hf & Hpath & Hpre).
    exists o, sg. repeat apply conj;
      [exact Hstk | exact Hob | exact Hit | exact Hundf | | |].
    + intros f w Hw. specialize (Hf f w Hw).
      assert (Hkne : k <> (o, f))
        by (apply (Hfld o f Hstk); by rewrite Hw).
      destruct w as [z | ].
      * destruct Hf as (oy & sgy & Hsy & Hcy & Hoy & Hity).
        exists oy, sgy. repeat apply conj;
          [exact Hsy | | exact Hoy | exact Hity].
        rewrite lookup_insert_ne; [exact Hcy | intros Hc; by apply Hkne].
      * rewrite lookup_insert_ne; [exact Hf | intros Hc; by apply Hkne].
    + exact (hstarC_stable_cell C k v root rho o (HP y rho N Hin) Hpath).
    + intros rho1 rho2 Happ. destruct (Hpre rho1 rho2 Happ)
        as (o' & sg' & Hp' & Hob' & Hit').
      exists o', sg'. repeat apply conj; [| exact Hob' | exact Hit'].
      apply hstarC_stable_cell; [| exact Hp'].
      intros Hc. apply (HP y rho N Hin). rewrite -Happ.
      exact (pathcells_prefix C root rho1 rho2 k Hc).
  - destruct Hty as (o & sg & Hstk & Hob & Hfr & Hundf & Hf & Hnull).
    exists o, sg. repeat apply conj;
      [exact Hstk | exact Hob | exact Hfr | exact Hundf | |].
    + intros f w Hw. specialize (Hf f w Hw).
      assert (Hkne : k <> (o, f))
        by (apply (Hfld o f Hstk); by rewrite Hw).
      destruct w as [z | ].
      * destruct Hf as (oy & sgy & Hsy & Hcy & Hoy & Hity).
        exists oy, sgy. repeat apply conj;
          [exact Hsy | | exact Hoy | exact Hity].
        rewrite lookup_insert_ne; [exact Hcy | intros Hc; by apply Hkne].
      * rewrite lookup_insert_ne; [exact Hf | intros Hc; by apply Hkne].
    + intros g Hg HNg. rewrite lookup_insert_ne; [exact (Hnull g Hg HNg) |].
      intros Hc. apply (HF y N o Hin Hstk). by rewrite Hc.
  - exact Hty.
  - exact Hty.
  - exact Hty.
  - exact Hty.
Qed.

Lemma EnvOK_obs root t U Qc FType fs Sm Ob C Fl G o sg' :
  ReadsObs root C Sm t G o ->
  EnvOK root t U Qc FType fs Sm Ob C Fl G ->
  EnvOK root t U Qc FType fs Sm (<[o := sg']> Ob) C Fl G.
Proof.
  intros (HV & HP & HR & HT) Hok y ty Hin. pose proof (Hok y ty Hin) as Hty.
  assert (Hne : forall o0, Sm !! (y, t) = Some o0 -> o <> o0).
  { intros o0 Hstk Hc. apply (HV y ty Hin). by rewrite Hc. }
  assert (Hfne : forall f z oy, tyN ty f = Some (FVar z) ->
            Sm !! (z, t) = Some oy -> o <> oy).
  { intros f z oy Hf Hsy Hc. apply (HT y ty f z Hin Hf). by rewrite Hc. }
  destruct ty; simpl in Hty |- *; simpl in Hfne.
  - destruct Hty as (o0 & sg & Hstk & Hob & Hit & Hundf & Hf & Hpath & Hpre).
    exists o0, sg. repeat apply conj;
      [exact Hstk | | exact Hit | exact Hundf | | exact Hpath |].
    + rewrite lookup_insert_ne; [exact Hob | exact (Hne o0 Hstk)].
    + intros f w Hw. specialize (Hf f w Hw). destruct w as [z | ].
      * destruct Hf as (oy & sgy & Hsy & Hcy & Hoy & Hity).
        exists oy, sgy. repeat apply conj;
          [exact Hsy | exact Hcy | | exact Hity].
        rewrite lookup_insert_ne; [exact Hoy | exact (Hfne f z oy Hw Hsy)].
      * exact Hf.
    + intros rho1 rho2 Happ. destruct (Hpre rho1 rho2 Happ)
        as (o' & sg2 & Hp' & Hob' & Hit').
      exists o', sg2. repeat apply conj; [exact Hp' | | exact Hit'].
      rewrite lookup_insert_ne; [exact Hob' |].
      intros ->. exact (HP y rho N rho1 rho2 Hin Happ Hp').
  - destruct Hty as (o0 & sg & Hstk & Hob & Hfr & Hundf & Hf & Hnull).
    exists o0, sg. repeat apply conj;
      [exact Hstk | | exact Hfr | exact Hundf | | exact Hnull].
    + rewrite lookup_insert_ne; [exact Hob | exact (Hne o0 Hstk)].
    + intros f w Hw. specialize (Hf f w Hw). destruct w as [z | ].
      * destruct Hf as (oy & sgy & Hsy & Hcy & Hoy & Hity).
        exists oy, sgy. repeat apply conj;
          [exact Hsy | exact Hcy | | exact Hity].
        rewrite lookup_insert_ne; [exact Hoy | exact (Hfne f z oy Hw Hsy)].
      * exact Hf.
  - destruct Hty as (o0 & sg & Hstk & Hob & Hin' & Hundf).
    exists o0, sg. repeat apply conj; [exact Hstk | | exact Hin' | exact Hundf].
    rewrite lookup_insert_ne; [exact Hob | exact (Hne o0 Hstk)].
  - destruct Hty as [(o0 & sg & Hstk & Hob & Hin' & Hundf) Hfle]. split.
    + exists o0, sg. repeat apply conj;
        [exact Hstk | | exact Hin' | exact Hundf].
      rewrite lookup_insert_ne; [exact Hob | exact (Hne o0 Hstk)].
    + exact Hfle.
  - exact Hty.
  - destruct Hty as (sg & Hstk & Hob & Hin').
    exists sg. repeat apply conj; [exact Hstk | | exact Hin'].
    rewrite lookup_insert_ne; [exact Hob |].
    intros ->. exact (HR y Hin eq_refl).
Qed.

Lemma EnvOK_stack root t U Qc FType fs Sm Ob C Fl G k o :
  (forall x ty, In (x, ty) G -> k <> (x, t)) ->
  (* nor is the rebound variable the target of a tracked field *)
  (forall x ty f z, In (x, ty) G -> tyN ty f = Some (FVar z) -> k <> (z, t)) ->
  EnvOK root t U Qc FType fs Sm Ob C Fl G ->
  EnvOK root t U Qc FType fs (<[k := o]> Sm) Ob C Fl G.
Proof.
  intros HK HT Hok y ty Hin. pose proof (Hok y ty Hin) as Hty.
  assert (Hne : <[k := o]> Sm !! (y, t) = Sm !! (y, t))
    by (rewrite lookup_insert_ne; [reflexivity | exact (HK y ty Hin)]).
  assert (Hfne : forall f z, tyN ty f = Some (FVar z) ->
            <[k := o]> Sm !! (z, t) = Sm !! (z, t))
    by (intros f z Hf; rewrite lookup_insert_ne;
        [reflexivity | exact (HT y ty f z Hin Hf)]).
  destruct ty; simpl in Hty |- *; simpl in Hfne.
  - destruct Hty as (o0 & sg & Hstk & Hob & Hit & Hundf & Hf & Hrest).
    exists o0, sg. rewrite Hne. repeat apply conj;
      [exact Hstk | exact Hob | exact Hit | exact Hundf | | exact (proj1 Hrest)
       | exact (proj2 Hrest)].
    intros f w Hw. specialize (Hf f w Hw). destruct w as [z | ]; [| exact Hf].
    destruct Hf as (oy & sgy & Hsy & Hrestf). exists oy, sgy.
    rewrite (Hfne f z Hw). by split.
  - destruct Hty as (o0 & sg & Hstk & Hob & Hfr & Hundf & Hf & Hnull).
    exists o0, sg. rewrite Hne. repeat apply conj;
      [exact Hstk | exact Hob | exact Hfr | exact Hundf | | exact Hnull].
    intros f w Hw. specialize (Hf f w Hw). destruct w as [z | ]; [| exact Hf].
    destruct Hf as (oy & sgy & Hsy & Hrestf). exists oy, sgy.
    rewrite (Hfne f z Hw). by split.
  - destruct Hty as (o0 & sg & Hstk & Hrest). exists o0, sg. by rewrite Hne.
  - destruct Hty as [(o0 & sg & Hstk & Hrest) Hfle]. split.
    + exists o0, sg. by rewrite Hne.
    + intros o' Hstk'. rewrite Hne in Hstk'. exact (Hfle o' Hstk').
  - exact Hty.
  - destruct Hty as (sg & Hstk & Hrest). exists sg. by rewrite Hne.
Qed.

(** ** The touched variable

    With the three framing lemmas and field maps in the reading, a rule's effect
    on the environment splits in two: the variables it does not touch are framed,
    and the one it does gets its new type.  The second half is not a lemma -- it
    is the definition, supplied.  These are the three that occur, written out so
    the claim is checkable rather than asserted.

    \textsc{T-UnlinkH} demotes the victim to [unlinked]. *)
Lemma TyOK_demoted root t U Qc FType fs Sm Ob C Fl x oz :
  Sm !! (x, t) = Some oz -> ~ U x t ->
  TyOK root t U Qc FType fs Sm (<[oz := {[Ounlk t]}]> Ob) C Fl x TUnlinked.
Proof.
  intros Hstk Hundf. exists oz, {[Ounlk t]}. repeat apply conj;
    [exact Hstk | by rewrite lookup_insert_eq | by apply elem_of_singleton
     | exact Hundf].
Qed.

(** \textsc{SyncStop} turns it into [freeable], which also needs the free-list
    entry the thread now holds. *)
Lemma TyOK_freeable root t U Qc FType fs Sm Ob C Fl x od e :
  Sm !! (x, t) = Some od -> ~ U x t -> Fl !! od = Some e -> Qc e ->
  TyOK root t U Qc FType fs Sm (<[od := {[Ofree t]}]> Ob) C Fl x TFreeable.
Proof.
  intros Hstk Hundf Hfl Hq. split.
  - exists od, {[Ofree t]}. repeat apply conj;
      [exact Hstk | by rewrite lookup_insert_eq | by apply elem_of_singleton
       | exact Hundf].
  - intros o' Hstk'. rewrite Hstk in Hstk'. injection Hstk' as <-.
    by exists e.
Qed.

(** \textsc{T-LinkF-Null} and \textsc{T-Insert} promote a fresh node to an
    iterator one field beyond its parent.  This is the only one with content,
    and the content is that the new path is the old one extended: the fold
    reaches the parent and then takes the cell the rule just wrote. *)
Lemma hstarC_snoc C root rho op f on :
  hstarC C root rho = Some op -> C !! (op, f) = Some (VLoc on) ->
  hstarC C root (rho ++ [f]) = Some on.
Proof.
  revert root. induction rho as [|g rho IH]; intros r Hp Hc; simpl in *.
  - injection Hp as <-. by rewrite Hc.
  - destruct (C !! (r, g)) as [[o1|]|] eqn:E; try discriminate.
    exact (IH o1 Hp Hc).
Qed.

Lemma TyOK_promoted root t U Qc FType fs Sm Ob C Fl x on op f rho sg N :
  Sm !! (x, t) = Some on -> ~ U x t ->
  Ob !! on = Some sg -> Oiter t ∈ sg ->
  FieldOK t Sm Ob C on N ->
  hstarC C root rho = Some op -> C !! (op, f) = Some (VLoc on) ->
  (forall rho1 rho2, rho1 ++ rho2 = rho ++ [f] ->
     exists o' sg', hstarC C root rho1 = Some o'
                 /\ Ob !! o' = Some sg' /\ Oiter t ∈ sg') ->
  TyOK root t U Qc FType fs Sm Ob C Fl x (TItr (rho ++ [f]) N).
Proof.
  intros Hstk Hundf Hob Hit Hfld Hpath Hcell Hpre.
  exists on, sg. repeat apply conj;
    [exact Hstk | exact Hob | exact Hit | exact Hundf | exact Hfld
     | exact (hstarC_snoc C root rho op f on Hpath Hcell) | exact Hpre].
Qed.

(** A prefix of a path extended by one field is either a prefix of the path or
    the whole of it.  This is what lets the promoted node inherit its parent's
    chain of iterator observations. *)
Lemma app_snoc_split {A : Type} (p1 : list A) : forall p2 rho f,
  p1 ++ p2 = rho ++ [f] -> (exists p2', p1 ++ p2' = rho) \/ p1 = rho ++ [f].
Proof.
  induction p1 as [|a p1 IH]; intros p2 rho f Happ.
  - left. by exists rho.
  - destruct rho as [|b rho]; simpl in Happ.
    + injection Happ as <- Hp. apply app_eq_nil in Hp as [-> ->].
      by right.
    + injection Happ as <- Hp.
      destruct (IH p2 rho f Hp) as [[p2' Hp'] | Hp'].
      * left. exists p2'. simpl. by rewrite Hp'.
      * right. simpl. by rewrite Hp'.
Qed.

Lemma hstarC_delete C k o p q :
  ~ In k (pathcells C o p) ->
  hstarC C o p = Some q -> hstarC (delete k C) o p = Some q.
Proof.
  revert o. induction p as [|f p IH]; intros o Hni Hp; simpl in *.
  - exact Hp.
  - destruct (C !! (o, f)) as [[o1|]|] eqn:E; try discriminate.
    assert (Hne : k <> (o, f)) by (intros ->; apply Hni; by left).
    rewrite lookup_delete_ne; [| intros Hc; by apply Hne].
    rewrite E. apply IH; [| exact Hp]. intros Hc. apply Hni. by right.
Qed.

(** The shape every rule's environment obligation has: the variables the step
    does not touch are framed, the ones it does are supplied.  Stating it once
    means each rule names its touched variables and discharges a [TyOK] for
    each, with no filtering. *)
Lemma EnvOK_step root t U Qc FType fs Sm Ob C Fl touched rest :
  EnvOK root t U Qc FType fs Sm Ob C Fl rest ->
  (forall x ty, In (x, ty) touched -> TyOK root t U Qc FType fs Sm Ob C Fl x ty) ->
  EnvOK root t U Qc FType fs Sm Ob C Fl (touched ++ rest).
Proof.
  intros Hrest Htouched x ty Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin];
    [exact (Htouched x ty Hin) | exact (Hrest x ty Hin)].
Qed.

(** Retargeting one field of a variable's map.  This is what happens to the
    *parent* in every mutation: its path and its observation are unchanged, and
    one entry of its field map now names a different variable.  The new entry is
    the cell the rule just wrote. *)
Lemma FieldOK_update t Sm Ob C o N f y oy sg :
  (forall g w, g <> f -> N g = Some w ->
     match w with
     | FVar z => exists oz sz, Sm !! (z, t) = Some oz
                            /\ C !! (o, g) = Some (VLoc oz)
                            /\ Ob !! oz = Some sz /\ Oiter t ∈ sz
     | FNull  => C !! (o, g) = Some VNull
     end) ->
  Sm !! (y, t) = Some oy -> C !! (o, f) = Some (VLoc oy) ->
  Ob !! oy = Some sg -> Oiter t ∈ sg ->
  FieldOK t Sm Ob C o (fun g => if decide (g = f) then Some (FVar y) else N g).
Proof.
  intros Hold Hsy Hcy Hoy Hity g w Hw.
  destruct (decide (g = f)) as [Heq | Hne].
  - subst g. destruct (decide (f = f)) as [_ | Hc];
      [| exfalso; by apply Hc].
    injection Hw as <-. by exists oy, sg.
  - destruct (decide (g = f)) as [Hc | _]; [exfalso; by apply Hne |].
    exact (Hold g w Hne Hw).
Qed.

(** An environment reading holds of any sub-environment.  Chaining rules needs
    this constantly: a rule's framing hypothesis is about the variables it does
    not touch, which is a sublist of what the previous rule handed back. *)
Lemma EnvOK_incl root t U Qc FType fs Sm Ob C Fl G G' :
  (forall x ty, In (x, ty) G' -> In (x, ty) G) ->
  EnvOK root t U Qc FType fs Sm Ob C Fl G ->
  EnvOK root t U Qc FType fs Sm Ob C Fl G'.
Proof. intros Hsub Hok x ty Hin. exact (Hok x ty (Hsub x ty Hin)). Qed.

Print Assumptions EnvOK_incl.

Print Assumptions EnvOK_step.
Print Assumptions FieldOK_update.

Print Assumptions app_snoc_split.

Print Assumptions TyOK_demoted.
Print Assumptions TyOK_promoted.

(** ** Framing across a replacement

    The three framing lemmas above cover a step whose footprint the environment
    does not read.  A replacement is not such a step, and [BST.v] shows the
    difference is real rather than an artefact: swapping a node for a mirror of
    itself re-routes every path that ran through it, so a variable below the
    replacement has the same path and a different intermediate node.

    What is true is that the paths are unchanged *as paths* and the nodes they
    pass through are swapped one for one.  [swapn] is that swap, and
    [hstarC_mirror] is the induction: a fold that reached [q] before reaches
    [swapn q] after, because at the one cell the rule rewrote the target moves
    from the old node to the new, and everywhere else the mirror makes the two
    indistinguishable. *)

Definition swapn (oo on q : Loc) : Loc := if decide (q = oo) then on else q.

Lemma swapn_ne oo on q : q <> oo -> swapn oo on q = q.
Proof. intros H. rewrite /swapn. by rewrite decide_False. Qed.

Lemma swapn_eq oo on : swapn oo on oo = on.
Proof. rewrite /swapn. by rewrite decide_True. Qed.

Lemma hstarC_mirror (C : gmap (Loc * FName) Val) op f oo on (fs' : list FName)
    a p q :
  C !! (op, f) = Some (VLoc oo) ->
  (forall g, In g fs' -> C !! (on, g) = C !! (oo, g)) ->
  (forall g, In g p -> In g fs') ->
  (* the replaced node has one predecessor, which is No-Sharing *)
  (forall b h, C !! (b, h) = Some (VLoc oo) -> (b, h) = (op, f)) ->
  on <> op -> op <> oo ->
  hstarC C a p = Some q ->
  hstarC (<[(op, f) := VLoc on]> C) (swapn oo on a) p = Some (swapn oo on q).
Proof.
  intros Hcell Hmir Hpfs Hsole Hop Hpo. revert a. revert Hpfs.
  induction p as [|g p IH]; intros Hp a Hstar; simpl in Hstar |- *.
  - injection Hstar as <-. reflexivity.
  - assert (Hgfs : In g fs') by (apply Hp; by left).
    assert (Hp' : forall h, In h p -> In h fs')
      by (intros h Hh; apply Hp; by right).
    destruct (decide (a = oo)) as [-> | Hane].
    + (* at the replaced node: the mirror makes the step the same one *)
      rewrite swapn_eq.
      assert (Hne : (op, f) <> (on, g))
        by (intros Hc; injection Hc as Hc1 _; by apply Hop).
      rewrite lookup_insert_ne; [| exact Hne].
      rewrite (Hmir g Hgfs).
      destruct (C !! (oo, g)) as [[o1|]|] eqn:E; try discriminate.
      assert (Ho1 : o1 <> oo).
      { intros ->. pose proof (Hsole oo g E) as Hc.
        injection Hc as Hc1 _. by apply Hpo. }
      pose proof (IH Hp' o1 Hstar) as Hres.
      rewrite (swapn_ne oo on o1 Ho1) in Hres. exact Hres.
    + rewrite (swapn_ne oo on a Hane).
      destruct (decide ((a, g) = (op, f))) as [Heq | Hne].
      * (* the cell the rule rewrote: the target moves to the new node *)
        injection Heq as -> ->. rewrite lookup_insert_eq.
        rewrite Hcell in Hstar.
        pose proof (IH Hp' oo Hstar) as Hres.
        rewrite swapn_eq in Hres. exact Hres.
      * rewrite lookup_insert_ne; [| intros Hc; by apply Hne].
        destruct (C !! (a, g)) as [[o1|]|] eqn:E; try discriminate.
        assert (Ho1 : o1 <> oo)
          by (intros ->; exact (Hne (Hsole a g E))).
        pose proof (IH Hp' o1 Hstar) as Hres.
        rewrite (swapn_ne oo on o1 Ho1) in Hres. exact Hres.
Qed.

Print Assumptions hstarC_mirror.

(** What framing across a replacement asks of the rest of the environment.  It
    is longer than the other two because a replacement does more: it rewrites a
    cell *and* changes two locations' observations, and the paths that ran
    through the old node now run through the new one. *)
Definition MirrorOK (root : Loc) (C : gmap (Loc * FName) Val)
    (Sm : gmap (Var * TID) Loc) (t : TID) (G : Env)
    (op : Loc) (f : FName) (oo on : Loc) (fs : list FName) : Prop :=
  (* no surviving variable is either of the two nodes, or names one *)
  (forall x ty, In (x, ty) G -> Sm !! (x, t) <> Some oo)
  /\ (forall x ty, In (x, ty) G -> Sm !! (x, t) <> Some on)
  /\ (forall x ty g z, In (x, ty) G -> tyN ty g = Some (FVar z) ->
        Sm !! (z, t) <> Some oo /\ Sm !! (z, t) <> Some on)
  (* the paths run on declared fields, and none of them reaches the new node,
     which is fresh *)
  /\ (forall x rho N, In (x, TItr rho N) G -> forall g, In g rho -> In g fs)
  /\ (forall x rho N rho1 rho2, In (x, TItr rho N) G -> rho1 ++ rho2 = rho ->
        hstarC C root rho1 <> Some on)
  (* nor is any of them the node whose field the rule rewrites *)
  /\ (forall x ty, In (x, ty) G -> Sm !! (x, t) <> Some op).

Lemma EnvOK_mirror root t U Qc FType fs Sm Ob C Fl G op f oo on :
  C !! (op, f) = Some (VLoc oo) ->
  (forall g, In g fs -> C !! (on, g) = C !! (oo, g)) ->
  (forall b h, C !! (b, h) = Some (VLoc oo) -> (b, h) = (op, f)) ->
  on <> op -> op <> oo -> on <> oo ->
  (* neither node is the root: the replaced one has a predecessor, and the new
     one is fresh *)
  oo <> root -> on <> root ->
  MirrorOK root C Sm t G op f oo on fs ->
  EnvOK root t U Qc FType fs Sm Ob C Fl G ->
  EnvOK root t U Qc FType fs Sm
    (<[on := {[Oiter t]}]> (<[oo := {[Ounlk t]}]> Ob))
    (<[(op, f) := VLoc on]> C) Fl G.
Proof.
  intros Hcell Hmir Hsole Hop Hpo Hno Hor Hnr
         (HV & HW & HT & HP & HN & HF) Hok y ty Hin.
  assert (Hroo : root <> oo) by (intros Hc; apply Hor; by rewrite Hc).
  pose proof (Hok y ty Hin) as Hty.
  (* the observation of anything that is neither node is untouched *)
  assert (Hob : forall o sg, o <> oo -> o <> on -> Ob !! o = Some sg ->
            <[on := {[Oiter t]}]> (<[oo := {[Ounlk t]}]> Ob) !! o = Some sg).
  { intros o sg H1 H2 H3. rewrite lookup_insert_ne; [| intros ->; by apply H2].
    rewrite lookup_insert_ne; [exact H3 | intros ->; by apply H1]. }
  assert (Hfield : forall o g v, o <> op \/ g <> f ->
            C !! (o, g) = Some v -> <[(op, f) := VLoc on]> C !! (o, g) = Some v).
  { intros o g v Hne Hc. rewrite lookup_insert_ne; [exact Hc |].
    intros Heq. injection Heq as H1 H2.
    destruct Hne as [Hd | Hd]; [by apply Hd | by apply Hd]. }
  (* the field-map entries, which every case but [undef] carries *)
  assert (Hflds : forall o, Sm !! (y, t) = Some o ->
            FieldOK t Sm Ob C o (tyN ty) ->
            FieldOK t Sm
              (<[on := {[Oiter t]}]> (<[oo := {[Ounlk t]}]> Ob))
              (<[(op, f) := VLoc on]> C) o (tyN ty)).
  { intros o Hstk Hfld g w Hw. specialize (Hfld g w Hw).
    assert (Hcellne : o <> op \/ g <> f)
      by (left; intros ->; by apply (HF y ty Hin)).
    destruct w as [z | ].
    - destruct Hfld as (oy & sgy & Hsy & Hcy & Hoy & Hity).
      destruct (HT y ty g z Hin Hw) as [Hz1 Hz2].
      exists oy, sgy. repeat apply conj.
      + exact Hsy.
      + exact (Hfield o g (VLoc oy) Hcellne Hcy).
      + apply Hob; [intros ->; by apply Hz1 | intros ->; by apply Hz2
                    | exact Hoy].
      + exact Hity.
    - exact (Hfield o g VNull Hcellne Hfld). }
  destruct ty; simpl in Hty |- *.
  - destruct Hty as (o & sg & Hstk & Hobo & Hit & Hundf & Hfld & Hpath & Hpre).
    assert (Ho1 : o <> oo) by (intros ->; by apply (HV y _ Hin)).
    assert (Ho2 : o <> on) by (intros ->; by apply (HW y _ Hin)).
    exists o, sg. repeat apply conj.
    + exact Hstk.
    + exact (Hob o sg Ho1 Ho2 Hobo).
    + exact Hit.
    + exact Hundf.
    + exact (Hflds o Hstk Hfld).
    + pose proof (hstarC_mirror C op f oo on fs root rho o Hcell Hmir
                    (HP y rho N Hin) Hsole Hop Hpo Hpath) as Hm.
      rewrite (swapn_ne oo on root Hroo) in Hm.
      rewrite (swapn_ne oo on o Ho1) in Hm. exact Hm.
    + intros rho1 rho2 Happ. destruct (Hpre rho1 rho2 Happ)
        as (o' & sg' & Hp' & Hob' & Hit').
      assert (Hrcu1 : forall g, In g rho1 -> In g fs).
      { intros g Hg. apply (HP y rho N Hin). rewrite -Happ.
        apply in_or_app. by left. }
      pose proof (hstarC_mirror C op f oo on fs root rho1 o' Hcell Hmir
                    Hrcu1 Hsole Hop Hpo Hp') as Hm.
      rewrite (swapn_ne oo on root Hroo) in Hm.
      destruct (decide (o' = oo)) as [-> | Hne].
      * (* the path passed through the replaced node: it now passes through
           the new one, which is an iterator *)
        rewrite swapn_eq in Hm.
        exists on, {[Oiter t]}. repeat apply conj;
          [exact Hm | by rewrite lookup_insert_eq | by apply elem_of_singleton].
      * rewrite (swapn_ne oo on o' Hne) in Hm.
        exists o', sg'. repeat apply conj.
        -- exact Hm.
        -- apply Hob; [exact Hne | | exact Hob'].
           intros ->. exact (HN y rho N rho1 rho2 Hin Happ Hp').
        -- exact Hit'.
  - destruct Hty as (o & sg & Hstk & Hobo & Hfr & Hundf & Hfld & Hnull).
    assert (Ho1 : o <> oo) by (intros ->; by apply (HV y _ Hin)).
    assert (Ho2 : o <> on) by (intros ->; by apply (HW y _ Hin)).
    exists o, sg. repeat apply conj.
    + exact Hstk.
    + exact (Hob o sg Ho1 Ho2 Hobo).
    + exact Hfr.
    + exact Hundf.
    + exact (Hflds o Hstk Hfld).
    + intros g Hg HNg. apply Hfield; [| exact (Hnull g Hg HNg)].
      left. intros ->. by apply (HF y (TFresh N) Hin).
  - destruct Hty as (o & sg & Hstk & Hobo & Hin' & Hundf).
    assert (Ho1 : o <> oo) by (intros ->; by apply (HV y _ Hin)).
    assert (Ho2 : o <> on) by (intros ->; by apply (HW y _ Hin)).
    exists o, sg. repeat apply conj;
      [exact Hstk | exact (Hob o sg Ho1 Ho2 Hobo) | exact Hin' | exact Hundf].
  - destruct Hty as [(o & sg & Hstk & Hobo & Hin' & Hundf) Hfle].
    assert (Ho1 : o <> oo) by (intros ->; by apply (HV y _ Hin)).
    assert (Ho2 : o <> on) by (intros ->; by apply (HW y _ Hin)).
    split; [| exact Hfle].
    exists o, sg. repeat apply conj;
      [exact Hstk | exact (Hob o sg Ho1 Ho2 Hobo) | exact Hin' | exact Hundf].
  - exact Hty.
  - destruct Hty as (sg & Hstk & Hobo & Hin').
    exists sg. repeat apply conj;
      [exact Hstk
       | apply Hob; [exact Hroo | intros Hc; apply Hnr; by rewrite Hc
                     | exact Hobo]
       | exact Hin'].
Qed.

Print Assumptions EnvOK_mirror.

Print Assumptions EnvOK_cell.
Print Assumptions EnvOK_obs.
Print Assumptions EnvOK_stack.

Section atomic_alloc.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (root : Loc) (fs : list FName).

  (** ** T-Alloc, with the location produced rather than assumed

      The six negative premises are discharged by the allocator, and the
      location it returns is existentially quantified in the postcondition --
      which is what allocation is.  The fresh-node environment comes back
      extended by the new node, which is exactly what the next \textsc{T-Replace}
      will consume: the two rules fit together as resources. *)
  Lemma alloc_typed N γm γh γl γs γo γf γr γe γq E lw x o0 U Qc Sm Ob C Fl Fr val G :
    ↑N ⊆ E ->
    NoDup fs ->
    (forall g, FType g = RCUField -> In g fs) ->
    FrCells Fr fs C val ->
    Sm !! (x, lw) = Some o0 ->
    (forall y ty f, In (y, ty) G -> tyN ty f <> Some (FVar x)) ->
    EnvOK root lw U Qc FType fs Sm Ob C Fl G ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    writer γo γs γh γl γf lw Sm Ob C Fl -∗
    fr_frag γr Fr
    ={E}=∗ ∃ n,
      writer γo γs γh γl γf lw
        (<[(x, lw) := n]> Sm) (<[n := {[Ofresh lw]}]> Ob)
        (newcells fs n ∪ C) Fl
      ∗ fr_frag γr (Fr ∪ {[n]})
      (* what a later rule needs about the new location: it is not one the
         caller's maps already mention, so their entries survive the extension.
         Without these the environment comes back but nothing can be looked up
         in the maps it is stated over. *)
      ∗ ⌜n <> root⌝
      ∗ ⌜forall k v, C !! k = Some v -> k.1 <> n⌝
      ∗ ⌜forall o sg, Ob !! o = Some sg -> o <> n⌝
      ∗ ⌜forall k o, Sm !! k = Some o -> o <> n⌝
      ∗ ⌜FrCells (Fr ∪ {[n]}) fs (newcells fs n ∪ C)
           (fun q g => if decide (q = n) then VNull else val q g)⌝
      ∗ ⌜EnvOK root lw (fun y t => U y t /\ (y, t) <> (x, lw)) Qc FType fs
           (<[(x, lw) := n]> Sm) (<[n := {[Ofresh lw]}]> Ob)
           (newcells fs n ∪ C) Fl
           ((x, TFresh (fun _ => None))
              :: List.filter (fun p => negb (Nat.eqb (fst p) x)) G)⌝.
  Proof.
    iIntros (HN Hnd Hrcu HFrC Hstkx HNx Hok) "#Hinv Hw Hfrg".
    iDestruct "Hw" as "(Hlk & Hsm & Hob & Hcells & Hflo)".
    iInv "Hinv" as (m Og U0 T F St Rg gg ww Fr0)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)" "Hclose".
    iDestruct (fr_agree with "Hfr Hfrg") as %->.
    iDestruct "Hp" as "(Hm & Hlka & %Hrt & Hhp & Hst)".
    iDestruct (lk_agree with "Hlka Hlk") as %Hlkm.
    iDestruct "Hst" as (S) "[%HRS Hb]".
    iDestruct "Hhp" as (H) "(%HR & %HS & Ha)".
    (* the allocator *)
    pose (n := fresh (used root H S Og F Fr)).
    assert (Hn : n ∉ used root H S Og F Fr) by apply is_fresh.
    iDestruct (cells_agree with "Ha Hcells") as %Hcsub.
    iDestruct (stk_own_agree with "Hb Hsm") as %Hsmsub.
    iDestruct (obs_own_agree with "Ho Hob") as %Hobsub.
    rewrite /stk_own (big_sepM_delete _ Sm (x, lw) o0); [| exact Hstkx].
    iDestruct "Hsm" as "[Hsv Hsmrest]".
    assert (HnF : n ∉ Fr) by exact (fresh_not_fresh root H S Og F Fr n Hn).
    assert (Hun : forall g, hp m n g = None).
    { intros g. rewrite HR. exact (fresh_unallocated root H S Og F Fr n Hn g). }
    assert (Hni : forall o g, hp m o g <> Some (VLoc n)).
    { intros o g Hc. rewrite HR in Hc.
      exact (fresh_unpointed root H S Og F Fr n Hn (o, g) (VLoc n) Hc eq_refl). }
    assert (Hnref : forall y t, stk m y t <> Some n).
    { intros y t Hc. rewrite HRS in Hc.
      exact (fresh_unreferenced root H S Og F Fr n Hn (y, t) Hc). }
    assert (Hnr0 : n <> root) by exact (fresh_not_root root H S Og F Fr n Hn).
    assert (Hnr : n <> rt m) by (rewrite Hrt; exact Hnr0).
    assert (Hnone : forall t, Og !! (n, t) = None)
      by exact (fresh_unobserved root H S Og F Fr n Hn).
    assert (Hfl : flist (to_LState_t m Og U0 T F) n = None).
    { simpl. by rewrite (fresh_unlisted root H S Og F Fr n Hn). }
    (* the writer's cell map has nothing at the new node *)
    assert (Hcn : forall k v, C !! k = Some v -> k.1 <> n).
    { intros k v Hk Hc. destruct k as [q g]. simpl in Hc. subst q.
      pose proof (Hcsub (n, g) v Hk) as Hh.
      by rewrite (fresh_unallocated root H S Og F Fr n Hn g) in Hh. }
    (* the scope change: x becomes defined and nothing else moves *)
    pose (U' := fun (y : Var) (t : TID) => U0 y t /\ (y, t) <> (x, lw)).
    assert (Hdef : ~ undf (to_LState_t m (<[(n, lw) := {[Ofresh lw]}]> Og)
                            U' T F) x lw).
    { simpl. intros [_ Hc]. by apply Hc. }
    assert (Hundf : forall y t, (y, t) <> (x, lw) ->
              (undf (to_LState_t m (<[(n, lw) := {[Ofresh lw]}]> Og) U' T F) y t
               <-> undf (to_LState_t m Og U0 T F) y t)).
    { intros y t Hne. simpl. split; [by intros [Hy _] | by intros Hy]. }
    destruct (alloc_pure FType m Og U0 U' T F lw n x fs
                HWF Hwf Hnone Hlkm Hdef Hundf Hun Hni Hnref Hnr Hfl Hrcu)
      as [HWF' Hwf'].
    (* the physical step, the ghost step, and the enumeration *)
    iAssert (phys γm γh γl γs root fs m) with "[Hm Hlka Ha Hb]" as "Hp".
    { rewrite /phys. iFrame "Hm Hlka". iSplitR; [by iPureIntro |].
      iSplitL "Ha"; [iExists H; by iFrame | iExists S; by iFrame]. }
    iMod (phys_alloc_step _ _ _ _ _ _ _ n x lw o0 Hnd Hun with "Hp Hsv")
      as "(Hp & Hsv & Hnew)".
    iMod (tobs_alloc_at with "Ho") as "[Ho Hctl]"; [exact (Hnone lw) |].
    iMod (fr_update _ _ _ (Fr ∪ {[n]}) with "Hfr Hfrg") as "[Hfr Hfrg]".
    (* the new node's cells join the writer's cell map *)
    iDestruct (cells_new γh fs n Hnd with "Hnew") as "Hncells".
    iAssert (cells γh (newcells fs n ∪ C)) with "[Hncells Hcells]" as "Hcells".
    { rewrite /cells. rewrite big_sepM_union; [iFrame |].
      apply map_disjoint_spec. intros k v1 v2 H1 H2.
      apply (Hcn k v2 H2). destruct (decide (k.1 = n)) as [Heq | Hne].
      - exact Heq.
      - by rewrite (newcells_other fs n k Hne) in H1. }
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext.
      iExists (alloc_ms m n fs x lw), (<[(n, lw) := {[Ofresh lw]}]> Og),
              U', T, F, St, Rg, gg, ww, (Fr ∪ {[n]}).
      iFrame. iPureIntro. split; [exact HWF' | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - intros o Tr Hfl'. destruct (HFLD o Tr Hfl') as [t0 Hdet].
        exists t0. destruct Hdet as [Hd | Hd];
          [left | right];
          (destruct Hd as [t' [sg [Hl Hin']]]; exists t', sg; split;
           [ rewrite lookup_insert_ne;
             [exact Hl | intros Hc; injection Hc as -> ->;
                         by rewrite Hnone in Hl]
           | exact Hin']).
      - intros o t0 Hf0'.
        destruct (tobs_ins_new m Og U0 T F n lw _ o (Ofresh t0) Hf0')
          as [[-> Hin'] | Hy].
        + apply elem_of_singleton in Hin'. injection Hin' as <-. exact Hlkm.
        + exact (HWFW o t0 Hy).
      - apply RefsRCU_alloc. exact HRefs.
      - intros q t0 Hq.
        destruct (tobs_ins_new m Og U0 T F n lw _ q (Ofresh t0) Hq)
          as [[-> Hin'] | Hy].
        + set_solver.
        + assert (Hq' : q ∈ Fr) by exact (HFrc q t0 Hy). set_solver.
      - exact Hwf'.
      - apply (WUNLKW_ins m _ _ _ _ _ _ _ _ lw);
          [ exact HWUW | reflexivity | exact Hlkm
          | intros t0 [Hz | Hz]; apply elem_of_singleton in Hz;
            discriminate ].
      - exact HFeq.
      - exact HEWF.
      - exact HRR.
      - exact HBnd.
      - exact HLk.
      - exact HWm.
      - first [ exact Hdom
              | by apply (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)
              | by apply (dom_ins Rg _ m _ lw _ Hlkm HLk
                            (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)) ]. }
    (* the three freshness facts the environment's survival needs, read off the
       thread's own maps because they are submaps of the invariant's *)
    assert (HSn : forall k o, Sm !! k = Some o -> o <> n).
    { intros k o Hk Hc. subst o.
      exact (fresh_unreferenced root H S Og F Fr n Hn k (Hsmsub k n Hk)). }
    assert (HOn : Ob !! n = None).
    { destruct (Ob !! n) as [sg|] eqn:Eo; [| reflexivity].
      exfalso. pose proof (Hobsub n sg Eo) as Hc.
      by rewrite (fresh_unobserved root H S Og F Fr n Hn lw) in Hc. }
    assert (HCn : forall k v, C !! k = Some v -> v <> VLoc n).
    { intros k v Hk.
      exact (fresh_unpointed root H S Og F Fr n Hn k v (Hcsub k v Hk)). }
    iModIntro. iExists n.
    iSplitL "Hlk Hsv Hsmrest Hctl Hob Hcells Hflo".
    { rewrite /writer /stk_own /obs_own. iFrame "Hlk Hcells Hflo".
      iSplitL "Hsv Hsmrest".
      - rewrite big_sepM_insert_delete. iFrame.
      - rewrite big_sepM_insert; [| exact HOn]. iFrame. }
    iFrame. iPureIntro.
    split; [exact Hnr0 |]. split; [exact Hcn |].
    split; [intros o sg Ho Hc; rewrite Hc in Ho; by rewrite HOn in Ho |].
    split; [exact HSn |]. split.
    - intros q g Hq Hg. apply elem_of_union in Hq. destruct Hq as [Hq | Hq].
      + rewrite decide_False; [| intros ->; by apply HnF].
        rewrite lookup_union_r; [exact (HFrC q g Hq Hg) |].
        apply (newcells_other fs n (q, g)). simpl. intros ->. by apply HnF.
      + apply elem_of_singleton in Hq. subst q.
        rewrite decide_True; [| reflexivity].
        apply lookup_union_Some_l. exact (newcells_at fs n g Hnd Hg).
    - assert (Hrest : EnvOK root lw
                (fun y t => U y t /\ (y, t) <> (x, lw)) Qc FType fs
                (<[(x, lw) := n]> Sm) (<[n := {[Ofresh lw]}]> Ob)
                (newcells fs n ∪ C) Fl
                (List.filter (fun p => negb (Nat.eqb (fst p) x)) G)).
      { apply (EnvOK_alloc root lw U _ Qc _ fs Sm _ Ob _ C _ Fl G x n);
          [| exact HSn | exact HOn | exact HCn | exact Hnr0 | | | |
           exact HNx | exact Hok].
        - intros y t' Hy [Hc _]. by apply Hy.
        - intros k Hk. by rewrite lookup_insert_ne.
        - intros o Ho. by rewrite lookup_insert_ne.
        - intros k Hk. apply lookup_union_r. exact (newcells_other fs n k Hk). }
      intros y ty Hin. destruct Hin as [Heq | Hin]; [| exact (Hrest y ty Hin)].
      injection Heq as <- <-. simpl.
      exists n, {[Ofresh lw]}. repeat apply conj.
      + by rewrite lookup_insert_eq.
      + by rewrite lookup_insert_eq.
      + by apply elem_of_singleton.
      + intros [_ Hc]. by apply Hc.
      + intros f w Hc. discriminate Hc.
      + intros g Hg _. apply lookup_union_Some_l.
        exact (newcells_at fs n g Hnd Hg).
  Qed.

End atomic_alloc.

Print Assumptions alloc_typed.



Section atomic_bind.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (root : Loc) (fs : list FName).

  (** ** The binding rules

      Binding a variable to a node the thread can already see.  Its two
      interesting premises are both negative -- the node is not detached, and it
      has no free-list entry -- and both come from the iterator the thread
      already holds: WULK excludes [unlinked] and [freeable], FNR excludes
      [fresh], and FLD then excludes the free-list entry.  Nothing new is
      needed, which is the point of doing it here: with the write side's
      resources in place the binding rules fall out. *)
  Lemma bind_atomic N γm γh γl γs γo γf γr γe γq E lw y o o0 sold :
    ↑N ⊆ E ->
    Oiter lw ∈ sold ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    lk_tok γl lw -∗
    tobs_ctl γo o lw sold -∗
    sv γs y lw o0
    ={E}=∗ lk_tok γl lw ∗ tobs_ctl γo o lw (sold ∪ {[Oiter lw]})
           ∗ sv γs y lw o.
  Proof.
    iIntros (HN Hip) "#Hinv Hlk Hctl Hsv".
    iInv "Hinv" as (m Og U0 T F St Rg gg ww Fr)
      ">(Hp & Ho & Hf & Hreg & Hwm & Hfr & %HWF & %HFLD & %HWFW & %HRefs & %HFrc
         & %Hwf & %HWUW & %HFeq & %HEWF & %HRR & %HBnd & %HLk & %HWm & %Hdom)" "Hclose".
    iDestruct (tobs_ctl_agree with "Ho Hctl") as %Hlook.
    assert (Hitr : obsv (to_LState_t m Og U0 T F) o (Oiter lw))
      by (by exists lw, sold).
    iDestruct "Hp" as "(Hm & Hlka & %Hrt & Hhp & Hst)".
    iDestruct (lk_agree with "Hlka Hlk") as %Hlkm.
    (* nothing the thread holds an iterator on is detached *)
    assert (Hdet : ~ Detached (to_LState_t m Og U0 T F) o).
    { intros [t0 [Hd | [Hd | Hd]]].
      - destruct Hwf as (_ & _ & _ & _ & _ & _ & HWU & _).
        exact (proj1 (HWU lw o t0 Hlkm Hitr) Hd).
      - destruct Hwf as (_ & _ & _ & _ & _ & _ & HWU & _).
        exact (proj2 (HWU lw o t0 Hlkm Hitr) Hd).
      - destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HFNR & _).
        exact (proj1 (HFNR o t0 lw Hd) Hitr). }
    assert (Hfl : flist (to_LState_t m Og U0 T F) o = None).
    { destruct Hwf as (_ & _ & _ & _ & _ & _ & HWU & _).
      exact (iter_no_flist _ lw o HFLD HWU Hlkm Hitr). }
    pose (U' := fun (z : Var) (t : TID) => U0 z t /\ (z, t) <> (y, lw)).
    assert (Hundf : forall z t, (z, t) <> (y, lw) ->
              (undf (to_LState_t (bind_ms m y lw o)
                       (<[(o, lw) := sold ∪ {[Oiter lw]}]> Og) U' T F) z t
               <-> undf (to_LState_t m Og U0 T F) z t)).
    { intros z t Hne. simpl. split; [by intros [Hz _] | by intros Hz]. }
    destruct (bind_pure (Σ := Σ) FType (fun _ => True%I) m Og U0 U' T F
                lw y o sold
                HWF Hwf (or_introl Hlkm) Hundf Hdet Hfl Hlook)
      as [HWF' Hwf'].
    iAssert (phys γm γh γl γs root fs m) with "[Hm Hlka Hhp Hst]" as "Hp".
    { rewrite /phys. by iFrame. }
    iMod (phys_bind _ _ _ _ _ _ _ y lw o o0 with "Hp Hsv") as "[Hp Hsv]".
    iMod (tobs_set with "Ho Hctl") as "[Ho Hctl]".
    iMod ("Hclose" with "[Hp Ho Hf Hreg Hwm Hfr]") as "_".
    { iNext.
      iExists (bind_ms m y lw o),
              (<[(o, lw) := sold ∪ {[Oiter lw]}]> Og), U', T, F, St,
              Rg, gg, ww, Fr.
      iFrame. iPureIntro. split; [exact HWF' | split; [| split; [| split; [| split; [| split;
        [| split; [| split; [| split; [| split; [| split; [| split;
        [| split]]]]]]]]]]]].
      - intros q Tr Hfl'. destruct (HFLD q Tr Hfl') as [t0 Hdt].
        exists t0. destruct Hdt as [Hd | Hd]; [left | right];
          (destruct Hd as [t' [sg [Hl Hin']]];
           destruct (decide ((q, t') = (o, lw))) as [Heq | Hne];
           [ injection Heq as -> ->; exists lw, (sold ∪ {[Oiter lw]});
             split; [by rewrite lookup_insert_eq |];
             rewrite Hlook in Hl; injection Hl as <-; by apply elem_of_union_l
           | exists t', sg; split; [by rewrite lookup_insert_ne | exact Hin']]).
      - intros q t0 Hq.
        destruct (tobs_ins_new m Og U0 T F o lw _ q (Ofresh t0) Hq)
          as [[-> Hin'] | Hy]; [| exact (HWFW q t0 Hy)].
        apply elem_of_union in Hin' as [Hin' | Hin'].
        + apply (HWFW o t0). by exists lw, sold.
        + apply elem_of_singleton in Hin'. discriminate.
      - exact HRefs.
      - intros q t0 Hq.
        destruct (tobs_ins_new m Og U0 T F o lw _ q (Ofresh t0) Hq)
          as [[-> Hin'] | Hy]; [| exact (HFrc q t0 Hy)].
        apply elem_of_union in Hin' as [Hin' | Hin'].
        + apply (HFrc o t0). by exists lw, sold.
        + apply elem_of_singleton in Hin'. discriminate.
      - exact Hwf'.
      - apply (WUNLKW_ins m _ _ _ _ _ _ _ _ lw);
          [ exact HWUW | reflexivity | exact Hlkm |].
        intros t0 Hz.
        assert (Hz' : lk m = Some t0).
        { destruct Hz as [Hz | Hz]; apply elem_of_union in Hz as [Hz | Hz];
            [ apply (HWUW o t0); left; by exists lw, sold
            | apply elem_of_singleton in Hz; discriminate
            | apply (HWUW o t0); right; by exists lw, sold
            | apply elem_of_singleton in Hz; discriminate ]. }
        rewrite Hlkm in Hz'. by injection Hz'.
      - exact HFeq.
      - exact HEWF.
      - exact HRR.
      - exact HBnd.
      - exact HLk.
      - exact HWm.
      - first [ exact Hdom
              | by apply (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)
              | by apply (dom_ins Rg _ m _ lw _ Hlkm HLk
                            (dom_ins Rg Og m _ lw _ Hlkm HLk Hdom)) ]. }
    iModIntro. iFrame.
  Qed.

End atomic_bind.

Print Assumptions bind_atomic.



Section typed_link.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (root : Loc) (fs : list FName).

  (** * A mutation, end to end

      \textsc{T-LinkF-Null} with a type environment on both sides.  The
      environment's variables split in two, as they do for every rule: the ones
      the step does not touch are framed across it, and the one it does gets its
      new type.

      The framing is the two lemmas, applied in the order the step changes
      things -- observations first, then the cell, so both hypotheses are about
      the cell map the caller started with.  The touched variable is
      [TyOK_promoted], and the only work in it is that the fresh node's new path
      is the parent's extended by the field just written.

      Nothing here is about RCU.  It is the bookkeeping that connects a rule's
      resources to a rule's types, and it is the same bookkeeping for all five
      mutations. *)
  Lemma link_null_typed N γm γh γl γs γo γf γr γe γq E lw x xp op f on rho f0
        U Qc Sm Ob C Fl G sp v Np :
    ↑N ⊆ E ->
    FType f = RCUField ->
    on <> root -> In f0 fs -> op <> on -> x <> xp ->
    (* what the environment already says about the parent and the fresh node *)
    In (xp, TItr rho Np) G ->
    Sm !! (xp, lw) = Some op -> Ob !! op = Some sp -> Oiter lw ∈ sp ->
    Sm !! (x, lw) = Some on -> Ob !! on = Some {[Ofresh lw]} -> ~ U x lw ->
    (forall g, In g fs -> C !! (on, g) = Some VNull) ->
    C !! (op, f) = Some v ->
    hstarC C root rho = Some op ->
    ~ In (op, f) (pathcells C root rho) ->
    (* and the framing conditions for everything else *)
    ReadsObs root C Sm lw
      (List.filter (fun p => negb (Nat.eqb (fst p) x)) G) on ->
    ReadsCell root C Sm lw
      (List.filter (fun p => negb (Nat.eqb (fst p) x)) G) (op, f) ->
    EnvOK root lw U Qc FType fs Sm Ob C Fl G ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    writer γo γs γh γl γf lw Sm Ob C Fl -∗
    sv γs x lw on
    ={E}=∗ writer γo γs γh γl γf lw Sm
             (<[on := {[Oiter lw]}]> Ob) (<[(op, f) := VLoc on]> C) Fl
           ∗ sv γs x lw on
           ∗ ⌜EnvOK root lw U Qc FType fs Sm
                (<[on := {[Oiter lw]}]> Ob) (<[(op, f) := VLoc on]> C) Fl
                ((x, TItr (rho ++ [f]) (fun _ => None))
                   :: List.filter (fun p => negb (Nat.eqb (fst p) x)) G)⌝.
  Proof.
    iIntros (HN Hfrcu Hnr Hf0 Hpn Hxp Hin Hstkp Hobp Hitp Hstkx Hobx Hundf
             Hnull Hcellf HpathC Hoff HRO HRC Hok) "#Hinv Hw Hsv".
    iDestruct "Hw" as "(Hlk & Hsm & Hob & Hcells & Hflo)".
    assert (Hinf : In (xp, TItr rho Np)
              (List.filter (fun p => negb (Nat.eqb (fst p) x)) G)).
    { apply List.filter_In. split; [exact Hin |]. simpl.
      apply Bool.negb_true_iff. apply Nat.eqb_neq.
      intros Hc. apply Hxp. by rewrite Hc. }
    (* the two observation entries the step reads *)
    rewrite /obs_own (big_sepM_delete _ Ob op sp); [| exact Hobp].
    iDestruct "Hob" as "[Hop Hob]".
    rewrite (big_sepM_delete _ (delete op Ob) on {[Ofresh lw]});
      [| rewrite lookup_delete_ne; [exact Hobx | intros Hc; by apply Hpn]].
    iDestruct "Hob" as "[Hon Hob]".
    (* and the cell it writes *)
    rewrite /cells (big_sepM_delete _ C (op, f) v); [| exact Hcellf].
    iDestruct "Hcells" as "[Hptf Hcells]".
    assert (Hnull' : forall g, In g fs ->
              delete (op, f) C !! (on, g) = Some VNull).
    { intros g Hg. rewrite lookup_delete_ne; [exact (Hnull g Hg) |].
      intros Hc. injection Hc as Ha Hb. exact (Hpn Ha). }
    iMod (link_null_atomic FType root fs N γm γh γl γs γo γf γr γe γq E lw op f on
            rho x f0 sp v (delete (op, f) C) HN Hfrcu Hnr Hf0 Hitp
            (hstarC_delete C (op, f) root rho op Hoff HpathC) Hnull'
            with "Hinv Hlk Hop Hon Hsv Hcells Hptf")
      as "(Hlk & Hop & Hon & Hsv & Hcells & Hptf)".
    iModIntro.
    iSplitL "Hlk Hsm Hop Hon Hob Hcells Hptf Hflo".
    { rewrite /writer /obs_own /cells. iFrame "Hlk Hsm Hflo".
      iSplitL "Hop Hon Hob".
      - rewrite (big_sepM_delete _ (<[on := {[Oiter lw]}]> Ob) op sp).
        + iFrame "Hop".
          rewrite (big_sepM_delete _ (delete op (<[on := {[Oiter lw]}]> Ob))
                     on {[Oiter lw]}).
          * iFrame "Hon".
            rewrite delete_insert_ne; [| intros Hc; by apply Hpn].
            by rewrite delete_insert_eq.
          * rewrite lookup_delete_ne; [| intros Hc; by apply Hpn].
            by rewrite lookup_insert_eq.
        + rewrite lookup_insert_ne; [exact Hobp | intros Hc; by apply Hpn].
      - rewrite (big_sepM_delete _ (<[(op, f) := VLoc on]> C) (op, f)
                   (VLoc on)); [| by rewrite lookup_insert_eq].
        iFrame "Hptf". by rewrite delete_insert_eq. }
    iFrame. iPureIntro.
    (* frame the rest of the environment, then give the touched variable its
       new type *)
    assert (Hframed : EnvOK root lw U Qc FType fs Sm
              (<[on := {[Oiter lw]}]> Ob) (<[(op, f) := VLoc on]> C) Fl
              (List.filter (fun p => negb (Nat.eqb (fst p) x)) G)).
    { apply EnvOK_cell; [exact HRC |].
      apply EnvOK_obs; [exact HRO |].
      intros y ty Hiny. apply List.filter_In in Hiny.
      exact (Hok y ty (proj1 Hiny)). }
    intros y ty Hiny. destruct Hiny as [Heq | Hiny];
      [| exact (Hframed y ty Hiny)].
    injection Heq as <- <-. simpl.
    (* the promoted node: its path is the parent's, extended *)
    destruct (Hok xp _ Hin)
      as (op' & sp' & Hstkp' & Hobp' & Hitp' & _ & _ & Hpp & Hprep).
    rewrite Hstkp in Hstkp'. injection Hstkp' as <-.
    apply (TyOK_promoted root lw U Qc FType fs Sm _ _ Fl x on op f rho
             {[Oiter lw]} (fun _ => None)).
    - exact Hstkx.
    - exact Hundf.
    - by rewrite lookup_insert_eq.
    - by apply elem_of_singleton.
    - intros g w Hc. discriminate Hc.
    - apply hstarC_stable_cell; [exact Hoff | exact HpathC].
    - by rewrite lookup_insert_eq.
    - intros rho1 rho2 Happ.
      destruct (app_snoc_split rho1 rho2 rho f Happ) as [[rho2' Hpre] | ->].
      + destruct (Hprep rho1 rho2' Hpre) as (o' & sg' & Hp' & Hob' & Hit').
        exists o', sg'. repeat apply conj.
        * apply hstarC_stable_cell; [| exact Hp'].
          intros Hc. apply Hoff. rewrite -Hpre.
          exact (pathcells_prefix C root rho1 rho2' (op, f) Hc).
        * rewrite lookup_insert_ne; [exact Hob' |].
          intros ->.
          exact (proj1 (proj2 HRO) xp rho Np rho1 rho2' Hinf Hpre Hp').
        * exact Hit'.
      + exists on, {[Oiter lw]}. repeat apply conj.
        * apply (hstarC_snoc _ root rho op f on);
            [apply hstarC_stable_cell; [exact Hoff | exact HpathC]
             | by rewrite lookup_insert_eq].
        * by rewrite lookup_insert_eq.
        * by apply elem_of_singleton.
  Qed.

End typed_link.

Print Assumptions link_null_typed.

Section typed_unlink.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (root : Loc) (fs : list FName).

  (** * The transcription

      \textsc{T-UnlinkH} with a type environment on both sides, written against
      the same toolkit as \textsc{T-LinkF-Null} and touching three variables
      rather than one: the parent's field map is retargeted, the victim is
      demoted to [unlinked], and the node below is promoted to the parent's
      field.  Each is one of [FieldOK_update], [TyOK_demoted] and
      [TyOK_promoted]; the rest of the environment is framed by the same two
      lemmas in the same order.

      This is the second of five and it took no new ideas, which is what the
      toolkit was for. *)
  Lemma unlink_typed N γm γh γl γs γo γf γr γe γq E lw xx xz xw ox f1 oz f2 ow rho
        U Qc Sm Ob C Fl Fr val sx sw rest :
    ↑N ⊆ E ->
    ox <> oz -> ox <> ow -> oz <> ow ->
    (* what the environment says about the three *)
    Sm !! (xx, lw) = Some ox -> Ob !! ox = Some sx -> Oiter lw ∈ sx ->
    Sm !! (xz, lw) = Some oz -> Ob !! oz = Some {[Oiter lw]} -> ~ U xz lw ->
    Sm !! (xw, lw) = Some ow ->
    Ob !! ow = Some sw -> Oiter lw ∈ sw -> ~ U xw lw -> ~ U xx lw ->
    (* the heap the step reads and writes *)
    C !! (ox, f1) = Some (VLoc oz) ->
    C !! (oz, f2) = Some (VLoc ow) ->
    hstarC C root rho = Some ox ->
    ~ In (ox, f1) (pathcells C root rho) ->
    (forall rho1 rho2, rho1 ++ rho2 = rho ->
       exists o' sg', hstarC C root rho1 = Some o'
                   /\ Ob !! o' = Some sg' /\ Oiter lw ∈ sg') ->
    (* the victim is not on the parent's path: uniqueness of paths, which the
       invariant gives and which the rule's premises make available *)
    (forall rho1 rho2, rho1 ++ rho2 = rho -> hstarC C root rho1 <> Some oz) ->
    FrCells Fr fs C val ->
    (forall q g, val q g <> VLoc oz) ->
    (* the framing conditions for the rest *)
    ReadsObs root C Sm lw rest oz ->
    ReadsCell root C Sm lw rest (ox, f1) ->
    EnvOK root lw U Qc FType fs Sm Ob C Fl rest ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    writer γo γs γh γl γf lw Sm Ob C Fl -∗
    fr_frag γr Fr
    ={E}=∗ writer γo γs γh γl γf lw Sm
             (<[oz := {[Ounlk lw]}]> Ob) (<[(ox, f1) := VLoc ow]> C) Fl
           ∗ fr_frag γr Fr
           ∗ ⌜EnvOK root lw U Qc FType fs Sm
                (<[oz := {[Ounlk lw]}]> Ob) (<[(ox, f1) := VLoc ow]> C) Fl
                ([(xx, TItr rho
                     (fun g => if decide (g = f1)
                               then Some (FVar xw) else None));
                  (xz, TUnlinked);
                  (xw, TItr (rho ++ [f1]) (fun _ => None))] ++ rest)⌝.
  Proof.
    iIntros (HN Hxz Hxw Hzw Hstkx Hobx Hitx Hstkz Hobz Hundz
             Hstkw Hobw Hitw Hundw Hundx Hc1 Hc2 HpathC Hoff
             Hpre Hnoz HFrC Hnf HRO HRC Hrest) "#Hinv Hw Hfrg".
    iDestruct "Hw" as "(Hlk & Hsm & Hob & Hcells & Hflo)".
    (* the three observation entries *)
    rewrite /obs_own (big_sepM_delete _ Ob ox sx); [| exact Hobx].
    iDestruct "Hob" as "[Hox Hob]".
    rewrite (big_sepM_delete _ (delete ox Ob) oz {[Oiter lw]});
      [| rewrite lookup_delete_ne; [exact Hobz | exact Hxz]].
    iDestruct "Hob" as "[Hoz Hob]".
    rewrite (big_sepM_delete _ (delete oz (delete ox Ob)) ow sw);
      [| rewrite lookup_delete_ne; [| exact Hzw];
         rewrite lookup_delete_ne; [exact Hobw | exact Hxw]].
    iDestruct "Hob" as "[How Hob]".
    (* and the one cell it writes *)
    rewrite /cells (big_sepM_delete _ C (ox, f1) (VLoc oz)); [| exact Hc1].
    iDestruct "Hcells" as "[Hpt1 Hcells]".
    assert (Hc2' : delete (ox, f1) C !! (oz, f2) = Some (VLoc ow)).
    { rewrite lookup_delete_ne; [exact Hc2 |].
      intros Hcc. injection Hcc as Ha Hb. by apply Hxz. }
    assert (HFrC' : FrCells Fr fs (delete (ox, f1) C) val).
    { intros q g Hq Hg. rewrite lookup_delete_ne; [exact (HFrC q g Hq Hg) |].
      intros Hcc. injection Hcc as Ha Hb.
      pose proof (HFrC q g Hq Hg) as Hv.
      rewrite Ha Hb in Hc1. rewrite Hc1 in Hv.
      injection Hv as Hv. exact (Hnf q g (eq_sym Hv)). }
    iMod (unlink_atomic FType root fs N γm γh γl γs γo γf γr γe γq E lw ox f1 oz f2
            ow rho sx sw Fr val (delete (ox, f1) C) HN Hitx Hitw HFrC'
            (hstarC_delete C (ox, f1) root rho ox Hoff HpathC) Hc2' Hnf
            with "Hinv Hlk Hox Hoz How Hcells Hpt1 Hfrg")
      as "(Hlk & Hox & Hoz & How & Hcells & Hpt1 & Hfrg)".
    iModIntro.
    iSplitL "Hlk Hsm Hox Hoz How Hob Hcells Hpt1 Hflo"; last first.
    { iFrame. iPureIntro. apply EnvOK_step.
      - apply EnvOK_cell; [exact HRC |]. by apply EnvOK_obs.
      - intros y ty Hin.
        destruct Hin as [Heq | [Heq | [Heq | []]]]; injection Heq as Hv1 Hv2;
          rewrite -Hv1 -Hv2.
        + (* the parent: same path, one field retargeted *)
          exists ox, sx. repeat apply conj.
          * exact Hstkx.
          * rewrite lookup_insert_ne; [exact Hobx | intros ->; by apply Hxz].
          * exact Hitx.
          * exact Hundx.
          * apply (FieldOK_update _ _ _ _ _ _ _ xw ow sw).
            -- intros g w _ Hc. discriminate Hc.
            -- exact Hstkw.
            -- by rewrite lookup_insert_eq.
            -- rewrite lookup_insert_ne; [exact Hobw | intros ->; by apply Hzw].
            -- exact Hitw.
          * apply hstarC_stable_cell; [exact Hoff | exact HpathC].
          * intros rho1 rho2 Happ. destruct (Hpre rho1 rho2 Happ)
              as (o' & sg' & Hp' & Hob' & Hit').
            exists o', sg'. repeat apply conj.
            -- apply hstarC_stable_cell; [| exact Hp'].
               intros Hcc. apply Hoff. rewrite -Happ.
               exact (pathcells_prefix C root rho1 rho2 (ox, f1) Hcc).
            -- rewrite lookup_insert_ne; [exact Hob' |].
               intros Heq. rewrite -Heq in Hp'.
               exact (Hnoz rho1 rho2 Happ Hp').
            -- exact Hit'.
        + exact (TyOK_demoted root lw U Qc FType fs Sm Ob C Fl xz oz
                   Hstkz Hundz).
        + (* the node below, promoted to the parent's field *)
          apply (TyOK_promoted root lw U Qc FType fs Sm _ _ Fl xw ow ox f1 rho
                   sw (fun _ => None)).
          * exact Hstkw.
          * exact Hundw.
          * rewrite lookup_insert_ne; [exact Hobw | intros ->; by apply Hzw].
          * exact Hitw.
          * intros g w Hc. discriminate Hc.
          * apply hstarC_stable_cell; [exact Hoff | exact HpathC].
          * by rewrite lookup_insert_eq.
          * intros rho1 rho2 Happ.
            destruct (app_snoc_split rho1 rho2 rho f1 Happ) as [[r2 Hp] | ->].
            -- destruct (Hpre rho1 r2 Hp) as (o' & sg' & Hp' & Hob' & Hit').
               exists o', sg'. repeat apply conj.
               ++ apply hstarC_stable_cell; [| exact Hp'].
                  intros Hcc. apply Hoff. rewrite -Hp.
                  exact (pathcells_prefix C root rho1 r2 (ox, f1) Hcc).
               ++ rewrite lookup_insert_ne; [exact Hob' |].
                  intros Heq. rewrite -Heq in Hp'.
                  exact (Hnoz rho1 r2 Hp Hp').
               ++ exact Hit'.
            -- exists ow, sw. repeat apply conj.
               ++ apply (hstarC_snoc _ root rho ox f1 ow);
                    [apply hstarC_stable_cell; [exact Hoff | exact HpathC]
                     | by rewrite lookup_insert_eq].
               ++ rewrite lookup_insert_ne;
                    [exact Hobw | intros ->; by apply Hzw].
               ++ exact Hitw. }
    (* the maps go back together *)
    rewrite /writer /obs_own /cells. iFrame "Hlk Hsm Hflo".
    iSplitL "Hox Hoz How Hob".
    - rewrite (big_sepM_delete _ (<[oz := {[Ounlk lw]}]> Ob) ox sx);
        [| rewrite lookup_insert_ne; [exact Hobx | intros ->; by apply Hxz]].
      iFrame "Hox".
      rewrite (big_sepM_delete _ (delete ox (<[oz := {[Ounlk lw]}]> Ob)) oz
                 {[Ounlk lw]});
        [| rewrite lookup_delete_ne; [by rewrite lookup_insert_eq | exact Hxz]].
      iFrame "Hoz".
      rewrite delete_insert_ne; [| exact Hxz]. rewrite delete_insert_eq.
      rewrite (big_sepM_delete _ (delete oz (delete ox Ob)) ow sw);
        [| rewrite lookup_delete_ne; [| exact Hzw];
           rewrite lookup_delete_ne; [exact Hobw | exact Hxw]].
      iFrame.
    - rewrite (big_sepM_delete _ (<[(ox, f1) := VLoc ow]> C) (ox, f1)
                 (VLoc ow)); [| by rewrite lookup_insert_eq].
      iFrame "Hpt1". by rewrite delete_insert_eq.
  Qed.

End typed_unlink.

Print Assumptions unlink_typed.

Section typed_rest.
  Context `{!rcuG Σ, !physG Σ, !heapG Σ, !lockG Σ, !stackG Σ, !freshG Σ,
            !invGS_gen hlc Σ}.
  Context (FType : FName -> FieldKind).
  Context (root : Loc) (fs : list FName).

  (** * The remaining three

      \textsc{T-WriteFH}, \textsc{T-Insert} and \textsc{T-Replace}, written
      against the same toolkit.  Each is the two framing lemmas for the
      untouched variables and a handful of [TyOK]s for the touched ones; the
      only thing that varies is which of the three touched-variable forms occur
      and how many times.

      \textsc{T-WriteFH} is the smallest: it changes no observation at all, so
      only the cell framing applies, and the one touched variable stays
      [rcuFresh] with a field added. *)
  Lemma write_fresh_typed N γm γh γl γs γo γf γr γe γq E lw x xy on f oy g
        U Qc Sm Ob C Fl sn sy v vy N0 rest :
    ↑N ⊆ E ->
    FType f = RCUField ->
    on <> root -> oy <> root -> on <> oy ->
    Sm !! (x, lw) = Some on -> Ob !! on = Some sn -> Ofresh lw ∈ sn ->
    ~ U x lw ->
    Sm !! (xy, lw) = Some oy -> Ob !! oy = Some sy -> Oiter lw ∈ sy ->
    C !! (on, f) = Some v -> C !! (oy, g) = Some vy ->
    (forall h w, h <> f -> N0 h = Some w ->
       match w with
       | FVar z => exists oz sz, Sm !! (z, lw) = Some oz
                              /\ C !! (on, h) = Some (VLoc oz)
                              /\ Ob !! oz = Some sz /\ Oiter lw ∈ sz
       | FNull  => C !! (on, h) = Some VNull
       end) ->
    (forall h, In h fs ->
       (fun h' => if decide (h' = f) then Some (FVar xy) else N0 h') h = None ->
       C !! (on, h) = Some VNull) ->
    ReadsCell root C Sm lw rest (on, f) ->
    EnvOK root lw U Qc FType fs Sm Ob C Fl rest ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    writer γo γs γh γl γf lw Sm Ob C Fl
    ={E}=∗ writer γo γs γh γl γf lw Sm Ob (<[(on, f) := VLoc oy]> C) Fl
           ∗ ⌜EnvOK root lw U Qc FType fs Sm Ob (<[(on, f) := VLoc oy]> C) Fl
                ([(x, TFresh (fun h => if decide (h = f)
                                       then Some (FVar xy) else N0 h))]
                 ++ rest)⌝.
  Proof.
    iIntros (HN Hfrcu Hnr Hyr Hny Hstk Hob Hfr Hundf Hstky Hoby Hity Hcf Hcg
             Hold Hnull HRC Hrest) "#Hinv Hw".
    iDestruct "Hw" as "(Hlk & Hsm & Hob & Hcells & Hflo)".
    rewrite /obs_own (big_sepM_delete _ Ob on sn); [| exact Hob].
    iDestruct "Hob" as "[Hon Hobr]".
    rewrite (big_sepM_delete _ (delete on Ob) oy sy);
      [| rewrite lookup_delete_ne; [exact Hoby | exact Hny]].
    iDestruct "Hobr" as "[Hoy Hobr]".
    rewrite /cells (big_sepM_delete _ C (on, f) v); [| exact Hcf].
    iDestruct "Hcells" as "[Hptn Hcells]".
    assert (Hcg' : delete (on, f) C !! (oy, g) = Some vy).
    { rewrite lookup_delete_ne; [exact Hcg |].
      intros Hcc. injection Hcc as Ha Hb. by apply Hny. }
    iDestruct (big_sepM_lookup_acc _ Sm (x, lw) on Hstk with "Hsm")
      as "[Hsv Hsmback]".
    iMod (write_fresh_atomic FType root fs N γm γh γl γs γo γf γr γe γq E lw on f oy
            x g sn sy v vy (delete (on, f) C) HN Hfrcu Hnr Hyr Hfr Hity Hcg'
            with "Hinv Hlk Hon Hoy Hsv Hcells Hptn")
      as "(Hlk & Hon & Hoy & Hsv & Hcells & Hptn)".
    iModIntro.
    iSplitL "Hlk Hsv Hsmback Hon Hoy Hobr Hcells Hptn Hflo".
    { rewrite /writer /obs_own /cells. iFrame "Hlk Hflo".
      iSplitL "Hsv Hsmback"; [by iApply "Hsmback" |].
      iSplitL "Hon Hoy Hobr".
      - rewrite (big_sepM_delete _ Ob on sn); [| exact Hob]. iFrame "Hon".
        rewrite (big_sepM_delete _ (delete on Ob) oy sy);
          [| rewrite lookup_delete_ne; [exact Hoby | exact Hny]].
        iFrame.
      - rewrite (big_sepM_delete _ (<[(on, f) := VLoc oy]> C) (on, f)
                   (VLoc oy)); [| by rewrite lookup_insert_eq].
        iFrame "Hptn". by rewrite delete_insert_eq. }
    iPureIntro. apply EnvOK_step.
    - by apply EnvOK_cell.
    - intros y ty Hin. destruct Hin as [Heq | []].
      injection Heq as Hv1 Hv2. rewrite -Hv1 -Hv2. simpl.
      exists on, sn. repeat apply conj;
        [exact Hstk | exact Hob | exact Hfr | exact Hundf | |].
      + apply (FieldOK_update _ _ _ _ _ _ _ xy oy sy).
        * intros h w Hne Hw. specialize (Hold h w Hne Hw).
          destruct w as [z | ].
          -- destruct Hold as (oz & sz & Hsz & Hcz & Hoz & Hitz).
             exists oz, sz. repeat apply conj;
               [exact Hsz | | exact Hoz | exact Hitz].
             rewrite lookup_insert_ne; [exact Hcz |].
             intros Hcc. injection Hcc as Hb. by apply Hne.
          -- rewrite lookup_insert_ne; [exact Hold |].
             intros Hcc. injection Hcc as Hb. by apply Hne.
        * exact Hstky.
        * by rewrite lookup_insert_eq.
        * exact Hoby.
        * exact Hity.
      + intros h Hh Hnone.
        assert (Hhf : h <> f).
        { intros ->. rewrite decide_True in Hnone; [discriminate | reflexivity]. }
        rewrite lookup_insert_ne;
          [exact (Hnull h Hh Hnone) | intros Hcc; injection Hcc as Hb;
                                      by apply Hhf].
  Qed.

  (** \textsc{T-Insert} links a fresh node that already points at the node it
      displaces.  Three touched variables again: the parent is retargeted, the
      fresh node is promoted to the parent's field, and the displaced node
      moves one step further down -- which is the same promotion lemma applied
      to the cell the fresh node already held. *)
  Lemma insert_typed N γm γh γl γs γo γf γr γe γq E lw xp x xo op f on oo f4 rho f0
        U Qc Sm Ob C Fl sp so rest :
    ↑N ⊆ E ->
    on <> root -> In f4 fs -> In f0 fs ->
    op <> on -> on <> oo -> op <> oo ->
    Sm !! (xp, lw) = Some op -> Ob !! op = Some sp -> Oiter lw ∈ sp ->
    ~ U xp lw ->
    Sm !! (x, lw) = Some on -> Ob !! on = Some {[Ofresh lw]} -> ~ U x lw ->
    Sm !! (xo, lw) = Some oo -> Ob !! oo = Some so -> Oiter lw ∈ so ->
    ~ U xo lw ->
    C !! (op, f) = Some (VLoc oo) ->
    (forall g, In g fs ->
       C !! (on, g) = Some (if decide (g = f4) then VLoc oo else VNull)) ->
    hstarC C root rho = Some op ->
    ~ In (op, f) (pathcells C root rho) ->
    (forall rho1 rho2, rho1 ++ rho2 = rho ->
       exists o' sg', hstarC C root rho1 = Some o'
                   /\ Ob !! o' = Some sg' /\ Oiter lw ∈ sg') ->
    (forall rho1 rho2, rho1 ++ rho2 = rho -> hstarC C root rho1 <> Some on) ->
    ReadsObs root C Sm lw rest on ->
    ReadsCell root C Sm lw rest (op, f) ->
    EnvOK root lw U Qc FType fs Sm Ob C Fl rest ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    writer γo γs γh γl γf lw Sm Ob C Fl
    ={E}=∗ writer γo γs γh γl γf lw Sm
             (<[on := {[Oiter lw]}]> Ob) (<[(op, f) := VLoc on]> C) Fl
           ∗ ⌜EnvOK root lw U Qc FType fs Sm
                (<[on := {[Oiter lw]}]> Ob) (<[(op, f) := VLoc on]> C) Fl
                ([(xp, TItr rho (fun g => if decide (g = f)
                                          then Some (FVar x) else None));
                  (x, TItr (rho ++ [f])
                        (fun g => if decide (g = f4)
                                  then Some (FVar xo) else None));
                  (xo, TItr ((rho ++ [f]) ++ [f4]) (fun _ => None))]
                 ++ rest)⌝.
  Proof.
    iIntros (HN Hnr Hf4 Hf0 Hpn Hno Hpo Hstkp Hobp Hitp Hundp
             Hstkx Hobx Hundx Hstko Hobo Hito Hundo Hcf Hcells0 HpathC Hoff
             Hpre Hnon HRO HRC Hrest) "#Hinv Hw".
    iDestruct "Hw" as "(Hlk & Hsm & Hob & Hcells & Hflo)".
    rewrite /obs_own (big_sepM_delete _ Ob op sp); [| exact Hobp].
    iDestruct "Hob" as "[Hop Hobr]".
    rewrite (big_sepM_delete _ (delete op Ob) on {[Ofresh lw]});
      [| rewrite lookup_delete_ne; [exact Hobx | exact Hpn]].
    iDestruct "Hobr" as "[Hon Hobr]".
    rewrite /cells (big_sepM_delete _ C (op, f) (VLoc oo)); [| exact Hcf].
    iDestruct "Hcells" as "[Hptf Hcells]".
    iDestruct (big_sepM_lookup_acc _ Sm (x, lw) on Hstkx with "Hsm")
      as "[Hsv Hsmback]".
    assert (Hcells' : forall g, In g fs ->
              delete (op, f) C !! (on, g)
              = Some (if decide (g = f4) then VLoc oo else VNull)).
    { intros g Hg. rewrite lookup_delete_ne; [exact (Hcells0 g Hg) |].
      intros Hcc. injection Hcc as Ha Hb. by apply Hpn. }
    iMod (insert_atomic FType root fs N γm γh γl γs γo γf γr γe γq E lw op f on oo
            f4 rho x sp (delete (op, f) C) HN Hnr Hf4 Hitp
            (hstarC_delete C (op, f) root rho op Hoff HpathC) Hcells'
            with "Hinv Hlk Hop Hon Hsv Hcells Hptf")
      as "(Hlk & Hop & Hon & Hsv & Hcells & Hptf)".
    iModIntro.
    iSplitL "Hlk Hsv Hsmback Hop Hon Hobr Hcells Hptf Hflo".
    { rewrite /writer /obs_own /cells. iFrame "Hlk Hflo".
      iSplitL "Hsv Hsmback"; [by iApply "Hsmback" |].
      iSplitL "Hop Hon Hobr".
      - rewrite (big_sepM_delete _ (<[on := {[Oiter lw]}]> Ob) op sp);
          [| rewrite lookup_insert_ne; [exact Hobp | intros ->; by apply Hpn]].
        iFrame "Hop".
        rewrite (big_sepM_delete _ (delete op (<[on := {[Oiter lw]}]> Ob)) on
                   {[Oiter lw]});
          [| rewrite lookup_delete_ne; [by rewrite lookup_insert_eq | exact Hpn]].
        iFrame "Hon".
        rewrite delete_insert_ne; [| exact Hpn]. by rewrite delete_insert_eq.
      - rewrite (big_sepM_delete _ (<[(op, f) := VLoc on]> C) (op, f)
                   (VLoc on)); [| by rewrite lookup_insert_eq].
        iFrame "Hptf". by rewrite delete_insert_eq. }
    iPureIntro.
    (* the fresh node's new path, which the other two are stated against *)
    assert (HpathC' : hstarC (<[(op, f) := VLoc on]> C) root rho = Some op)
      by exact (hstarC_stable_cell C (op, f) (VLoc on) root rho op Hoff HpathC).
    assert (Hnewpath : hstarC (<[(op, f) := VLoc on]> C) root (rho ++ [f])
                       = Some on)
      by (apply (hstarC_snoc _ root rho op f on);
          [exact HpathC' | by rewrite lookup_insert_eq]).
    assert (Hcell4 : <[(op, f) := VLoc on]> C !! (on, f4) = Some (VLoc oo)).
    { rewrite lookup_insert_ne.
      - rewrite (Hcells0 f4 Hf4). by rewrite decide_True.
      - intros Hcc. injection Hcc as Ha Hb. by apply Hpn. }
    assert (Hprefix' : forall rho1 rho2, rho1 ++ rho2 = rho ++ [f] ->
              exists o' sg', hstarC (<[(op, f) := VLoc on]> C) root rho1
                             = Some o'
                          /\ <[on := {[Oiter lw]}]> Ob !! o' = Some sg'
                          /\ Oiter lw ∈ sg').
    { intros rho1 rho2 Happ.
      destruct (app_snoc_split rho1 rho2 rho f Happ) as [[r2 Hp] | ->].
      - destruct (Hpre rho1 r2 Hp) as (o' & sg' & Hp' & Hob' & Hit').
        exists o', sg'. repeat apply conj.
        + apply hstarC_stable_cell; [| exact Hp'].
          intros Hcc. apply Hoff. rewrite -Hp.
          exact (pathcells_prefix C root rho1 r2 (op, f) Hcc).
        + rewrite lookup_insert_ne; [exact Hob' |].
          intros Heq. rewrite -Heq in Hp'. exact (Hnon rho1 r2 Hp Hp').
        + exact Hit'.
      - exists on, {[Oiter lw]}. repeat apply conj;
          [exact Hnewpath | by rewrite lookup_insert_eq
           | by apply elem_of_singleton]. }
    apply EnvOK_step.
    - apply EnvOK_cell; [exact HRC |]. by apply EnvOK_obs.
    - intros y ty Hin.
      destruct Hin as [Heq | [Heq | [Heq | []]]]; injection Heq as Hv1 Hv2;
        rewrite -Hv1 -Hv2.
      + (* the parent, retargeted at the fresh node *)
        exists op, sp. repeat apply conj.
        * exact Hstkp.
        * rewrite lookup_insert_ne; [exact Hobp | intros ->; by apply Hpn].
        * exact Hitp.
        * exact Hundp.
        * apply (FieldOK_update _ _ _ _ _ _ _ x on {[Oiter lw]});
            [intros h w _ Hc; discriminate Hc | exact Hstkx
             | by rewrite lookup_insert_eq | by rewrite lookup_insert_eq
             | by apply elem_of_singleton].
        * exact HpathC'.
        * intros rho1 rho2 Happ. destruct (Hpre rho1 rho2 Happ)
            as (o' & sg' & Hp' & Hob' & Hit').
          exists o', sg'. repeat apply conj.
          -- apply hstarC_stable_cell; [| exact Hp'].
             intros Hcc. apply Hoff. rewrite -Happ.
             exact (pathcells_prefix C root rho1 rho2 (op, f) Hcc).
          -- rewrite lookup_insert_ne; [exact Hob' |].
             intros Heq. rewrite -Heq in Hp'. exact (Hnon rho1 rho2 Happ Hp').
          -- exact Hit'.
      + (* the fresh node, promoted, keeping its one field *)
        exists on, {[Oiter lw]}. repeat apply conj.
        * exact Hstkx.
        * by rewrite lookup_insert_eq.
        * by apply elem_of_singleton.
        * exact Hundx.
        * apply (FieldOK_update _ _ _ _ _ _ _ xo oo so);
            [intros h w _ Hc; discriminate Hc | exact Hstko | exact Hcell4 | |].
          -- rewrite lookup_insert_ne; [exact Hobo | intros ->; by apply Hno].
          -- exact Hito.
        * exact Hnewpath.
        * exact Hprefix'.
      + (* the displaced node, one step further down *)
        apply (TyOK_promoted root lw U Qc FType fs Sm _ _ Fl xo oo on f4
                 (rho ++ [f]) so (fun _ => None)).
        * exact Hstko.
        * exact Hundo.
        * rewrite lookup_insert_ne; [exact Hobo | intros ->; by apply Hno].
        * exact Hito.
        * intros h w Hc. discriminate Hc.
        * exact Hnewpath.
        * exact Hcell4.
        * intros rho1 rho2 Happ.
          destruct (app_snoc_split rho1 rho2 (rho ++ [f]) f4 Happ)
            as [[r2 Hp] | ->].
          -- exact (Hprefix' rho1 r2 Hp).
          -- exists oo, so. repeat apply conj.
             ++ exact (hstarC_snoc _ root (rho ++ [f]) on f4 oo
                         Hnewpath Hcell4).
             ++ rewrite lookup_insert_ne;
                  [exact Hobo | intros ->; by apply Hno].
             ++ exact Hito.
  Qed.

  (** \textsc{T-Replace} is the last, and it is the two forms of the other two
      at once: the fresh node is promoted to the parent's field and the node it
      replaces is demoted to \unlk{}.  Two observation entries change, so the
      observation framing applies twice. *)
  Lemma replace_typed N γm γh γl γs γo γf γr γe γq E lw xp x xo op f oo on rho f0
        U Qc Sm Ob C Fl Fr val valo sp rest :
    ↑N ⊆ E ->
    on <> oo -> on <> root -> In f0 fs ->
    op <> on -> op <> oo ->
    Sm !! (xp, lw) = Some op -> Ob !! op = Some sp -> Oiter lw ∈ sp ->
    ~ U xp lw ->
    Sm !! (x, lw) = Some on -> Ob !! on = Some {[Ofresh lw]} -> ~ U x lw ->
    Sm !! (xo, lw) = Some oo -> Ob !! oo = Some {[Oiter lw]} -> ~ U xo lw ->
    C !! (op, f) = Some (VLoc oo) ->
    (forall g, In g fs -> C !! (on, g) = Some (valo g)) ->
    (forall g, In g fs -> C !! (oo, g) = Some (valo g)) ->
    hstarC C root rho = Some op ->
    ~ In (op, f) (pathcells C root rho) ->
    (forall rho1 rho2, rho1 ++ rho2 = rho ->
       exists o' sg', hstarC C root rho1 = Some o'
                   /\ Ob !! o' = Some sg' /\ Oiter lw ∈ sg') ->
    (forall rho1 rho2, rho1 ++ rho2 = rho -> hstarC C root rho1 <> Some on) ->
    (forall rho1 rho2, rho1 ++ rho2 = rho -> hstarC C root rho1 <> Some oo) ->
    FrCells Fr fs C val ->
    (forall q g, val q g <> VLoc oo) ->
    (* the replaced node has one predecessor, which is No-Sharing, and neither
       node is the root.  The rest of the environment is framed by the mirror
       lemma rather than the other two: a replacement moves what the paths pass
       through, so what survives is that the fresh node is indistinguishable
       from the one it replaces. *)
    (forall b h, C !! (b, h) = Some (VLoc oo) -> (b, h) = (op, f)) ->
    oo <> root ->
    MirrorOK root C Sm lw rest op f oo on fs ->
    EnvOK root lw U Qc FType fs Sm Ob C Fl rest ->
    rcu_invT FType (phys γm γh γl γs root fs) N γo γf γr γe γq -∗
    writer γo γs γh γl γf lw Sm Ob C Fl -∗
    fr_frag γr Fr
    ={E}=∗ writer γo γs γh γl γf lw Sm
             (<[on := {[Oiter lw]}]> (<[oo := {[Ounlk lw]}]> Ob))
             (<[(op, f) := VLoc on]> C) Fl
           ∗ fr_frag γr Fr
           ∗ ⌜EnvOK root lw U Qc FType fs Sm
                (<[on := {[Oiter lw]}]> (<[oo := {[Ounlk lw]}]> Ob))
                (<[(op, f) := VLoc on]> C) Fl
                ([(xp, TItr rho (fun g => if decide (g = f)
                                          then Some (FVar x) else None));
                  (x, TItr (rho ++ [f]) (fun _ => None));
                  (xo, TUnlinked)] ++ rest)⌝.
  Proof.
    iIntros (HN Hno Hnr Hf0 Hpn Hpo Hstkp Hobp Hitp Hundp
             Hstkx Hobx Hundx Hstko Hobo Hundo Hcf Hcn0 Hco0 HpathC Hoff
             Hpre Hnon Hnoo HFrC Hnf Hsole Hoor HMir Hrest) "#Hinv Hw Hfrg".
    iDestruct "Hw" as "(Hlk & Hsm & Hob & Hcells & Hflo)".
    rewrite /obs_own (big_sepM_delete _ Ob on {[Ofresh lw]}); [| exact Hobx].
    iDestruct "Hob" as "[Hon Hobr]".
    rewrite (big_sepM_delete _ (delete on Ob) oo {[Oiter lw]});
      [| rewrite lookup_delete_ne; [exact Hobo | intros ->; by apply Hno]].
    iDestruct "Hobr" as "[Hoo Hobr]".
    rewrite (big_sepM_delete _ (delete oo (delete on Ob)) op sp);
      [| rewrite lookup_delete_ne; [| intros ->; by apply Hpo];
         rewrite lookup_delete_ne; [exact Hobp | intros ->; by apply Hpn]].
    iDestruct "Hobr" as "[Hop Hobr]".
    rewrite /cells (big_sepM_delete _ C (op, f) (VLoc oo)); [| exact Hcf].
    iDestruct "Hcells" as "[Hptf Hcells]".
    iDestruct (big_sepM_lookup_acc _ Sm (x, lw) on Hstkx with "Hsm")
      as "[Hsv Hsmback]".
    assert (Hcn' : forall g, In g fs ->
              delete (op, f) C !! (on, g) = Some (valo g)).
    { intros g Hg. rewrite lookup_delete_ne; [exact (Hcn0 g Hg) |].
      intros Hcc. injection Hcc as Ha Hb. by apply Hpn. }
    assert (Hco' : forall g, In g fs ->
              delete (op, f) C !! (oo, g) = Some (valo g)).
    { intros g Hg. rewrite lookup_delete_ne; [exact (Hco0 g Hg) |].
      intros Hcc. injection Hcc as Ha Hb. by apply Hpo. }
    assert (HFrC' : FrCells Fr fs (delete (op, f) C) val).
    { intros q g Hq Hg. rewrite lookup_delete_ne; [exact (HFrC q g Hq Hg) |].
      intros Hcc. injection Hcc as Ha Hb.
      pose proof (HFrC q g Hq Hg) as Hv. rewrite Ha Hb in Hcf.
      rewrite Hcf in Hv. injection Hv as Hv. exact (Hnf q g (eq_sym Hv)). }
    iMod (replace_atomic FType root fs N γm γh γl γs γo γf γr γe γq E lw op f oo on
            rho x f0 sp Fr val valo (delete (op, f) C) HN Hno Hnr Hf0 Hitp
            HFrC' (hstarC_delete C (op, f) root rho op Hoff HpathC) Hcn' Hco'
            Hnf with "Hinv Hlk Hop Hon Hoo Hsv Hcells Hptf Hfrg")
      as "(Hlk & Hop & Hon & Hoo & Hsv & Hcells & Hptf & Hfrg)".
    iModIntro.
    iSplitL "Hlk Hsv Hsmback Hop Hon Hoo Hobr Hcells Hptf Hflo".
    { rewrite /writer /obs_own /cells. iFrame "Hlk Hflo".
      iSplitL "Hsv Hsmback"; [by iApply "Hsmback" |].
      iSplitL "Hop Hon Hoo Hobr".
      - rewrite big_sepM_insert_delete. iFrame "Hon".
        rewrite delete_insert_ne; [| intros ->; by apply Hno].
        rewrite big_sepM_insert_delete. iFrame "Hoo".
        rewrite (big_sepM_delete _ (delete oo (delete on Ob)) op sp);
          [| rewrite lookup_delete_ne; [| intros ->; by apply Hpo];
             rewrite lookup_delete_ne; [exact Hobp | intros ->; by apply Hpn]].
        iFrame.
      - rewrite (big_sepM_delete _ (<[(op, f) := VLoc on]> C) (op, f)
                   (VLoc on)); [| by rewrite lookup_insert_eq].
        iFrame "Hptf". by rewrite delete_insert_eq. }
    iFrame. iPureIntro.
    assert (HpathC' : hstarC (<[(op, f) := VLoc on]> C) root rho = Some op)
      by exact (hstarC_stable_cell C (op, f) (VLoc on) root rho op Hoff HpathC).
    assert (Hnewpath : hstarC (<[(op, f) := VLoc on]> C) root (rho ++ [f])
                       = Some on)
      by (apply (hstarC_snoc _ root rho op f on);
          [exact HpathC' | by rewrite lookup_insert_eq]).
    assert (Hprefix : forall rho1 rho2, rho1 ++ rho2 = rho ->
              exists o' sg', hstarC (<[(op, f) := VLoc on]> C) root rho1
                             = Some o'
                          /\ <[on := {[Oiter lw]}]>
                               (<[oo := {[Ounlk lw]}]> Ob) !! o' = Some sg'
                          /\ Oiter lw ∈ sg').
    { intros rho1 rho2 Happ. destruct (Hpre rho1 rho2 Happ)
        as (o' & sg' & Hp' & Hob' & Hit').
      exists o', sg'. repeat apply conj.
      - apply hstarC_stable_cell; [| exact Hp'].
        intros Hcc. apply Hoff. rewrite -Happ.
        exact (pathcells_prefix C root rho1 rho2 (op, f) Hcc).
      - rewrite lookup_insert_ne;
          [| intros Heq; rewrite -Heq in Hp';
             exact (Hnon rho1 rho2 Happ Hp')].
        rewrite lookup_insert_ne;
          [exact Hob' | intros Heq; rewrite -Heq in Hp';
                        exact (Hnoo rho1 rho2 Happ Hp')].
      - exact Hit'. }
    apply EnvOK_step.
    - apply (EnvOK_mirror root lw U Qc FType fs Sm Ob C Fl rest op f oo on);
        [exact Hcf | | exact Hsole | intros ->; by apply Hpn
         | exact Hpo | intros ->; by apply Hno
         | exact Hoor | exact Hnr | exact HMir | exact Hrest].
      intros g Hg. by rewrite (Hcn0 g Hg) (Hco0 g Hg).
    - intros y ty Hin.
      destruct Hin as [Heq | [Heq | [Heq | []]]]; injection Heq as Hv1 Hv2;
        rewrite -Hv1 -Hv2.
      + exists op, sp. repeat apply conj.
        * exact Hstkp.
        * rewrite lookup_insert_ne; [| intros ->; by apply Hpn].
          rewrite lookup_insert_ne; [exact Hobp | intros ->; by apply Hpo].
        * exact Hitp.
        * exact Hundp.
        * apply (FieldOK_update _ _ _ _ _ _ _ x on {[Oiter lw]});
            [intros h w _ Hc; discriminate Hc | exact Hstkx
             | by rewrite lookup_insert_eq | by rewrite lookup_insert_eq
             | by apply elem_of_singleton].
        * exact HpathC'.
        * exact Hprefix.
      + apply (TyOK_promoted root lw U Qc FType fs Sm _ _ Fl x on op f rho
                 {[Oiter lw]} (fun _ => None)).
        * exact Hstkx.
        * exact Hundx.
        * by rewrite lookup_insert_eq.
        * by apply elem_of_singleton.
        * intros h w Hc. discriminate Hc.
        * exact HpathC'.
        * by rewrite lookup_insert_eq.
        * intros rho1 rho2 Happ.
          destruct (app_snoc_split rho1 rho2 rho f Happ) as [[r2 Hp] | ->].
          -- exact (Hprefix rho1 r2 Hp).
          -- exists on, {[Oiter lw]}. repeat apply conj;
               [exact Hnewpath | by rewrite lookup_insert_eq
                | by apply elem_of_singleton].
      + exists oo, {[Ounlk lw]}. repeat apply conj.
        * exact Hstko.
        * rewrite lookup_insert_ne; [| intros ->; by apply Hno].
          by rewrite lookup_insert_eq.
        * by apply elem_of_singleton.
        * exact Hundo.
  Qed.

End typed_rest.

Print Assumptions write_fresh_typed.
Print Assumptions insert_typed.
Print Assumptions replace_typed.

(** * Where this stands

    All fifteen atomic actions are restated against the Iris invariant, and
    eight are closed triples: parameter-free, with every premise either derived
    from the invariant or carried by a resource the thread holds.  They are
    \textsc{Free}, all five heap mutations, \textsc{T-Alloc}, and the binding
    rules -- which is to say the entire write side.  The seven that are not are
    the six RCU control actions and the reader's read.

    Four kinds of premise, four ways of discharging them.

    *Observational* premises come from the thread's own ghost fragment:
    exclusive control of its entry at a node, plus the agreement lemma.  The
    typing side condition becomes a resource.

    *Physical* premises come from points-to, the lock token and the stack
    fragment -- none of which existed before the field list made the heap
    finite.

    *Path* premises come from [hstarC] on the thread's cell map: a fold of
    lookups in what it owns.
    What that derivation does not use is the point: no invariant, no uniqueness,
    no shape condition.  Reachability by a *named* path is a local fact about
    the cells on it.

    *Negative* premises -- that something is absent -- cannot come from a
    fragment at all, and they come from invariants.  "No free-list entry here"
    is FLD with WULK, or with FNR for a fresh node.  "This fresh node is
    unreachable" is FR with the pinned root.  "No other thread observes this
    node as fresh" is the repaired WFresh.  "Every detaching observation is the
    writer's" is WUNLK.  "This node is not detached" is WULK and FNR together.
    That is a concrete answer to what the global invariants are *for* in a
    separation-logic reading: they are exactly the facts a resource cannot
    carry, and three of the five just named are invariants this development
    adds.

    Two premises are of no such kind, and each needed something built.

    The aliasing premise the unlinking rules carry -- no \frsh{} reference
    anywhere points at the node being unlinked -- is negative and is not an
    invariant.  What discharges it in the type system is the environment, whose
    denotation is an intersection over all of it.  Here the invariant records
    that the fresh nodes are *enumerated*, the thread holds the enumeration and
    those nodes' cells, and the premise becomes [forall q g, val q g <> VLoc oz]
    -- a statement about values the thread owns, and exactly what the checker's
    [noFreshPointsAt] decides by walking the environment.  The quantifier does
    not disappear; it moves from the shared state, where nothing could discharge
    it, to the thread's own resources, where the type system already had it.

    \textsc{T-Alloc}'s six premises say the new location is unallocated,
    unreferenced, pointed at by nothing, unobserved, unlisted and not the root.
    Those look like they need an operational semantics -- something has to
    *produce* a fresh address.  They do not.  An allocator is a function of the
    state, and the state is now finite in every component, so the locations used
    for anything form a finite set and [fresh] of it satisfies all six at once.
    The field-list repair pays twice: it made the heap representable, and it
    made the allocator constructible.

    What is left is the read side and the protocol, and the two obstacles are
    specific rather than general.

    The reader's read cannot be stated at all, because [pt] is exclusive: a
    reader must read cells the writer also holds, and an exclusive points-to
    forbids it.  The repair is a fractional or discardable-fraction heap, which
    is standard and which changes the camera under everything above.  Worth
    saying plainly: the write side needed no fractions, and the read side cannot
    be done without them.

    \textsc{WriteBegin} asks that the lock is free and \textsc{SyncStop} that
    no thread is still bounding.  Those are the two points where the protocol
    *tests* or *waits on* shared state rather than acting on state it owns, and
    neither is a fact any thread can hold.  They are what an operational
    semantics is for -- a compare-and-set and a wait loop -- and they are the
    only two places in the system that need one.  \textsc{ReadBegin},
    \textsc{ReadEnd}, \textsc{SyncStart} and \textsc{WriteEnd} need reader-set
    and bounding-set tokens, which is the lock's construction done twice more.

    One last thing the field-list repair exposed, recorded rather than fixed:
    the mutation rules are stated with [forall g, FType g = RCUField], which
    with a finite field list contradicts the class declaration the allocation
    rule needs, so the two cannot appear in one lemma.  The honest repair is to
    restrict No-Sharing's field conditions to declared fields. *)
