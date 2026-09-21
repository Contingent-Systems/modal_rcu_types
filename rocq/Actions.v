(** * Actions: joining the ghost updates to the pure state.

    Milestone 4c.  [IrisGhost.v] can change the ghost maps; [Denotations.v] can
    say what the resulting *pure* state must satisfy.  Nothing so far connects
    them: an atomic action changes the heap and the observation map together,
    and the invariant has to be re-established on the state those two
    reconstruct.

    This file is that connection.  It is short, and deliberately so -- if the
    two representations were not lined up, it would not be.  The content is that
    [to_LState] commutes with both kinds of update:

      - a field write moves through untouched, so every reachability result of
        [HeapPaths.v] applies to the post-state as stated;
      - the ghost update of [obs_add] shows up in the reconstructed state as
        exactly the observation added, and leaves the others alone.

    With those, an action lemma about the pure state is an action lemma about
    the state under the invariant.

    Checked with Rocq 9.2, axiom-free. *)

From iris.algebra Require Import auth gmap gset.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.
From stdpp Require Import gmap sets.
From RCU Require Import WellFormed HeapPaths IrisGhost Denotations.

(** ** The machine-state transformer for a field write *)

Definition write_ms (m : MState) (o : Loc) (f : FName) (v : Val) : MState :=
  {| stk := stk m;
     hp  := upd (hp m) o f v;
     lk  := lk m;
     rt  := rt m;
     rds := rds m;
     bnd := bnd m |}.

(** A write changes the heap and nothing else, and the reconstruction is
    transparent to it.  These are all [reflexivity]; that is the point. *)

Lemma to_LState_write_hp m O U T F o f v :
  hp (ms (to_LState (write_ms m o f v) O U T F)) = upd (hp m) o f v.
Proof. reflexivity. Qed.

Lemma to_LState_write_rt m O U T F o f v :
  rt (ms (to_LState (write_ms m o f v) O U T F)) = rt m.
Proof. reflexivity. Qed.

Lemma to_LState_write_stk m O U T F o f v :
  stk (ms (to_LState (write_ms m o f v) O U T F)) = stk m.
Proof. reflexivity. Qed.

Lemma to_LState_write_obsv m O U T F o f v :
  obsv (to_LState (write_ms m o f v) O U T F) = obsv (to_LState m O U T F).
Proof. reflexivity. Qed.

Lemma to_LState_write_flist m O U T F o f v :
  flist (to_LState (write_ms m o f v) O U T F) = flist (to_LState m O U T F).
Proof. reflexivity. Qed.

(** ** The observation update

    [obs_add] takes the authority from [O] to [{[o := {[ob]}]} . O].  What that
    means for the reconstructed state is the following two facts: the new
    observation is recorded at [o], and nothing else changes.  Together they are
    what lets an action lemma reason about the post-state's observations. *)

(** Destructing the map lookup directly does not work here: the occurrence the
    rewrite leaves in the goal elaborates at the camera level and is not the
    term [destruct] abstracts.  Stating the case analysis over a bound variable
    sidesteps it, and unification bridges the two. *)
Lemma option_op_mem (x : gset obs) (my : option (gset obs)) (ob : obs) :
  ob ∈ x -> match Some x ⋅ my with Some s => ob ∈ s | None => False end.
Proof. intros Hin. destruct my as [y|]; simpl; rewrite ?gset_op; set_solver. Qed.

Lemma option_op_mem_r (x : gset obs) (my : option (gset obs)) (ob : obs) :
  match my with Some s => ob ∈ s | None => False end ->
  match Some x ⋅ my with Some s => ob ∈ s | None => False end.
Proof. destruct my as [y|]; simpl; [rewrite ?gset_op; set_solver | done]. Qed.

Lemma to_LState_obs_added m O U T F o ob :
  obsv (to_LState m ({[o := {[ob]}]} ⋅ O) U T F) o ob.
Proof.
  unfold to_LState; simpl.
  rewrite lookup_op lookup_singleton_eq.
  apply option_op_mem. set_solver.
Qed.

Lemma to_LState_obs_kept m O U T F o ob x :
  x <> o ->
  forall obx, obsv (to_LState m ({[o := {[ob]}]} ⋅ O) U T F) x obx
          <-> obsv (to_LState m O U T F) x obx.
Proof.
  intros Hne obx. simpl.
  rewrite lookup_op lookup_singleton_ne //.
  by rewrite left_id.
Qed.

(** Observations already present survive the update. *)
Lemma to_LState_obs_mono m O U T F o ob x obx :
  obsv (to_LState m O U T F) x obx ->
  obsv (to_LState m ({[o := {[ob]}]} ⋅ O) U T F) x obx.
Proof.
  simpl. destruct (decide (x = o)) as [->|Hne].
  - rewrite lookup_op lookup_singleton_eq. apply option_op_mem_r.
  - rewrite lookup_op lookup_singleton_ne //. by rewrite left_id.
Qed.

(** ** The three mutations, on the state under the invariant

    Restating the action lemmas of [Denotations.v] over [to_LState] and
    [write_ms].  Each is the pure lemma with the reconstruction unfolded, which
    the commutation lemmas above make immediate -- so the representation change
    costs nothing, which is the property worth having. *)

Section actions.

  Variable FType : FName -> FieldKind.

  Theorem replace_post_UNQR m O U T F t xr xp xo xn f rho rho1 N Np op oo on :
    let s := to_LState m O U T F in
    (forall g, FType g = RCUField) ->
    UNQR_h (hp m) (rt m) ->
    FR s ->
    D_rcuRoot  s t xr ->
    D_rcuItr   s t xp rho  Np ->
    D_rcuItr   s t xo rho1 N ->
    D_rcuFresh FType s t xn N ->
    stk m xp t = Some op ->
    stk m xo t = Some oo ->
    stk m xn t = Some on ->
    xr <> xn ->
    Np f = Some (FVar xo) ->
    (forall g, FType g = RCUField -> N g <> None) ->
    UNQR_h (hp (ms (to_LState (write_ms m op f (VLoc on)) O U T F)))
           (rt (ms (to_LState (write_ms m op f (VLoc on)) O U T F))).
  Proof.
    intros s Hall HU HFR Hroot Hp Ho Hn Hstkp Hstko Hstkn Hne Hpf Hdom.
    rewrite to_LState_write_hp to_LState_write_rt.
    exact (replace_preserves_UNQR FType s t xr xp xo xn f rho rho1 N Np op oo on
             Hall HU HFR Hroot Hp Ho Hn Hstkp Hstko Hstkn Hne Hpf Hdom).
  Qed.

  Theorem unlink_post_UNQR m O U T F t xx xz xw f1 f2 rho Nx Nz ox oz ow :
    let s := to_LState m O U T F in
    UNQR_h (hp m) (rt m) ->
    D_rcuItr s t xx rho Nx ->
    D_rcuItr s t xz (rho ++ [f1]) Nz ->
    stk m xx t = Some ox ->
    stk m xz t = Some oz ->
    stk m xw t = Some ow ->
    Nx f1 = Some (FVar xz) ->
    Nz f2 = Some (FVar xw) ->
    UNQR_h (hp (ms (to_LState (write_ms m ox f1 (VLoc ow)) O U T F)))
           (rt (ms (to_LState (write_ms m ox f1 (VLoc ow)) O U T F))).
  Proof.
    intros s HU Hx Hz Hstkx Hstkz Hstkw Hf1 Hf2.
    rewrite to_LState_write_hp to_LState_write_rt.
    exact (unlink_preserves_UNQR s t xx xz xw f1 f2 rho Nx Nz ox oz ow
             HU Hx Hz Hstkx Hstkz Hstkw Hf1 Hf2).
  Qed.

  Theorem insert_post_UNQR m O U T F t xr xp xo xn f f4 rho N1 Np op oo on :
    let s := to_LState m O U T F in
    (forall g, FType g = RCUField) ->
    UNQR_h (hp m) (rt m) ->
    FR s ->
    D_rcuRoot  s t xr ->
    D_rcuItr   s t xp rho Np ->
    D_rcuFresh FType s t xn N1 ->
    stk m xp t = Some op ->
    stk m xo t = Some oo ->
    stk m xn t = Some on ->
    xr <> xn ->
    Np f  = Some (FVar xo) ->
    N1 f4 = Some (FVar xo) ->
    (forall g, N1 g <> None -> g <> f4 -> N1 g = Some FNull) ->
    UNQR_h (hp (ms (to_LState (write_ms m op f (VLoc on)) O U T F)))
           (rt (ms (to_LState (write_ms m op f (VLoc on)) O U T F))).
  Proof.
    intros s Hall HU HFR Hroot Hp Hn Hstkp Hstko Hstkn Hne Hpf Hnf4 Hother.
    rewrite to_LState_write_hp to_LState_write_rt.
    exact (insert_preserves_UNQR FType s t xr xp xo xn f f4 rho N1 Np op oo on
             Hall HU HFR Hroot Hp Hn Hstkp Hstko Hstkn Hne Hpf Hnf4 Hother).
  Qed.

End actions.

(** ** Revoking an observation

    This is where the first version of the ghost state failed, and it is worth
    recording what the failure was, because the shape of the fix is the
    interesting part.

    Unlinking must *withdraw* an observation: the replaced node loses
    [iterator] and gains [unlinked], and WULK makes those exclusive.  The first
    value camera was [gsetUR], whose operation is union.  All its elements are
    [CoreId], so every fragment was persistent -- an observation once handed out
    was held forever, and by [observes_mem] the authority had to go on recording
    it forever too.  No action that unlinks could then re-establish the
    invariant.  The lemma below is the positive form of what was impossible:
    holding a location's entry, a thread can replace it outright, and the
    reconstructed state afterwards records the new observations and not the old.

    The union camera is right for a quantity that only grows.  Observations are
    not one. *)

Section revocation.
  Context `{!rcuG Σ}.

  (** Unlinking, at the level of the ghost state: the writer holds the entry for
      [o], replaces its iterator observation by an unlinked one, and the
      reconstructed state reflects exactly that. *)
  Lemma obs_unlink_step γ O m U T F o lw t :
    obs_auth γ O -∗ obs_ctl γ o {[Oiter lw]} ==∗
      obs_auth γ (<[o := {[Ounlk t]}]> O)
      ∗ obs_ctl γ o {[Ounlk t]}
      ∗ ⌜obsv (to_LState m (<[o := {[Ounlk t]}]> O) U T F) o (Ounlk t)⌝
      ∗ ⌜~ obsv (to_LState m (<[o := {[Ounlk t]}]> O) U T F) o (Oiter lw)⌝.
  Proof.
    iIntros "Ha Hf".
    iMod (obs_set with "Ha Hf") as "[Ha Hf]".
    iModIntro. iFrame. iPureIntro. split.
    - simpl. rewrite lookup_insert_eq. set_solver.
    - simpl. rewrite lookup_insert_eq. set_solver.
  Qed.

  (** Entries elsewhere are untouched, which is what lets the rest of
      WellFormed survive the step. *)
  Lemma obs_unlink_step_ne m O U T F o t x ob :
    x <> o ->
    (obsv (to_LState m (<[o := {[Ounlk t]}]> O) U T F) x ob
     <-> obsv (to_LState m O U T F) x ob).
  Proof. intros Hne. simpl. by rewrite lookup_insert_ne. Qed.

End revocation.

(** ** FPI for unlinking

    The invariant whose failure forced the repair to T-Replace and T-UnlinkH.
    Now that an observation can be withdrawn, the case can be stated, and the
    repaired premise is visible as the hypothesis [Hno_fresh_pred] below: no
    fresh node points at the node being unlinked.  Without it the conclusion is
    false, which is what [FPI_not_preserved_by_replace] exhibits.

    The other hypotheses are pre-state facts.  [Hox_not_fresh] says the node
    written is not itself fresh -- it is an [rcuItr] in both rules -- and is
    what rules out the newly created edge originating at a fresh node.

    The argument does not depend on which rule caused the write: it needs only
    that one field was written and one node lost its iterator observation.  So
    it is stated once, and T-UnlinkH and T-Replace are instances -- the first
    writing [x.f1 := r] and unlinking [z], the second writing [p.f := n] and
    unlinking [o]. *)

Section fpi.

  Variable FType : FName -> FieldKind.

  Theorem write_preserves_FPI m O U T F lw ox f1 oz ow tz :
    let s  := to_LState m O U T F in
    let s' := to_LState (write_ms m ox f1 (VLoc ow))
                        (<[oz := {[Ounlk tz]}]> O) U T F in
    lk m = Some lw ->
    FPI FType s ->
    (forall tf, ~ obsv s ox (Ofresh tf)) ->
    (forall tf, ~ obsv s oz (Ofresh tf)) ->
    (forall op tf g, obsv s op (Ofresh tf) -> FType g = RCUField ->
        hp m op g <> Some (VLoc oz)) ->
    FPI FType s'.
  Proof.
    intros s s' Hlk HFPI Hox_not_fresh Hoz_not_fresh Hno_fresh_pred.
    intros o f o' t lw' Hfresh Hedge HF Hlk'.
    (* the lock is untouched by the write *)
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    (* o is not the unlinked node, so its observations are the old ones *)
    assert (Hone : o <> oz).
    { intros ->. simpl in Hfresh. rewrite lookup_insert_eq in Hfresh.
      set_solver. }
    assert (Hfresh0 : obsv s o (Ofresh t)).
    { revert Hfresh. subst s s'. simpl. by rewrite lookup_insert_ne. }
    (* the written edge cannot start at a fresh node *)
    assert (Hedge0 : hp m o f = Some (VLoc o')).
    { unfold Edge in Hedge. subst s'.
      rewrite to_LState_write_hp in Hedge.
      destruct (Nat.eq_dec o ox) as [->|Hno].
      - exfalso. exact (Hox_not_fresh t Hfresh0).
      - rewrite upd_other in Hedge; [exact Hedge |].
        intros HH. injection HH as HH1 _. contradiction. }
    (* so the edge is one the pre-state had, and FPI applies to it *)
    assert (Hiter0 : obsv s o' (Oiter lw))
      by exact (HFPI o f o' t lw Hfresh0 Hedge0 HF Hlk).
    (* and o' is not the unlinked node, by the repaired premise *)
    assert (Ho'ne : o' <> oz)
      by (intros ->; exact (Hno_fresh_pred o t f Hfresh0 HF Hedge0)).
    subst s s'. simpl. by rewrite lookup_insert_ne.
  Qed.

  (** T-UnlinkH: writes [x.f1 := r], unlinks [z]. *)
  Corollary unlink_preserves_FPI m O U T F lw ox f1 oz ow tz :
    lk m = Some lw ->
    FPI FType (to_LState m O U T F) ->
    (forall tf, ~ obsv (to_LState m O U T F) ox (Ofresh tf)) ->
    (forall tf, ~ obsv (to_LState m O U T F) oz (Ofresh tf)) ->
    (forall op tf g, obsv (to_LState m O U T F) op (Ofresh tf) ->
        FType g = RCUField -> hp m op g <> Some (VLoc oz)) ->
    FPI FType (to_LState (write_ms m ox f1 (VLoc ow))
                         (<[oz := {[Ounlk tz]}]> O) U T F).
  Proof. apply write_preserves_FPI. Qed.

  (** T-Replace: writes [p.f := n], unlinks [o].  Same lemma, different
      instance -- the fresh node written is [n], and the node losing its
      iterator observation is the one it replaces. *)
  Corollary replace_preserves_FPI m O U T F lw op f oo on to :
    lk m = Some lw ->
    FPI FType (to_LState m O U T F) ->
    (forall tf, ~ obsv (to_LState m O U T F) op (Ofresh tf)) ->
    (forall tf, ~ obsv (to_LState m O U T F) oo (Ofresh tf)) ->
    (forall opn tf g, obsv (to_LState m O U T F) opn (Ofresh tf) ->
        FType g = RCUField -> hp m opn g <> Some (VLoc oo)) ->
    FPI FType (to_LState (write_ms m op f (VLoc on))
                         (<[oo := {[Ounlk to]}]> O) U T F).
  Proof. apply write_preserves_FPI. Qed.

End fpi.

(** ** Status

    The two representations are lined up: a field write is transparent to
    [to_LState], and a ghost observation update appears in the reconstructed
    state as exactly the observation added.  So the pure action lemmas are
    action lemmas about the state the invariant holds, and the remaining work is
    the other invariants for each action rather than any further plumbing.

    The one piece still abstract is [phys] in [rcu_inv]: it is a parameter, so
    the Hoare triple for an action cannot be stated until the language's heap
    assertion is chosen.  That is a choice about the object language, not about
    this development. *)

Print Assumptions to_LState_obs_added.
Print Assumptions to_LState_obs_kept.
Print Assumptions replace_post_UNQR.
Print Assumptions unlink_post_UNQR.
Print Assumptions insert_post_UNQR.
Print Assumptions obs_unlink_step.
Print Assumptions obs_unlink_step_ne.
Print Assumptions write_preserves_FPI.
Print Assumptions unlink_preserves_FPI.
Print Assumptions replace_preserves_FPI.

(** ** The reader side

    Reader rules are trivial as rules -- T-ReadS and T-ReadH both just produce
    another [rcuItr] -- and the content is entirely in what acquiring an
    observation obliges.  A reader following [x.f] to [z] does not already
    observe [z]; the action must add [iterator t] to *its own* entry for [z],
    which is the per-thread update.

    The obligation is IFL.  If [z] is already on the free list, some grace
    period is waiting on a set of threads before reclaiming it, and a reader
    acquiring a reference to [z] must be in that set -- otherwise it could hold
    the reference past the reclamation it is not delaying.  This is the
    condition RCU implementations discharge by having a reader that entered its
    critical section after SyncStart not reach unlinked nodes at all. *)

Section readers.

  Variable FType : FName -> FieldKind.

  (** Acquiring an observation preserves IFL exactly when the acquiring thread
      already bounds any pending reclamation of the node. *)
  Theorem reader_acquire_preserves_IFL m Og U T F t z sz :
    let s  := to_LState_t m Og U T F in
    let s' := to_LState_t m (<[(z, t) := sz ∪ {[Oiter t]}]> Og) U T F in
    IFL s ->
    (forall ob, ob ∈ sz -> exists S, Og !! (z, t) = Some S /\ ob ∈ S) ->
    (forall Tr, flist s z = Some Tr -> Tr t) ->
    IFL s'.
  Proof.
    intros s s' HIFL Hprev Hbound t' o Tr Hiter Hfl.
    assert (Hlk : forall ob, ob ∈ sz ->
             exists t0 S, Og !! (z, t0) = Some S /\ ob ∈ S).
    { intros ob Hob. destruct (Hprev ob Hob) as [S [HS Hin]]. by exists t, S. }
    (* the free list is untouched *)
    assert (Hfl0 : flist s o = Some Tr) by exact Hfl.
    destruct Hiter as [t'' [s'' [Hlk'' Hin]]].
    destruct (decide ((o, t'') = (z, t))) as [Heq|Hne].
    - injection Heq as -> ->.
      rewrite lookup_insert_eq in Hlk''. injection Hlk'' as <-.
      apply elem_of_union in Hin as [Hin | Hin].
      + (* an observation that was already there *)
        destruct (Hlk _ Hin) as [t0 [S0 [HS0 Hin0]]].
        exact (HIFL t' z Tr (ex_intro _ t0 (ex_intro _ S0 (conj HS0 Hin0)))
                 Hfl0).
      + (* the one just acquired *)
        apply elem_of_singleton in Hin. injection Hin as <-.
        exact (Hbound Tr Hfl0).
    - rewrite lookup_insert_ne // in Hlk''.
      exact (HIFL t' o Tr (ex_intro _ t'' (ex_intro _ s'' (conj Hlk'' Hin))) Hfl0).
  Qed.

  (** And it preserves RITR unconditionally: a reader acquires an [iterator]
      observation, which is the only kind RITR permits it. *)
  Theorem reader_acquire_preserves_RITR m Og U T F t z sz :
    let s  := to_LState_t m Og U T F in
    let s' := to_LState_t m (<[(z, t) := sz ∪ {[Oiter t]}]> Og) U T F in
    RITR s ->
    (forall ob, ob ∈ sz -> exists S, Og !! (z, t) = Some S /\ ob ∈ S) ->
    RITR s'.
  Proof.
    intros s s' HR Hprev o t' Hrd.
    (* what the entry held before, read back as an observation.  The acquired
       set may be the union with a prior entry or with nothing, and the two
       cases differ only here *)
    assert (Hlk : forall ob, ob <> Oroot -> ob ∈ sz -> obsv s z ob).
    { intros ob Hnr Hob. destruct (Hprev ob Hob) as [S [HS Hin]].
      exact (to_LState_t_obs Og m U T F z t S ob Hnr HS Hin). }
    (* readers are unchanged by the update *)
    assert (Hrd0 : rds (ms s) t') by exact Hrd.
    destruct (HR o t' Hrd0) as (Hu & Hf & Hfr).
    (* an observation in the post-state is either old, or the acquired iterator *)
    assert (Hback : forall ob, obsv s' o ob -> obsv s o ob \/ ob = Oiter t).
    { intros ob Hob. destruct ob; [.. | by left].
      all: destruct Hob as [t'' [s'' [Hlk'' Hin]]].
      all: destruct (decide ((o, t'') = (z, t))) as [Heq|Hne].
      all: try (rewrite lookup_insert_ne // in Hlk''; left; by exists t'', s'').
      all: injection Heq as -> ->;
           rewrite lookup_insert_eq in Hlk''; injection Hlk'' as <-;
           apply elem_of_union in Hin as [Hin | Hin].
      all: try (left; apply Hlk; [discriminate | exact Hin]).
      all: apply elem_of_singleton in Hin; try discriminate.
      right. exact Hin. }
    repeat split; intros Hbad;
      destruct (Hback _ Hbad) as [Hold | Heq]; try discriminate;
      [exact (Hu Hold) | exact (Hf Hold) | exact (Hfr Hold)].
  Qed.

End readers.

Print Assumptions reader_acquire_preserves_IFL.
Print Assumptions reader_acquire_preserves_RITR.

(** ** ReadEnd

    A reader leaving its critical section stops being a reader, stops bounding
    any pending reclamation, drops its observations, and is removed from every
    free-list entry.  This is where the free list actually shrinks, and so where
    Free eventually becomes possible.

    The four have to happen together, and the proofs say why.  IFL needs the
    observations dropped in the same step as the free-list removal: a thread
    removed from an entry while still observing that node as an iterator is
    exactly the state IFL forbids.  RINFL needs the bounding-thread set narrowed
    with the entries, since it says every thread in an entry is a bounding
    thread.  Neither is a step that can be taken on its own. *)

Definition read_end_ms (m : MState) (t : TID) : MState :=
  {| stk := stk m; hp := hp m; lk := lk m; rt := rt m;
     rds := fun t' => rds m t' /\ t' <> t;
     bnd := fun t' => bnd m t' /\ t' <> t |}.

Definition read_end_F (F : gmap Loc (gset TID)) (t : TID) : gmap Loc (gset TID) :=
  (fun s => s ∖ {[t]}) <$> F.

(** ** Why BR is not decoration

    SyncStop blocks until the bounding set is empty, and ReadEnd is the only
    action that takes a thread out of it.  So if the bounding set contains a
    thread that is not a reader, no sequence of ReadEnds can remove it.

    [read_ends] is any number of them, in any order.  The statement below is
    that the offending thread survives all of them, which is the formal content
    of ``the grace period never completes'': not a liveness proof, which this
    development has no semantics to state, but the safety-shaped half of one --
    the obstruction is invariant under every step that could clear it. *)

Fixpoint read_ends (m : MState) (ts : list TID) : MState :=
  match ts with
  | []       => m
  | t :: ts' => read_ends (read_end_ms m t) ts'
  end.

Lemma read_ends_rds m ts t : rds (read_ends m ts) t -> rds m t.
Proof.
  revert m. induction ts as [|t' ts IH]; intros m H; [exact H |].
  destruct (IH _ H) as [H' _]. exact H'.
Qed.

Lemma bnd_stuck m t ts :
  bnd m t -> ~ In t ts -> bnd (read_ends m ts) t.
Proof.
  revert m. induction ts as [|t' ts IH]; intros m Hb Hni; [exact Hb |].
  apply IH.
  - split; [exact Hb | intros ->; apply Hni; by left].
  - intros Hc. apply Hni. by right.
Qed.

(** A thread that is not a reader is not one of the threads that can step, so
    the hypothesis of [bnd_stuck] is discharged by BR's failure alone. *)
Theorem grace_period_stuck m t ts :
  bnd m t -> ~ rds m t ->
  (forall t', In t' ts -> rds m t') ->
  bnd (read_ends m ts) t.
Proof.
  intros Hb Hr Hts. apply (bnd_stuck m t ts Hb).
  intros Hin. exact (Hr (Hts t Hin)).
Qed.

Section readend.

  (** [Og'] is [Og] with thread [t]'s entries gone; stated by its two defining
      properties rather than as a filter, which keeps the proofs about what
      matters. *)
  Theorem read_end_preserves_IFL m Og Og' U T F t :
    ObsWF Og' ->
    (forall o, Og' !! (o, t) = None) ->
    (forall o t', t' <> t -> Og' !! (o, t') = Og !! (o, t')) ->
    IFL (to_LState_t m Og U T F) ->
    IFL (to_LState_t (read_end_ms m t) Og' U T (read_end_F F t)).
  Proof.
    intros HWF Hgone Hkept HIFL t' o Tr Hiter Hfl.
    (* the observation is thread t''s own, and t' is not the departing thread *)
    destruct (obsv_t_locates _ _ _ _ _ o t' (Oiter t') HWF eq_refl Hiter)
      as [s [Hlk Hin]].
    assert (Hne : t' <> t) by (intros ->; rewrite Hgone in Hlk; discriminate).
    (* the free-list entry is the old one minus t *)
    unfold read_end_F in Hfl. simpl in Hfl.
    rewrite lookup_fmap in Hfl.
    destruct (F !! o) as [s0|] eqn:Hs0; [| discriminate].
    simpl in Hfl. injection Hfl as <-.
    (* so it suffices that t' was in the old entry *)
    assert (Hold : IFL (to_LState_t m Og U T F)) by exact HIFL.
    assert (Hiter0 : obsv (to_LState_t m Og U T F) o (Oiter t'))
      by (exists t', s; rewrite -(Hkept o t' Hne); done).
    assert (Hfl0 : flist (to_LState_t m Og U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite Hs0).
    pose proof (Hold t' o _ Hiter0 Hfl0) as Hmem.
    set_solver.
  Qed.

  (** RINFL: every thread in a free-list entry is a bounding thread.  Narrowing
      the entries and the bounding set together preserves it. *)
  Theorem read_end_preserves_RINFL m Og' U T F t :
    RINFL (to_LState_t m Og' U T F) ->
    RINFL (to_LState_t (read_end_ms m t) Og' U T (read_end_F F t)).
  Proof.
    intros HR o Tr t' Hfl Hin.
    unfold read_end_F in Hfl. simpl in Hfl.
    rewrite lookup_fmap in Hfl.
    destruct (F !! o) as [s0|] eqn:Hs0; [| discriminate].
    simpl in Hfl. injection Hfl as <-.
    assert (Hne : t' <> t) by set_solver.
    assert (Hin0 : t' ∈ s0) by set_solver.
    assert (Hfl0 : flist (to_LState_t m Og' U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite Hs0).
    split; [exact (HR o _ t' Hfl0 Hin0) | exact Hne].
  Qed.

End readend.

Print Assumptions read_end_preserves_IFL.
Print Assumptions grace_period_stuck.
Print Assumptions read_end_preserves_RINFL.

(** ** Free

    The endpoint the reclamation argument exists to justify, and the case the
    report calls trivial.

    Under the published HD it is not provable at all: HD constrains every edge,
    and an unlinked node retains a pointer to its old child, so freeing that
    child leaves a dangling edge ([HD_not_preserved_by_free]).  Under the
    corrected HD it goes through by exactly the argument the write-up claimed --
    ULKR is what supplies it.

    The shape is worth noting.  The obligation is that nothing *live* points at
    the freed node.  ULKR gives that every predecessor of a freeable node is
    itself unlinked or freeable, hence detached; the corrected HD asks only
    about non-detached sources; so the two meet exactly.  The published HD asked
    about detached sources too, where ULKR has nothing to offer. *)

Definition free_ms (m : MState) (d : Loc) : MState :=
  {| stk := stk m; hp := free (hp m) d; lk := lk m; rt := rt m;
     rds := rds m; bnd := bnd m |}.

Section freeing.

  Theorem free_preserves_HD m Og U T F d t :
    let s  := to_LState_t m Og U T F in
    let s' := to_LState_t (free_ms m d) Og U T F in
    HD s -> ULKR s -> obsv s d (Ofree t) -> HD s'.
  Proof.
    intros s s' HHD HULKR Hfree o f o' Hedge Hlive.
    (* the edge survived the free, so its source is not the freed node *)
    unfold Edge in Hedge. subst s'. simpl in Hedge.
    destruct (Nat.eq_dec o d) as [->|Hod];
      [rewrite free_same in Hedge; discriminate |].
    rewrite free_other in Hedge; [| exact Hod].
    (* observations are untouched, so the source is live in the old state too *)
    assert (Hlive0 : ~ Detached s o) by exact Hlive.
    (* the target is not the freed node: ULKR would make the source detached *)
    assert (Hne : o' <> d).
    { intros ->. apply Hlive0.
      destruct (HULKR d o f t (or_intror Hfree) Hedge) as [Hu | Hf];
        [exists t; by left | exists t; right; by left]. }
    (* so HD in the old state gives what we need, and the free did not touch it *)
    destruct (HHD o f o' Hedge Hlive0) as [g [v Hv]].
    exists g, v. simpl. by rewrite free_other.
  Qed.

End freeing.

Print Assumptions free_preserves_HD.

(** ** SyncStart and SyncStop

    The grace period.  SyncStart sets the bounding threads to the current
    readers and populates a free-list entry for each unlinked node with that
    same set; SyncStop blocks until the bounding set is empty, after which the
    unlinked nodes become freeable.

    Two facts carry the whole thing, and each is short once the invariants are
    right.

    The first is where the FLR direction settled earlier is used.  Every entry
    created by one SyncStart holds the *same* set, so along a chain of unlinked
    nodes the inclusion FLR demands holds with equality -- which is the
    same-critical-section case of the argument that fixed the direction.  ULKR
    is what supplies that a predecessor of an entry holder is an entry holder.

    The second is what makes Free possible at all: after SyncStop the bounding
    set is empty, and RINFL says every thread in an entry is a bounding thread,
    so every entry is empty.  That is exactly the conjunct the [freeable]
    denotation asks for. *)

Section grace.

  (** SyncStart: one snapshot, so all entries agree, so FLR holds with
      equality rather than mere inclusion. *)
  Theorem sync_start_FLR m Og U T F Rs :
    let s := to_LState_t m Og U T F in
    ULKR s ->
    (forall o s0, F !! o = Some s0 -> s0 = Rs) ->
    (forall o t, (obsv s o (Ounlk t) \/ obsv s o (Ofree t)) ->
        exists s0, F !! o = Some s0) ->
    (forall o s0, F !! o = Some s0 ->
        exists t, obsv s o (Ounlk t) \/ obsv s o (Ofree t)) ->
    FLR s.
  Proof.
    intros s HULKR Hsame Hcovers Honly o o' f' Tr Hfl Hedge.
    simpl in Hfl. destruct (F !! o) as [s0|] eqn:Hs0; [| discriminate].
    injection Hfl as <-.
    (* o is detached, so by ULKR so is its predecessor *)
    destruct (Honly o s0 Hs0) as [t Hdet].
    pose proof (HULKR o o' f' t Hdet Hedge) as Hdet'.
    (* hence the predecessor has an entry, and it is the same snapshot *)
    destruct (Hcovers o' t Hdet') as [s1 Hs1].
    exists (fun x => x ∈ s1). split; [simpl; by rewrite Hs1 |].
    rewrite (Hsame o' s1 Hs1) (Hsame o s0 Hs0). done.
  Qed.

  (** SyncStop: the bounding set is empty, so every entry is. *)
  Theorem sync_stop_entries_empty m Og U T F :
    RINFL (to_LState_t m Og U T F) ->
    (forall t, ~ bnd m t) ->
    forall o s0 t, F !! o = Some s0 -> t ∉ s0.
  Proof.
    intros HR Hb o s0 t Hlk Hin.
    assert (Hfl : flist (to_LState_t m Og U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite Hlk).
    exact (Hb t (HR o _ t Hfl Hin)).
  Qed.


  (** The conjunct FNR gained (change 10b) is discharged by the conjunct it
      already had, so strengthening it costs nothing.  SyncStop's only effect on
      observations is to turn [unlinked] into [freeable]; a node observed
      [fresh] holds no [unlinked] observation, so it gains no [freeable] one.

      Stated over the observation *step* rather than a SyncStop transformer:
      what the argument needs is only that [freeable] arrives from [unlinked],
      and saying so keeps the lemma independent of how the grace period is
      encoded. *)
  Theorem sync_stop_preserves_FNR (s s' : LState) :
    FNR s ->
    (forall o ob, obsv s' o ob ->
       obsv s o ob \/ exists t, ob = Ofree t /\ obsv s o (Ounlk t)) ->
    FNR s'.
  Proof.
    intros HF Hstep o t t' Hfr'.
    assert (Hfr : obsv s o (Ofresh t)).
    { destruct (Hstep o (Ofresh t) Hfr') as [H | [t0 [Hc _]]];
        [exact H | discriminate Hc]. }
    destruct (HF o t t' Hfr) as [H1 [H2 H3]].
    repeat apply conj; intros Hbad;
      destruct (Hstep _ _ Hbad) as [H | [t0 [Hc Hu]]].
    - exact (H1 H).
    - discriminate Hc.
    - exact (H2 H).
    - discriminate Hc.
    - exact (H3 H).
    - injection Hc as <-. exact (H2 Hu).
  Qed.

End grace.

Print Assumptions sync_start_FLR.
Print Assumptions sync_stop_entries_empty.
Print Assumptions sync_stop_preserves_FNR.

(** ** The invariants a heap write cannot touch

    Most of WellFormed does not mention the heap.  A field write changes [hp]
    and nothing else, so those invariants transfer definitionally -- each proof
    below is the identity.  Recording it as eleven one-line lemmas rather than
    leaving it implicit is worth the space: it says precisely which cases of an
    atomic-action lemma have content and which do not, and the report's habit of
    calling a case trivial without saying why is what hid three defects.

    The nine that are *not* here -- OW, ULKR, FLR, FPI, FR, HD, UNQR and the two
    halves of UNQRT -- all mention the heap, and every one of them needed a real
    argument. *)

Section untouched.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (o : Loc) (f : FName) (v : Val).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m o f v) Og U T F.

  Lemma write_RWOW   : RWOW s   -> RWOW s'.   Proof. exact (fun H => H). Qed.
  Lemma write_AWRT   : AWRT s   -> AWRT s'.   Proof. exact (fun H => H). Qed.
  Lemma write_IFL    : IFL s    -> IFL s'.    Proof. exact (fun H => H). Qed.
  Lemma write_WULK   : WULK s   -> WULK s'.   Proof. exact (fun H => H). Qed.
  Lemma write_WFresh : WFresh s -> WFresh s'. Proof. exact (fun H => H). Qed.
  Lemma write_FNR    : FNR s    -> FNR s'.    Proof. exact (fun H => H). Qed.
  Lemma write_RITR   : RITR s   -> RITR s'.   Proof. exact (fun H => H). Qed.
  Lemma write_RINFL  : RINFL s  -> RINFL s'.  Proof. exact (fun H => H). Qed.
  Lemma write_WNR    : WNR s    -> WNR s'.    Proof. exact (fun H => H). Qed.
  (* The two the revision added, which belong here for the same reason and
     were missing only because the section predates them. *)
  Lemma write_WUNLK  : WUNLK s  -> WUNLK s'.  Proof. exact (fun H => H). Qed.
  Lemma write_WITR   : WITR s   -> WITR s'.   Proof. exact (fun H => H). Qed.

End untouched.

(** ** OW for a field write

    In-degree at most one, for live nodes.  A write creates one edge, so the
    obligation is that the node written was not already pointed at -- which for
    the two rules that write a fresh node is FR, the same hypothesis their UNQR
    cases use.  Nothing is needed about the edge that was overwritten: removing
    an edge cannot raise anyone's in-degree. *)

Section sharing.

  Variable FType : FName -> FieldKind.

  Theorem write_preserves_OW m Og U T F op f on :
    let s  := to_LState_t m Og U T F in
    let s' := to_LState_t (write_ms m op f (VLoc on)) Og U T F in
    OW FType s ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    OW FType s'.
  Proof.
    intros s s' HOW Hno o o' g g' x He He' Hg Hg'.
    assert (Hsplit : forall a b y,
              hp (ms s') a b = Some (VLoc y) ->
              ((a, b) = (op, f) /\ y = on) \/ hp m a b = Some (VLoc y)).
    { intros a b y Hab. subst s'. simpl in Hab.
      destruct (edge_eq_dec a b op f) as [Heq|Hne].
      - left. injection Heq as -> ->. rewrite upd_same in Hab.
        injection Hab as <-. split; reflexivity.
      - right. by rewrite upd_other in Hab. }
    destruct (Hsplit o g x He) as [[Hoe Hx] | Hold];
    destruct (Hsplit o' g' x He') as [[Hoe' Hx'] | Hold'].
    - injection Hoe as -> ->. injection Hoe' as -> ->. by left.
    - exfalso. rewrite Hx in Hold'. exact (Hno o' g' Hold').
    - exfalso. rewrite Hx' in Hold. exact (Hno o g Hold).
    - exact (HOW o o' g g' x Hold Hold' Hg Hg').
  Qed.

End sharing.

Print Assumptions write_WULK.
Print Assumptions write_preserves_OW.

(** ** The rest of the invariants a field write does touch

    [write_preserves_OW] settled the first of the eight; this settles five more.
    HD, UNQRT_a, ULKR, FLR and FR each mention the heap, so each has a real case
    at the written edge -- and in every one of them the case at the *old* edge is
    empty, because a write only removes that edge and no invariant here is
    endangered by an edge going away.  What is left is one obligation per
    invariant about the edge created, and each turns out to be a premise the
    rules already carry, or -- once, for ULKR -- an invariant they do not.

    The eighth, UNQRT_b, is not a write lemma: its hypothesis is [Reaches], so it
    needs the path characterizations of [HeapPaths.v] and belongs with the
    per-rule UNQR theorems above rather than here.

    FR is the one whose statement has to say less than one might hope.  A write
    that stores a *fresh* node destroys FR outright -- the node acquires an
    in-edge -- and no side condition repairs that, because FR is not meant to
    survive: T-Replace and T-Insert re-establish it by revoking the [fresh]
    observation in the same step.  So the write lemma covers the writes that
    store something else, which is T-WriteFH, and the linking rules get FR from
    the observation update instead. *)

Section heapinv.

  Variables (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (op : Loc) (fw : FName) (on : Loc).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m op fw (VLoc on)) Og U T F.

  (** Every edge after the write is either the one written or one that was
      there before.  Both directions of the case split used below. *)
  Lemma write_edge_split o g x :
    Edge s' o g x -> ((o, g) = (op, fw) /\ x = on) \/ Edge s o g x.
  Proof.
    unfold Edge; simpl; intros He.
    destruct (edge_eq_dec o g op fw) as [Heq | Hne].
    - left. injection Heq as -> ->. rewrite upd_same in He.
      injection He as <-. split; reflexivity.
    - right. by rewrite upd_other in He.
  Qed.

  (** A write never deallocates: it assigns one field, so anything allocated
      stays allocated. *)
  Lemma write_InHeap o : InHeap s o -> InHeap s' o.
  Proof.
    intros [g [v Hv]]. unfold InHeap; simpl.
    destruct (edge_eq_dec o g op fw) as [Heq | Hne].
    - injection Heq as -> ->. exists fw, (VLoc on). apply upd_same.
    - exists g, v. by rewrite upd_other.
  Qed.

  (** ** HD

      Heap-domain closure, in the corrected form with the [Detached] exemption
      (change 7).  The hypothesis is under that exemption, and deliberately so:
      what a *detached* node's fields point at is nobody's business, since the
      node is unreachable and OW and HD both excuse it.  A write through a live
      node has to store something allocated; a write through an unlinked one
      need not. *)
  Theorem write_preserves_HD :
    HD s -> (~ Detached s op -> InHeap s on) -> HD s'.
  Proof.
    intros HHD Hon o g x He Hnd.
    destruct (write_edge_split o g x He) as [[Heq ->] | Hold].
    - injection Heq as -> ->. exact (write_InHeap on (Hon Hnd)).
    - exact (write_InHeap x (HHD o g x Hold Hnd)).
  Qed.

  (** ** UNQRT_a

      Nothing points at the root.  The obligation is that the write does not
      make the root a target, and every rule supplies it: the node stored is an
      [rcuItr] at a non-empty path or an [rcuFresh], and the root is neither. *)
  Theorem write_preserves_UNQRT_a :
    UNQRT_a s -> on <> rt m -> UNQRT_a s'.
  Proof.
    intros HU Hne o g He.
    destruct (write_edge_split o g (rt (ms s')) He) as [[_ Hx] | Hold].
    - exact (Hne (eq_sym Hx)).
    - exact (HU o g Hold).
  Qed.

  (** ** ULKR

      Detachment propagates upwards: a predecessor of an unlinked-or-freeable
      node is itself unlinked or freeable.  The new edge makes [op] a
      predecessor of [on], so the obligation is that [on] being detached forces
      [op] to be. *)
  Theorem write_preserves_ULKR :
    ULKR s ->
    (forall t, (obsv s on (Ounlk t) \/ obsv s on (Ofree t)) ->
               obsv s op (Ounlk t) \/ obsv s op (Ofree t)) ->
    ULKR s'.
  Proof.
    intros HU Hnew o o' f' t Hobs He.
    destruct (write_edge_split o' f' o He) as [[Heq ->] | Hold].
    - injection Heq as -> ->. exact (Hnew t Hobs).
    - exact (HU o o' f' t Hobs Hold).
  Qed.

  (** ** FLR

      The same shape, on the free list rather than the observations. *)
  Theorem write_preserves_FLR :
    FLR s ->
    (forall Tr, flist s on = Some Tr ->
       exists Tr', flist s op = Some Tr' /\ (forall t, Tr' t -> Tr t)) ->
    FLR s'.
  Proof.
    intros HF Hnew o o' f' Tr Hfl He.
    destruct (write_edge_split o' f' o He) as [[Heq ->] | Hold].
    - injection Heq as -> ->. exact (Hnew Tr Hfl).
    - exact (HF o o' f' Tr Hfl Hold).
  Qed.

  (** ** FR

      For a write that stores a node nobody observes as fresh.  The second
      conjunct of FR is about the stack, which a write does not touch, so only
      the in-edge obligation has content. *)
  Theorem write_preserves_FR :
    FR s -> (forall t, ~ obsv s on (Ofresh t)) -> FR s'.
  Proof.
    intros HFR Hnf t x o Hstk Hfresh.
    destruct (HFR t x o Hstk Hfresh) as [Hin Halias].
    split; [| exact Halias].
    intros o' g He.
    destruct (write_edge_split o' g o He) as [[_ ->] | Hold].
    - exact (Hnf t Hfresh).
    - exact (Hin o' g Hold).
  Qed.

  (** ** Linking a fresh node, and what ULKR costs there

      This is the case the two linking rules are in, and it is where FNR's third
      conjunct (change 10b) is spent.  [on] is fresh, so FNR denies it both
      [unlinked] and [freeable], and the ULKR obligation is discharged without
      any premise on [op] at all. *)
  Corollary link_fresh_ULKR t0 :
    ULKR s -> FNR s -> obsv s on (Ofresh t0) -> ULKR s'.
  Proof.
    intros HU HF Hfr. apply write_preserves_ULKR; [exact HU |].
    intros t [Hu | Hf]; exfalso.
    - exact (proj1 (proj2 (HF on t0 t Hfr)) Hu).
    - exact (proj2 (proj2 (HF on t0 t Hfr)) Hf).
  Qed.

  (** And the published FNR does not pay for it.  Its two conjuncts leave [on]
      free to be [freeable]; [op] is the writer's iterator, which WULK denies
      both observations, so the obligation fails outright -- there is no weaker
      premise to fall back on.  [WellFormed.fresh_freeable] is a state
      satisfying the other eighteen invariants and the published FNR in which
      this applies. *)
  Theorem link_freeable_breaks_ULKR lw t :
    WULK s -> lk (ms s) = Some lw ->
    obsv s op (Oiter lw) -> obsv s on (Ofree t) ->
    ~ ULKR s'.
  Proof.
    intros HW Hlk Hit Hfr HU.
    assert (He : Edge s' op fw on) by (unfold Edge; simpl; apply upd_same).
    destruct (HW lw op t Hlk Hit) as [Hnu Hnf].
    destruct (HU on op fw t (or_intror Hfr) He) as [H | H];
      [exact (Hnu H) | exact (Hnf H)].
  Qed.

End heapinv.

Print Assumptions write_preserves_HD.
Print Assumptions write_preserves_UNQRT_a.
Print Assumptions write_preserves_ULKR.
Print Assumptions write_preserves_FLR.
Print Assumptions write_preserves_FR.
Print Assumptions link_fresh_ULKR.
Print Assumptions link_freeable_breaks_ULKR.

(** ** UNQRT_b, the eighth

    The last of the eight, and the one that is not a write lemma.  UNQRT_b says
    the writer observes every reachable node as an iterator, so its hypothesis
    is [Reaches] and it has to be discharged against the path characterizations
    of [HeapPaths.v] rather than against the written edge.  It is also the only
    invariant that couples the heap change to the observation change: each of
    the three rules updates both, and UNQRT_b is where the two have to agree.

    Doing it makes the asymmetry between the rules visible, and it is not the
    asymmetry the report's case structure suggests.

      - T-Insert is the easy one.  Nothing loses an observation, and everything
        reachable afterwards was either reachable before or is the inserted node
        itself, which the step observes as an iterator.

      - T-UnlinkH and T-Replace each revoke an iterator observation, so for them
        the invariant needs something UNQR does not say: that the node losing it
        is gone from the structure.  That is [unlink_unreachable] and
        [replace_unreachable].  UNQR alone is not enough -- it says the result
        is still a tree, not which nodes are in it -- and this is the one case
        where the difference bites. *)

Section roots.

  (** T-UnlinkH: writes [x.f1 := r] and unlinks [z].  No node is added, so the
      whole content is that [z] left. *)
  Theorem unlink_preserves_UNQRT_b m O U T F lw ox f1 oz f2 ow tz rho :
    let s  := to_LState m O U T F in
    let s' := to_LState (write_ms m ox f1 (VLoc ow))
                        (<[oz := {[Ounlk tz]}]> O) U T F in
    lk m = Some lw ->
    UNQRT_b s ->
    UNQR_h (hp m) (rt m) ->
    hstar (hp m) (rt m) rho = Some ox ->
    hp m ox f1 = Some (VLoc oz) ->
    hp m oz f2 = Some (VLoc ow) ->
    UNQRT_b s'.
  Proof.
    intros s s' Hlk HB HU Hrho HXf1 Hzf2 p x lw' Hlk' Hreach.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    assert (Hnoback : forall tau, hstar (hp m) ow tau <> Some ox).
    { apply (UNQR_no_back (hp m) (rt m) ox rho [f1; f2] ow HU Hrho);
        [discriminate |].
      rewrite hstar_app Hrho /=. rewrite HXf1 /=. by rewrite Hzf2. }
    (* the unlinked node is no longer in the structure *)
    assert (Hnz : x <> oz).
    { intros ->.
      exact (unlink_unreachable (hp m) (rt m) ox f1 oz f2 ow rho
               HU Hrho HXf1 Hzf2 p Hreach). }
    (* and everything that is was there before *)
    assert (Hpre : exists q, hstar (hp m) (rt m) q = Some x).
    { destruct (hstar_unlink_char (hp m) (rt m) ox f1 oz f2 ow p x
                  HXf1 Hzf2 Hnoback Hreach)
        as [[Ha _] | [p1 [s2 [_ [_ Hr]]]]].
      - exists p. exact Ha.
      - exists (p1 ++ f1 :: f2 :: s2). exact Hr. }
    destruct Hpre as [q Hq].
    assert (Htr : forall ob, obsv s x ob -> obsv s' x ob).
    { intros ob. subst s s'. simpl. by rewrite lookup_insert_ne. }
    destruct (HB q x lw Hlk Hq) as [Hit | Hrt];
      [left; exact (Htr _ Hit) | right; exact (Htr _ Hrt)].
  Qed.

  (** T-Replace: writes [p.f := n] and unlinks [o].  Both halves at once -- [n]
      arrives as an iterator, [o] leaves -- so both [replace_unreachable] and
      the added observation are used. *)
  Theorem replace_preserves_UNQRT_b m O U T F lw op f oo on to rho :
    let s  := to_LState m O U T F in
    let s' := to_LState (write_ms m op f (VLoc on))
                        (<[on := {[Oiter lw]}]> (<[oo := {[Ounlk to]}]> O))
                        U T F in
    lk m = Some lw ->
    UNQRT_b s ->
    UNQR_h (hp m) (rt m) ->
    Mirrors (hp m) on oo ->
    hstar (hp m) (rt m) rho = Some op ->
    hp m op f = Some (VLoc oo) ->
    (forall sigma, hstar (hp m) (rt m) sigma <> Some on) ->
    UNQRT_b s'.
  Proof.
    intros s s' Hlk HB HU Hmir Hrho HPf Hfresh p x lw' Hlk' Hreach.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (Nat.eq_dec x on) as [-> | Hxn].
    - (* the node written in: the step observes it as the writer's iterator *)
      left. subst s'. simpl. rewrite lookup_insert_eq. set_solver.
    - assert (Hnp : on <> op) by (intros ->; exact (Hfresh rho Hrho)).
      assert (Hnoback : forall tau, hstar (hp m) oo tau <> Some op)
        by exact (UNQR_no_back_edge (hp m) (rt m) op f oo rho HU Hrho HPf).
      (* not the replaced node, which left the structure *)
      assert (Hxo : x <> oo).
      { intros ->.
        exact (replace_unreachable (hp m) (rt m) op f oo on rho
                 HU Hmir Hrho HPf Hfresh p Hreach). }
      (* so it was reachable before, by the same path *)
      assert (Hq : hstar (hp m) (rt m) p = Some x).
      { destruct (hstar_replace_char (hp m) (rt m) op f oo on p x
                    Hmir Hnp HPf Hnoback Hreach) as [Ha | [Hx _]];
          [exact Ha | contradiction]. }
      assert (Htr : forall ob, obsv s x ob -> obsv s' x ob).
      { intros ob. subst s s'. simpl. by rewrite !lookup_insert_ne. }
      destruct (HB p x lw Hlk Hq) as [Hit | Hrt];
        [left; exact (Htr _ Hit) | right; exact (Htr _ Hrt)].
  Qed.

  (** T-Insert: writes [p.f := n], unlinks nothing.  No unreachability result is
      needed, which is exactly the difference. *)
  Theorem insert_preserves_UNQRT_b m O U T F lw op f oo on f4 rho :
    let s  := to_LState m O U T F in
    let s' := to_LState (write_ms m op f (VLoc on))
                        (<[on := {[Oiter lw]}]> O) U T F in
    lk m = Some lw ->
    UNQRT_b s ->
    UNQR_h (hp m) (rt m) ->
    PointsOnlyAt (hp m) on f4 oo ->
    hstar (hp m) (rt m) rho = Some op ->
    hp m op f = Some (VLoc oo) ->
    (forall sigma, hstar (hp m) (rt m) sigma <> Some on) ->
    UNQRT_b s'.
  Proof.
    intros s s' Hlk HB HU Hpo Hrho HPf Hfresh p x lw' Hlk' Hreach.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (Nat.eq_dec x on) as [-> | Hxn].
    - left. subst s'. simpl. rewrite lookup_insert_eq. set_solver.
    - assert (Hnp : on <> op) by (intros ->; exact (Hfresh rho Hrho)).
      assert (Hnoback : forall tau, hstar (hp m) oo tau <> Some op)
        by exact (UNQR_no_back_edge (hp m) (rt m) op f oo rho HU Hrho HPf).
      assert (Hq : exists q, hstar (hp m) (rt m) q = Some x).
      { destruct (hstar_insert_char (hp m) (rt m) op f oo on f4 p x
                    Hpo Hnp HPf Hnoback Hreach)
          as [[Ha _] | [[Hx _] | [p1 [tau [_ [_ Hr]]]]]].
        - exists p. exact Ha.
        - contradiction.
        - exists (p1 ++ f :: tau). exact Hr. }
      destruct Hq as [q Hq].
      assert (Htr : forall ob, obsv s x ob -> obsv s' x ob).
      { intros ob. subst s s'. simpl. by rewrite lookup_insert_ne. }
      destruct (HB q x lw Hlk Hq) as [Hit | Hrt];
        [left; exact (Htr _ Hit) | right; exact (Htr _ Hrt)].
  Qed.

End roots.

Print Assumptions unlink_preserves_UNQRT_b.
Print Assumptions replace_preserves_UNQRT_b.
Print Assumptions insert_preserves_UNQRT_b.

(** ** Free, all nineteen

    The first action taken end to end: not one invariant at a time, but
    [WellFormed] itself, for the whole step.  Free is the right one to do first
    for two reasons.  It needs no type denotations -- it is a state transition,
    not a typing rule -- so nothing outside this file has to be assumed.  And it
    is the action the report handled worst: its HD case is the one dismissed as
    trivial along with everything else, and it is the one case that is not.

    Doing the whole thing shows how lopsided it is.  Eighteen of the nineteen
    fall out of [hstar_free_sub] and [free_edge_inv] -- free removes edges, so
    every invariant with an [Edge] or [Reaches] hypothesis gets *weaker*, and
    the eleven that do not mention the heap are untouched outright.  The
    nineteenth, HD, is the only one whose conclusion is about the heap, and it
    is the only one that needs an argument.  It also needs the corrected
    statement: under the published HD the theorem below is false, which
    [HD_not_preserved_by_free] exhibits.

    That is the whole content of the case, and it is a sentence long once the
    invariants are right.  It is worth having the other eighteen written out
    anyway: "trivial" is the claim that hid three defects, and the difference
    between an identity proof and a proof that inverts an edge is exactly what
    the report never recorded. *)

Section reclamation.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)) (d : Loc).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (free_ms m d) Og U T (delete d F).

  (** The free list loses the node too.  [WellFormed] does not need this -- the
      invariant half of the case goes through with [F] untouched -- but the type
      half does: the rule retypes the variable as [undef], and that denotation
      asks that the variable's referent not be on the free list.  A reclamation
      that left the entry behind would satisfy every invariant and fail its own
      post-type environment.  See [free_post_env]. *)

  (** Edges and paths only go away, and the source of a surviving edge is not
      the node freed. *)
  Lemma free_edge_inv o f o' : Edge s' o f o' -> Edge s o f o' /\ o <> d.
  Proof.
    unfold Edge; simpl; intros He.
    destruct (Nat.eq_dec o d) as [->|Hne].
    - rewrite free_same in He. discriminate.
    - rewrite (free_other (hp m) d o f Hne) in He. by split.
  Qed.

  Lemma free_reaches_inv p o : Reaches s' p o -> Reaches s p o.
  Proof. unfold Reaches; simpl. apply hstar_free_sub. Qed.

  (** The ten that do not mention the heap.  Free changes [hp] and nothing
      else, so each is the identity -- as for a write, and for the same
      reason. *)
  Lemma free_RWOW   : RWOW s   -> RWOW s'.   Proof. exact (fun H => H). Qed.
  Lemma free_AWRT   : AWRT s   -> AWRT s'.   Proof. exact (fun H => H). Qed.
  (** The free list shrinks, so its entries' invariants only get weaker. *)
  Lemma free_flist_inv o Tr :
    flist s' o = Some Tr -> flist s o = Some Tr /\ o <> d.
  Proof.
    intros H. simpl in H. destruct (decide (o = d)) as [-> | Hne].
    - rewrite lookup_delete_eq in H. discriminate.
    - rewrite lookup_delete_ne // in H.
  Qed.

  Lemma free_flist_keep o : o <> d -> flist s' o = flist s o.
  Proof. intros Hne. simpl. rewrite lookup_delete_ne //. Qed.

  Lemma free_IFL : IFL s -> IFL s'.
  Proof.
    intros H t o Tr Hit Hfl.
    exact (H t o Tr Hit (proj1 (free_flist_inv o Tr Hfl))).
  Qed.
  Lemma free_WULK   : WULK s   -> WULK s'.   Proof. exact (fun H => H). Qed.
  Lemma free_WFresh : WFresh s -> WFresh s'. Proof. exact (fun H => H). Qed.
  Lemma free_FNR    : FNR s    -> FNR s'.    Proof. exact (fun H => H). Qed.
  Lemma free_WNR    : WNR s    -> WNR s'.    Proof. exact (fun H => H). Qed.
  Lemma free_RITR   : RITR s   -> RITR s'.   Proof. exact (fun H => H). Qed.
  Lemma free_RINFL : RINFL s -> RINFL s'.
  Proof.
    intros H o Tr t Hfl Hin.
    exact (H o Tr t (proj1 (free_flist_inv o Tr Hfl)) Hin).
  Qed.
  Lemma free_WUNLK  : WUNLK s  -> WUNLK s'.  Proof. exact (fun H => H). Qed.
  Lemma free_WITR   : WITR s   -> WITR s'.   Proof. exact (fun H => H). Qed.

  (** The seven with an [Edge] or [Reaches] hypothesis.  Each is the old
      invariant applied to the inverted hypothesis; none needs a side
      condition, because a vanishing edge can only discharge an obligation. *)
  Lemma free_OW : OW FType s -> OW FType s'.
  Proof.
    intros H o o' f f' x He He'.
    exact (H o o' f f' x (proj1 (free_edge_inv o f x He))
             (proj1 (free_edge_inv o' f' x He'))).
  Qed.

  Lemma free_ULKR : ULKR s -> ULKR s'.
  Proof.
    intros H o o' f' t Hobs He.
    exact (H o o' f' t Hobs (proj1 (free_edge_inv o' f' o He))).
  Qed.

  Lemma free_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' f' Tr Hfl He.
    destruct (free_flist_inv o Tr Hfl) as [Hfl0 _].
    destruct (free_edge_inv o' f' o He) as [He0 Hne'].
    destruct (H o o' f' Tr Hfl0 He0) as [Tr' [Hfl' Hsub]].
    exists Tr'. split; [| exact Hsub]. by rewrite (free_flist_keep o' Hne').
  Qed.

  Lemma free_FPI : FPI FType s -> FPI FType s'.
  Proof.
    intros H o f o' t lw Hfr He Hft Hlk.
    exact (H o f o' t lw Hfr (proj1 (free_edge_inv o f o' He)) Hft Hlk).
  Qed.

  Lemma free_FR : FR s -> FR s'.
  Proof.
    intros H t x o Hstk Hfr.
    destruct (H t x o Hstk Hfr) as [Hin Hal].
    split; [| exact Hal].
    intros o' f' He. exact (Hin o' f' (proj1 (free_edge_inv o' f' o He))).
  Qed.

  Lemma free_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof. intros H o f He. exact (H o f (proj1 (free_edge_inv o f (rt m) He))). Qed.

  Lemma free_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p o lw Hlk Hr. exact (H p o lw Hlk (free_reaches_inv p o Hr)).
  Qed.

  Lemma free_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros H p p' o H1 H2.
    exact (H p p' o (free_reaches_inv p o H1) (free_reaches_inv p' o H2)).
  Qed.

  (** The action lemma.  [obsv s d (Ofree t)] is the rule's premise -- the
      variable freed is typed [freeable] -- and it is used in exactly one place,
      the HD case, through ULKR. *)
  Theorem free_preserves_WellFormed t :
    WellFormed FType s -> obsv s d (Ofree t) -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HU) Hfree.
    repeat apply conj.
    - exact (free_OW HOW).
    - exact (free_RWOW HRWOW).
    - exact (free_AWRT HAWRT).
    - exact (free_IFL HIFL).
    - exact (free_ULKR HULKR).
    - exact (free_FLR HFLR).
    - exact (free_WULK HWULK).
    - exact (free_FR HFR).
    - exact (free_WFresh HWFresh).
    - exact (free_FNR HFNR).
    - exact (free_FPI HFPI).
    - exact (free_WNR HWNR).
    - exact (free_RITR HRITR).
    - exact (free_RINFL HRINFL).
    - exact (free_preserves_HD m Og U T F d t HHD HULKR Hfree).
    - exact (free_UNQRT_a HUa).
    - exact (free_UNQRT_b HUb).
    - exact (free_WUNLK HWU).
    - exact (free_WITR HWI).
    - exact (free_UNQR HU).
  Qed.

  (** *** The post-type environment: [x : undef]

      The rule retypes the freed variable, so the step must also make it
      undefined -- which is [forget], the same ghost move T-TSub's soundness
      turns on, and which [forget_WellFormed] already shows harmless.  The
      second conjunct of the [undef] denotation is where the free list entry had
      to go: it asks that the variable's referent not be on the free list, and
      the referent is the node just reclaimed. *)
  Variables (xf : Var) (tf : TID).
  Hypothesis Hstk_f : stk m xf tf = Some d.

  Theorem free_post_env : D_undef (forget s' xf tf) tf xf.
  Proof.
    split.
    - by right.
    - intros o Hstk. simpl in Hstk. rewrite Hstk_f in Hstk.
      injection Hstk as <-. simpl. by rewrite lookup_delete_eq.
  Qed.

  Theorem free_post_WellFormed t :
    WellFormed FType s -> obsv s d (Ofree t) ->
    WellFormed FType (forget s' xf tf).
  Proof.
    intros HWF Hfree.
    exact (forget_WellFormed FType s' xf tf
             (free_preserves_WellFormed t HWF Hfree)).
  Qed.

End reclamation.

Print Assumptions free_edge_inv.
Print Assumptions free_reaches_inv.
Print Assumptions free_preserves_WellFormed.
Print Assumptions free_post_env.
Print Assumptions free_post_WellFormed.

(** ** SyncStop, all nineteen

    The second action taken whole, and the one that pays for the FNR repair.

    SyncStop does two things: it returns once the bounding set is empty, and it
    turns every [unlinked] observation into the matching [freeable] one.  Both
    halves are needed and each carries different invariants -- the empty
    bounding set is the whole of RINFL, and the observation change is everything
    else.

    The change is stated by what it does to observations rather than as a map
    operation, which is the choice ReadEnd already makes and for the same
    reason: two properties suffice, and they are the two directions.  Nothing
    appears that was not there, except [freeable] arriving from [unlinked]
    ([Hfwd]); and everything survives, [unlinked] as [freeable] ([Hmap]).  Every
    one of the nineteen cases is one of those two applied once, which is worth
    seeing -- the invariants that look like they should care about a grace
    period ending mostly do not, and the ones that do are not the ones the
    protocol's informal story points at.

    Two cases have content beyond the bookkeeping.  RINFL is where the empty
    bounding set is spent: it says every thread in a free-list entry bounds a
    reclamation, and after SyncStop there are no bounding threads, so the
    entries must be empty -- which is exactly the conjunct the [freeable]
    denotation asks for, obtained rather than assumed.  And FNR is
    [sync_stop_preserves_FNR]: the conjunct added to FNR to make T-Insert and
    T-Replace preserve ULKR is discharged here from the conjunct FNR already
    had, so the repair costs nothing at the one action that could have paid for
    it. *)

Definition sync_obs (ob : obs) : obs :=
  match ob with Ounlk t => Ofree t | _ => ob end.

Definition sync_stop_ms (m : MState) : MState :=
  {| stk := stk m; hp := hp m; lk := lk m; rt := rt m;
     rds := rds m; bnd := fun _ => False |}.

Section quiescence.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (sync_stop_ms m) Og' U T F.

  (** Nothing appears that was not there, except [freeable] from [unlinked]. *)
  Hypothesis Hfwd : forall o ob,
    obsv s' o ob ->
    obsv s o ob \/ exists t, ob = Ofree t /\ obsv s o (Ounlk t).

  (** And everything survives, [unlinked] as [freeable]. *)
  Hypothesis Hmap : forall o ob, obsv s o ob -> obsv s' o (sync_obs ob).

  (** SyncStop returns only once the grace period has completed. *)
  Hypothesis Hquiet : forall t, ~ bnd m t.

  (** The inversions [Hfwd] gives, once each.  Note the one that is missing:
      nothing maps *to* [unlinked], so after SyncStop no location is observed
      unlinked at all -- which is why [ss_detach] can collapse the disjunction
      the detachment invariants quantify over. *)
  Lemma ss_iter o t : obsv s' o (Oiter t) -> obsv s o (Oiter t).
  Proof.
    intros H. destruct (Hfwd o _ H) as [Ho | [t0 [Hc _]]];
      [exact Ho | discriminate].
  Qed.

  Lemma ss_fresh o t : obsv s' o (Ofresh t) -> obsv s o (Ofresh t).
  Proof.
    intros H. destruct (Hfwd o _ H) as [Ho | [t0 [Hc _]]];
      [exact Ho | discriminate].
  Qed.

  Lemma ss_root o : obsv s' o Oroot -> obsv s o Oroot.
  Proof.
    intros H. destruct (Hfwd o _ H) as [Ho | [t0 [Hc _]]];
      [exact Ho | discriminate].
  Qed.

  Lemma ss_detach o t :
    obsv s' o (Ounlk t) \/ obsv s' o (Ofree t) ->
    obsv s o (Ounlk t) \/ obsv s o (Ofree t).
  Proof.
    intros [H | H]; destruct (Hfwd o _ H) as [Ho | [t0 [Hc Hu]]].
    - by left.
    - discriminate.
    - by right.
    - injection Hc as <-. by left.
  Qed.

  Lemma ss_detached o : Detached s o -> Detached s' o.
  Proof.
    intros [t [H | [H | H]]]; exists t.
    - right; left.  exact (Hmap o (Ounlk t) H).
    - right; left.  exact (Hmap o (Ofree t) H).
    - right; right. exact (Hmap o (Ofresh t) H).
  Qed.

  (** The four the grace period cannot reach: heap, stack, lock and readers are
      all untouched, and neither the free list nor its [Edge] hypotheses move. *)
  Lemma ss_FLR     : FLR s     -> FLR s'.     Proof. exact (fun H => H). Qed.
  Lemma ss_WNR     : WNR s     -> WNR s'.     Proof. exact (fun H => H). Qed.
  Lemma ss_UNQRT_a : UNQRT_a s -> UNQRT_a s'. Proof. exact (fun H => H). Qed.
  Lemma ss_UNQR    : UNQR s    -> UNQR s'.    Proof. exact (fun H => H). Qed.

  (** The rest, each one application of [Hmap] or of an inversion. *)
  Lemma ss_OW : OW FType s -> OW FType s'.
  Proof.
    intros H o o' f f' x He He' Hf Hf'.
    destruct (H o o' f f' x He He' Hf Hf') as [Heq | [Hd | Hd]].
    - by left.
    - right; left.  exact (ss_detached o Hd).
    - right; right. exact (ss_detached o' Hd).
  Qed.

  Lemma ss_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hundf.
    destruct (H x t o Hstk Hundf) as [Hit | [Hlk [Hu | [Hfr | Hfs]]]].
    - left. exact (Hmap o (Oiter t) Hit).
    - right. split; [exact Hlk |]. right; left.  exact (Hmap o (Ounlk t) Hu).
    - right. split; [exact Hlk |]. right; left.  exact (Hmap o (Ofree t) Hfr).
    - right. split; [exact Hlk |]. right; right. exact (Hmap o (Ofresh t) Hfs).
  Qed.

  Lemma ss_AWRT : AWRT s -> AWRT s'.
  Proof. intros H y t Hstk Hundf. exact (Hmap _ (Oiter t) (H y t Hstk Hundf)). Qed.

  Lemma ss_IFL : IFL s -> IFL s'.
  Proof. intros H t o Tr Hit Hfl. exact (H t o Tr (ss_iter o t Hit) Hfl). Qed.

  Lemma ss_ULKR : ULKR s -> ULKR s'.
  Proof.
    intros H o o' f' t Hobs He.
    destruct (H o o' f' t (ss_detach o t Hobs) He) as [Hu | Hf]; right.
    - exact (Hmap o' (Ounlk t) Hu).
    - exact (Hmap o' (Ofree t) Hf).
  Qed.

  Lemma ss_WULK : WULK s -> WULK s'.
  Proof.
    intros H lw o t Hlk Hit.
    destruct (H lw o t Hlk (ss_iter o lw Hit)) as [Hnu Hnf].
    split; intros Hbad.
    - destruct (ss_detach o t (or_introl Hbad)) as [X | X];
        [exact (Hnu X) | exact (Hnf X)].
    - destruct (ss_detach o t (or_intror Hbad)) as [X | X];
        [exact (Hnu X) | exact (Hnf X)].
  Qed.

  Lemma ss_FR : FR s -> FR s'.
  Proof. intros H t x o Hstk Hfr. exact (H t x o Hstk (ss_fresh o t Hfr)). Qed.

  Lemma ss_WFresh : WFresh s -> WFresh s'.
  Proof. intros H t x o Hstk Hfr. exact (H t x o Hstk (ss_fresh o t Hfr)). Qed.

  Lemma ss_FNR : FNR s -> FNR s'.
  Proof. intros H. exact (sync_stop_preserves_FNR s s' H Hfwd). Qed.

  Lemma ss_FPI : FPI FType s -> FPI FType s'.
  Proof.
    intros H o f o' t lw Hfr He Hft Hlk.
    exact (Hmap o' (Oiter lw) (H o f o' t lw (ss_fresh o t Hfr) He Hft Hlk)).
  Qed.

  Lemma ss_RITR : RITR s -> RITR s'.
  Proof.
    intros H o t Hrd. destruct (H o t Hrd) as (Hnu & Hnf & Hnfr).
    repeat apply conj; intros Hbad.
    - destruct (ss_detach o t (or_introl Hbad)) as [X | X];
        [exact (Hnu X) | exact (Hnf X)].
    - destruct (ss_detach o t (or_intror Hbad)) as [X | X];
        [exact (Hnu X) | exact (Hnf X)].
    - exact (Hnfr (ss_fresh o t Hbad)).
  Qed.

  (** Where the empty bounding set is spent: no thread bounds anything, and
      RINFL says every thread in an entry does, so no entry has a thread in
      it. *)
  Lemma ss_RINFL : RINFL s -> RINFL s'.
  Proof. intros H o Tr t Hfl Hin. exact (Hquiet t (H o Tr t Hfl Hin)). Qed.

  Lemma ss_HD : HD s -> HD s'.
  Proof.
    intros H o f o' He Hnd. apply (H o f o' He).
    intros Hd. exact (Hnd (ss_detached o Hd)).
  Qed.

  Lemma ss_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p o lw Hlk Hr. destruct (H p o lw Hlk Hr) as [Hit | Hrt].
    - left.  exact (Hmap o (Oiter lw) Hit).
    - right. exact (Hmap o Oroot Hrt).
  Qed.

  Lemma ss_WUNLK : WUNLK s -> WUNLK s'.
  Proof. intros H o t lw Hlk Hobs. exact (H o t lw Hlk (ss_detach o t Hobs)). Qed.

  Lemma ss_WITR : WITR s -> WITR s'.
  Proof. intros H o t Hit. exact (H o t (ss_iter o t Hit)). Qed.

  Theorem sync_stop_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HU).
    repeat apply conj.
    - exact (ss_OW HOW).
    - exact (ss_RWOW HRWOW).
    - exact (ss_AWRT HAWRT).
    - exact (ss_IFL HIFL).
    - exact (ss_ULKR HULKR).
    - exact (ss_FLR HFLR).
    - exact (ss_WULK HWULK).
    - exact (ss_FR HFR).
    - exact (ss_WFresh HWFresh).
    - exact (ss_FNR HFNR).
    - exact (ss_FPI HFPI).
    - exact (ss_WNR HWNR).
    - exact (ss_RITR HRITR).
    - exact (ss_RINFL HRINFL).
    - exact (ss_HD HHD).
    - exact (ss_UNQRT_a HUa).
    - exact (ss_UNQRT_b HUb).
    - exact (ss_WUNLK HWU).
    - exact (ss_WITR HWI).
    - exact (ss_UNQR HU).
  Qed.

End quiescence.

(** The two hypotheses are not vacuous: the obvious map does satisfy them.
    Worth checking, for the reason RITR gives -- an abstractly stated step can
    be one no concrete step implements, and then the theorem above says
    nothing. *)
Definition sync_stop_Og (Og : ObsMap) : ObsMap := (set_map sync_obs) <$> Og.

Lemma sync_stop_Og_map m Og U T F o ob :
  obsv (to_LState_t m Og U T F) o ob ->
  obsv (to_LState_t (sync_stop_ms m) (sync_stop_Og Og) U T F) o (sync_obs ob).
Proof.
  intros Hob. destruct ob; [.. | exact Hob].
  all: destruct Hob as (th & S & Hlk & Hin).
  all: exists th, (set_map sync_obs S).
  all: split; [by rewrite /sync_stop_Og lookup_fmap Hlk |].
  all: apply (elem_of_map_2 sync_obs); exact Hin.
Qed.

Lemma sync_stop_Og_fwd m Og U T F o ob :
  obsv (to_LState_t (sync_stop_ms m) (sync_stop_Og Og) U T F) o ob ->
  obsv (to_LState_t m Og U T F) o ob
  \/ exists t, ob = Ofree t /\ obsv (to_LState_t m Og U T F) o (Ounlk t).
Proof.
  intros Hob. destruct ob; [.. | by left].
  all: destruct Hob as (th & S' & Hlk & Hin).
  all: rewrite /sync_stop_Og lookup_fmap in Hlk.
  all: apply fmap_Some in Hlk as (S & HS & ->).
  all: apply elem_of_map in Hin as (ob0 & Heq & Hin0).
  all: destruct ob0 as [t0|t0|t0|t0|]; simpl in Heq; try discriminate.
  all: injection Heq as Heq0; subst.
  all: try (left; by exists th, S).
  right. eexists. split; [reflexivity | by exists th, S].
Qed.

Corollary sync_stop_WellFormed FType m Og U T F :
  (forall t, ~ bnd m t) ->
  WellFormed FType (to_LState_t m Og U T F) ->
  WellFormed FType (to_LState_t (sync_stop_ms m) (sync_stop_Og Og) U T F).
Proof.
  intros Hq.
  exact (sync_stop_preserves_WellFormed FType m Og (sync_stop_Og Og) U T F
           (sync_stop_Og_fwd m Og U T F) (sync_stop_Og_map m Og U T F) Hq).
Qed.

Print Assumptions sync_stop_preserves_WellFormed.
Print Assumptions sync_stop_WellFormed.

(** ** ReadEnd, all nineteen

    The third action taken whole, and the one where doing it whole changes the
    statement rather than confirming it.  Two things had to be added that the
    per-invariant lemmas above did not need, and neither is a detail.

    The first is the departing thread's variables.  RWOW says a live variable's
    referent carries an observation; ReadEnd drops the thread's observations; so
    unless the thread's variables stop being live in the same step, RWOW fails
    immediately.  The type system does supply this -- \textsc{ToRCURead} types
    the read critical section as a *block*, and the reader's [rcuItr] variables
    are scoped to it, so they are gone at the end and never appear in the
    outer environment.  But that is a fact about the rule, and it has to be
    carried into the action's statement to be usable: hence [Hundf_t].  The
    earlier [read_end_preserves_IFL] and [read_end_preserves_RINFL] did not
    need it because neither invariant mentions the stack.

    The second is [Oroot], and it is the more interesting one -- see
    [read_end_naive_breaks_UNQRT_b] below.

    With those, the step is characterized by three properties of the
    observations, the same shape SyncStop uses: the thread's own observations
    are gone, everything else survives, and nothing new appears.  The pivotal
    hypothesis is [Hrd] -- ReadEnd is a *reader's* -- because RITR then says the
    departing thread held no detaching observation, so nothing that any
    detachment invariant depends on is among what is dropped.  Without RITR the
    action would be unsound, and this is the only place it is load-bearing. *)

Section departure.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U U' : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)) (t : TID).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t).

  (** The departing thread's own observations are gone, ... *)
  Hypothesis Hself : forall o ob, obs_tid ob = Some t -> ~ obsv s' o ob.
  (** ... everything that is not its own survives -- [Oroot] included, which is
      the whole of the second addition, ... *)
  Hypothesis Hkeep : forall o ob,
    obsv s o ob -> obs_tid ob <> Some t -> obsv s' o ob.
  (** ... and nothing new appears. *)
  Hypothesis Hshrink : forall o ob, obsv s' o ob -> obsv s o ob.

  (** The thread's variables leave scope, which ToRCURead's block supplies. *)
  Hypothesis Hundf_t    : forall x, undf s' x t.
  Hypothesis Hundf_grow : forall x t', undf s x t' -> undf s' x t'.

  (** And the departing thread is a reader. *)
  Hypothesis Hrd : rds m t.

  (** RITR is what makes the step safe: a reader holds no detaching
      observation, so dropping its entries drops nothing any detachment
      invariant relies on. *)
  Lemma re_detach_kept o ob :
    RITR s -> obsv s o ob ->
    (exists t0, ob = Ounlk t0 \/ ob = Ofree t0 \/ ob = Ofresh t0) ->
    obsv s' o ob.
  Proof.
    intros HR Hob [t0 [-> | [-> | ->]]]; apply (Hkeep o _ Hob); simpl;
      intros Hc; injection Hc as ->;
      destruct (HR o t Hrd) as (Hu & Hf & Hfr);
      [exact (Hu Hob) | exact (Hf Hob) | exact (Hfr Hob)].
  Qed.

  Lemma re_detached_fwd o : RITR s -> Detached s o -> Detached s' o.
  Proof.
    intros HR [t0 [H | [H | H]]]; exists t0.
    - left. apply (re_detach_kept o (Ounlk t0) HR H). by exists t0; left.
    - right; left. apply (re_detach_kept o (Ofree t0) HR H).
      by exists t0; right; left.
    - right; right. apply (re_detach_kept o (Ofresh t0) HR H).
      by exists t0; right; right.
  Qed.

  Lemma re_detached_bwd o : Detached s' o -> Detached s o.
  Proof.
    intros [t0 [H | [H | H]]]; exists t0;
      [left | right; left | right; right]; exact (Hshrink _ _ H).
  Qed.

  (** The writer is not the departing thread, so its observations are among
      those that survive.  This is WNR's only use in the development. *)
  Lemma re_writer_ne lw : WNR s -> lk m = Some lw -> lw <> t.
  Proof. intros HW Hlk ->. exact (HW t Hlk Hrd). Qed.

  (** A live variable of the departing thread is a contradiction. *)
  Lemma re_not_t x t' : ~ undf s' x t' -> t' <> t.
  Proof. intros Hnu ->. exact (Hnu (Hundf_t x)). Qed.

  (** The free list loses [t] from every entry and keeps its domain. *)
  Lemma re_flist_inv o Tr :
    flist s' o = Some Tr ->
    exists s0, F !! o = Some s0 /\ Tr = (fun x => x ∈ s0 ∖ {[t]}).
  Proof.
    simpl. rewrite /read_end_F lookup_fmap.
    destruct (F !! o) as [s0|] eqn:HS; simpl; [| discriminate].
    intros H. injection H as <-. by exists s0.
  Qed.

  Lemma re_flist o s0 :
    F !! o = Some s0 -> flist s' o = Some (fun x => x ∈ s0 ∖ {[t]}).
  Proof. intros H. simpl. by rewrite /read_end_F lookup_fmap H. Qed.

  (** The four the departure cannot reach. *)
  Lemma re_UNQRT_a : UNQRT_a s -> UNQRT_a s'. Proof. exact (fun H => H). Qed.
  Lemma re_UNQR    : UNQR s    -> UNQR s'.    Proof. exact (fun H => H). Qed.

  Lemma re_WNR : WNR s -> WNR s'.
  Proof. intros H t0 Hlk [Hrd0 _]. exact (H t0 Hlk Hrd0). Qed.

  Lemma re_HD : RITR s -> HD s -> HD s'.
  Proof.
    intros HR H o f o' He Hnd. apply (H o f o' He).
    intros Hd. exact (Hnd (re_detached_fwd o HR Hd)).
  Qed.

  Lemma re_OW : RITR s -> OW FType s -> OW FType s'.
  Proof.
    intros HR H o o' f f' x He He' Hf Hf'.
    destruct (H o o' f f' x He He' Hf Hf') as [Heq | [Hd | Hd]].
    - by left.
    - right; left.  exact (re_detached_fwd o HR Hd).
    - right; right. exact (re_detached_fwd o' HR Hd).
  Qed.

  Lemma re_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t0 o Hstk Hnu.
    assert (Hne : t0 <> t) by exact (re_not_t x t0 Hnu).
    assert (Hnu0 : ~ undf s x t0) by (intros Hc; exact (Hnu (Hundf_grow x t0 Hc))).
    destruct (H x t0 o Hstk Hnu0) as [Hit | [Hlk [Hu | [Hfr | Hfs]]]].
    - left. apply (Hkeep o _ Hit). simpl. by injection 1 as ->.
    - right. split; [exact Hlk |]. left.
      apply (Hkeep o _ Hu). simpl. by injection 1 as ->.
    - right. split; [exact Hlk |]. right; left.
      apply (Hkeep o _ Hfr). simpl. by injection 1 as ->.
    - right. split; [exact Hlk |]. right; right.
      apply (Hkeep o _ Hfs). simpl. by injection 1 as ->.
  Qed.

  Lemma re_AWRT : AWRT s -> AWRT s'.
  Proof.
    intros H y t0 Hstk Hnu.
    assert (Hne : t0 <> t) by exact (re_not_t y t0 Hnu).
    assert (Hnu0 : ~ undf s y t0) by (intros Hc; exact (Hnu (Hundf_grow y t0 Hc))).
    apply (Hkeep _ _ (H y t0 Hstk Hnu0)). simpl. by injection 1 as ->.
  Qed.

  Lemma re_IFL : IFL s -> IFL s'.
  Proof.
    intros H t0 o Tr Hit Hfl.
    assert (Hne : t0 <> t) by (intros ->; exact (Hself o (Oiter t) eq_refl Hit)).
    destruct (re_flist_inv o Tr Hfl) as [s0 [HS ->]].
    assert (Hfl0 : flist (to_LState_t m Og U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite HS).
    assert (Hin : t0 ∈ s0) by exact (H t0 o _ (Hshrink _ _ Hit) Hfl0).
    set_solver.
  Qed.

  Lemma re_ULKR : ULKR s -> RITR s -> ULKR s'.
  Proof.
    intros H HR o o' f' t0 Hobs He.
    assert (Hobs0 : obsv s o (Ounlk t0) \/ obsv s o (Ofree t0))
      by (destruct Hobs as [X | X]; [left | right]; exact (Hshrink _ _ X)).
    destruct (H o o' f' t0 Hobs0 He) as [Hu | Hf].
    - left.  apply (re_detach_kept o' (Ounlk t0) HR Hu). by exists t0; left.
    - right. apply (re_detach_kept o' (Ofree t0) HR Hf).
      by exists t0; right; left.
  Qed.

  Lemma re_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' f' Tr Hfl He.
    destruct (re_flist_inv o Tr Hfl) as [s0 [HS ->]].
    assert (Hfl0 : flist (to_LState_t m Og U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite HS).
    destruct (H o o' f' _ Hfl0 He) as [Tr' [Hfl' Hsub]].
    simpl in Hfl'. destruct (F !! o') as [s1|] eqn:HS'; [| discriminate].
    injection Hfl' as <-.
    exists (fun x => x ∈ s1 ∖ {[t]}). split; [exact (re_flist o' s1 HS') |].
    intros t0 Hin. assert (t0 ∈ s1) by set_solver.
    assert (t0 <> t) by set_solver. set_solver.
  Qed.

  Lemma re_WULK : WULK s -> WULK s'.
  Proof.
    intros H lw o t0 Hlk Hit.
    destruct (H lw o t0 Hlk (Hshrink _ _ Hit)) as [Hnu Hnf].
    split; intros Hbad; [exact (Hnu (Hshrink _ _ Hbad))
                        | exact (Hnf (Hshrink _ _ Hbad))].
  Qed.

  Lemma re_FR : FR s -> FR s'.
  Proof. intros H t0 x o Hstk Hfr. exact (H t0 x o Hstk (Hshrink _ _ Hfr)). Qed.

  Lemma re_WFresh : WFresh s -> WFresh s'.
  Proof. intros H t0 x o Hstk Hfr. exact (H t0 x o Hstk (Hshrink _ _ Hfr)). Qed.

  Lemma re_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t0 t1 Hfr.
    destruct (H o t0 t1 (Hshrink _ _ Hfr)) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad; [exact (H1 (Hshrink _ _ Hbad))
                                    | exact (H2 (Hshrink _ _ Hbad))
                                    | exact (H3 (Hshrink _ _ Hbad))].
  Qed.

  Lemma re_FPI : WNR s -> FPI FType s -> FPI FType s'.
  Proof.
    intros HW H o f o' t0 lw Hfr He Hft Hlk.
    apply (Hkeep o' _ (H o f o' t0 lw (Hshrink _ _ Hfr) He Hft Hlk)).
    simpl. intros Hc. injection Hc as Heq. exact (re_writer_ne lw HW Hlk Heq).
  Qed.

  Lemma re_RITR : RITR s -> RITR s'.
  Proof.
    intros H o t0 [Hrd0 _]. destruct (H o t0 Hrd0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad; [exact (H1 (Hshrink _ _ Hbad))
                                    | exact (H2 (Hshrink _ _ Hbad))
                                    | exact (H3 (Hshrink _ _ Hbad))].
  Qed.

  Lemma re_RINFL : RINFL s -> RINFL s'.
  Proof.
    intros H o Tr t0 Hfl Hin.
    destruct (re_flist_inv o Tr Hfl) as [s0 [HS ->]].
    assert (Hin0 : t0 ∈ s0) by set_solver.
    assert (Hfl0 : flist (to_LState_t m Og U T F) o = Some (fun x => x ∈ s0))
      by (simpl; by rewrite HS).
    split; [exact (H o _ t0 Hfl0 Hin0) |]. set_solver.
  Qed.

  Lemma re_UNQRT_b : WNR s -> UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros HW H p o lw Hlk Hr.
    destruct (H p o lw Hlk Hr) as [Hit | Hrt].
    - left. apply (Hkeep o _ Hit). simpl. intros Hc. injection Hc as Heq.
      exact (re_writer_ne lw HW Hlk Heq).
    - right. apply (Hkeep o _ Hrt). simpl. discriminate.
  Qed.

  Lemma re_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t0 lw Hlk [X | X];
      [exact (H o t0 lw Hlk (or_introl (Hshrink _ _ X)))
      |exact (H o t0 lw Hlk (or_intror (Hshrink _ _ X)))].
  Qed.

  Lemma re_WITR : WITR s -> WITR s'.
  Proof.
    intros H o t0 Hit.
    assert (Hne : t0 <> t)
      by (intros ->; exact (Hself o (Oiter t) eq_refl Hit)).
    destruct (H o t0 (Hshrink _ _ Hit)) as [Hlk | Hrd0];
      [by left | right; by split].
  Qed.

  Theorem read_end_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HU).
    repeat apply conj.
    - exact (re_OW HRITR HOW).
    - exact (re_RWOW HRWOW).
    - exact (re_AWRT HAWRT).
    - exact (re_IFL HIFL).
    - exact (re_ULKR HULKR HRITR).
    - exact (re_FLR HFLR).
    - exact (re_WULK HWULK).
    - exact (re_FR HFR).
    - exact (re_WFresh HWFresh).
    - exact (re_FNR HFNR).
    - exact (re_FPI HWNR HFPI).
    - exact (re_WNR HWNR).
    - exact (re_RITR HRITR).
    - exact (re_RINFL HRINFL).
    - exact (re_HD HRITR HHD).
    - exact (re_UNQRT_a HUa).
    - exact (re_UNQRT_b HWNR HUb).
    - exact (re_WUNLK HWU).
    - exact (re_WITR HWI).
    - exact (re_UNQR HU).
  Qed.

End departure.

Print Assumptions read_end_preserves_WellFormed.

(** ** The root observation, and a defect that stopped being one

    The three hypotheses above were, for a time, the best that could be said.
    The obvious way to describe what ReadEnd does to the observation map is to
    drop the departing thread's entries, and for every invariant about a
    *thread's* observations that is right: an observation names its observer,
    and the old [ObsWF] put it in that observer's entry.

    [Oroot] did not name an observer.  It is anonymous by design -- being the
    root is a property of the structure, not of anyone looking -- so the old
    [ObsWF] permitted it in any entry, a reader's included.  Dropping that
    reader's entries then destroyed it, and UNQRT_b, the one invariant that asks
    about [Oroot], failed.  There was a state witnessing exactly that, and the
    repair at the time was the smaller of the two available: keep [Hkeep] as an
    assumption about the action, and add [RTO] to the invariant to tie [Oroot]
    to [rt].

    That was the wrong half of the choice, and the other half is what the
    reconstruction now does.  [Oroot] is read off the machine state, so no entry
    holds it, no thread can drop it, and [ObsWF] can say what it wanted to say
    all along: an entry at [(o, t)] holds observations tagged [t].  The witness
    state is no longer well formed as an encoding -- that is the first lemma
    below -- and [Hkeep] stops being an assumption, because the naive step
    satisfies it.  [RTO] stops being an invariant: it is now true by
    computation.

    Two things are worth separating here.  The defect was real: under the old
    encoding the naive step was unsound, and the mechanization found it.  But it
    was a defect of the bridge and not of the type system, and the repair that
    removes it removes an invariant rather than adding one.  That is the only
    one of the twenty that went that way. *)

(** The old witness: the root observation filed under a reader.  The encoding
    now rejects it outright, which is the whole of the repair. *)
Definition ce_Og : ObsMap := {[ (0%nat, 2%nat) := {[Oroot]} ]}.

Lemma root_has_no_owner : ~ ObsWF ce_Og.
Proof.
  intros HWF.
  assert (Hlk : ce_Og !! (0%nat, 2%nat) = Some {[Oroot]})
    by apply lookup_singleton_eq.
  pose proof (HWF _ _ _ Oroot Hlk (elem_of_singleton_2 _ _ eq_refl)) as Hc.
  simpl in Hc. discriminate.
Qed.

(** The naive step, as a map operation rather than as three hypotheses. *)
Definition drop_thread (Og : ObsMap) (t : TID) : ObsMap :=
  filter (fun kv => kv.1.2 <> t) Og.

Lemma drop_thread_lookup Og t o t' :
  drop_thread Og t !! (o, t') = (if decide (t' = t) then None else Og !! (o, t')).
Proof.
  case_decide as Ht.
  - apply map_lookup_filter_None. right.
    intros S _ Hc. simpl in Hc. exact (Hc Ht).
  - destruct (Og !! (o, t')) as [S|] eqn:HS.
    + apply map_lookup_filter_Some. split; [exact HS | exact Ht].
    + apply map_lookup_filter_None. by left.
Qed.

Section naive.

  Variables (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)) (t : TID).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (read_end_ms m t) (drop_thread Og t) U T
              (read_end_F F t).

  (** Nothing of the departing thread's survives. *)
  Lemma drop_self o ob : ObsWF Og -> obs_tid ob = Some t -> ~ obsv s' o ob.
  Proof.
    intros HWF Htid Hob.
    destruct ob as [t0|t0|t0|t0|]; simpl in Htid;
      [| | | | discriminate];
      (injection Htid as ->;
       destruct Hob as [t1 [S [Hlk Hin]]];
       rewrite drop_thread_lookup in Hlk;
       case_decide as Ht1; [discriminate |];
       pose proof (HWF _ _ _ _ Hlk Hin) as Hc; simpl in Hc;
       injection Hc as ->; exact (Ht1 eq_refl)).
  Qed.

  (** Everything that is not its own survives, [Oroot] included -- and that last
      is now a matter of [rt], which the step does not touch. *)
  Lemma drop_keep o ob :
    ObsWF Og -> obsv s o ob -> obs_tid ob <> Some t -> obsv s' o ob.
  Proof.
    intros HWF Hob Htid. destruct ob as [t0|t0|t0|t0|]; [| | | | exact Hob];
      (destruct Hob as [t1 [S [Hlk Hin]]];
       pose proof (HWF _ _ _ _ Hlk Hin) as Htag; simpl in Htag;
       injection Htag as ->;
       exists t1, S; split; [| exact Hin];
       rewrite drop_thread_lookup; case_decide as Ht1; [| exact Hlk];
       exfalso; apply Htid; simpl; by rewrite Ht1).
  Qed.

  (** And nothing new appears. *)
  Lemma drop_shrink o ob : obsv s' o ob -> obsv s o ob.
  Proof.
    intros Hob. destruct ob as [t0|t0|t0|t0|]; [| | | | exact Hob];
      (destruct Hob as [t1 [S [Hlk Hin]]];
       rewrite drop_thread_lookup in Hlk; case_decide as Ht1;
       [discriminate | by exists t1, S]).
  Qed.

End naive.

(** The three hypotheses of [Section departure], discharged at the map operation
    that the old encoding could not support. *)
Theorem read_end_naive_is_sound m Og U T F t :
  ObsWF Og ->
  let s  := to_LState_t m Og U T F in
  let s' := to_LState_t (read_end_ms m t) (drop_thread Og t) U T
              (read_end_F F t) in
  (forall o ob, obs_tid ob = Some t -> ~ obsv s' o ob)
  /\ (forall o ob, obsv s o ob -> obs_tid ob <> Some t -> obsv s' o ob)
  /\ (forall o ob, obsv s' o ob -> obsv s o ob).
Proof.
  intros HWF s s'. repeat apply conj.
  - intros o ob. exact (drop_self m Og U T F t o ob HWF).
  - intros o ob. exact (drop_keep m Og U T F t o ob HWF).
  - exact (drop_shrink m Og U T F t).
Qed.

(** Dropping entries also cannot break [ObsWF], so the step composes with
    itself: two readers may leave in either order. *)
Lemma drop_thread_ObsWF Og t : ObsWF Og -> ObsWF (drop_thread Og t).
Proof.
  intros HWF o t' S ob Hlk Hin.
  rewrite drop_thread_lookup in Hlk. case_decide as Ht'; [discriminate |].
  exact (HWF _ _ _ _ Hlk Hin).
Qed.

Print Assumptions root_has_no_owner.
Print Assumptions read_end_naive_is_sound.
Print Assumptions drop_thread_ObsWF.

(** * The heap mutations, whole

    The three rules the paper is about, each taken as a step rather than one
    invariant at a time.  They are harder than Free, SyncStop and ReadEnd for a
    reason that only shows up when the whole action is attempted: each writes a
    field *and* changes the writer's observations, and for those three actions
    the eleven heap-free invariants were identities precisely because nothing
    touched the observation map.  Here they are not.  T-Insert promotes a node
    from [fresh] to [iterator], T-UnlinkH demotes one from [iterator] to
    [unlinked], and T-Replace does both at once, so RWOW, AWRT, IFL, WULK,
    WFresh, FNR, RITR and RINFL all acquire content.

    The observation change is given by properties rather than by a map
    operation, as for SyncStop and ReadEnd.  That is not only for uniformity.
    The revocation an unlink performs is of *the writer's* iterator observation
    and of nothing else -- the readers still holding the node must keep theirs,
    which is the entire point of the structure -- so an update that replaced a
    location's whole observation set would be wrong, and wrong in a way FPI
    cannot see and RWOW can.  [write_preserves_FPI] above uses exactly such an
    update; it is sound there because its conclusion never asks about a reader's
    observation, and it would not be sound here. *)

(** ** T-Insert

    [p.f := n] with [n] fresh and [n.f4] already pointing at [o].  Nothing is
    revoked, which makes this the least entangled of the three: the only
    observation that disappears is the freshness the step consumes.

    Two cases have content past the bookkeeping.  OW is one, and it is the case
    that shows why a fresh node cannot simply be treated as detached throughout:
    the pre-state discharges some of OW by [n]'s detachment, and after the step
    [n] is live, so those cases have to be re-discharged from the edge the write
    *removed*.  WULK is the other, and it spends FNR's third conjunct -- the one
    the ULKR obligation forced -- for the second time. *)

Section insertion.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (lw : TID) (op : Loc) (f : FName) (on oo : Loc) (f4 : FName)
            (rho : list FName).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m op f (VLoc on)) Og' U T F.

  Hypothesis Hlk : lk m = Some lw.

  (** The observation change: [n] becomes the writer's iterator and stops being
      fresh; nothing else appears, and nothing else is lost. *)
  Hypothesis Hpromote : obsv s' on (Oiter lw).
  Hypothesis Hnofresh : forall t, ~ obsv s' on (Ofresh t).
  Hypothesis Hnew : forall o ob,
    obsv s' o ob -> obsv s o ob \/ (o = on /\ ob = Oiter lw).
  Hypothesis Hkeep : forall o ob,
    obsv s o ob -> (o, ob) <> (on, Ofresh lw) -> obsv s' o ob.

  (** The rule's premises, and what the denotations make of them. *)
  (** References live in RCU fields.

      This replaces "every field is an RCU field", which is what the published
      proofs assume and which a class declaration forbids -- there are
      infinitely many field names and finitely many declared ones, so the two
      cannot both hold, and [rocq/BST.v] shows that stops the paper's own
      worked example from being typed.

      What the proofs actually need is weaker and is the natural reading of the
      model: the heap's reference structure lives entirely in RCU fields, so a
      scalar field holds a scalar.  Every use below applies it to an edge
      already in hand, which is why the weakening costs nothing. *)
  Hypothesis Hrefs : forall o g o',
    hp m o g = Some (VLoc o') -> FType g = RCUField.
  Hypothesis Hedge    : hp m op f = Some (VLoc oo).
  Hypothesis Hfresh   : obsv s on (Ofresh lw).
  Hypothesis Hitr_op  : obsv s op (Oiter lw).
  Hypothesis Hpo      : PointsOnlyAt (hp m) on f4 oo.
  Hypothesis Hno_in   : forall o g, hp m o g <> Some (VLoc on).
  Hypothesis Hin_on   : InHeap s on.
  Hypothesis Hnrt     : on <> rt m.
  Hypothesis Hfl_on   : flist s on = None.
  Hypothesis Hrho     : hstar (hp m) (rt m) rho = Some op.
  Hypothesis HU       : UNQR_h (hp m) (rt m).

  (** [n] is unreachable: nothing points at it and it is not the root. *)
  Lemma ins_unreach : forall sigma, hstar (hp m) (rt m) sigma <> Some on.
  Proof.
    apply (no_incoming_unreachable (hp m) (rt m) on Hno_in).
    intros Hc. exact (Hnrt (eq_sym Hc)).
  Qed.

  Lemma ins_np : on <> op.
  Proof. intros Hc. apply (ins_unreach rho). by rewrite Hrho Hc. Qed.

  (** The edge split, recording that an old edge is not at the written
      position -- which the OW case needs and a pure write lemma does not. *)
  Lemma ins_edge_split o g x :
    Edge s' o g x ->
    ((o, g) = (op, f) /\ x = on) \/ (Edge s o g x /\ (o, g) <> (op, f)).
  Proof.
    unfold Edge; simpl; intros He.
    destruct (edge_eq_dec o g op f) as [Heq | Hne].
    - left. injection Heq as -> ->. rewrite upd_same in He.
      injection He as <-. split; reflexivity.
    - right. rewrite upd_other in He; [| exact Hne]. by split.
  Qed.

  Lemma ins_InHeap o : InHeap s o -> InHeap s' o.
  Proof.
    intros [g [v Hv]]. unfold InHeap; simpl.
    destruct (edge_eq_dec o g op f) as [Heq | Hne].
    - injection Heq as -> ->. exists f, (VLoc on). apply upd_same.
    - exists g, v. by rewrite upd_other.
  Qed.

  (** Transfer, in both directions, for everything but [n]'s freshness. *)
  Lemma ins_keep_ob o ob : obsv s o ob -> ob <> Ofresh lw -> obsv s' o ob.
  Proof.
    intros Hob Hne. apply (Hkeep o ob Hob). intros Hc.
    injection Hc as _ Hc2. exact (Hne Hc2).
  Qed.

  Lemma ins_keep_iter o t : obsv s o (Oiter t) -> obsv s' o (Oiter t).
  Proof. intros H. apply (ins_keep_ob o _ H). discriminate. Qed.
  Lemma ins_keep_unlk o t : obsv s o (Ounlk t) -> obsv s' o (Ounlk t).
  Proof. intros H. apply (ins_keep_ob o _ H). discriminate. Qed.
  Lemma ins_keep_free o t : obsv s o (Ofree t) -> obsv s' o (Ofree t).
  Proof. intros H. apply (ins_keep_ob o _ H). discriminate. Qed.
  Lemma ins_keep_root o : obsv s o Oroot -> obsv s' o Oroot.
  Proof. intros H. apply (ins_keep_ob o _ H). discriminate. Qed.

  Lemma ins_keep_ne o ob : o <> on -> obsv s o ob -> obsv s' o ob.
  Proof. intros Hne Hob. apply (Hkeep o ob Hob). by injection 1 as ->. Qed.

  Lemma ins_back_ne o ob : o <> on -> obsv s' o ob -> obsv s o ob.
  Proof.
    intros Hne Hob. destruct (Hnew o ob Hob) as [X | [-> _]];
      [exact X | by contradiction].
  Qed.

  Lemma ins_detached_keep o : o <> on -> Detached s o -> Detached s' o.
  Proof.
    intros Hne [t0 [Hb | [Hb | Hb]]]; exists t0;
      [left | right; left | right; right]; exact (ins_keep_ne o _ Hne Hb).
  Qed.

  Lemma ins_fresh_inv o t : obsv s' o (Ofresh t) -> o <> on /\ obsv s o (Ofresh t).
  Proof.
    intros Hob.
    assert (Hne : o <> on) by (intros ->; exact (Hnofresh t Hob)).
    split; [exact Hne | exact (ins_back_ne o _ Hne Hob)].
  Qed.

  (** [n]'s only edge is the one the rule names. *)
  Lemma ins_fresh_edge g x : Edge s on g x -> g = f4 /\ x = oo.
  Proof.
    intros He. destruct Hpo as [Hf4 Hother].
    destruct (decide (g = f4)) as [-> | Hne].
    - split; [reflexivity |]. unfold Edge in He; simpl in He.
      rewrite Hf4 in He. by injection He as <-.
    - exfalso. exact (Hother g x Hne He).
  Qed.

  (** The writer's iterator is not detached: WULK denies it [unlinked] and
      [freeable], FNR denies it [fresh]. *)
  Lemma ins_op_live : FNR s -> WULK s -> ~ Detached s op.
  Proof.
    intros HF HW [t0 [Hb | [Hb | Hb]]].
    - exact (proj1 (HW lw op t0 Hlk Hitr_op) Hb).
    - exact (proj2 (HW lw op t0 Hlk Hitr_op) Hb).
    - exact (proj1 (HF op t0 lw Hb) Hitr_op).
  Qed.

  Lemma ins_op_not_fresh : FNR s -> forall t, ~ obsv s op (Ofresh t).
  Proof. intros HF t Hob. exact (proj1 (HF op t lw Hob) Hitr_op). Qed.

  (** Any predecessor of [o] other than [p] is detached.  This is OW applied to
      that edge against [p.f], and it is what re-discharges the OW cases the
      pre-state settled by [n]'s detachment. *)
  Lemma ins_other_pred_detached w h :
    FNR s -> WULK s -> OW FType s ->
    Edge s w h oo -> (w, h) <> (op, f) -> Detached s w.
  Proof.
    intros HF HW H He Hne.
    destruct (H op w f h oo Hedge He (Hrefs _ _ _ Hedge) (Hrefs _ _ _ He))
      as [Hsame | [Hd | Hd]].
    - exfalso. apply Hne. destruct Hsame as [H1 H2]. by subst.
    - exfalso. exact (ins_op_live HF HW Hd).
    - exact Hd.
  Qed.

  (** *** The cases the observation change carries *)

  Lemma ins_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hnu.
    destruct (H x t o Hstk Hnu) as [Hit | [Hlk' [Hu | [Hfr | Hfs]]]].
    - left. exact (ins_keep_iter o t Hit).
    - right. split; [exact Hlk' |]. left. exact (ins_keep_unlk o t Hu).
    - right. split; [exact Hlk' |]. right; left. exact (ins_keep_free o t Hfr).
    - destruct (decide (o = on)) as [-> | Hne].
      + (* the freshness the step consumes is replaced by the iterator *)
        rewrite Hlk in Hlk'. injection Hlk' as <-. by left.
      + right. split; [exact Hlk' |]. right; right.
        exact (ins_keep_ne o _ Hne Hfs).
  Qed.

  Lemma ins_AWRT : AWRT s -> AWRT s'.
  Proof. intros H y t Hstk Hnu. exact (ins_keep_iter _ t (H y t Hstk Hnu)). Qed.

  Lemma ins_IFL : IFL s -> IFL s'.
  Proof.
    intros H t o Tr Hit Hfl.
    destruct (Hnew o _ Hit) as [Hit0 | [-> _]].
    - exact (H t o Tr Hit0 Hfl).
    - exfalso. rewrite Hfl_on in Hfl. discriminate.
  Qed.

  Lemma ins_WULK : FNR s -> WULK s -> WULK s'.
  Proof.
    intros HF H lw' o t Hlk' Hit.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (decide (o = on)) as [-> | Hne].
    - (* fresh before, so FNR denied it both -- the third conjunct included *)
      destruct (HF on lw t Hfresh) as (_ & Hnu & Hnf).
      split; intros Hbad; destruct (Hnew on _ Hbad) as [Y | [_ Hc]];
        try discriminate; [exact (Hnu Y) | exact (Hnf Y)].
    - destruct (H lw o t Hlk (ins_back_ne o _ Hne Hit)) as [Hnu Hnf].
      split; intros Hbad; [exact (Hnu (ins_back_ne o _ Hne Hbad))
                          | exact (Hnf (ins_back_ne o _ Hne Hbad))].
  Qed.

  Lemma ins_FR : FR s -> FR s'.
  Proof.
    intros H t x o Hstk Hob.
    destruct (ins_fresh_inv o t Hob) as [Hne Hob0].
    destruct (H t x o Hstk Hob0) as [Hin Hal].
    split; [| exact Hal].
    intros o' g He. destruct (ins_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exact (Hne Hx).
    - exact (Hin o' g Hold).
  Qed.

  Lemma ins_WFresh : WFresh s -> WFresh s'.
  Proof.
    intros H t x o Hstk Hob.
    exact (H t x o Hstk (proj2 (ins_fresh_inv o t Hob))).
  Qed.

  Lemma ins_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t t' Hob.
    destruct (ins_fresh_inv o t Hob) as [Hne Hob0].
    destruct (H o t t' Hob0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      [exact (H1 (ins_back_ne o _ Hne Hbad))
      |exact (H2 (ins_back_ne o _ Hne Hbad))
      |exact (H3 (ins_back_ne o _ Hne Hbad))].
  Qed.

  Lemma ins_RITR : RITR s -> RITR s'.
  Proof.
    intros H o t Hrd. destruct (H o t Hrd) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      destruct (Hnew o _ Hbad) as [X | [_ Hc]]; try discriminate.
    - exact (H1 X).
    - exact (H2 X).
    - exact (H3 X).
  Qed.

  Lemma ins_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.
  Lemma ins_WNR   : WNR s   -> WNR s'.   Proof. exact (fun H => H). Qed.

  (** *** The cases the write carries *)

  Lemma ins_OW : FNR s -> WULK s -> OW FType s -> OW FType s'.
  Proof.
    intros HF HW H o o' g g' x He He' Hg Hg'.
    destruct (ins_edge_split o  g  x He)  as [[Heq  Hx ] | [Hold  Hnep ]];
    destruct (ins_edge_split o' g' x He') as [[Heq' Hx'] | [Hold' Hnep']].
    - injection Heq as -> ->. injection Heq' as -> ->. by left.
    - exfalso. rewrite Hx in Hold'. exact (Hno_in o' g' Hold').
    - exfalso. rewrite Hx' in Hold. exact (Hno_in o g Hold).
    - destruct (decide (o = on)) as [-> | Hne].
      + destruct (ins_fresh_edge g x Hold) as [-> ->].
        destruct (decide (o' = on)) as [-> | Hne'].
        * destruct (ins_fresh_edge g' oo Hold') as [-> _].
          left. split; reflexivity.
        * right; right. apply (ins_detached_keep o' Hne').
          exact (ins_other_pred_detached o' g' HF HW H Hold' Hnep').
      + destruct (decide (o' = on)) as [-> | Hne'].
        * destruct (ins_fresh_edge g' x Hold') as [-> ->].
          right; left. apply (ins_detached_keep o Hne).
          exact (ins_other_pred_detached o g HF HW H Hold Hnep).
        * destruct (H o o' g g' x Hold Hold' Hg Hg') as [Hsame | [Hd | Hd]].
          -- by left.
          -- right; left.  exact (ins_detached_keep o Hne Hd).
          -- right; right. exact (ins_detached_keep o' Hne' Hd).
  Qed.

  Lemma ins_ULKR : FNR s -> ULKR s -> ULKR s'.
  Proof.
    intros HF H o o' g t Hobs He.
    assert (Hobs0 : obsv s o (Ounlk t) \/ obsv s o (Ofree t)).
    { destruct Hobs as [X | X].
      - destruct (Hnew o _ X) as [Y | [_ Hc]]; [by left | discriminate].
      - destruct (Hnew o _ X) as [Y | [_ Hc]]; [by right | discriminate]. }
    destruct (ins_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exfalso. subst o. destruct Hobs0 as [Y | Y];
        [exact (proj1 (proj2 (HF on lw t Hfresh)) Y)
        |exact (proj2 (proj2 (HF on lw t Hfresh)) Y)].
    - destruct (H o o' g t Hobs0 Hold) as [Y | Y];
        [left; exact (ins_keep_unlk o' t Y) | right; exact (ins_keep_free o' t Y)].
  Qed.

  Lemma ins_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' g Tr Hfl He.
    destruct (ins_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exfalso. subst o. rewrite Hfl_on in Hfl. discriminate.
    - exact (H o o' g Tr Hfl Hold).
  Qed.

  Lemma ins_FPI : FNR s -> FPI FType s -> FPI FType s'.
  Proof.
    intros HF H o g x t lw' Hob He Hft Hlk'.
    destruct (ins_fresh_inv o t Hob) as [Hne Hob0].
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (ins_edge_split o g x He) as [[Heq _] | [Hold _]].
    - exfalso. injection Heq as -> ->. exact (ins_op_not_fresh HF t Hob0).
    - exact (ins_keep_iter x lw (H o g x t lw Hob0 Hold Hft Hlk)).
  Qed.

  Lemma ins_HD : FNR s -> WULK s -> HD s -> HD s'.
  Proof.
    intros HF HW H o g x He Hnd.
    destruct (ins_edge_split o g x He) as [[_ ->] | [Hold _]].
    - exact (ins_InHeap on Hin_on).
    - destruct (decide (o = on)) as [-> | Hne].
      + destruct (ins_fresh_edge g x Hold) as [-> ->].
        apply ins_InHeap. exact (H op f oo Hedge (ins_op_live HF HW)).
      + apply ins_InHeap. apply (H o g x Hold).
        intros Hd. exact (Hnd (ins_detached_keep o Hne Hd)).
  Qed.

  Lemma ins_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof.
    intros H o g He.
    destruct (ins_edge_split o g (rt (ms s')) He) as [[_ Hx] | [Hold _]].
    - exact (Hnrt (eq_sym Hx)).
    - exact (H o g Hold).
  Qed.

  Lemma ins_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p x lw' Hlk' Hr.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (decide (x = on)) as [-> | Hne].
    - by left.
    - assert (Hnoback : forall tau, hstar (hp m) oo tau <> Some op)
        by exact (UNQR_no_back_edge (hp m) (rt m) op f oo rho HU Hrho Hedge).
      assert (Hq : exists q, hstar (hp m) (rt m) q = Some x).
      { destruct (hstar_insert_char (hp m) (rt m) op f oo on f4 p x
                    Hpo ins_np Hedge Hnoback Hr)
          as [[Ha _] | [[Hx _] | [p1 [tau [_ [_ Hr2]]]]]].
        - exists p. exact Ha.
        - by contradiction.
        - exists (p1 ++ f :: tau). exact Hr2. }
      destruct Hq as [q Hq]. destruct (H q x lw Hlk Hq) as [Hit | Hrt].
      + left.  exact (ins_keep_iter x lw Hit).
      + right. exact (ins_keep_root x Hrt).
  Qed.

  Lemma ins_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t lw' Hlk' Hobs. apply (H o t lw' Hlk').
    destruct Hobs as [X | X]; destruct (Hnew o _ X) as [Y | [_ Hc]];
      [by left | discriminate | by right | discriminate].
  Qed.

  Lemma ins_WITR : WITR s -> WITR s'.
  Proof.
    intros H o t Hit. destruct (Hnew o _ Hit) as [Y | [_ Hc]].
    - exact (H o t Y).
    - injection Hc as Ht. left. rewrite Ht. exact Hlk.
  Qed.

  Lemma ins_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros _ p p' x H1 H2.
    exact (UNQR_insert_reachable (hp m) (rt m) op f oo on f4 rho HU Hpo Hrho
             Hedge ins_unreach p p' x H1 H2).
  Qed.

  (** *** The post-type environment: [n : rcuItr (rho.f) N1]

      The inserted node takes the path to [p] extended by [f].  Two of the eight
      conjuncts have content.  The path itself is the write, walked: [rho]
      avoids the written edge -- it reaches [p], and a path to [p] cannot
      traverse an edge out of [p] -- so it walks unchanged and then the new edge
      is taken.  The prefix condition is the same fact applied to each prefix,
      which is what [avoids_prefix] is for.  The rest transfer. *)
  Variables (xn : Var) (N1 : FieldMap).
  Hypothesis Hstk_n  : stk m xn lw = Some on.
  Hypothesis Hundf_n : ~ undf s xn lw.
  Hypothesis Hfields_n : forall g v, N1 g = Some v -> FieldHolds s lw on g v.
  Hypothesis Hprefix : forall rho1 rho2, rho1 ++ rho2 = rho ->
    exists o', hstar (hp m) (rt m) rho1 = Some o' /\ obsv s o' (Oiter lw).

  Lemma ins_avoids : avoids (hp m) (rt m) rho op f.
  Proof. exact (UNQR_avoids (hp m) (rt m) op f rho HU Hrho). Qed.

  Lemma ins_prefix_walk rho1 rho2 :
    rho1 ++ rho2 = rho ->
    hstar (hp (ms s')) (rt m) rho1 = hstar (hp m) (rt m) rho1.
  Proof.
    intros Heq. apply hstar_upd_avoids.
    apply (avoids_prefix (hp m) rho1 rho2). rewrite Heq. exact ins_avoids.
  Qed.

  Lemma ins_path : hstar (hp (ms s')) (rt m) (rho ++ [f]) = Some on.
  Proof.
    rewrite (hstar_upd_through (hp m) op f on rho [] (rt m) ins_avoids Hrho).
    reflexivity.
  Qed.

  (** The fresh node's own field, untouched by a write at [p]. *)
  Lemma ins_hp_n g : hp (ms s') on g = hp m on g.
  Proof.
    apply upd_other. intros Hc. injection Hc as Hc1 _. exact (ins_np Hc1).
  Qed.

  Lemma ins_FieldHolds g v : FieldHolds s lw on g v -> FieldHolds s' lw on g v.
  Proof.
    assert (Hg : hp (ms s') on g = hp (ms s) on g) by exact (ins_hp_n g).
    destruct v as [z|].
    - intros [oz (Hz & He & Hit & Hfl)]. unfold FieldHolds. rewrite Hg.
      exists oz. repeat apply conj;
        [exact Hz | exact He | exact (ins_keep_iter oz lw Hit) | exact Hfl].
    - intros He. unfold FieldHolds. rewrite Hg. exact He.
  Qed.

  Theorem insert_post_env : D_rcuItr s' lw xn (rho ++ [f]) N1.
  Proof.
    exists on. repeat apply conj.
    - exact Hstk_n.
    - exact Hpromote.
    - intros Hc. exact (Hundf_n Hc).
    - intros g v HN. exact (ins_FieldHolds g v (Hfields_n g v HN)).
    - intros rho1 rho2 Heq.
      destruct (decide (rho1 = rho ++ [f])) as [-> | Hne].
      + exists on. split; [exact ins_path | exact Hpromote].
      + (* a proper prefix: it lies within [rho] and walks unchanged *)
        assert (Hne2 : rho2 <> []).
        { intros ->. apply Hne. by rewrite app_nil_r in Heq. }
        destruct (prefix_of_snoc rho1 rho2 rho f Heq Hne2) as [sigma Hs].
        destruct (Hprefix rho1 sigma Hs) as [o' [Hr Hit]].
        exists o'. split.
        * rewrite (ins_prefix_walk rho1 sigma Hs). exact Hr.
        * exact (ins_keep_iter o' lw Hit).
    - exact ins_path.
    - exact Hlk.
    - exact Hfl_on.
  Qed.

  (** *** The parent: [p : rcuItr rho Np[f |-> n]]

      The rule records the written field in the parent's map, so the denotation
      has to hold the new entry: [p.f] now holds [n], which the writer observes
      as an iterator.  Every other entry transfers, the write having touched one
      field and nothing having pointed at [n] before. *)
  Variables (xp : Var) (Np : FieldMap).
  Hypothesis Hstk_p    : stk m xp lw = Some op.
  Hypothesis Hundf_p   : ~ undf s xp lw.
  Hypothesis Hfl_op    : flist s op = None.
  Hypothesis Hfields_p : forall g v, Np g = Some v -> FieldHolds s lw op g v.

  Definition Nparent : FieldMap :=
    fun g => if decide (g = f) then Some (FVar xn) else Np g.

  Lemma ins_hp_p g : g <> f -> hp (ms s') op g = hp m op g.
  Proof.
    intros Hne. apply upd_other. intros Hc. injection Hc as Hc2. exact (Hne Hc2).
  Qed.

  Lemma ins_FieldHolds_p g v :
    g <> f -> FieldHolds s lw op g v -> FieldHolds s' lw op g v.
  Proof.
    intros Hne.
    assert (Hg : hp (ms s') op g = hp (ms s) op g) by exact (ins_hp_p g Hne).
    destruct v as [z|].
    - intros [oz (Hz & He & Hit & Hfl)].
      assert (Hon : oz <> on) by (intros ->; exact (Hno_in op g He)).
      unfold FieldHolds. rewrite Hg. exists oz.
      repeat apply conj;
        [exact Hz | exact He | exact (ins_keep_ne oz _ Hon Hit) | exact Hfl].
    - intros He. unfold FieldHolds. rewrite Hg. exact He.
  Qed.

  Theorem insert_post_env_parent : D_rcuItr s' lw xp rho Nparent.
  Proof.
    exists op. repeat apply conj.
    - exact Hstk_p.
    - exact (ins_keep_iter op lw Hitr_op).
    - intros Hc. exact (Hundf_p Hc).
    - intros g v HN. unfold Nparent in HN.
      destruct (decide (g = f)) as [-> | Hne].
      + injection HN as <-. unfold FieldHolds. exists on.
        repeat apply conj;
          [exact Hstk_n | apply upd_same | exact Hpromote | exact Hfl_on].
      + exact (ins_FieldHolds_p g v Hne (Hfields_p g v HN)).
    - intros rho1 rho2 Heq. destruct (Hprefix rho1 rho2 Heq) as [o' [Hr Hit]].
      exists o'. split.
      + rewrite (hstar_upd_avoids (hp m) op f (VLoc on) rho1 (rt m)
                   (avoids_prefix (hp m) rho1 rho2 (rt m) op f
                      ltac:(rewrite Heq; exact ins_avoids))).
        exact Hr.
      + exact (ins_keep_iter o' lw Hit).
    - rewrite (hstar_upd_avoids (hp m) op f (VLoc on) rho (rt m) ins_avoids).
      exact Hrho.
    - exact Hlk.
    - exact Hfl_op.
  Qed.

  (** *** The displaced node: [o : rcuItr (rho.f.f4) N2]

      The one component of an insertion's post-environment that is neither the
      new node nor the parent.  Inserting *lengthens* the path to everything
      below [o] by one field, and the denotation records that: [o] now sits at
      [rho.f.f4] rather than [rho.f].  The prefix condition is the only case
      with work, and it is a three-way split -- a prefix of [rho], [rho.f]
      itself, or the whole path -- which two applications of
      [prefix_of_snoc] separate. *)
  Variables (xo : Var) (N2 : FieldMap).
  Hypothesis Hstk_o    : stk m xo lw = Some oo.
  Hypothesis Hundf_o   : ~ undf s xo lw.
  Hypothesis Hitr_oo   : obsv s oo (Oiter lw).
  Hypothesis Hfl_oo    : flist s oo = None.
  Hypothesis Hfields_o : forall g v, N2 g = Some v -> FieldHolds s lw oo g v.

  Lemma ins_oo_ne_op : oo <> op.
  Proof.
    intros Hc. assert (Hr : hstar (hp m) (rt m) (rho ++ [f]) = Some op)
      by (rewrite hstar_app Hrho /=; rewrite Hedge; by rewrite Hc).
    assert (Hx : rho ++ [f] = rho) by exact (HU (rho ++ [f]) rho op Hr Hrho).
    assert (Hlen : length (rho ++ [f]) = length rho) by (rewrite Hx; reflexivity).
    rewrite length_app in Hlen. simpl in Hlen. lia.
  Qed.

  Lemma ins_oo_reach : hstar (hp (ms s')) (rt m) (rho ++ [f; f4]) = Some oo.
  Proof.
    rewrite (hstar_upd_through (hp m) op f on rho [f4] (rt m) ins_avoids Hrho).
    simpl. rewrite upd_other; [| intros Hc; injection Hc as Hc1 _;
                                 exact (ins_np Hc1)].
    by rewrite (proj1 Hpo).
  Qed.

  Lemma ins_hp_oo g : hp (ms s') oo g = hp m oo g.
  Proof.
    apply upd_other. intros Hc. injection Hc as Hc1 _.
    exact (ins_oo_ne_op Hc1).
  Qed.

  Lemma ins_FieldHolds_o g v :
    FieldHolds s lw oo g v -> FieldHolds s' lw oo g v.
  Proof.
    assert (Hg : hp (ms s') oo g = hp (ms s) oo g) by exact (ins_hp_oo g).
    destruct v as [z|].
    - intros [oq (Hq & He & Hit & Hfl)].
      assert (Hon : oq <> on) by (intros ->; exact (Hno_in oo g He)).
      unfold FieldHolds. rewrite Hg. exists oq.
      repeat apply conj;
        [exact Hq | exact He | exact (ins_keep_ne oq _ Hon Hit) | exact Hfl].
    - intros He. unfold FieldHolds. rewrite Hg. exact He.
  Qed.

  Theorem insert_post_env_displaced : D_rcuItr s' lw xo (rho ++ [f; f4]) N2.
  Proof.
    exists oo. repeat apply conj.
    - exact Hstk_o.
    - exact (ins_keep_iter oo lw Hitr_oo).
    - intros Hc. exact (Hundf_o Hc).
    - intros g v HN. exact (ins_FieldHolds_o g v (Hfields_o g v HN)).
    - intros rho1 rho2 Heq.
      destruct (decide (rho1 = rho ++ [f; f4])) as [-> | Hne1].
      + exists oo. split; [exact ins_oo_reach | exact (ins_keep_iter oo lw Hitr_oo)].
      + assert (Hne2 : rho2 <> []).
        { intros ->. apply Hne1. by rewrite app_nil_r in Heq. }
        assert (Heq' : rho1 ++ rho2 = (rho ++ [f]) ++ [f4])
          by (rewrite -app_assoc; exact Heq).
        destruct (prefix_of_snoc rho1 rho2 (rho ++ [f]) f4 Heq' Hne2)
          as [sigma Hs].
        destruct (decide (rho1 = rho ++ [f])) as [-> | Hne3].
        * exists on. split; [exact ins_path | exact Hpromote].
        * assert (Hne4 : sigma <> []).
          { intros ->. apply Hne3. by rewrite app_nil_r in Hs. }
          destruct (prefix_of_snoc rho1 sigma rho f Hs Hne4) as [tau Ht].
          destruct (Hprefix rho1 tau Ht) as [o' [Hr Hit]].
          exists o'. split.
          -- rewrite (ins_prefix_walk rho1 tau Ht). exact Hr.
          -- exact (ins_keep_iter o' lw Hit).
    - exact ins_oo_reach.
    - exact Hlk.
    - exact Hfl_oo.
  Qed.

  Theorem insert_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact (ins_OW HFNR HWULK HOW).
    - exact (ins_RWOW HRWOW).
    - exact (ins_AWRT HAWRT).
    - exact (ins_IFL HIFL).
    - exact (ins_ULKR HFNR HULKR).
    - exact (ins_FLR HFLR).
    - exact (ins_WULK HFNR HWULK).
    - exact (ins_FR HFR).
    - exact (ins_WFresh HWFresh).
    - exact (ins_FNR HFNR).
    - exact (ins_FPI HFNR HFPI).
    - exact (ins_WNR HWNR).
    - exact (ins_RITR HRITR).
    - exact (ins_RINFL HRINFL).
    - exact (ins_HD HFNR HWULK HHD).
    - exact (ins_UNQRT_a HUa).
    - exact (ins_UNQRT_b HUb).
    - exact (ins_WUNLK HWU).
    - exact (ins_WITR HWI).
    - exact (ins_UNQR HUq).
  Qed.

End insertion.

Print Assumptions insert_preserves_WellFormed.
Print Assumptions insert_post_env.
Print Assumptions insert_post_env_parent.
Print Assumptions insert_post_env_displaced.

(** ** T-UnlinkH

    [x.f1 := r], where [x.f1] was [z] and [z.f2] is [r]: [z] leaves the
    structure and becomes [unlinked].  The revocation is what makes this harder
    than T-Insert, and it is a revocation of *the writer's* iterator observation
    only -- the readers still traversing [z] keep theirs, which is what the RWOW
    case turns on and what a whole-entry update would have destroyed.

    Two of the rule's premises are spent here, and both were added by earlier
    repairs.  The premise excluding a [rcuFresh] predecessor of [z] -- the repair
    that [FPI_not_preserved_by_replace] forced -- is used twice, once in ULKR and
    once in FPI.  And ULKR needs one thing more, which the invariant set does not
    supply; see [Hunlk_writer] and the discussion at
    [unlinked_observations_need_not_be_the_writers] below. *)

Section unlinking.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (lw : TID) (ox : Loc) (f1 : FName) (oz : Loc) (f2 : FName)
            (ow : Loc) (rho : list FName).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m ox f1 (VLoc ow)) Og' U T F.

  Hypothesis Hlk : lk m = Some lw.

  (** The observation change: the writer's iterator on [z] becomes an unlinked
      observation.  Everything else -- including every reader's iterator on [z]
      -- is untouched. *)
  Hypothesis Hdemote : obsv s' oz (Ounlk lw).
  Hypothesis Hnoiter : ~ obsv s' oz (Oiter lw).
  Hypothesis Hnew : forall o ob,
    obsv s' o ob -> obsv s o ob \/ (o = oz /\ ob = Ounlk lw).
  Hypothesis Hkeep : forall o ob,
    obsv s o ob -> (o, ob) <> (oz, Oiter lw) -> obsv s' o ob.

  (** The rule's premises. *)
  (** References live in RCU fields; see the note in the T-Insert section. *)
  Hypothesis Hrefs : forall o g o',
    hp m o g = Some (VLoc o') -> FType g = RCUField.
  Hypothesis Hedge1  : hp m ox f1 = Some (VLoc oz).
  Hypothesis Hedge2  : hp m oz f2 = Some (VLoc ow).
  Hypothesis Hitr_ox : obsv s ox (Oiter lw).
  Hypothesis Hitr_oz : obsv s oz (Oiter lw).
  Hypothesis Hitr_ow : obsv s ow (Oiter lw).
  Hypothesis Hfl_ow  : flist s ow = None.
  Hypothesis Hrho    : hstar (hp m) (rt m) rho = Some ox.
  Hypothesis HU      : UNQR_h (hp m) (rt m).

  (** The repaired premise of T-UnlinkH: no fresh reference points at [z]. *)
  Hypothesis Hno_fresh_pred :
    forall q t g, obsv s q (Ofresh t) -> hp m q g <> Some (VLoc oz).

  Lemma unl_oz_reach : hstar (hp m) (rt m) (rho ++ [f1]) = Some oz.
  Proof. rewrite hstar_app Hrho /=. by rewrite Hedge1. Qed.

  (** Nothing below [r] reaches back to [z], nor to [x]: the tree shape, at the
      two depths the characterisation and the disequality need. *)
  Lemma unl_noback_z : forall tau, hstar (hp m) ow tau <> Some oz.
  Proof.
    apply (UNQR_no_back (hp m) (rt m) oz (rho ++ [f1]) [f2] ow HU unl_oz_reach);
      [discriminate |].
    rewrite hstar_app unl_oz_reach /=. by rewrite Hedge2.
  Qed.

  Lemma unl_noback_x : forall tau, hstar (hp m) ow tau <> Some ox.
  Proof.
    apply (UNQR_no_back (hp m) (rt m) ox rho [f1; f2] ow HU Hrho); [discriminate |].
    rewrite hstar_app Hrho /=. rewrite Hedge1 /=. by rewrite Hedge2.
  Qed.

  Lemma unl_wz : ow <> oz.
  Proof. intros Hc. apply (unl_noback_z []). by rewrite /= Hc. Qed.

  Lemma unl_edge_split o g x :
    Edge s' o g x ->
    ((o, g) = (ox, f1) /\ x = ow) \/ (Edge s o g x /\ (o, g) <> (ox, f1)).
  Proof.
    unfold Edge; simpl; intros He.
    destruct (edge_eq_dec o g ox f1) as [Heq | Hne].
    - left. injection Heq as -> ->. rewrite upd_same in He.
      injection He as <-. split; reflexivity.
    - right. rewrite upd_other in He; [| exact Hne]. by split.
  Qed.

  Lemma unl_InHeap o : InHeap s o -> InHeap s' o.
  Proof.
    intros [g [v Hv]]. unfold InHeap; simpl.
    destruct (edge_eq_dec o g ox f1) as [Heq | Hne].
    - injection Heq as -> ->. exists f1, (VLoc ow). apply upd_same.
    - exists g, v. by rewrite upd_other.
  Qed.

  Lemma unl_keep_ne o ob : o <> oz -> obsv s o ob -> obsv s' o ob.
  Proof. intros Hne Hob. apply (Hkeep o ob Hob). by injection 1 as ->. Qed.

  Lemma unl_back_ne o ob : o <> oz -> obsv s' o ob -> obsv s o ob.
  Proof.
    intros Hne Hob. destruct (Hnew o ob Hob) as [X | [-> _]];
      [exact X | by contradiction].
  Qed.

  Lemma unl_keep_ob o ob : obsv s o ob -> ob <> Oiter lw -> obsv s' o ob.
  Proof.
    intros Hob Hne. apply (Hkeep o ob Hob). intros Hc.
    injection Hc as _ Hc2. exact (Hne Hc2).
  Qed.

  (** Detachment only grows: [z] acquires it and nothing loses it. *)
  Lemma unl_detached_keep o : Detached s o -> Detached s' o.
  Proof.
    intros [t0 [Hb | [Hb | Hb]]]; exists t0;
      [left | right; left | right; right]; apply unl_keep_ob;
      [exact Hb | discriminate | exact Hb | discriminate | exact Hb | discriminate].
  Qed.

  (** The writer's iterators are not detached. *)
  Lemma unl_live q : FNR s -> WULK s -> obsv s q (Oiter lw) -> ~ Detached s q.
  Proof.
    intros HF HW Hit [t0 [Hb | [Hb | Hb]]].
    - exact (proj1 (HW lw q t0 Hlk Hit) Hb).
    - exact (proj2 (HW lw q t0 Hlk Hit) Hb).
    - exact (proj1 (HF q t0 lw Hb) Hit).
  Qed.

  (** Any predecessor of [z] other than [x] is detached -- OW against the edge
      the rule names -- and, not being fresh, is unlinked or freeable. *)
  Lemma unl_other_pred q g :
    FNR s -> WULK s -> OW FType s -> WUNLK s ->
    Edge s q g oz -> (q, g) <> (ox, f1) ->
    obsv s q (Ounlk lw) \/ obsv s q (Ofree lw).
  Proof.
    intros HF HW H HWU He Hne.
    destruct (H ox q f1 g oz Hedge1 He (Hrefs _ _ _ Hedge1) (Hrefs _ _ _ He))
      as [Hsame | [Hd | Hd]].
    - exfalso. apply Hne. destruct Hsame as [H1 H2]. by subst.
    - exfalso. exact (unl_live ox HF HW Hitr_ox Hd).
    - destruct Hd as [t0 [Hb | [Hb | Hb]]].
      + assert (Ht : t0 = lw) by exact (HWU q t0 lw Hlk (or_introl Hb)).
        rewrite Ht in Hb. by left.
      + assert (Ht : t0 = lw) by exact (HWU q t0 lw Hlk (or_intror Hb)).
        rewrite Ht in Hb. by right.
      + exfalso. exact (Hno_fresh_pred q t0 g Hb He).
  Qed.

  (** *** The cases the observation change carries *)

  Lemma unl_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hnu.
    destruct (H x t o Hstk Hnu) as [Hit | [Hlk' [Hu | [Hfr | Hfs]]]].
    - destruct (decide ((o, Oiter t) = (oz, Oiter lw))) as [Heq | Hne].
      + (* the writer's own reference to the node it just unlinked: it is
           typed [unlinked] after the step, and RWOW's second disjunct is
           exactly that.  A *reader's* iterator on [z] is not this case. *)
        injection Heq as -> ->. right. split; [exact Hlk | left; exact Hdemote].
      + left. exact (Hkeep o _ Hit Hne).
    - right. split; [exact Hlk' |]. left. apply unl_keep_ob; [exact Hu | discriminate].
    - right. split; [exact Hlk' |]. right; left.
      apply unl_keep_ob; [exact Hfr | discriminate].
    - right. split; [exact Hlk' |]. right; right.
      apply unl_keep_ob; [exact Hfs | discriminate].
  Qed.

  Lemma unl_oz_not_root : UNQRT_a s -> oz <> rt m.
  Proof.
    intros H Hc. apply (H ox f1). unfold Edge; simpl. rewrite -Hc. exact Hedge1.
  Qed.

  Lemma unl_ow_not_root : UNQRT_a s -> ow <> rt m.
  Proof.
    intros H Hc. apply (H oz f2). unfold Edge; simpl. rewrite -Hc. exact Hedge2.
  Qed.

  Lemma unl_AWRT : UNQRT_a s -> AWRT s -> AWRT s'.
  Proof.
    intros Ha H y t Hstk Hnu. apply (Hkeep _ _ (H y t Hstk Hnu)).
    injection 1 as Hc _. exact (unl_oz_not_root Ha (eq_sym Hc)).
  Qed.

  Lemma unl_IFL : IFL s -> IFL s'.
  Proof.
    intros H t o Tr Hit Hfl.
    destruct (Hnew o _ Hit) as [Hit0 | [_ Hc]]; [| discriminate].
    exact (H t o Tr Hit0 Hfl).
  Qed.

  Lemma unl_WULK : WULK s -> WULK s'.
  Proof.
    intros H lw' o t Hlk' Hit.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    assert (Hne : o <> oz) by (intros ->; exact (Hnoiter Hit)).
    destruct (H lw o t Hlk (unl_back_ne o _ Hne Hit)) as [Hnu Hnf].
    split; intros Hbad; [exact (Hnu (unl_back_ne o _ Hne Hbad))
                        | exact (Hnf (unl_back_ne o _ Hne Hbad))].
  Qed.

  Lemma unl_fresh_inv o t : obsv s' o (Ofresh t) -> obsv s o (Ofresh t).
  Proof.
    intros Hob. destruct (Hnew o _ Hob) as [X | [_ Hc]]; [exact X | discriminate].
  Qed.

  Lemma unl_FR : FR s -> FR s'.
  Proof.
    intros H t x o Hstk Hob.
    destruct (H t x o Hstk (unl_fresh_inv o t Hob)) as [Hin Hal].
    split; [| exact Hal].
    intros o' g He. destruct (unl_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - subst o. exact (Hin oz f2 Hedge2).
    - exact (Hin o' g Hold).
  Qed.

  Lemma unl_WFresh : WFresh s -> WFresh s'.
  Proof. intros H t x o Hstk Hob. exact (H t x o Hstk (unl_fresh_inv o t Hob)). Qed.

  Lemma unl_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t t' Hob.
    assert (Hob0 : obsv s o (Ofresh t)) by exact (unl_fresh_inv o t Hob).
    assert (Hne : o <> oz) by (intros ->; exact (proj1 (H oz t lw Hob0) Hitr_oz)).
    destruct (H o t t' Hob0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      [exact (H1 (unl_back_ne o _ Hne Hbad))
      |exact (H2 (unl_back_ne o _ Hne Hbad))
      |exact (H3 (unl_back_ne o _ Hne Hbad))].
  Qed.

  Lemma unl_RITR : WNR s -> RITR s -> RITR s'.
  Proof.
    intros HW H o t Hrd. destruct (H o t Hrd) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      destruct (Hnew o _ Hbad) as [X | [_ Hc]].
    - exact (H1 X).
    - injection Hc as Ht. rewrite Ht in Hrd. exact (HW lw Hlk Hrd).
    - exact (H2 X).
    - discriminate.
    - exact (H3 X).
    - discriminate.
  Qed.

  Lemma unl_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.
  Lemma unl_WNR   : WNR s   -> WNR s'.   Proof. exact (fun H => H). Qed.

  (** *** The cases the write carries *)

  Lemma unl_OW : FNR s -> WULK s -> OW FType s -> OW FType s'.
  Proof.
    intros HF HW H o o' g g' x He He' Hg Hg'.
    destruct (unl_edge_split o  g  x He)  as [[Heq  Hx ] | [Hold  Hnep ]];
    destruct (unl_edge_split o' g' x He') as [[Heq' Hx'] | [Hold' Hnep']].
    - injection Heq as -> ->. injection Heq' as -> ->. by left.
    - (* the new edge into [r], against an old one: the old source is [z],
         which is now detached, or is detached already by OW *)
      injection Heq as -> ->. subst x. right; right.
      destruct (decide (o' = oz)) as [-> | Hne'].
      + exists lw. by left.
      + apply unl_detached_keep.
        destruct (H oz o' f2 g' ow Hedge2 Hold' (Hrefs _ _ _ Hedge2) Hg')
          as [Hsame | [Hd | Hd]].
        * exfalso. destruct Hsame as [H1 _]. exact (Hne' (eq_sym H1)).
        * exfalso. exact (unl_live oz HF HW Hitr_oz Hd).
        * exact Hd.
    - injection Heq' as -> ->. subst x. right; left.
      destruct (decide (o = oz)) as [-> | Hne].
      + exists lw. by left.
      + apply unl_detached_keep.
        destruct (H oz o f2 g ow Hedge2 Hold (Hrefs _ _ _ Hedge2) Hg)
          as [Hsame | [Hd | Hd]].
        * exfalso. destruct Hsame as [H1 _]. exact (Hne (eq_sym H1)).
        * exfalso. exact (unl_live oz HF HW Hitr_oz Hd).
        * exact Hd.
    - destruct (H o o' g g' x Hold Hold' Hg Hg') as [Hsame | [Hd | Hd]].
      + by left.
      + right; left.  exact (unl_detached_keep o Hd).
      + right; right. exact (unl_detached_keep o' Hd).
  Qed.

  Lemma unl_ULKR : FNR s -> WULK s -> OW FType s -> WUNLK s -> ULKR s -> ULKR s'.
  Proof.
    intros HF HW HOW HWU H o o' g t Hobs He.
    assert (Hcase : (obsv s o (Ounlk t) \/ obsv s o (Ofree t))
                    \/ (o = oz /\ t = lw)).
    { destruct Hobs as [X | X]; destruct (Hnew o _ X) as [Y | [Ho Hc]].
      - left; by left.
      - injection Hc as Ht. right. by split.
      - left; by right.
      - discriminate. }
    destruct Hcase as [Hpre | [-> Ht]].
    - destruct (unl_edge_split o' g o He) as [[_ Hx] | [Hold _]].
      + (* the edge the write created points at [r], which the writer still
           holds as an iterator, so it is neither unlinked nor freeable *)
        exfalso. subst o. destruct Hpre as [Y | Y];
          [exact (proj1 (HW lw ow t Hlk Hitr_ow) Y)
          |exact (proj2 (HW lw ow t Hlk Hitr_ow) Y)].
      + destruct (H o o' g t Hpre Hold) as [Y | Y];
          [left | right]; apply unl_keep_ob;
          [exact Y | discriminate | exact Y | discriminate].
    - (* the node just unlinked: its remaining predecessors are the detached
         ones OW allows, and the repaired premise says none of them is fresh *)
      subst t.
      destruct (unl_edge_split o' g oz He) as [[_ Hx] | [Hold Hnep]].
      + exfalso. exact (unl_wz (eq_sym Hx)).
      + destruct (unl_other_pred o' g HF HW HOW HWU Hold Hnep) as [Y | Y];
          [left | right]; apply unl_keep_ob;
          [exact Y | discriminate | exact Y | discriminate].
  Qed.

  Lemma unl_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' g Tr Hfl He.
    destruct (unl_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exfalso. subst o. rewrite Hfl_ow in Hfl. discriminate.
    - exact (H o o' g Tr Hfl Hold).
  Qed.

  Lemma unl_FPI : FNR s -> FPI FType s -> FPI FType s'.
  Proof.
    intros HF H o g x t lw' Hob He Hft Hlk'.
    assert (Hob0 : obsv s o (Ofresh t)) by exact (unl_fresh_inv o t Hob).
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (unl_edge_split o g x He) as [[Heq _] | [Hold _]].
    - exfalso. injection Heq as -> ->. exact (proj1 (HF ox t lw Hob0) Hitr_ox).
    - assert (Hxne : x <> oz)
        by (intros ->; exact (Hno_fresh_pred o t g Hob0 Hold)).
      exact (unl_keep_ne x _ Hxne (H o g x t lw Hob0 Hold Hft Hlk)).
  Qed.

  Lemma unl_HD : FNR s -> WULK s -> HD s -> HD s'.
  Proof.
    intros HF HW H o g x He Hnd.
    destruct (unl_edge_split o g x He) as [[_ ->] | [Hold _]].
    - apply unl_InHeap. exact (H oz f2 ow Hedge2 (unl_live oz HF HW Hitr_oz)).
    - apply unl_InHeap. apply (H o g x Hold).
      intros Hd. exact (Hnd (unl_detached_keep o Hd)).
  Qed.

  Lemma unl_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof.
    intros H o g He.
    destruct (unl_edge_split o g (rt (ms s')) He) as [[_ Hx] | [Hold _]].
    - exact (unl_ow_not_root H (eq_sym Hx)).
    - exact (H o g Hold).
  Qed.

  Lemma unl_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p x lw' Hlk' Hr.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    assert (Hne : x <> oz).
    { intros ->. exact (unlink_unreachable (hp m) (rt m) ox f1 oz f2 ow rho
                          HU Hrho Hedge1 Hedge2 p Hr). }
    assert (Hq : exists q, hstar (hp m) (rt m) q = Some x).
    { destruct (hstar_unlink_char (hp m) (rt m) ox f1 oz f2 ow p x
                  Hedge1 Hedge2 unl_noback_x Hr)
        as [[Ha' _] | [p1 [s2 [_ [_ Hr2]]]]].
      - exists p. exact Ha'.
      - exists (p1 ++ f1 :: f2 :: s2). exact Hr2. }
    destruct Hq as [q Hq]. destruct (H q x lw Hlk Hq) as [Hit | Hrt].
    - left.  exact (unl_keep_ne x _ Hne Hit).
    - right. exact (unl_keep_ne x _ Hne Hrt).
  Qed.

  Lemma unl_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t lw' Hlk' Hobs.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct Hobs as [X | X]; destruct (Hnew o _ X) as [Y | [_ Hc]].
    - exact (H o t lw Hlk (or_introl Y)).
    - injection Hc as Ht. exact Ht.
    - exact (H o t lw Hlk (or_intror Y)).
    - discriminate.
  Qed.

  Lemma unl_WITR : WITR s -> WITR s'.
  Proof.
    intros H o t Hit. destruct (Hnew o _ Hit) as [Y | [_ Hc]];
      [exact (H o t Y) | discriminate].
  Qed.

  Lemma unl_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros _ p p' x H1 H2.
    exact (UNQR_unlink_reachable (hp m) (rt m) ox f1 oz f2 ow rho
             HU Hrho Hedge1 Hedge2 p p' x H1 H2).
  Qed.

  (** *** The post-type environment: [z : unlinked]

      The variable and its binding are the rule's; the observation is the one
      the step grants.  The stack and [U] are untouched by an unlink, so both
      transfer unchanged. *)
  Variable xz : Var.
  Hypothesis Hstk_z  : stk m xz lw = Some oz.
  Hypothesis Hundf_z : ~ undf s xz lw.

  Theorem unlink_post_env : D_unlinked s' lw xz.
  Proof.
    exists oz. repeat apply conj;
      [exact Hstk_z | exact Hdemote | exact Hlk | exact Hundf_z].
  Qed.

  (** *** The parent: [x : rcuItr rho Nx[f1 |-> r]]

      As for T-Replace, one case needs OW: a field of [x] other than [f1] must
      not already point at [z]. *)
  Variables (xx xw : Var) (Nx : FieldMap).
  Hypothesis Hstk_x    : stk m xx lw = Some ox.
  Hypothesis Hstk_w    : stk m xw lw = Some ow.
  Hypothesis Hundf_x   : ~ undf s xx lw.
  Hypothesis Hfl_ox    : flist s ox = None.
  Hypothesis Hfields_x : forall g v, Nx g = Some v -> FieldHolds s lw ox g v.
  Hypothesis Hprefix_x : forall rho1 rho2, rho1 ++ rho2 = rho ->
    exists o', hstar (hp m) (rt m) rho1 = Some o' /\ obsv s o' (Oiter lw).

  Definition UNparent : FieldMap :=
    fun g => if decide (g = f1) then Some (FVar xw) else Nx g.

  Lemma unl_avoids : avoids (hp m) (rt m) rho ox f1.
  Proof. exact (UNQR_avoids (hp m) (rt m) ox f1 rho HU Hrho). Qed.

  Lemma unl_prefix_ne_oz rho1 rho2 o' :
    rho1 ++ rho2 = rho -> hstar (hp m) (rt m) rho1 = Some o' -> o' <> oz.
  Proof.
    intros Heq Hr Hc. subst o'.
    assert (Hx : rho1 = rho ++ [f1])
      by exact (HU rho1 (rho ++ [f1]) oz Hr unl_oz_reach).
    assert (Hle : length rho1 <= length rho)
      by (rewrite -Heq length_app; lia).
    rewrite Hx length_app in Hle. simpl in Hle. lia.
  Qed.

  Lemma unl_parent_other g :
    FNR s -> WULK s -> OW FType s -> g <> f1 -> hp m ox g <> Some (VLoc oz).
  Proof.
    intros HF HW H Hne He.
    destruct (H ox ox f1 g oz Hedge1 He (Hrefs _ _ _ Hedge1) (Hrefs _ _ _ He))
      as [[_ Hfg] | [Hd | Hd]].
    - exact (Hne (eq_sym Hfg)).
    - exact (unl_live ox HF HW Hitr_ox Hd).
    - exact (unl_live ox HF HW Hitr_ox Hd).
  Qed.

  Lemma unl_hp_p g : g <> f1 -> hp (ms s') ox g = hp m ox g.
  Proof.
    intros Hne. apply upd_other. intros Hc. injection Hc as Hc2. exact (Hne Hc2).
  Qed.

  Lemma unl_FieldHolds_p g v :
    FNR s -> WULK s -> OW FType s ->
    g <> f1 -> FieldHolds s lw ox g v -> FieldHolds s' lw ox g v.
  Proof.
    intros HF HW H Hne.
    assert (Hg : hp (ms s') ox g = hp (ms s) ox g) by exact (unl_hp_p g Hne).
    destruct v as [z|].
    - intros [oq (Hq & He & Hit & Hfl)].
      assert (Hoz : oq <> oz)
        by (intros ->; exact (unl_parent_other g HF HW H Hne He)).
      unfold FieldHolds. rewrite Hg. exists oq.
      repeat apply conj;
        [exact Hq | exact He | exact (unl_keep_ne oq _ Hoz Hit) | exact Hfl].
    - intros He. unfold FieldHolds. rewrite Hg. exact He.
  Qed.

  Theorem unlink_post_env_parent :
    FNR s -> WULK s -> OW FType s -> D_rcuItr s' lw xx rho UNparent.
  Proof.
    intros HF HW H. exists ox. repeat apply conj.
    - exact Hstk_x.
    - exact (unl_keep_ne ox _ (unl_prefix_ne_oz rho [] ox (app_nil_r rho) Hrho)
               Hitr_ox).
    - intros Hc. exact (Hundf_x Hc).
    - intros g v HN. unfold UNparent in HN.
      destruct (decide (g = f1)) as [-> | Hne].
      + injection HN as <-. unfold FieldHolds. exists ow.
        repeat apply conj;
          [exact Hstk_w | apply upd_same
          |exact (unl_keep_ne ow _ unl_wz Hitr_ow) | exact Hfl_ow].
      + exact (unl_FieldHolds_p g v HF HW H Hne (Hfields_x g v HN)).
    - intros rho1 rho2 Heq. destruct (Hprefix_x rho1 rho2 Heq) as [o' [Hr Hit]].
      exists o'. split.
      + rewrite (hstar_upd_avoids (hp m) ox f1 (VLoc ow) rho1 (rt m)
                   (avoids_prefix (hp m) rho1 rho2 (rt m) ox f1
                      ltac:(rewrite Heq; exact unl_avoids))).
        exact Hr.
      + exact (unl_keep_ne o' _ (unl_prefix_ne_oz rho1 rho2 o' Heq Hr) Hit).
    - rewrite (hstar_upd_avoids (hp m) ox f1 (VLoc ow) rho (rt m) unl_avoids).
      exact Hrho.
    - exact Hlk.
    - exact Hfl_ox.
  Qed.

  (** *** The promoted node: [r : rcuItr (rho.f1) N2]

      Unlinking *shortens* the path to everything below [z] by one field, and
      [r] is where that shows: it sat at [rho.f1.f2] and now sits at [rho.f1].
      The path is the edge the write created, walked. *)
  Variables (xr : Var) (Nw : FieldMap).
  Hypothesis Hundf_w   : ~ undf s xw lw.
  Hypothesis Hfields_w : forall g v, Nw g = Some v -> FieldHolds s lw ow g v.

  Lemma unl_ow_ne_ox : ow <> ox.
  Proof. intros Hc. apply (unl_noback_x []). by rewrite /= Hc. Qed.

  Lemma unl_ow_path : hstar (hp (ms s')) (rt m) (rho ++ [f1]) = Some ow.
  Proof.
    rewrite (hstar_upd_through (hp m) ox f1 ow rho [] (rt m) unl_avoids Hrho).
    reflexivity.
  Qed.

  Lemma unl_hp_ow g : hp (ms s') ow g = hp m ow g.
  Proof.
    apply upd_other. intros Hc. injection Hc as Hc1 _. exact (unl_ow_ne_ox Hc1).
  Qed.

  Lemma unl_FieldHolds_w g v :
    FieldHolds s lw ow g v -> FieldHolds s' lw ow g v.
  Proof.
    assert (Hg : hp (ms s') ow g = hp (ms s) ow g) by exact (unl_hp_ow g).
    destruct v as [z|].
    - intros [oq (Hq & He & Hit & Hfl)].
      (* a field of [r] cannot point back at [z]: that would reach [z] twice *)
      assert (Hoz : oq <> oz).
      { intros ->. assert (He' : hp m ow g = Some (VLoc oz)) by exact He.
        apply (unl_noback_z [g]). by rewrite /= He'. }
      unfold FieldHolds. rewrite Hg. exists oq.
      repeat apply conj;
        [exact Hq | exact He | exact (unl_keep_ne oq _ Hoz Hit) | exact Hfl].
    - intros He. unfold FieldHolds. rewrite Hg. exact He.
  Qed.

  Theorem unlink_post_env_promoted : D_rcuItr s' lw xw (rho ++ [f1]) Nw.
  Proof.
    exists ow. repeat apply conj.
    - exact Hstk_w.
    - exact (unl_keep_ne ow _ unl_wz Hitr_ow).
    - intros Hc. exact (Hundf_w Hc).
    - intros g v HN. exact (unl_FieldHolds_w g v (Hfields_w g v HN)).
    - intros rho1 rho2 Heq.
      destruct (decide (rho1 = rho ++ [f1])) as [-> | Hne].
      + exists ow. split;
          [exact unl_ow_path | exact (unl_keep_ne ow _ unl_wz Hitr_ow)].
      + assert (Hne2 : rho2 <> []).
        { intros ->. apply Hne. by rewrite app_nil_r in Heq. }
        destruct (prefix_of_snoc rho1 rho2 rho f1 Heq Hne2) as [sigma Hs].
        destruct (Hprefix_x rho1 sigma Hs) as [o' [Hr Hit]].
        exists o'. split.
        * rewrite (hstar_upd_avoids (hp m) ox f1 (VLoc ow) rho1 (rt m)
                     (avoids_prefix (hp m) rho1 sigma (rt m) ox f1
                        ltac:(rewrite Hs; exact unl_avoids))).
          exact Hr.
        * exact (unl_keep_ne o' _ (unl_prefix_ne_oz rho1 sigma o' Hs Hr) Hit).
    - exact unl_ow_path.
    - exact Hlk.
    - exact Hfl_ow.
  Qed.

  Theorem unlink_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact (unl_OW HFNR HWULK HOW).
    - exact (unl_RWOW HRWOW).
    - exact (unl_AWRT HUa HAWRT).
    - exact (unl_IFL HIFL).
    - exact (unl_ULKR HFNR HWULK HOW HWU HULKR).
    - exact (unl_FLR HFLR).
    - exact (unl_WULK HWULK).
    - exact (unl_FR HFR).
    - exact (unl_WFresh HWFresh).
    - exact (unl_FNR HFNR).
    - exact (unl_FPI HFNR HFPI).
    - exact (unl_WNR HWNR).
    - exact (unl_RITR HWNR HRITR).
    - exact (unl_RINFL HRINFL).
    - exact (unl_HD HFNR HWULK HHD).
    - exact (unl_UNQRT_a HUa).
    - exact (unl_UNQRT_b HUb).
    - exact (unl_WUNLK HWU).
    - exact (unl_WITR HWI).
    - exact (unl_UNQR HUq).
  Qed.

End unlinking.

Print Assumptions unlink_preserves_WellFormed.
Print Assumptions unlink_post_env.
Print Assumptions unlink_post_env_parent.
Print Assumptions unlink_post_env_promoted.

(** ** T-Replace

    [p.f := n] with [n] fresh and mirroring [o], which the write unlinks.  Both
    of the previous two at once: [n] is promoted from [fresh] to the writer's
    iterator and [o] is demoted from it to [unlinked], so every case has to keep
    two locations apart rather than one.

    The rule's two repairs both earn their place here.  The premise excluding a
    [rcuFresh] predecessor of [o] is spent in ULKR and again in FPI; and
    [Mirrors], which the added side condition on the field map is what makes
    derivable, is what carries OW and HD through the case where [n] -- detached
    before the step and live after it -- is the source of the edge under
    consideration. *)

Section replacement.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (lw : TID) (op : Loc) (f : FName) (oo on : Loc) (rho : list FName).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m op f (VLoc on)) Og' U T F.

  Hypothesis Hlk : lk m = Some lw.

  (** The observation change: [n] is promoted, [o] demoted, and every other
      observation of either -- a reader's iterator on [o], above all -- stays. *)
  Hypothesis Hpromote : obsv s' on (Oiter lw).
  Hypothesis Hnofresh : forall t, ~ obsv s' on (Ofresh t).
  Hypothesis Hdemote  : obsv s' oo (Ounlk lw).
  Hypothesis Hnoiter  : ~ obsv s' oo (Oiter lw).
  Hypothesis Hnew : forall o ob,
    obsv s' o ob ->
    obsv s o ob \/ (o = on /\ ob = Oiter lw) \/ (o = oo /\ ob = Ounlk lw).
  Hypothesis Hkeep : forall o ob,
    obsv s o ob -> (o, ob) <> (on, Ofresh lw) -> (o, ob) <> (oo, Oiter lw) ->
    obsv s' o ob.

  (** The rule's premises. *)
  (** References live in RCU fields; see the note in the T-Insert section. *)
  Hypothesis Hrefs : forall o g o',
    hp m o g = Some (VLoc o') -> FType g = RCUField.
  Hypothesis Hedge   : hp m op f = Some (VLoc oo).
  Hypothesis Hmir    : Mirrors (hp m) on oo.
  Hypothesis Hfresh  : obsv s on (Ofresh lw).
  Hypothesis Hitr_op : obsv s op (Oiter lw).
  Hypothesis Hitr_oo : obsv s oo (Oiter lw).
  Hypothesis Hno_in  : forall o g, hp m o g <> Some (VLoc on).
  Hypothesis Hin_on  : InHeap s on.
  Hypothesis Hnrt    : on <> rt m.
  Hypothesis Hfl_on  : flist s on = None.
  Hypothesis Hrho    : hstar (hp m) (rt m) rho = Some op.
  Hypothesis HU      : UNQR_h (hp m) (rt m).
  Hypothesis Hno_fresh_pred :
    forall q t g, obsv s q (Ofresh t) -> hp m q g <> Some (VLoc oo).

  Lemma rep_unreach : forall sigma, hstar (hp m) (rt m) sigma <> Some on.
  Proof.
    apply (no_incoming_unreachable (hp m) (rt m) on Hno_in).
    intros Hc. exact (Hnrt (eq_sym Hc)).
  Qed.

  Lemma rep_np : on <> op.
  Proof. intros Hc. apply (rep_unreach rho). by rewrite Hrho Hc. Qed.

  Lemma rep_oo_reach : hstar (hp m) (rt m) (rho ++ [f]) = Some oo.
  Proof. rewrite hstar_app Hrho /=. by rewrite Hedge. Qed.

  Lemma rep_no : on <> oo.
  Proof. intros Hc. apply (rep_unreach (rho ++ [f])). by rewrite rep_oo_reach Hc. Qed.

  Lemma rep_noback : forall tau, hstar (hp m) oo tau <> Some op.
  Proof. exact (UNQR_no_back_edge (hp m) (rt m) op f oo rho HU Hrho Hedge). Qed.

  Lemma rep_edge_split o g x :
    Edge s' o g x ->
    ((o, g) = (op, f) /\ x = on) \/ (Edge s o g x /\ (o, g) <> (op, f)).
  Proof.
    unfold Edge; simpl; intros He.
    destruct (edge_eq_dec o g op f) as [Heq | Hne].
    - left. injection Heq as -> ->. rewrite upd_same in He.
      injection He as <-. split; reflexivity.
    - right. rewrite upd_other in He; [| exact Hne]. by split.
  Qed.

  Lemma rep_InHeap o : InHeap s o -> InHeap s' o.
  Proof.
    intros [g [v Hv]]. unfold InHeap; simpl.
    destruct (edge_eq_dec o g op f) as [Heq | Hne].
    - injection Heq as -> ->. exists f, (VLoc on). apply upd_same.
    - exists g, v. by rewrite upd_other.
  Qed.

  (** [n]'s edges are [o]'s, which is what [Mirrors] says. *)
  Lemma rep_mirror_edge g x : Edge s on g x -> Edge s oo g x.
  Proof. unfold Edge; simpl. by rewrite Hmir. Qed.

  Lemma rep_keep_ne o ob : o <> on -> o <> oo -> obsv s o ob -> obsv s' o ob.
  Proof.
    intros H1 H2 Hob. apply (Hkeep o ob Hob);
      [by injection 1 as -> | by injection 1 as ->].
  Qed.

  (** At [n] itself, everything but the granted iterator came from before. *)
  Lemma rep_back_on ob : ob <> Oiter lw -> obsv s' on ob -> obsv s on ob.
  Proof.
    intros Hne Hob. destruct (Hnew on ob Hob) as [X | [[_ Hc] | [Hc _]]].
    - exact X.
    - by contradiction.
    - exfalso. exact (rep_no Hc).
  Qed.

  Lemma rep_back_ne o ob : o <> on -> o <> oo -> obsv s' o ob -> obsv s o ob.
  Proof.
    intros H1 H2 Hob.
    destruct (Hnew o ob Hob) as [X | [[-> _] | [-> _]]];
      [exact X | by contradiction | by contradiction].
  Qed.

  (** Detaching observations survive; [n]'s freshness and [o]'s iterator are the
      only two things that do not. *)
  Lemma rep_keep_det o ob : obsv s o ob -> ob <> Ofresh lw -> ob <> Oiter lw ->
    obsv s' o ob.
  Proof.
    intros Hob H1 H2. apply (Hkeep o ob Hob);
      [intros Hc; injection Hc as _ Hc2; exact (H1 Hc2)
      |intros Hc; injection Hc as _ Hc2; exact (H2 Hc2)].
  Qed.

  Lemma rep_detached_keep o : o <> on -> Detached s o -> Detached s' o.
  Proof.
    intros Hne Hd. destruct (decide (o = oo)) as [-> | Hno].
    - exists lw. by left.
    - destruct Hd as [t0 [Hb | [Hb | Hb]]]; exists t0;
        [left | right; left | right; right]; exact (rep_keep_ne o _ Hne Hno Hb).
  Qed.

  Lemma rep_live q : FNR s -> WULK s -> obsv s q (Oiter lw) -> ~ Detached s q.
  Proof.
    intros HF HW Hit [t0 [Hb | [Hb | Hb]]].
    - exact (proj1 (HW lw q t0 Hlk Hit) Hb).
    - exact (proj2 (HW lw q t0 Hlk Hit) Hb).
    - exact (proj1 (HF q t0 lw Hb) Hit).
  Qed.

  Lemma rep_other_pred q g :
    FNR s -> WULK s -> OW FType s -> WUNLK s ->
    Edge s q g oo -> (q, g) <> (op, f) ->
    obsv s q (Ounlk lw) \/ obsv s q (Ofree lw).
  Proof.
    intros HF HW H HWU He Hne.
    destruct (H op q f g oo Hedge He (Hrefs _ _ _ Hedge) (Hrefs _ _ _ He))
      as [Hsame | [Hd | Hd]].
    - exfalso. apply Hne. destruct Hsame as [H1 H2]. by subst.
    - exfalso. exact (rep_live op HF HW Hitr_op Hd).
    - destruct Hd as [t0 [Hb | [Hb | Hb]]].
      + assert (Ht : t0 = lw) by exact (HWU q t0 lw Hlk (or_introl Hb)).
        rewrite Ht in Hb. by left.
      + assert (Ht : t0 = lw) by exact (HWU q t0 lw Hlk (or_intror Hb)).
        rewrite Ht in Hb. by right.
      + exfalso. exact (Hno_fresh_pred q t0 g Hb He).
  Qed.

  (** *** The cases the observation change carries *)

  Lemma rep_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hnu.
    destruct (H x t o Hstk Hnu) as [Hit | [Hlk' [Hu | [Hfr | Hfs]]]].
    - destruct (decide ((o, Oiter t) = (oo, Oiter lw))) as [Heq | Hne].
      + (* the writer's own reference to the node it replaced *)
        injection Heq as -> ->. right. split; [exact Hlk | left; exact Hdemote].
      + left. apply (Hkeep o _ Hit); [by injection 1 | exact Hne].
    - right. split; [exact Hlk' |]. left.
      apply rep_keep_det; [exact Hu | discriminate | discriminate].
    - right. split; [exact Hlk' |]. right; left.
      apply rep_keep_det; [exact Hfr | discriminate | discriminate].
    - destruct (decide (o = on)) as [-> | Hne].
      + (* the freshness the step consumes, replaced by the iterator *)
        rewrite Hlk in Hlk'. injection Hlk' as <-. by left.
      + right. split; [exact Hlk' |]. right; right.
        apply (Hkeep o _ Hfs); [by injection 1 as -> | by injection 1].
  Qed.

  Lemma rep_oo_not_root : UNQRT_a s -> oo <> rt m.
  Proof.
    intros H Hc. apply (H op f). unfold Edge; simpl. rewrite -Hc. exact Hedge.
  Qed.

  Lemma rep_AWRT : UNQRT_a s -> AWRT s -> AWRT s'.
  Proof.
    intros Ha H y t Hstk Hnu. apply (Hkeep _ _ (H y t Hstk Hnu)).
    - by injection 1.
    - injection 1 as Hc _. exact (rep_oo_not_root Ha (eq_sym Hc)).
  Qed.

  Lemma rep_IFL : IFL s -> IFL s'.
  Proof.
    intros H t o Tr Hit Hfl.
    destruct (Hnew o _ Hit) as [Hit0 | [[-> _] | [_ Hc]]].
    - exact (H t o Tr Hit0 Hfl).
    - exfalso. rewrite Hfl_on in Hfl. discriminate.
    - discriminate.
  Qed.

  Lemma rep_WULK : FNR s -> WULK s -> WULK s'.
  Proof.
    intros HF H lw' o t Hlk' Hit.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    assert (Hno : o <> oo) by (intros ->; exact (Hnoiter Hit)).
    destruct (decide (o = on)) as [-> | Hne].
    - destruct (HF on lw t Hfresh) as (_ & Hnu & Hnf).
      split; intros Hbad.
      + apply Hnu. apply rep_back_on; [discriminate | exact Hbad].
      + apply Hnf. apply rep_back_on; [discriminate | exact Hbad].
    - destruct (H lw o t Hlk (rep_back_ne o _ Hne Hno Hit)) as [Hnu Hnf].
      split; intros Hbad; [exact (Hnu (rep_back_ne o _ Hne Hno Hbad))
                          | exact (Hnf (rep_back_ne o _ Hne Hno Hbad))].
  Qed.

  Lemma rep_fresh_inv o t : obsv s' o (Ofresh t) -> o <> on /\ obsv s o (Ofresh t).
  Proof.
    intros Hob.
    assert (Hne : o <> on) by (intros ->; exact (Hnofresh t Hob)).
    split; [exact Hne |].
    destruct (Hnew o _ Hob) as [X | [[-> _] | [_ Hc]]];
      [exact X | by contradiction | discriminate].
  Qed.

  Lemma rep_FR : FR s -> FR s'.
  Proof.
    intros H t x o Hstk Hob.
    destruct (rep_fresh_inv o t Hob) as [Hne Hob0].
    destruct (H t x o Hstk Hob0) as [Hin Hal].
    split; [| exact Hal].
    intros o' g He. destruct (rep_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exact (Hne Hx).
    - exact (Hin o' g Hold).
  Qed.

  Lemma rep_WFresh : WFresh s -> WFresh s'.
  Proof.
    intros H t x o Hstk Hob. exact (H t x o Hstk (proj2 (rep_fresh_inv o t Hob))).
  Qed.

  Lemma rep_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t t' Hob.
    destruct (rep_fresh_inv o t Hob) as [Hne Hob0].
    assert (Hno : o <> oo) by (intros ->; exact (proj1 (H oo t lw Hob0) Hitr_oo)).
    destruct (H o t t' Hob0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      [exact (H1 (rep_back_ne o _ Hne Hno Hbad))
      |exact (H2 (rep_back_ne o _ Hne Hno Hbad))
      |exact (H3 (rep_back_ne o _ Hne Hno Hbad))].
  Qed.

  Lemma rep_RITR : WNR s -> RITR s -> RITR s'.
  Proof.
    intros HW H o t Hrd. destruct (H o t Hrd) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      destruct (Hnew o _ Hbad) as [X | [[_ Hc] | [_ Hc]]].
    - exact (H1 X).
    - discriminate.
    - injection Hc as Ht. rewrite Ht in Hrd. exact (HW lw Hlk Hrd).
    - exact (H2 X).
    - discriminate.
    - discriminate.
    - exact (H3 X).
    - discriminate.
    - discriminate.
  Qed.

  Lemma rep_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.
  Lemma rep_WNR   : WNR s   -> WNR s'.   Proof. exact (fun H => H). Qed.

  (** *** The cases the write carries *)

  Lemma rep_OW : FNR s -> WULK s -> OW FType s -> OW FType s'.
  Proof.
    intros HF HW H o o' g g' x He He' Hg Hg'.
    destruct (rep_edge_split o  g  x He)  as [[Heq  Hx ] | [Hold  Hnep ]];
    destruct (rep_edge_split o' g' x He') as [[Heq' Hx'] | [Hold' Hnep']].
    - injection Heq as -> ->. injection Heq' as -> ->. by left.
    - exfalso. rewrite Hx in Hold'. exact (Hno_in o' g' Hold').
    - exfalso. rewrite Hx' in Hold. exact (Hno_in o g Hold).
    - (* both edges predate the write.  [n] was detached then and is not now, so
         a case OW discharged by [n]'s detachment is re-discharged through the
         node [n] mirrors. *)
      destruct (decide (o = on)) as [-> | Hne].
      + destruct (decide (o' = on)) as [-> | Hne'].
        * destruct (H oo oo g g' x (rep_mirror_edge g x Hold)
                      (rep_mirror_edge g' x Hold') Hg Hg')
            as [[_ ->] | [Hd | Hd]].
          -- left. by split.
          -- exfalso. exact (rep_live oo HF HW Hitr_oo Hd).
          -- exfalso. exact (rep_live oo HF HW Hitr_oo Hd).
        * destruct (H oo o' g g' x (rep_mirror_edge g x Hold) Hold' Hg Hg')
            as [[H1 _] | [Hd | Hd]].
          -- right; right. rewrite -H1. exists lw. by left.
          -- exfalso. exact (rep_live oo HF HW Hitr_oo Hd).
          -- right; right. exact (rep_detached_keep o' Hne' Hd).
      + destruct (decide (o' = on)) as [-> | Hne'].
        * destruct (H o oo g g' x Hold (rep_mirror_edge g' x Hold') Hg Hg')
            as [[H1 _] | [Hd | Hd]].
          -- right; left. rewrite H1. exists lw. by left.
          -- right; left. exact (rep_detached_keep o Hne Hd).
          -- exfalso. exact (rep_live oo HF HW Hitr_oo Hd).
        * destruct (H o o' g g' x Hold Hold' Hg Hg') as [Hsame | [Hd | Hd]].
          -- by left.
          -- right; left.  exact (rep_detached_keep o Hne Hd).
          -- right; right. exact (rep_detached_keep o' Hne' Hd).
  Qed.

  Lemma rep_ULKR : FNR s -> WULK s -> OW FType s -> WUNLK s -> ULKR s -> ULKR s'.
  Proof.
    intros HF HW HOW HWU H o o' g t Hobs He.
    assert (Hcase : (obsv s o (Ounlk t) \/ obsv s o (Ofree t))
                    \/ (o = oo /\ t = lw)).
    { destruct Hobs as [X | X];
        destruct (Hnew o _ X) as [Y | [[_ Hc] | [Ho Hc]]].
      - left; by left.
      - discriminate.
      - injection Hc as Ht. right. by split.
      - left; by right.
      - discriminate.
      - discriminate. }
    destruct Hcase as [Hpre | [-> Ht]].
    - destruct (rep_edge_split o' g o He) as [[_ Hx] | [Hold _]].
      + exfalso. subst o. destruct Hpre as [Y | Y];
          [exact (proj1 (proj2 (HF on lw t Hfresh)) Y)
          |exact (proj2 (proj2 (HF on lw t Hfresh)) Y)].
      + destruct (H o o' g t Hpre Hold) as [Y | Y];
          [left | right]; apply rep_keep_det;
          [exact Y | discriminate | discriminate
          |exact Y | discriminate | discriminate].
    - subst t.
      destruct (rep_edge_split o' g oo He) as [[_ Hx] | [Hold Hnep]].
      + exfalso. exact (rep_no (eq_sym Hx)).
      + destruct (rep_other_pred o' g HF HW HOW HWU Hold Hnep) as [Y | Y];
          [left | right]; apply rep_keep_det;
          [exact Y | discriminate | discriminate
          |exact Y | discriminate | discriminate].
  Qed.

  Lemma rep_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' g Tr Hfl He.
    destruct (rep_edge_split o' g o He) as [[_ Hx] | [Hold _]].
    - exfalso. subst o. rewrite Hfl_on in Hfl. discriminate.
    - exact (H o o' g Tr Hfl Hold).
  Qed.

  Lemma rep_FPI : FNR s -> FPI FType s -> FPI FType s'.
  Proof.
    intros HF H o g x t lw' Hob He Hft Hlk'.
    destruct (rep_fresh_inv o t Hob) as [Hne Hob0].
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (rep_edge_split o g x He) as [[Heq _] | [Hold _]].
    - exfalso. injection Heq as -> ->. exact (proj1 (HF op t lw Hob0) Hitr_op).
    - assert (Hxne : x <> oo)
        by (intros ->; exact (Hno_fresh_pred o t g Hob0 Hold)).
      apply (Hkeep x _ (H o g x t lw Hob0 Hold Hft Hlk));
        [by injection 1 | by injection 1 as ->].
  Qed.

  Lemma rep_HD : FNR s -> WULK s -> HD s -> HD s'.
  Proof.
    intros HF HW H o g x He Hnd.
    destruct (rep_edge_split o g x He) as [[_ ->] | [Hold _]].
    - exact (rep_InHeap on Hin_on).
    - destruct (decide (o = on)) as [-> | Hne].
      + apply rep_InHeap.
        exact (H oo g x (rep_mirror_edge g x Hold) (rep_live oo HF HW Hitr_oo)).
      + apply rep_InHeap. apply (H o g x Hold).
        intros Hd. exact (Hnd (rep_detached_keep o Hne Hd)).
  Qed.

  Lemma rep_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof.
    intros H o g He.
    destruct (rep_edge_split o g (rt (ms s')) He) as [[_ Hx] | [Hold _]].
    - exact (Hnrt (eq_sym Hx)).
    - exact (H o g Hold).
  Qed.

  Lemma rep_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p x lw' Hlk' Hr.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (hstar_replace_char (hp m) (rt m) op f oo on p x
                Hmir rep_np Hedge rep_noback Hr) as [Hpre | [-> _]].
    - assert (Hno : x <> oo).
      { intros ->. exact (replace_unreachable (hp m) (rt m) op f oo on rho
                            HU Hmir Hrho Hedge rep_unreach p Hr). }
      destruct (H p x lw Hlk Hpre) as [Hit | Hrt].
      + left. apply (Hkeep x _ Hit); [by injection 1 | by injection 1 as ->].
      + right. apply (Hkeep x _ Hrt); [by injection 1 | by injection 1].
    - by left.
  Qed.

  Lemma rep_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t lw' Hlk' Hobs.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct Hobs as [X | X];
      destruct (Hnew o _ X) as [Y | [[_ Hc] | [_ Hc]]].
    - exact (H o t lw Hlk (or_introl Y)).
    - discriminate.
    - injection Hc as Ht. exact Ht.
    - exact (H o t lw Hlk (or_intror Y)).
    - discriminate.
    - discriminate.
  Qed.

  Lemma rep_WITR : WITR s -> WITR s'.
  Proof.
    intros H o t Hit. destruct (Hnew o _ Hit) as [Y | [[_ Hc] | [_ Hc]]].
    - exact (H o t Y).
    - injection Hc as Ht. left. rewrite Ht. exact Hlk.
    - discriminate.
  Qed.

  Lemma rep_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros _ p p' x H1 H2.
    exact (UNQR_replace (hp m) (rt m) op f oo on HU Hmir rep_np Hedge
             rep_noback rep_unreach p p' x H1 H2).
  Qed.

  (** *** Half of the post-type environment: [o : unlinked]

      The other half, that the fresh reference becomes an [rcuItr] at the
      replaced node's path, needs the path reasoning and is below. *)
  Variable xo : Var.
  Hypothesis Hstk_o  : stk m xo lw = Some oo.
  Hypothesis Hundf_o : ~ undf s xo lw.

  Theorem replace_post_env_unlinked : D_unlinked s' lw xo.
  Proof.
    exists oo. repeat apply conj;
      [exact Hstk_o | exact Hdemote | exact Hlk | exact Hundf_o].
  Qed.

  (** *** The other half: [n : rcuItr (rho.f) N]

      The fresh node takes the replaced node's position, so its path is [p]'s
      extended by [f] -- the same path T-Insert gives, for a different reason.

      The field clause is where the repaired premise is spent a third time: the
      fresh node's field targets must still be the writer's iterators
      afterwards, and the one node that stops being one is [o].  That no fresh
      reference points at [o] is exactly the premise \textsc{T-Replace} carries,
      and FR supplies that none points at [n]. *)
  Variables (xn : Var) (N : FieldMap).
  Hypothesis Hstk_n    : stk m xn lw = Some on.
  Hypothesis Hundf_n   : ~ undf s xn lw.
  Hypothesis Hfields_n : forall g v, N g = Some v -> FieldHolds s lw on g v.
  Hypothesis Hprefix   : forall rho1 rho2, rho1 ++ rho2 = rho ->
    exists o', hstar (hp m) (rt m) rho1 = Some o' /\ obsv s o' (Oiter lw).
  Hypothesis Hfresh_on_ne : forall g, hp m on g <> Some (VLoc oo).

  Lemma rep_avoids : avoids (hp m) (rt m) rho op f.
  Proof. exact (UNQR_avoids (hp m) (rt m) op f rho HU Hrho). Qed.

  Lemma rep_path : hstar (hp (ms s')) (rt m) (rho ++ [f]) = Some on.
  Proof.
    rewrite (hstar_upd_through (hp m) op f on rho [] (rt m) rep_avoids Hrho).
    reflexivity.
  Qed.

  Lemma rep_hp_n g : hp (ms s') on g = hp m on g.
  Proof.
    apply upd_other. intros Hc. injection Hc as Hc1 _. exact (rep_np Hc1).
  Qed.

  Lemma rep_FieldHolds g v : FieldHolds s lw on g v -> FieldHolds s' lw on g v.
  Proof.
    assert (Hg : hp (ms s') on g = hp (ms s) on g) by exact (rep_hp_n g).
    destruct v as [z|].
    - intros [oz (Hz & He & Hit & Hfl)].
      assert (Hoo : oz <> oo) by (intros ->; exact (Hfresh_on_ne g He)).
      assert (Hon : oz <> on) by (intros ->; exact (Hno_in on g He)).
      unfold FieldHolds. rewrite Hg. exists oz.
      repeat apply conj;
        [exact Hz | exact He | exact (rep_keep_ne oz _ Hon Hoo Hit) | exact Hfl].
    - intros He. unfold FieldHolds. rewrite Hg. exact He.
  Qed.

  Theorem replace_post_env_itr : D_rcuItr s' lw xn (rho ++ [f]) N.
  Proof.
    exists on. repeat apply conj.
    - exact Hstk_n.
    - exact Hpromote.
    - intros Hc. exact (Hundf_n Hc).
    - intros g v HN. exact (rep_FieldHolds g v (Hfields_n g v HN)).
    - intros rho1 rho2 Heq.
      destruct (decide (rho1 = rho ++ [f])) as [-> | Hne].
      + exists on. split; [exact rep_path | exact Hpromote].
      + assert (Hne2 : rho2 <> []).
        { intros ->. apply Hne. by rewrite app_nil_r in Heq. }
        destruct (prefix_of_snoc rho1 rho2 rho f Heq Hne2) as [sigma Hs].
        destruct (Hprefix rho1 sigma Hs) as [o' [Hr Hit]].
        (* distinct paths reach distinct nodes, and this one is not [o]'s *)
        assert (Hoo' : o' <> oo).
        { intros ->. exact (Hne (HU rho1 (rho ++ [f]) oo Hr rep_oo_reach)). }
        exists o'. split.
        * rewrite (hstar_upd_avoids (hp m) op f (VLoc on) rho1 (rt m)
                     (avoids_prefix (hp m) rho1 sigma (rt m) op f
                        ltac:(rewrite Hs; exact rep_avoids))).
          exact Hr.
        * exact (rep_keep_ne o' _ ltac:(intros ->; exact (rep_unreach rho1 Hr))
                   Hoo' Hit).
    - exact rep_path.
    - exact Hlk.
    - exact Hfl_on.
  Qed.

  (** *** The parent: [p : rcuItr rho Np[f |-> n]]

      One case needs an invariant rather than a premise.  A field of [p] other
      than [f] must not already point at [o], or the entry would name a node
      that the step unlinks; OW is what rules that out, [o] and [p] both being
      the writer's iterators and so neither detached. *)
  Variables (xp : Var) (Np : FieldMap).
  Hypothesis Hstk_p    : stk m xp lw = Some op.
  Hypothesis Hundf_p   : ~ undf s xp lw.
  Hypothesis Hfl_op    : flist s op = None.
  Hypothesis Hfields_p : forall g v, Np g = Some v -> FieldHolds s lw op g v.

  Definition RPparent : FieldMap :=
    fun g => if decide (g = f) then Some (FVar xn) else Np g.

  Lemma rep_parent_other g :
    FNR s -> WULK s -> OW FType s -> g <> f -> hp m op g <> Some (VLoc oo).
  Proof.
    intros HF HW H Hne He.
    destruct (H op op f g oo Hedge He (Hrefs _ _ _ Hedge) (Hrefs _ _ _ He))
      as [[_ Hfg] | [Hd | Hd]].
    - exact (Hne (eq_sym Hfg)).
    - exact (rep_live op HF HW Hitr_op Hd).
    - exact (rep_live op HF HW Hitr_op Hd).
  Qed.

  Lemma rep_hp_p g : g <> f -> hp (ms s') op g = hp m op g.
  Proof.
    intros Hne. apply upd_other. intros Hc. injection Hc as Hc2. exact (Hne Hc2).
  Qed.

  Lemma rep_FieldHolds_p g v :
    FNR s -> WULK s -> OW FType s ->
    g <> f -> FieldHolds s lw op g v -> FieldHolds s' lw op g v.
  Proof.
    intros HF HW H Hne.
    assert (Hg : hp (ms s') op g = hp (ms s) op g) by exact (rep_hp_p g Hne).
    destruct v as [z|].
    - intros [oz (Hz & He & Hit & Hfl)].
      assert (Hon : oz <> on) by (intros ->; exact (Hno_in op g He)).
      assert (Hoo : oz <> oo)
        by (intros ->; exact (rep_parent_other g HF HW H Hne He)).
      unfold FieldHolds. rewrite Hg. exists oz.
      repeat apply conj;
        [exact Hz | exact He | exact (rep_keep_ne oz _ Hon Hoo Hit) | exact Hfl].
    - intros He. unfold FieldHolds. rewrite Hg. exact He.
  Qed.

  (** A node on a prefix of [p]'s path is not [o]: [o] sits one field beyond
      [p], and distinct paths reach distinct nodes. *)
  Lemma rep_prefix_ne_oo rho1 rho2 o' :
    rho1 ++ rho2 = rho -> hstar (hp m) (rt m) rho1 = Some o' -> o' <> oo.
  Proof.
    intros Heq Hr Hc. subst o'.
    assert (Hx : rho1 = rho ++ [f])
      by exact (HU rho1 (rho ++ [f]) oo Hr rep_oo_reach).
    assert (Hle : length rho1 <= length rho)
      by (rewrite -Heq length_app; lia).
    rewrite Hx length_app in Hle. simpl in Hle. lia.
  Qed.

  Lemma rep_prefix_ne_on rho1 o' :
    hstar (hp m) (rt m) rho1 = Some o' -> o' <> on.
  Proof. intros Hr Hc. apply (rep_unreach rho1). by rewrite Hr Hc. Qed.

  Theorem replace_post_env_parent :
    FNR s -> WULK s -> OW FType s -> D_rcuItr s' lw xp rho RPparent.
  Proof.
    intros HF HW H. exists op. repeat apply conj.
    - exact Hstk_p.
    - exact (rep_keep_ne op _ (rep_prefix_ne_on rho op Hrho)
               (rep_prefix_ne_oo rho [] op (app_nil_r rho) Hrho) Hitr_op).
    - intros Hc. exact (Hundf_p Hc).
    - intros g v HN. unfold RPparent in HN.
      destruct (decide (g = f)) as [-> | Hne].
      + injection HN as <-. unfold FieldHolds. exists on.
        repeat apply conj;
          [exact Hstk_n | apply upd_same | exact Hpromote | exact Hfl_on].
      + exact (rep_FieldHolds_p g v HF HW H Hne (Hfields_p g v HN)).
    - intros rho1 rho2 Heq. destruct (Hprefix rho1 rho2 Heq) as [o' [Hr Hit]].
      exists o'. split.
      + rewrite (hstar_upd_avoids (hp m) op f (VLoc on) rho1 (rt m)
                   (avoids_prefix (hp m) rho1 rho2 (rt m) op f
                      ltac:(rewrite Heq; exact rep_avoids))).
        exact Hr.
      + exact (rep_keep_ne o' _ (rep_prefix_ne_on rho1 o' Hr)
                 (rep_prefix_ne_oo rho1 rho2 o' Heq Hr) Hit).
    - rewrite (hstar_upd_avoids (hp m) op f (VLoc on) rho (rt m) rep_avoids).
      exact Hrho.
    - exact Hlk.
    - exact Hfl_op.
  Qed.

  Theorem replace_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact (rep_OW HFNR HWULK HOW).
    - exact (rep_RWOW HRWOW).
    - exact (rep_AWRT HUa HAWRT).
    - exact (rep_IFL HIFL).
    - exact (rep_ULKR HFNR HWULK HOW HWU HULKR).
    - exact (rep_FLR HFLR).
    - exact (rep_WULK HFNR HWULK).
    - exact (rep_FR HFR).
    - exact (rep_WFresh HWFresh).
    - exact (rep_FNR HFNR).
    - exact (rep_FPI HFNR HFPI).
    - exact (rep_WNR HWNR).
    - exact (rep_RITR HWNR HRITR).
    - exact (rep_RINFL HRINFL).
    - exact (rep_HD HFNR HWULK HHD).
    - exact (rep_UNQRT_a HUa).
    - exact (rep_UNQRT_b HUb).
    - exact (rep_WUNLK HWU).
    - exact (rep_WITR HWI).
    - exact (rep_UNQR HUq).
  Qed.

End replacement.

Print Assumptions replace_preserves_WellFormed.
Print Assumptions replace_post_env_itr.
Print Assumptions replace_post_env_parent.
Print Assumptions replace_post_env_unlinked.

(** * The reader side and the start of a grace period, whole

    The three actions left: entering a read critical section, acquiring a
    reference inside one, and taking the snapshot that begins a grace period.
    None writes the heap, so the eight heap-mentioning invariants are identities
    throughout and the content is entirely in the observation, reader and
    free-list state.

    SyncStart is where WITR is spent, and it is the reason WITR exists. *)

(** ** ReadBegin

    [rds] gains the entering thread and nothing else changes.  Three invariants
    mention [rds]; the other sixteen are identities.

    Both premises are the rule's.  A reader is not the writer, and a thread
    entering a read section holds no detaching observation -- which is what the
    read-side environment being free of [unlinked], [freeable] and [rcuFresh]
    types amounts to. *)

Definition read_begin_ms (m : MState) (t : TID) : MState :=
  {| stk := stk m; hp := hp m; lk := lk m; rt := rt m;
     rds := fun t' => rds m t' \/ t' = t;
     bnd := bnd m |}.

Section entry.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)) (t : TID).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (read_begin_ms m t) Og U T F.

  Hypothesis Hnotwriter : forall lw, lk m = Some lw -> lw <> t.
  Hypothesis Hclean : forall o,
    ~ obsv s o (Ounlk t) /\ ~ obsv s o (Ofree t) /\ ~ obsv s o (Ofresh t).

  Lemma rb_WNR : WNR s -> WNR s'.
  Proof.
    intros H t0 Hlk [Hrd | Heq].
    - exact (H t0 Hlk Hrd).
    - exact (Hnotwriter t0 Hlk Heq).
  Qed.

  Lemma rb_RITR : RITR s -> RITR s'.
  Proof.
    intros H o t0 [Hrd | ->]; [exact (H o t0 Hrd) | exact (Hclean o)].
  Qed.

  Lemma rb_WITR : WITR s -> WITR s'.
  Proof.
    intros H o t0 Hit. destruct (H o t0 Hit) as [Hlk | Hrd];
      [by left | right; by left].
  Qed.

  Theorem read_begin_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj; try exact HOW; try exact HRWOW; try exact HAWRT;
      try exact HIFL; try exact HULKR; try exact HFLR; try exact HWULK;
      try exact HFR; try exact HWFresh; try exact HFNR; try exact HFPI;
      try exact HRINFL; try exact HHD; try exact HUa; try exact HUb;
      try exact HWU; try exact HUq.
    - exact (rb_WNR HWNR).
    - exact (rb_RITR HRITR).
    - exact (rb_WITR HWI).
  Qed.

End entry.

Print Assumptions read_begin_preserves_WellFormed.

(** ** Why ReadEnd has to write the free list

    ReadEnd's free-list update is the one step in the development that writes
    state another thread owns: the entries are the writer's, created by
    SyncStart, and the departing reader rewrites every one it appears in.  The
    resource-level lemma has to hold all of them, which is the wrong resource
    for a per-thread act.

    The obvious economy is to leave the entries alone and read them against the
    threads still running.  A thread that has left its read section bounds
    nothing, so intersecting the snapshot with [R] looks like it should have the
    same effect as removing the thread from the snapshot -- and it would make
    ReadEnd touch nothing but its own reader cell.

    It does not work, and the reason is re-entrancy.  A thread that leaves its
    read section and enters a new one is in [R] again, and the intersected
    reading puts it back into every snapshot it was ever in, including grace
    periods that started after it left and have nothing to do with its new
    section.  We tried this repair and record why it is wrong, because the
    failure is not visible until ReadBegin is asked to preserve the invariant.

    So the recorded repair is the right one: the free-list value should be a
    disjoint union of tickets, one per bounding thread, so that a reader owns
    its own membership and deallocates it.  That makes ReadEnd's write
    thread-local, and re-entry does not restore a ticket that has been spent.
    (The other sound repair is to index snapshots by read-side critical section
    rather than by thread, which is what an implementation's grace-period
    counter does; then the intersected reading is sound, because a section
    identity is never reused.  It costs a change to the state model, which the
    ticket does not.) *)

Definition flistR (m : MState) (F : gmap Loc (gset TID)) (o : Loc)
  : option (TID -> Prop) :=
  match F !! o with
  | Some s => Some (fun t => t ∈ s /\ rds m t)
  | None   => None
  end.

Definition RINFL_R (m : MState) (F : gmap Loc (gset TID)) : Prop :=
  forall o Tr t, flistR m F o = Some Tr -> Tr t -> bnd m t.

(** Thread 9 is in a snapshot it has already left: under the intersected
    reading that is harmless, because it is not a reader. *)
Definition stale_ms : MState :=
  {| stk := fun _ _ => None;
     hp  := fun o _ => if Nat.eqb o 0 then Some VNull else None;
     lk  := Some 0; rt := 0;
     rds := fun _ => False;
     bnd := fun _ => False |}.

Definition stale_F : gmap Loc (gset TID) := {[ 1 := {[ 9 ]} ]}.

Lemma stale_RINFL_R : RINFL_R stale_ms stale_F.
Proof.
  intros o Tr t Hfl HTr. rewrite /flistR in Hfl.
  destruct (stale_F !! o) as [s0|] eqn:HS; [| discriminate].
  injection Hfl as <-. destruct HTr as [_ H]. destruct H.
Qed.

(** Until it starts reading again, and rejoins a grace period that is not
    waiting for it. *)
Theorem reentry_breaks_the_intersected_reading :
  RINFL_R stale_ms stale_F
  /\ ~ rds stale_ms 9
  /\ ~ RINFL_R (read_begin_ms stale_ms 9) stale_F.
Proof.
  repeat apply conj; [exact stale_RINFL_R | intros H; exact H |].
  intros H.
  apply (H 1 (fun t => t ∈ ({[9]} : gset TID)
                       /\ rds (read_begin_ms stale_ms 9) t) 9).
  - rewrite /flistR /stale_F lookup_insert_eq. reflexivity.
  - split; [by apply elem_of_singleton | by right].
Qed.

Print Assumptions reentry_breaks_the_intersected_reading.

(** ** Acquiring a reference

    A reader following [x.f] to [z] adds [iterator] to its own entry for [z] and
    changes nothing else.  Observations only grow, so most of the nineteen get
    easier; three do not.

    IFL is the one with content, and it was already proved above: the acquiring
    thread must bound any pending reclamation of [z].  WULK needs the acquirer
    not to be the writer, which WNR gives since it is a reader.  And FNR needs
    [z] not to be fresh -- a reader cannot reach a fresh node, since nothing
    points at one, but the action lemma has to be told. *)

Section acquisition.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)) (t : TID) (z : Loc)
            (sz : gset obs).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t m (<[(z, t) := sz ∪ {[Oiter t]}]> Og) U T F.

  (** What the acquiring thread's entry held before.  Stated as two
      containments rather than as an equation, so that the case where the
      thread has no entry at [z] yet -- which is the case the reader's read
      needs, and the one the registration cell now decides -- is covered by
      [sz = ∅] rather than by a second lemma. *)
  Hypothesis Hsub   : forall S, Og !! (z, t) = Some S -> S ⊆ sz.
  Hypothesis Hprev  : forall ob, ob ∈ sz ->
                        exists S, Og !! (z, t) = Some S /\ ob ∈ S.
  Hypothesis Hrd    : rds m t.
  Hypothesis Hbound : forall Tr, flist s z = Some Tr -> Tr t.
  Hypothesis Hznf   : forall t0, ~ obsv s z (Ofresh t0).

  (** Observations grow by exactly the acquired iterator. *)
  Lemma ra_mono o ob : obsv s o ob -> obsv s' o ob.
  Proof.
    intros Hob. destruct ob as [t0|t0|t0|t0|]; [| | | | exact Hob].
    all: destruct Hob as [t' [S [Hl Hin]]].
    all: destruct (decide ((o, t') = (z, t))) as [Heq | Hne].
    all: try solve [exists t', S; split; [| exact Hin];
                    rewrite lookup_insert_ne //].
    all: injection Heq as -> ->.
    all: exists t, (sz ∪ {[Oiter t]});
         rewrite lookup_insert_eq; split; [reflexivity |];
         apply elem_of_union_l; exact (Hsub S Hl _ Hin).
  Qed.

  Lemma ra_back o ob : obsv s' o ob -> obsv s o ob \/ (o = z /\ ob = Oiter t).
  Proof.
    intros Hob. destruct ob as [t0|t0|t0|t0|]; [| | | | by left].
    all: destruct Hob as [t' [S [Hl Hin]]].
    all: destruct (decide ((o, t') = (z, t))) as [Heq | Hne].
    all: try solve [rewrite lookup_insert_ne // in Hl; left; by exists t', S].
    all: injection Heq as -> ->; rewrite lookup_insert_eq in Hl;
         injection Hl as <-; apply elem_of_union in Hin as [Hin | Hin].
    all: try solve [left; destruct (Hprev _ Hin) as [S0 [HS0 Hin0]];
                    by exists t, S0].
    all: apply elem_of_singleton in Hin; try discriminate.
    right. split; [reflexivity | exact Hin].
  Qed.

  Lemma ra_detached o : Detached s o <-> Detached s' o.
  Proof.
    split.
    - intros [t0 [H | [H | H]]]; exists t0;
        [left | right; left | right; right]; exact (ra_mono o _ H).
    - intros [t0 [H | [H | H]]]; exists t0;
        [left | right; left | right; right];
        destruct (ra_back o _ H) as [Y | [_ Hc]]; try discriminate; exact Y.
  Qed.

  Lemma ra_not_writer : WNR s -> forall lw, lk m = Some lw -> lw <> t.
  Proof. intros H lw Hlk ->. exact (H t Hlk Hrd). Qed.

  Lemma ra_OW : OW FType s -> OW FType s'.
  Proof.
    intros H o o' f f' x He He' Hf Hf'.
    destruct (H o o' f f' x He He' Hf Hf') as [Hs | [Hd | Hd]];
      [by left | right; left; by apply ra_detached
      | right; right; by apply ra_detached].
  Qed.

  Lemma ra_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t0 o Hstk Hnu.
    destruct (H x t0 o Hstk Hnu) as [Hit | [Hlk [Hu | [Hfr | Hfs]]]].
    - left. exact (ra_mono o _ Hit).
    - right. split; [exact Hlk |]. left. exact (ra_mono o _ Hu).
    - right. split; [exact Hlk |]. right; left. exact (ra_mono o _ Hfr).
    - right. split; [exact Hlk |]. right; right. exact (ra_mono o _ Hfs).
  Qed.

  Lemma ra_AWRT : AWRT s -> AWRT s'.
  Proof. intros H y t0 Hstk Hnu. exact (ra_mono _ _ (H y t0 Hstk Hnu)). Qed.

  Lemma ra_ULKR : ULKR s -> ULKR s'.
  Proof.
    intros H o o' f' t0 Hobs He.
    assert (Hobs0 : obsv s o (Ounlk t0) \/ obsv s o (Ofree t0)).
    { destruct Hobs as [X | X]; destruct (ra_back o _ X) as [Y | [_ Hc]];
        try discriminate; [by left | by right]. }
    destruct (H o o' f' t0 Hobs0 He) as [Y | Y];
      [left | right]; exact (ra_mono o' _ Y).
  Qed.

  Lemma ra_WULK : WNR s -> WULK s -> WULK s'.
  Proof.
    intros HW H lw o t0 Hlk Hit.
    assert (Hne : lw <> t) by exact (ra_not_writer HW lw Hlk).
    assert (Hit0 : obsv s o (Oiter lw)).
    { destruct (ra_back o _ Hit) as [Y | [_ Hc]];
        [exact Y | injection Hc as Hc; by contradiction]. }
    destruct (H lw o t0 Hlk Hit0) as [Hnu Hnf].
    split; intros Hbad; destruct (ra_back o _ Hbad) as [Y | [_ Hc]];
      try discriminate; [exact (Hnu Y) | exact (Hnf Y)].
  Qed.

  Lemma ra_fresh_inv o t0 : obsv s' o (Ofresh t0) -> obsv s o (Ofresh t0).
  Proof.
    intros H. destruct (ra_back o _ H) as [Y | [_ Hc]];
      [exact Y | discriminate].
  Qed.

  Lemma ra_FR : FR s -> FR s'.
  Proof. intros H t0 x o Hstk Hob. exact (H t0 x o Hstk (ra_fresh_inv o t0 Hob)). Qed.

  Lemma ra_WFresh : WFresh s -> WFresh s'.
  Proof. intros H t0 x o Hstk Hob. exact (H t0 x o Hstk (ra_fresh_inv o t0 Hob)). Qed.

  Lemma ra_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t0 t' Hob.
    assert (Hob0 : obsv s o (Ofresh t0)) by exact (ra_fresh_inv o t0 Hob).
    assert (Hne : o <> z) by (intros ->; exact (Hznf t0 Hob0)).
    destruct (H o t0 t' Hob0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      destruct (ra_back o _ Hbad) as [Y | [Hc _]];
      [exact (H1 Y) | by contradiction
      |exact (H2 Y) | by contradiction
      |exact (H3 Y) | by contradiction].
  Qed.

  Lemma ra_FPI : FPI FType s -> FPI FType s'.
  Proof.
    intros H o f o' t0 lw Hob He Hft Hlk.
    exact (ra_mono o' _ (H o f o' t0 lw (ra_fresh_inv o t0 Hob) He Hft Hlk)).
  Qed.

  Lemma ra_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p o lw Hlk Hr. destruct (H p o lw Hlk Hr) as [Hit | Hrt];
      [left | right]; exact (ra_mono o _ Hit) || exact (ra_mono o _ Hrt).
  Qed.

  Lemma ra_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t0 lw Hlk Hobs. apply (H o t0 lw Hlk).
    destruct Hobs as [X | X]; destruct (ra_back o _ X) as [Y | [_ Hc]];
      try discriminate; [by left | by right].
  Qed.

  Lemma ra_WITR : WITR s -> WITR s'.
  Proof.
    intros H o t0 Hit. destruct (ra_back o _ Hit) as [Y | [_ Hc]].
    - exact (H o t0 Y).
    - injection Hc as Ht. right. by rewrite Ht.
  Qed.

  Lemma ra_HD : HD s -> HD s'.
  Proof.
    intros H o f o' He Hnd. apply (H o f o' He).
    intros Hd. exact (Hnd (proj1 (ra_detached o) Hd)).
  Qed.

  (** *** The read-side post-type environment: [y : rcuItr]

      The reader's version of the type, with no path and no field map.  Two of
      its conjuncts are the acquisition; the third is the bounding-thread
      condition, and it is the one the denotation asks for and the action does
      not give.  [Hbnd_entry] below is that gap, stated rather than hidden: if
      the acquiring reader is a bounding thread, the node it takes must already
      carry a free-list entry.  Nothing in the rule establishes it, and a
      bounding reader holding an iterator on a live node -- which has no entry
      at all -- is a state the denotation as written excludes.  Given the
      hypothesis, [Hbound] supplies the reader's membership and RINFL supplies
      that the entry holds only bounding threads. *)
  Variables (yv : Var).
  Hypothesis Hstk_y     : stk m yv t = Some z.
  Hypothesis Hundf_y    : ~ undf s yv t.
  Hypothesis Hbnd_entry : bnd m t -> flist s z <> None.

  Lemma ra_acquired : obsv s' z (Oiter t).
  Proof.
    exists t, (sz ∪ {[Oiter t]}).
    split; [by rewrite lookup_insert_eq | set_solver].
  Qed.

  Theorem reader_post_env : RINFL s -> D_rcuItrR s' t yv.
  Proof.
    intros HR. exists z. repeat apply conj.
    - exact Hstk_y.
    - exact ra_acquired.
    - intros Hc. exact (Hundf_y Hc).
    - intros Hb. case_eq (flist s z).
      + intros Tr E. exists Tr. repeat apply conj.
        * exact E.
        * exact (Hbound Tr E).
        * intros t' Hin. exact (HR z Tr t' E Hin).
      + intros E. exfalso. exact (Hbnd_entry Hb E).
  Qed.

  Theorem reader_acquire_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact (ra_OW HOW).
    - exact (ra_RWOW HRWOW).
    - exact (ra_AWRT HAWRT).
    - exact (reader_acquire_preserves_IFL m Og U T F t z sz HIFL Hprev Hbound).
    - exact (ra_ULKR HULKR).
    - exact HFLR.
    - exact (ra_WULK HWNR HWULK).
    - exact (ra_FR HFR).
    - exact (ra_WFresh HWFresh).
    - exact (ra_FNR HFNR).
    - exact (ra_FPI HFPI).
    - exact HWNR.
    - exact (reader_acquire_preserves_RITR m Og U T F t z sz HRITR Hprev).
    - exact HRINFL.
    - exact (ra_HD HHD).
    - exact HUa.
    - exact (ra_UNQRT_b HUb).
    - exact (ra_WUNLK HWU).
    - exact (ra_WITR HWI).
    - exact HUq.
  Qed.

End acquisition.

Print Assumptions reader_acquire_preserves_WellFormed.
Print Assumptions reader_post_env.

(** ** SyncStart

    The snapshot that opens a grace period: the bounding set becomes the current
    readers, and every detached node gets a free-list entry holding that same
    set.  Nothing else moves, so the sixteen invariants that mention neither the
    free list nor the bounding set are identities.

    The three that remain are the grace period's whole specification.  FLR holds
    with equality because one snapshot creates every entry -- the
    same-critical-section case of the argument that fixed its direction.  RINFL
    is immediate, the entries being the bounding set by construction.  And IFL
    is the obligation that matters: a thread still observing a detached node as
    an [iterator] must be among the readers the grace period will wait for,
    since otherwise SyncStop returns while a live reference remains.  WULK rules
    out the writer.  Ruling out a thread that is neither writer nor reader is
    exactly WITR, and is why it had to be added. *)

Definition sync_start_ms (m : MState) : MState :=
  {| stk := stk m; hp := hp m; lk := lk m; rt := rt m;
     rds := rds m; bnd := rds m |}.

Section snapshot.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F F' : gmap Loc (gset TID)) (Rs : gset TID).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (sync_start_ms m) Og U T F'.

  (** The snapshot is of the current readers. *)
  Hypothesis Hsnap : forall t, t ∈ Rs <-> rds m t.
  (** Every entry holds it, ... *)
  Hypothesis Hsame : forall o s0, F' !! o = Some s0 -> s0 = Rs.
  (** ... every detached node has one, ... *)
  Hypothesis Hcovers : forall o t,
    (obsv s o (Ounlk t) \/ obsv s o (Ofree t)) -> exists s0, F' !! o = Some s0.
  (** ... and nothing else does. *)
  Hypothesis Honly : forall o s0,
    F' !! o = Some s0 -> exists t, obsv s o (Ounlk t) \/ obsv s o (Ofree t).

  Lemma sst_entry o s0 :
    F' !! o = Some s0 -> flist s' o = Some (fun x => x ∈ s0).
  Proof. intros H. simpl. by rewrite H. Qed.

  Lemma sst_entry_inv o Tr :
    flist s' o = Some Tr -> exists s0, F' !! o = Some s0 /\ Tr = (fun x => x ∈ s0).
  Proof.
    simpl. destruct (F' !! o) as [s0|] eqn:HS; [| discriminate].
    intros H. injection H as <-. by exists s0.
  Qed.

  (** IFL: the grace period waits for everyone who could still be looking. *)
  Lemma sst_IFL : WULK s -> WITR s -> IFL s'.
  Proof.
    intros HW HI t o Tr Hit Hfl.
    destruct (sst_entry_inv o Tr Hfl) as [s0 [HS ->]].
    rewrite (Hsame o s0 HS).
    destruct (Honly o s0 HS) as [t0 Hdet].
    destruct (HI o t Hit) as [Hlk | Hrd].
    - (* the writer does not observe a detached node as an iterator *)
      exfalso. destruct (HW t o t0 Hlk Hit) as [Hnu Hnf].
      destruct Hdet as [Y | Y]; [exact (Hnu Y) | exact (Hnf Y)].
    - apply (proj2 (Hsnap t)). exact Hrd.
  Qed.

  Lemma sst_RINFL : RINFL s'.
  Proof.
    intros o Tr t Hfl Hin.
    destruct (sst_entry_inv o Tr Hfl) as [s0 [HS ->]].
    rewrite (Hsame o s0 HS) in Hin.
    exact (proj1 (Hsnap t) Hin).
  Qed.

  Lemma sst_FLR : ULKR s -> FLR s'.
  Proof.
    intros H.
    exact (sync_start_FLR (sync_start_ms m) Og U T F' Rs H Hsame Hcovers Honly).
  Qed.

  Theorem sync_start_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj; try exact HOW; try exact HRWOW; try exact HAWRT;
      try exact HULKR; try exact HWULK; try exact HFR; try exact HWFresh;
      try exact HFNR; try exact HFPI; try exact HWNR; try exact HRITR;
      try exact HHD; try exact HUa; try exact HUb; try exact HWU;
      try exact HWI; try exact HUq.
    - exact (sst_IFL HWULK HWI).
    - exact (sst_FLR HULKR).
    - exact sst_RINFL.
  Qed.

End snapshot.

Print Assumptions sync_start_preserves_WellFormed.

(** ** T-Alloc

    [x = new].  The one action that *adds* a location, as Free is the one that
    removes one, and the two are opposite in shape: Free's only real case is HD,
    because it shrinks the domain and can strand an edge, whereas allocation
    extends the domain and so can strand nothing.

    The new node carries one observation, [fresh], its RCU fields are all null,
    and -- by the rule's premises -- nothing points at it and no other reference
    names it.  That is exactly the shape FR, FNR and FPI ask of a fresh node,
    which is why this is where the fresh-node conditions that T-Insert and
    T-Replace consume are established rather than assumed. *)

Definition alloc_ms (m : MState) (n : Loc) (fs : list FName)
                    (x : Var) (t : TID) : MState :=
  {| stk := fun y t' => if decide ((y, t') = (x, t)) then Some n else stk m y t';
     hp  := alloc (hp m) n fs;
     lk  := lk m; rt := rt m; rds := rds m; bnd := bnd m |}.

Section allocation.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U U' : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (lw : TID) (n : Loc) (x : Var) (fs : list FName).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (alloc_ms m n fs x lw) Og' U' T F.

  Hypothesis Hlk : lk m = Some lw.

  (** The observation change: the new node becomes the writer's fresh one, and
      nothing else moves. *)
  Hypothesis Hfresh : obsv s' n (Ofresh lw).
  Hypothesis Hnew : forall o ob,
    obsv s' o ob -> obsv s o ob \/ (o = n /\ ob = Ofresh lw).
  Hypothesis Hkeep : forall o ob, obsv s o ob -> obsv s' o ob.

  (** [x] becomes defined and nothing else changes definedness. *)
  Hypothesis Hdef : ~ undf s' x lw.
  Hypothesis Hundf : forall y t,
    (y, t) <> (x, lw) -> (undf s' y t <-> undf s y t).

  (** The rule's premises: the location is genuinely new -- unallocated,
      unobserved, unreferenced, not pointed at, and not the root. *)
  Hypothesis Hunalloc : forall g, hp m n g = None.
  Hypothesis Hno_obs  : forall ob, ~ obsv s n ob.
  Hypothesis Hno_in   : forall o g, hp m o g <> Some (VLoc n).
  Hypothesis Hno_ref  : forall y t, stk m y t <> Some n.
  Hypothesis Hnrt     : n <> rt m.
  Hypothesis Hfl_n    : flist s n = None.

  (** The class declaration.  [fs] is the node's RCU field list, and it holds
      every RCU field name: that is what makes it a declaration rather than an
      arbitrary subset, and it is what the fresh node's denotation needs, since
      that denotation asks for a null at every RCU field.  It is also what makes
      the heap finite, which is the whole point of the repair -- an infinite
      supply of field names is harmless as long as only finitely many of them
      are RCU fields and only those are allocated. *)
  Hypothesis Hrcu_fs : forall g, FType g = RCUField -> In g fs.

  (** *** The stack and the heap after the allocation *)

  Lemma al_stk_new : stk (ms s') x lw = Some n.
  Proof. simpl. by destruct (decide ((x, lw) = (x, lw))). Qed.

  Lemma al_stk_old y t o :
    (y, t) <> (x, lw) -> stk (ms s') y t = Some o -> stk m y t = Some o.
  Proof. intros Hne. simpl. by destruct (decide ((y, t) = (x, lw))). Qed.

  Lemma al_stk_inv y t o :
    stk (ms s') y t = Some o -> ((y, t) = (x, lw) /\ o = n)
                                \/ (stk m y t = Some o /\ (y, t) <> (x, lw)).
  Proof.
    simpl. destruct (decide ((y, t) = (x, lw))) as [Heq | Hne].
    - intros H. injection H as <-. by left.
    - intros H. by right.
  Qed.

  (** The new node has no edges, in or out.  Under the field list the declared
      fields are null and the rest are absent, and [alloc_no_edge] covers both
      -- which is all any use of the old "every field is null" ever needed. *)
  Lemma al_hp_new g : In g fs -> hp (ms s') n g = Some VNull.
  Proof. exact (alloc_same (hp m) n fs g). Qed.

  Lemma al_hp_old o g : o <> n -> hp (ms s') o g = hp m o g.
  Proof. exact (alloc_other (hp m) n fs o g). Qed.

  Lemma al_no_out g o : ~ Edge s' n g o.
  Proof. exact (alloc_no_edge (hp m) n fs g o Hunalloc). Qed.

  Lemma al_edge_inv o g y : Edge s' o g y -> Edge s o g y /\ o <> n.
  Proof.
    unfold Edge. intros He.
    assert (Hne : o <> n) by (intros ->; exact (al_no_out g y He)).
    split; [| exact Hne].
    rewrite (al_hp_old o g Hne) in He. exact He.
  Qed.

  Lemma al_no_in o g : ~ Edge s' o g n.
  Proof.
    intros He. exact (Hno_in o g (proj1 (al_edge_inv o g n He))).
  Qed.

  Lemma al_InHeap o : InHeap s o -> InHeap s' o.
  Proof. exact (InHeap_h_alloc (hp m) n fs o). Qed.

  (** Nothing new is reachable. *)
  Lemma al_reach p o : Reaches s' p o -> Reaches s p o /\ o <> n.
  Proof.
    unfold Reaches; simpl.
    assert (Hsub : forall q a b, hstar (alloc (hp m) n fs) a q = Some b ->
                     a <> n -> hstar (hp m) a q = Some b /\ b <> n).
    { induction q as [|g q IH]; intros a b H Ha; simpl in H |- *.
      - injection H as <-. by split.
      - rewrite (alloc_other (hp m) n fs a g Ha) in H.
        destruct (hp m a g) as [[a1|]|] eqn:E; try discriminate.
        assert (Ha1 : a1 <> n) by (intros ->; exact (Hno_in a g E)).
        exact (IH a1 b H Ha1). }
    intros H. exact (Hsub p (rt m) o H (fun Hc => Hnrt (eq_sym Hc))).
  Qed.

  Lemma al_detached_keep o : Detached s o -> Detached s' o.
  Proof.
    intros [t0 [X|[X|X]]]; exists t0;
      [left | right; left | right; right]; exact (Hkeep o _ X).
  Qed.

  Lemma al_obs_n ob : obsv s' n ob -> ob = Ofresh lw.
  Proof.
    intros H. destruct (Hnew n ob H) as [Y | [_ Hc]];
      [exfalso; exact (Hno_obs ob Y) | exact Hc].
  Qed.

  (** *** The nineteen *)

  Lemma al_OW : OW FType s -> OW FType s'.
  Proof.
    intros H o o' f f' y He He' Hf Hf'.
    destruct (H o o' f f' y (proj1 (al_edge_inv o f y He))
                (proj1 (al_edge_inv o' f' y He')) Hf Hf')
      as [Hs | [Hd | Hd]].
    - by left.
    - right; left.  exact (al_detached_keep o Hd).
    - right; right. exact (al_detached_keep o' Hd).
  Qed.

  Lemma al_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H y t o Hstk Hnu.
    destruct (al_stk_inv y t o Hstk) as [[Heq ->] | [Hstk0 Hne]].
    - injection Heq as -> ->. right. split; [exact Hlk |].
      right; right. exact Hfresh.
    - destruct (H y t o Hstk0 (fun Hc => Hnu (proj2 (Hundf y t Hne) Hc)))
        as [Hit | [Hlk' [Hu | [Hfr | Hfs]]]].
      + left. exact (Hkeep o _ Hit).
      + right. split; [exact Hlk' |]. left. exact (Hkeep o _ Hu).
      + right. split; [exact Hlk' |]. right; left. exact (Hkeep o _ Hfr).
      + right. split; [exact Hlk' |]. right; right. exact (Hkeep o _ Hfs).
  Qed.

  Lemma al_AWRT : AWRT s -> AWRT s'.
  Proof.
    intros H y t Hstk Hnu.
    destruct (al_stk_inv y t _ Hstk) as [[_ Hc] | [Hstk0 Hne]].
    - exfalso. exact (Hnrt (eq_sym Hc)).
    - exact (Hkeep _ _ (H y t Hstk0 (fun Hc => Hnu (proj2 (Hundf y t Hne) Hc)))).
  Qed.

  Lemma al_back_ne o ob : ob <> Ofresh lw -> obsv s' o ob -> obsv s o ob.
  Proof.
    intros Hne H. destruct (Hnew o ob H) as [Y | [_ Hc]];
      [exact Y | by contradiction].
  Qed.

  Lemma al_back_iter o t : obsv s' o (Oiter t) -> obsv s o (Oiter t).
  Proof. intros H. apply (al_back_ne o _); [discriminate | exact H]. Qed.
  Lemma al_back_unlk o t : obsv s' o (Ounlk t) -> obsv s o (Ounlk t).
  Proof. intros H. apply (al_back_ne o _); [discriminate | exact H]. Qed.
  Lemma al_back_free o t : obsv s' o (Ofree t) -> obsv s o (Ofree t).
  Proof. intros H. apply (al_back_ne o _); [discriminate | exact H]. Qed.

  Lemma al_IFL : IFL s -> IFL s'.
  Proof.
    intros H t o Tr Hit Hfl.
    exact (H t o Tr (al_back_iter o t Hit) Hfl).
  Qed.

  Lemma al_ULKR : ULKR s -> ULKR s'.
  Proof.
    intros H o o' g t Hobs He.
    assert (Hobs0 : obsv s o (Ounlk t) \/ obsv s o (Ofree t)).
    { destruct Hobs as [X | X];
        [left; exact (al_back_unlk o t X) | right; exact (al_back_free o t X)]. }
    destruct (H o o' g t Hobs0 (proj1 (al_edge_inv o' g o He))) as [Y | Y];
      [left | right]; exact (Hkeep o' _ Y).
  Qed.

  Lemma al_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' g Tr Hfl He.
    exact (H o o' g Tr Hfl (proj1 (al_edge_inv o' g o He))).
  Qed.

  Lemma al_WULK : WULK s -> WULK s'.
  Proof.
    intros H lw' o t Hlk' Hit.
    destruct (H lw' o t Hlk' (al_back_iter o lw' Hit)) as [Hnu Hnf].
    split; intros Hbad;
      [exact (Hnu (al_back_unlk o t Hbad)) | exact (Hnf (al_back_free o t Hbad))].
  Qed.

  Lemma al_fresh_inv o t :
    obsv s' o (Ofresh t) -> obsv s o (Ofresh t) \/ (o = n /\ t = lw).
  Proof.
    intros H. destruct (Hnew o _ H) as [Y | [Ho Hc]];
      [by left | injection Hc as Ht; right; by split].
  Qed.

  Lemma al_FR : FR s -> FR s'.
  Proof.
    intros H t y o Hstk Hob.
    destruct (al_fresh_inv o t Hob) as [Hob0 | [-> ->]].
    - destruct (al_stk_inv y t o Hstk) as [[_ ->] | [Hstk0 Hne]].
      + exfalso. exact (Hno_obs _ Hob0).
      + destruct (H t y o Hstk0 Hob0) as [Hin Hal]. split.
        * intros o' g He. exact (Hin o' g (proj1 (al_edge_inv o' g o He))).
        * intros z t' Hpne Hc.
          destruct (al_stk_inv z t' o Hc) as [[_ ->] | [Hc0 _]].
          -- exact (Hno_obs _ Hob0).
          -- exact (Hal z t' Hpne Hc0).
    - (* the new node: nothing points at it, and only [x] names it *)
      split.
      + intros o' g He. exact (al_no_in o' g He).
      + intros z t' Hpne Hc. apply Hpne.
        destruct (al_stk_inv z t' n Hc) as [[Heq _] | [Hc0 _]];
          [| exfalso; exact (Hno_ref z t' Hc0)].
        destruct (al_stk_inv y lw n Hstk) as [[Heq' _] | [Hc1 _]];
          [| exfalso; exact (Hno_ref y lw Hc1)].
        by rewrite Heq Heq'.
  Qed.

  Lemma al_WFresh : WFresh s -> WFresh s'.
  Proof.
    intros H t y o Hstk Hob.
    destruct (al_fresh_inv o t Hob) as [Hob0 | [-> ->]]; [| exact Hlk].
    destruct (al_stk_inv y t o Hstk) as [[_ ->] | [Hstk0 _]].
    - exfalso. exact (Hno_obs _ Hob0).
    - exact (H t y o Hstk0 Hob0).
  Qed.

  Lemma al_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t t' Hob.
    destruct (al_fresh_inv o t Hob) as [Hob0 | [-> ->]].
    - destruct (H o t t' Hob0) as (H1 & H2 & H3).
      repeat apply conj; intros Hbad;
        [exact (H1 (al_back_iter o t' Hbad))
        |exact (H2 (al_back_unlk o t' Hbad))
        |exact (H3 (al_back_free o t' Hbad))].
    - (* the new node carries its freshness and nothing else *)
      repeat apply conj; intros Hbad;
        pose proof (al_obs_n _ Hbad) as Hc; discriminate.
  Qed.

  Lemma al_FPI : FPI FType s -> FPI FType s'.
  Proof.
    intros H o g y t lw' Hob He Hft Hlk'.
    destruct (al_fresh_inv o t Hob) as [Hob0 | [-> _]].
    - exact (Hkeep y _ (H o g y t lw' Hob0
                          (proj1 (al_edge_inv o g y He)) Hft Hlk')).
    - exfalso. exact (al_no_out g y He).
  Qed.

  Lemma al_WNR   : WNR s   -> WNR s'.   Proof. exact (fun H => H). Qed.
  Lemma al_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.

  Lemma al_RITR : WNR s -> RITR s -> RITR s'.
  Proof.
    intros HW H o t Hrd. destruct (H o t Hrd) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad; destruct (Hnew o _ Hbad) as [Y | [_ Hc]].
    - exact (H1 Y).
    - discriminate.
    - exact (H2 Y).
    - discriminate.
    - exact (H3 Y).
    - injection Hc as Ht. rewrite Ht in Hrd. exact (HW lw Hlk Hrd).
  Qed.

  Lemma al_HD : HD s -> HD s'.
  Proof.
    intros H o g y He Hnd.
    apply al_InHeap. apply (H o g y (proj1 (al_edge_inv o g y He))).
    intros Hd. exact (Hnd (al_detached_keep o Hd)).
  Qed.

  Lemma al_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof.
    intros H o g He. exact (H o g (proj1 (al_edge_inv o g _ He))).
  Qed.

  Lemma al_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p o lw' Hlk' Hr.
    destruct (H p o lw' Hlk' (proj1 (al_reach p o Hr))) as [Hit | Hrt];
      [left | right]; exact (Hkeep o _ Hit) || exact (Hkeep o _ Hrt).
  Qed.

  Lemma al_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t lw' Hlk' Hobs. apply (H o t lw' Hlk').
    destruct Hobs as [X | X];
      [left; exact (al_back_unlk o t X) | right; exact (al_back_free o t X)].
  Qed.

  Lemma al_WITR : WITR s -> WITR s'.
  Proof.
    intros H o t Hit. exact (H o t (al_back_iter o t Hit)).
  Qed.

  Lemma al_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros H p p' o H1 H2.
    exact (H p p' o (proj1 (al_reach p o H1)) (proj1 (al_reach p' o H2))).
  Qed.

  (** *** The post-type environment

      [WellFormed] preservation is half of axiom soundness; the other half is
      that the post-state satisfies the denotation of the rule's output
      environment.  For T-Alloc that is [x : rcuFresh N_empty], and every
      conjunct of it is a hypothesis of this section or an immediate consequence
      -- which is the point: the premises that make the invariants survive are
      the same ones that make the new type hold. *)
  Definition Nempty : FieldMap := fun _ => None.

  Theorem alloc_post_env : D_rcuFresh FType s' lw x Nempty.
  Proof.
    exists n. repeat apply conj.
    - exact al_stk_new.
    - exact Hfresh.
    - exact Hdef.
    - exact Hfl_n.
    - intros g v Hc. discriminate Hc.
    - intros g Hg _. exact (al_hp_new g (Hrcu_fs g Hg)).
  Qed.

  Theorem alloc_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact (al_OW HOW).
    - exact (al_RWOW HRWOW).
    - exact (al_AWRT HAWRT).
    - exact (al_IFL HIFL).
    - exact (al_ULKR HULKR).
    - exact (al_FLR HFLR).
    - exact (al_WULK HWULK).
    - exact (al_FR HFR).
    - exact (al_WFresh HWFresh).
    - exact (al_FNR HFNR).
    - exact (al_FPI HFPI).
    - exact (al_WNR HWNR).
    - exact (al_RITR HWNR HRITR).
    - exact (al_RINFL HRINFL).
    - exact (al_HD HHD).
    - exact (al_UNQRT_a HUa).
    - exact (al_UNQRT_b HUb).
    - exact (al_WUNLK HWU).
    - exact (al_WITR HWI).
    - exact (al_UNQR HUq).
  Qed.

End allocation.

Print Assumptions alloc_preserves_WellFormed.
Print Assumptions alloc_post_env.

(** ** T-Root, T-ReadS and T-ReadH

    The three rules that bind a writer's variable to a node already in the
    structure.  They differ only in where the node comes from -- the root, another
    variable, or a field -- and not at all in what they do to the state, so they
    are one lemma: bind [y] to [o], and let the writer observe [o] as an
    iterator.  T-ReadS is the degenerate case in which it already did.

    The premise that carries them is that [o] is live.  A writer's variable may
    not be bound to a node that is fresh, unlinked or freeable, and each of the
    three invariants that would otherwise break says so from a different side:
    FNR (a fresh node carries no iterator), WULK (an iterator carries neither
    [unlinked] nor [freeable]) and FR (a fresh node has at most one reference). *)

Definition bind_ms (m : MState) (y : Var) (t : TID) (o : Loc) : MState :=
  {| stk := fun z t' => if decide ((z, t') = (y, t)) then Some o else stk m z t';
     hp  := hp m; lk := lk m; rt := rt m; rds := rds m; bnd := bnd m |}.

Section binding.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U U' : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (tb : TID) (y : Var) (o : Loc).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (bind_ms m y tb o) Og' U' T F.

  (** The binder is the writer or a reader: T-Root, T-ReadS and T-ReadH are
      the writer's instances, the read-side rules the reader's. *)
  Hypothesis Howner : lk m = Some tb \/ rds m tb.

  (** The writer observes [o] as an iterator afterwards, and observations grow
      by that and nothing else. *)
  Hypothesis Hitr : obsv s' o (Oiter tb).
  Hypothesis Hnew : forall q ob,
    obsv s' q ob -> obsv s q ob \/ (q = o /\ ob = Oiter tb).
  Hypothesis Hkeep : forall q ob, obsv s q ob -> obsv s' q ob.

  (** [y] becomes defined; nothing else changes definedness. *)
  Hypothesis Hdef : ~ undf s' y tb.
  Hypothesis Hundf : forall z t,
    (z, t) <> (y, tb) -> (undf s' z t <-> undf s z t).

  (** The node bound is live, and not awaiting reclamation. *)
  Hypothesis Hlive : ~ Detached s o.
  Hypothesis Hfl_o : flist s o = None.

  Lemma bd_stk_inv z t q :
    stk (ms s') z t = Some q -> ((z, t) = (y, tb) /\ q = o)
                                \/ (stk m z t = Some q /\ (z, t) <> (y, tb)).
  Proof.
    simpl. destruct (decide ((z, t) = (y, tb))) as [Heq | Hne].
    - intros H. injection H as <-. by left.
    - intros H. by right.
  Qed.

  Lemma bd_back_ne q ob : ob <> Oiter tb -> obsv s' q ob -> obsv s q ob.
  Proof.
    intros Hne H. destruct (Hnew q ob H) as [Y | [_ Hc]];
      [exact Y | by contradiction].
  Qed.

  Lemma bd_back_unlk q t : obsv s' q (Ounlk t) -> obsv s q (Ounlk t).
  Proof. intros H. apply (bd_back_ne q _); [discriminate | exact H]. Qed.
  Lemma bd_back_free q t : obsv s' q (Ofree t) -> obsv s q (Ofree t).
  Proof. intros H. apply (bd_back_ne q _); [discriminate | exact H]. Qed.
  Lemma bd_back_fresh q t : obsv s' q (Ofresh t) -> obsv s q (Ofresh t).
  Proof. intros H. apply (bd_back_ne q _); [discriminate | exact H]. Qed.

  Lemma bd_detached q : Detached s q <-> Detached s' q.
  Proof.
    split.
    - intros [t0 [X|[X|X]]]; exists t0;
        [left | right; left | right; right]; exact (Hkeep q _ X).
    - intros [t0 [X|[X|X]]]; exists t0;
        [left | right; left | right; right];
        [exact (bd_back_unlk q t0 X) | exact (bd_back_free q t0 X)
        |exact (bd_back_fresh q t0 X)].
  Qed.

  (** [o] is live, so it is none of the three the new observation could clash
      with.  This is where the premise is spent. *)
  Lemma bd_o_not_fresh t : ~ obsv s o (Ofresh t).
  Proof. intros H. apply Hlive. exists t. by right; right. Qed.

  Lemma bd_o_not_unlk t : ~ obsv s o (Ounlk t).
  Proof. intros H. apply Hlive. exists t. by left. Qed.

  Lemma bd_o_not_free t : ~ obsv s o (Ofree t).
  Proof. intros H. apply Hlive. exists t. by right; left. Qed.

  Lemma bd_OW : OW FType s -> OW FType s'.
  Proof.
    intros H q q' f f' z He He' Hf Hf'.
    destruct (H q q' f f' z He He' Hf Hf') as [Hs | [Hd | Hd]];
      [by left | right; left; by apply bd_detached
      | right; right; by apply bd_detached].
  Qed.

  Lemma bd_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H z t q Hstk Hnu.
    destruct (bd_stk_inv z t q Hstk) as [[Heq ->] | [Hstk0 Hne]].
    - injection Heq as -> ->. by left.
    - destruct (H z t q Hstk0 (fun Hc => Hnu (proj2 (Hundf z t Hne) Hc)))
        as [Hit | [Hlk' [Hu | [Hfr | Hfs]]]].
      + left. exact (Hkeep q _ Hit).
      + right. split; [exact Hlk' |]. left. exact (Hkeep q _ Hu).
      + right. split; [exact Hlk' |]. right; left. exact (Hkeep q _ Hfr).
      + right. split; [exact Hlk' |]. right; right. exact (Hkeep q _ Hfs).
  Qed.

  Lemma bd_AWRT : AWRT s -> AWRT s'.
  Proof.
    intros H z t Hstk Hnu.
    destruct (bd_stk_inv z t _ Hstk) as [[Heq Hq] | [Hstk0 Hne]].
    - injection Heq as -> ->. rewrite Hq. exact Hitr.
    - exact (Hkeep _ _ (H z t Hstk0 (fun Hc => Hnu (proj2 (Hundf z t Hne) Hc)))).
  Qed.

  Lemma bd_IFL : IFL s -> IFL s'.
  Proof.
    intros H t q Tr Hit Hfl.
    destruct (Hnew q _ Hit) as [Hit0 | [-> Hc]].
    - exact (H t q Tr Hit0 Hfl).
    - exfalso. rewrite Hfl_o in Hfl. discriminate.
  Qed.

  Lemma bd_ULKR : ULKR s -> ULKR s'.
  Proof.
    intros H q q' f t Hobs He.
    assert (Hobs0 : obsv s q (Ounlk t) \/ obsv s q (Ofree t))
      by (destruct Hobs as [X | X];
          [left; exact (bd_back_unlk q t X) | right; exact (bd_back_free q t X)]).
    destruct (H q q' f t Hobs0 He) as [Y | Y];
      [left | right]; exact (Hkeep q' _ Y).
  Qed.

  Lemma bd_FLR   : FLR s   -> FLR s'.   Proof. exact (fun H => H). Qed.
  Lemma bd_WNR   : WNR s   -> WNR s'.   Proof. exact (fun H => H). Qed.
  Lemma bd_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.
  Lemma bd_UNQRT_a : UNQRT_a s -> UNQRT_a s'. Proof. exact (fun H => H). Qed.
  Lemma bd_UNQR    : UNQR s    -> UNQR s'.    Proof. exact (fun H => H). Qed.

  Lemma bd_WULK : WULK s -> WULK s'.
  Proof.
    intros H lw' q t Hlk' Hit.
    destruct (Hnew q _ Hit) as [Hit0 | [-> _]].
    - destruct (H lw' q t Hlk' Hit0) as [Hnu Hnf].
      split; intros Hbad;
        [exact (Hnu (bd_back_unlk q t Hbad)) | exact (Hnf (bd_back_free q t Hbad))].
    - split; intros Hbad;
        [exact (bd_o_not_unlk t (bd_back_unlk o t Hbad))
        |exact (bd_o_not_free t (bd_back_free o t Hbad))].
  Qed.

  Lemma bd_fresh_ne q t : obsv s' q (Ofresh t) -> obsv s q (Ofresh t) /\ q <> o.
  Proof.
    intros H. pose proof (bd_back_fresh q t H) as H0.
    split; [exact H0 | intros ->; exact (bd_o_not_fresh t H0)].
  Qed.

  Lemma bd_FR : FR s -> FR s'.
  Proof.
    intros H t z q Hstk Hob.
    destruct (bd_fresh_ne q t Hob) as [Hob0 Hqo].
    destruct (bd_stk_inv z t q Hstk) as [[_ ->] | [Hstk0 _]];
      [by contradiction |].
    destruct (H t z q Hstk0 Hob0) as [Hin Hal]. split; [exact Hin |].
    intros w t' Hpne Hc.
    destruct (bd_stk_inv w t' q Hc) as [[_ ->] | [Hc0 _]];
      [by contradiction | exact (Hal w t' Hpne Hc0)].
  Qed.

  Lemma bd_WFresh : WFresh s -> WFresh s'.
  Proof.
    intros H t z q Hstk Hob.
    destruct (bd_fresh_ne q t Hob) as [Hob0 Hqo].
    destruct (bd_stk_inv z t q Hstk) as [[_ ->] | [Hstk0 _]];
      [by contradiction | exact (H t z q Hstk0 Hob0)].
  Qed.

  Lemma bd_FNR : FNR s -> FNR s'.
  Proof.
    intros H q t t' Hob.
    destruct (bd_fresh_ne q t Hob) as [Hob0 Hqo].
    destruct (H q t t' Hob0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      [destruct (Hnew q _ Hbad) as [Y | [Hc _]];
         [exact (H1 Y) | by contradiction]
      |exact (H2 (bd_back_unlk q t' Hbad))
      |exact (H3 (bd_back_free q t' Hbad))].
  Qed.

  Lemma bd_FPI : FPI FType s -> FPI FType s'.
  Proof.
    intros H q f q' t lw' Hob He Hft Hlk'.
    exact (Hkeep q' _ (H q f q' t lw' (bd_back_fresh q t Hob) He Hft Hlk')).
  Qed.

  Lemma bd_RITR : RITR s -> RITR s'.
  Proof.
    intros H q t Hrd. destruct (H q t Hrd) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      [destruct (Hnew q _ Hbad) as [Y | [_ Hc]]; [exact (H1 Y) | discriminate]
      |exact (H2 (bd_back_free q t Hbad))
      |exact (H3 (bd_back_fresh q t Hbad))].
  Qed.

  Lemma bd_HD : HD s -> HD s'.
  Proof.
    intros H q f q' He Hnd. apply (H q f q' He).
    intros Hd. exact (Hnd (proj1 (bd_detached q) Hd)).
  Qed.

  Lemma bd_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p q lw' Hlk' Hr. destruct (H p q lw' Hlk' Hr) as [Hit | Hrt];
      [left | right]; exact (Hkeep q _ Hit) || exact (Hkeep q _ Hrt).
  Qed.

  Lemma bd_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H q t lw' Hlk' Hobs. apply (H q t lw' Hlk').
    destruct Hobs as [X | X];
      [left; exact (bd_back_unlk q t X) | right; exact (bd_back_free q t X)].
  Qed.

  Lemma bd_WITR : WITR s -> WITR s'.
  Proof.
    intros H q t Hit. destruct (Hnew q _ Hit) as [Y | [_ Hc]].
    - exact (H q t Y).
    - injection Hc as Ht. rewrite Ht. exact Howner.
  Qed.

  (** *** The post-type environment: [y : rcuItr rho N]

      T-Root, T-ReadS and T-ReadH all land here, and only for the writer: the
      read-side [rcuItr] carries no path or field map and has no denotation in
      this development, so the reader's instances of these rules have their
      invariant half and not their type half.

      The heap does not move, so the path and every prefix of it transfer
      unchanged.  What the rule has to supply is the free-variable condition --
      that rebinding [y] does not invalidate a field map that mentions it --
      which is [Hfields_ne], and which the rules carry for exactly this
      reason. *)
  Variables (rho : list FName) (N : FieldMap).
  Hypothesis Hlk_w   : lk m = Some tb.
  Hypothesis Hpath   : hstar (hp m) (rt m) rho = Some o.
  Hypothesis Hprefix : forall rho1 rho2, rho1 ++ rho2 = rho ->
    exists o', hstar (hp m) (rt m) rho1 = Some o' /\ obsv s o' (Oiter tb).
  Hypothesis Hfields : forall f v, N f = Some v -> FieldHolds s tb o f v.
  Hypothesis Hfields_ne : forall f z, N f = Some (FVar z) -> z <> y.

  Lemma bd_stk_other z : z <> y -> stk (ms s') z tb = stk m z tb.
  Proof.
    intros Hne. simpl. destruct (decide ((z, tb) = (y, tb))) as [Heq | _];
      [| reflexivity].
    exfalso. injection Heq as Hc. exact (Hne Hc).
  Qed.

  Lemma bd_FieldHolds f v :
    N f = Some v -> FieldHolds s tb o f v -> FieldHolds s' tb o f v.
  Proof.
    destruct v as [z|].
    - intros HN [oz (Hz & He & Hit & Hfl)].
      assert (Hs : stk (ms s') z tb = stk (ms s) z tb)
        by exact (bd_stk_other z (Hfields_ne f z HN)).
      unfold FieldHolds. rewrite Hs. exists oz.
      repeat apply conj;
        [exact Hz | exact He | exact (Hkeep oz _ Hit) | exact Hfl].
    - intros _ He. exact He.
  Qed.

  Theorem bind_post_env : D_rcuItr s' tb y rho N.
  Proof.
    exists o. repeat apply conj.
    - simpl. by destruct (decide ((y, tb) = (y, tb))).
    - exact Hitr.
    - exact Hdef.
    - intros f v HN. exact (bd_FieldHolds f v HN (Hfields f v HN)).
    - intros rho1 rho2 Heq. destruct (Hprefix rho1 rho2 Heq) as [o' [Hr Hit]].
      exists o'. split; [exact Hr | exact (Hkeep o' _ Hit)].
    - exact Hpath.
    - exact Hlk_w.
    - exact Hfl_o.
  Qed.

  Theorem bind_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact (bd_OW HOW).
    - exact (bd_RWOW HRWOW).
    - exact (bd_AWRT HAWRT).
    - exact (bd_IFL HIFL).
    - exact (bd_ULKR HULKR).
    - exact (bd_FLR HFLR).
    - exact (bd_WULK HWULK).
    - exact (bd_FR HFR).
    - exact (bd_WFresh HWFresh).
    - exact (bd_FNR HFNR).
    - exact (bd_FPI HFPI).
    - exact (bd_WNR HWNR).
    - exact (bd_RITR HRITR).
    - exact (bd_RINFL HRINFL).
    - exact (bd_HD HHD).
    - exact (bd_UNQRT_a HUa).
    - exact (bd_UNQRT_b HUb).
    - exact (bd_WUNLK HWU).
    - exact (bd_WITR HWI).
    - exact (bd_UNQR HUq).
  Qed.

End binding.

Print Assumptions bind_preserves_WellFormed.
Print Assumptions bind_post_env.

(** ** T-WriteFH

    [x.f := y] with [x] a [rcuFresh] object and [y] an [rcuItr].  The last of
    the rules, and the only heap mutation that changes no observation: the fresh
    node is still fresh afterwards and the node stored is still an iterator, so
    the eleven heap-free invariants are identities and only the write matters.

    It is also the only heap mutation whose UNQR case needs nothing beyond the
    unreachability of the node written.  The write goes *into* an unreachable
    node, so it creates no path from the root at all, and
    [UNQR_h_upd_unreachable] applies directly; the linking and unlinking rules
    write into the reachable structure and each needs a characterization of the
    paths their edge creates or destroys.

    Every obligation is discharged by [y] being an iterator and [x] fresh, which
    between them place the two nodes on opposite sides of every invariant that
    could complain.  The one exception is UNQRT$_a$: nothing in the invariants
    prevents the stored node from being the root, so the rule must say so, and
    [Hyrt] is that premise.  It is not a burden -- a fresh node is built to be
    spliced in below some existing node, never above the root -- but it does have
    to be stated, and the published rule does not state it. *)

Section freshwrite.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (lw : TID) (on : Loc) (f : FName) (oy : Loc).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m on f (VLoc oy)) Og U T F.

  Hypothesis Hlk : lk m = Some lw.

  (** [x] is fresh, [y] is the writer's iterator. *)
  Hypothesis Hfresh : obsv s on (Ofresh lw).
  Hypothesis Hitr   : obsv s oy (Oiter lw).
  (** [x] is unreachable, which FR gives, and [y] is allocated and not on the
      free list, which the [rcuItr] denotation gives. *)
  Hypothesis Hunreach : forall p, hstar (hp m) (rt m) p <> Some on.
  Hypothesis Hin_oy   : InHeap s oy.
  Hypothesis Hfl_oy   : flist s oy = None.
  (** The rule's own side condition. *)
  Hypothesis Hyrt : oy <> rt m.

  Lemma fw_edge_split q g z :
    Edge s' q g z -> ((q, g) = (on, f) /\ z = oy) \/ Edge s q g z.
  Proof.
    unfold Edge; simpl; intros He.
    destruct (edge_eq_dec q g on f) as [Heq | Hne].
    - left. injection Heq as -> ->. rewrite upd_same in He.
      injection He as <-. split; reflexivity.
    - right. by rewrite upd_other in He.
  Qed.

  Lemma fw_InHeap q : InHeap s q -> InHeap s' q.
  Proof.
    intros [g [v Hv]]. unfold InHeap; simpl.
    destruct (edge_eq_dec q g on f) as [Heq | Hne].
    - injection Heq as -> ->. exists f, (VLoc oy). apply upd_same.
    - exists g, v. by rewrite upd_other.
  Qed.

  (** The fresh node is detached and the iterator is not.  Between them these
      settle every case with content. *)
  Lemma fw_on_detached : Detached s on.
  Proof. exists lw. by right; right. Qed.

  Lemma fw_oy_live : FNR s -> WULK s -> ~ Detached s oy.
  Proof.
    intros HF HW [t0 [X | [X | X]]].
    - exact (proj1 (HW lw oy t0 Hlk Hitr) X).
    - exact (proj2 (HW lw oy t0 Hlk Hitr) X).
    - exact (proj1 (HF oy t0 lw X) Hitr).
  Qed.

  (** *** The eleven the write cannot reach *)

  Lemma fw_RWOW   : RWOW s   -> RWOW s'.   Proof. exact (fun H => H). Qed.
  Lemma fw_AWRT   : AWRT s   -> AWRT s'.   Proof. exact (fun H => H). Qed.
  Lemma fw_IFL    : IFL s    -> IFL s'.    Proof. exact (fun H => H). Qed.
  Lemma fw_WULK   : WULK s   -> WULK s'.   Proof. exact (fun H => H). Qed.
  Lemma fw_WFresh : WFresh s -> WFresh s'. Proof. exact (fun H => H). Qed.
  Lemma fw_FNR    : FNR s    -> FNR s'.    Proof. exact (fun H => H). Qed.
  Lemma fw_WNR    : WNR s    -> WNR s'.    Proof. exact (fun H => H). Qed.
  Lemma fw_RITR   : RITR s   -> RITR s'.   Proof. exact (fun H => H). Qed.
  Lemma fw_RINFL  : RINFL s  -> RINFL s'.  Proof. exact (fun H => H). Qed.
  Lemma fw_WUNLK  : WUNLK s  -> WUNLK s'.  Proof. exact (fun H => H). Qed.
  Lemma fw_WITR   : WITR s   -> WITR s'.   Proof. exact (fun H => H). Qed.

  (** *** The eight the write does reach *)

  Lemma fw_OW : OW FType s -> OW FType s'.
  Proof.
    intros H q q' g g' z He He' Hg Hg'.
    destruct (fw_edge_split q  g  z He)  as [[Heq  Hz ] | Hold ];
    destruct (fw_edge_split q' g' z He') as [[Heq' Hz'] | Hold'].
    - injection Heq as -> ->. injection Heq' as -> ->. by left.
    - injection Heq as -> ->. right; left. exact fw_on_detached.
    - injection Heq' as -> ->. right; right. exact fw_on_detached.
    - exact (H q q' g g' z Hold Hold' Hg Hg').
  Qed.

  Lemma fw_ULKR : WULK s -> ULKR s -> ULKR s'.
  Proof.
    intros HW H q q' g t Hobs He.
    destruct (fw_edge_split q' g q He) as [[Heq Hz] | Hold].
    - (* the edge created points at the iterator, which is neither *)
      exfalso. subst q. destruct Hobs as [Y | Y];
        [exact (proj1 (HW lw oy t Hlk Hitr) Y)
        |exact (proj2 (HW lw oy t Hlk Hitr) Y)].
    - exact (H q q' g t Hobs Hold).
  Qed.

  Lemma fw_FLR : FLR s -> FLR s'.
  Proof.
    intros H q q' g Tr Hfl He.
    destruct (fw_edge_split q' g q He) as [[_ Hz] | Hold].
    - exfalso. subst q. rewrite Hfl_oy in Hfl. discriminate.
    - exact (H q q' g Tr Hfl Hold).
  Qed.

  Lemma fw_FR : FNR s -> FR s -> FR s'.
  Proof.
    intros HF H t z q Hstk Hob.
    destruct (H t z q Hstk Hob) as [Hin Hal]. split; [| exact Hal].
    intros q' g He. destruct (fw_edge_split q' g q He) as [[_ Hz] | Hold].
    - (* the target is an iterator, so it is not the fresh node *)
      subst q. exact (proj1 (HF oy t lw Hob) Hitr).
    - exact (Hin q' g Hold).
  Qed.

  (** FPI is the case the rule exists to establish: the fresh node's new field
      points at the writer's iterator, which is exactly what FPI asks. *)
  Lemma fw_FPI : FPI FType s -> FPI FType s'.
  Proof.
    intros H q g z t lw' Hob He Hft Hlk'.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (fw_edge_split q g z He) as [[_ ->] | Hold].
    - exact Hitr.
    - exact (H q g z t lw Hob Hold Hft Hlk).
  Qed.

  Lemma fw_HD : HD s -> HD s'.
  Proof.
    intros H q g z He Hnd.
    destruct (fw_edge_split q g z He) as [[_ ->] | Hold].
    - exact (fw_InHeap oy Hin_oy).
    - exact (fw_InHeap z (H q g z Hold Hnd)).
  Qed.

  Lemma fw_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof.
    intros H q g He.
    destruct (fw_edge_split q g (rt (ms s')) He) as [[_ Hz] | Hold].
    - exact (Hyrt (eq_sym Hz)).
    - exact (H q g Hold).
  Qed.

  (** Reachability is untouched, the written node being unreachable. *)
  Lemma fw_reach p q : Reaches s' p q -> Reaches s p q.
  Proof.
    unfold Reaches; simpl.
    by rewrite (hstar_upd_unreachable (hp m) (rt m) on f (VLoc oy) Hunreach p).
  Qed.

  Lemma fw_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p q lw' Hlk' Hr. exact (H p q lw' Hlk' (fw_reach p q Hr)).
  Qed.

  Lemma fw_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros H p p' q H1 H2. exact (H p p' q (fw_reach p q H1) (fw_reach p' q H2)).
  Qed.

  (** *** The post-type environment: [x : rcuFresh N[f |-> y]]

      The rule's whole effect at the type level is to record the written field
      in the fresh node's map, and the denotation's two field clauses are what
      has to follow: the written field now holds [y], and every field outside
      the map is still null.  Both are the write, read off. *)
  Variables (xn xy : Var) (N : FieldMap).
  Hypothesis Hden_n : D_rcuFresh FType s lw xn N.
  Hypothesis Hstk_n : stk m xn lw = Some on.
  Hypothesis Hstk_y : stk m xy lw = Some oy.

  Definition Nupd : FieldMap :=
    fun g => if decide (g = f) then Some (FVar xy) else N g.

  Lemma fw_hp_f : hp (ms s') on f = Some (VLoc oy).
  Proof. apply upd_same. Qed.

  Lemma fw_hp_other g : g <> f -> hp (ms s') on g = hp m on g.
  Proof.
    intros Hne. apply upd_other. intros Hc. injection Hc as Hc2.
    exact (Hne Hc2).
  Qed.

  Lemma fw_FieldHolds g v :
    g <> f -> FieldHolds s lw on g v -> FieldHolds s' lw on g v.
  Proof.
    intros Hne.
    assert (Hg : hp (ms s') on g = hp (ms s) on g) by exact (fw_hp_other g Hne).
    destruct v as [z|]; unfold FieldHolds; rewrite Hg; intros H; exact H.
  Qed.

  Theorem write_fresh_post_env : D_rcuFresh FType s' lw xn Nupd.
  Proof.
    destruct Hden_n as [o' (Hstk' & Hfr' & Hnu' & Hfl' & Hfields & Hnulls)].
    rewrite Hstk_n in Hstk'. injection Hstk' as <-.
    exists on. repeat apply conj.
    - exact Hstk_n.
    - exact Hfr'.
    - exact Hnu'.
    - exact Hfl'.
    - intros g v Hg. unfold Nupd in Hg.
      destruct (decide (g = f)) as [-> | Hne].
      + injection Hg as <-. simpl. exists oy.
        repeat apply conj; [exact Hstk_y | exact fw_hp_f | exact Hitr | exact Hfl_oy].
      + exact (fw_FieldHolds g v Hne (Hfields g v Hg)).
    - intros g Hrcu Hnone. unfold Nupd in Hnone.
      destruct (decide (g = f)) as [-> | Hne]; [discriminate |].
      rewrite (fw_hp_other g Hne). exact (Hnulls g Hrcu Hnone).
  Qed.

  Theorem write_fresh_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact (fw_OW HOW).
    - exact (fw_RWOW HRWOW).
    - exact (fw_AWRT HAWRT).
    - exact (fw_IFL HIFL).
    - exact (fw_ULKR HWULK HULKR).
    - exact (fw_FLR HFLR).
    - exact (fw_WULK HWULK).
    - exact (fw_FR HFNR HFR).
    - exact (fw_WFresh HWFresh).
    - exact (fw_FNR HFNR).
    - exact (fw_FPI HFPI).
    - exact (fw_WNR HWNR).
    - exact (fw_RITR HRITR).
    - exact (fw_RINFL HRINFL).
    - exact (fw_HD HHD).
    - exact (fw_UNQRT_a HUa).
    - exact (fw_UNQRT_b HUb).
    - exact (fw_WUNLK HWU).
    - exact (fw_WITR HWI).
    - exact (fw_UNQR HUq).
  Qed.

End freshwrite.

Print Assumptions write_fresh_preserves_WellFormed.
Print Assumptions write_fresh_post_env.

(** ** WriteEnd

    Releasing the lock.  ReadEnd's counterpart, and it has the same shape: the
    departing writer drops its observations and its variables in the same step
    as the lock, since RWOW would fail at once otherwise.

    It also has a premise ReadEnd does not, and this is the rule that supplies
    it: the critical section leaves nothing detached.  \textsc{ToRCUWrite}
    enforces exactly that by forbidding [unlinked] and [freeable] in the post
    environment, and the same holds of [rcuFresh] -- a fresh node never linked
    in would simply leak.  With it most of the nineteen become vacuous rather
    than merely easier, which is the sense in which a write critical section is
    a closed unit. *)

Definition write_end_ms (m : MState) : MState :=
  {| stk := stk m; hp := hp m; lk := None; rt := rt m;
     rds := rds m; bnd := bnd m |}.

Section release.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U U' : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)) (lw : TID).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_end_ms m) Og' U' T F.

  Hypothesis Hlk : lk m = Some lw.

  Hypothesis Hself : forall o ob, obs_tid ob = Some lw -> ~ obsv s' o ob.
  Hypothesis Hkeep : forall o ob,
    obsv s o ob -> obs_tid ob <> Some lw -> obsv s' o ob.
  Hypothesis Hshrink : forall o ob, obsv s' o ob -> obsv s o ob.

  Hypothesis Hundf_w    : forall x, undf s' x lw.
  Hypothesis Hundf_grow : forall x t, undf s x t -> undf s' x t.

  (** Nothing is left detached. *)
  Hypothesis Hclean : forall o, ~ Detached s o.

  Lemma we_lk : lk (ms s') = None.
  Proof. reflexivity. Qed.

  Lemma we_not_w o t : obsv s' o (Oiter t) -> t <> lw.
  Proof. intros H ->. exact (Hself o (Oiter lw) eq_refl H). Qed.

  Lemma we_no_fresh o t : ~ obsv s' o (Ofresh t).
  Proof.
    intros H. apply (Hclean o). exists t. right; right. exact (Hshrink _ _ H).
  Qed.

  Lemma we_no_det o t :
    ~ obsv s' o (Ounlk t) /\ ~ obsv s' o (Ofree t).
  Proof.
    split; intros H; apply (Hclean o); exists t.
    - left. exact (Hshrink _ _ H).
    - right; left. exact (Hshrink _ _ H).
  Qed.

  Lemma we_OW : OW FType s -> OW FType s'.
  Proof.
    intros H o o' f f' x He He' Hf Hf'.
    destruct (H o o' f f' x He He' Hf Hf') as [Hs | [Hd | Hd]];
      [by left | exfalso; exact (Hclean o Hd) | exfalso; exact (Hclean o' Hd)].
  Qed.

  Lemma we_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hnu.
    assert (Hne : t <> lw) by (intros ->; exact (Hnu (Hundf_w x))).
    destruct (H x t o Hstk (fun Hc => Hnu (Hundf_grow x t Hc)))
      as [Hit | [Hlk' Hrest]].
    - left. apply (Hkeep o _ Hit). simpl. by injection 1 as ->.
    - exfalso. rewrite Hlk in Hlk'. injection Hlk' as <-. by apply Hne.
  Qed.

  Lemma we_AWRT : AWRT s -> AWRT s'.
  Proof.
    intros H y t Hstk Hnu.
    assert (Hne : t <> lw) by (intros ->; exact (Hnu (Hundf_w y))).
    apply (Hkeep _ _ (H y t Hstk (fun Hc => Hnu (Hundf_grow y t Hc)))).
    simpl. by injection 1 as ->.
  Qed.

  Lemma we_IFL : IFL s -> IFL s'.
  Proof. intros H t o Tr Hit Hfl. exact (H t o Tr (Hshrink _ _ Hit) Hfl). Qed.

  Lemma we_ULKR : ULKR s -> ULKR s'.
  Proof.
    intros H o o' f t Hobs He. exfalso.
    destruct Hobs as [X | X];
      [exact (proj1 (we_no_det o t) X) | exact (proj2 (we_no_det o t) X)].
  Qed.

  Lemma we_WULK : WULK s -> WULK s'.
  Proof. intros H lw' o t Hlk' Hit. discriminate Hlk'. Qed.

  Lemma we_FR : FR s -> FR s'.
  Proof. intros H t x o Hstk Hob. exfalso. exact (we_no_fresh o t Hob). Qed.

  Lemma we_WFresh : WFresh s -> WFresh s'.
  Proof. intros H t x o Hstk Hob. exfalso. exact (we_no_fresh o t Hob). Qed.

  Lemma we_FNR : FNR s -> FNR s'.
  Proof. intros H o t t' Hob. exfalso. exact (we_no_fresh o t Hob). Qed.

  Lemma we_FPI : FPI FType s -> FPI FType s'.
  Proof.
    intros H o f o' t lw' Hob He Hft Hlk'. exfalso. exact (we_no_fresh o t Hob).
  Qed.

  Lemma we_WNR : WNR s -> WNR s'.
  Proof. intros H t Hlk'. discriminate Hlk'. Qed.

  Lemma we_RITR : RITR s -> RITR s'.
  Proof.
    intros H o t Hrd. repeat apply conj; intros Hbad;
      [exact (proj1 (we_no_det o t) Hbad) | exact (proj2 (we_no_det o t) Hbad)
      |exact (we_no_fresh o t Hbad)].
  Qed.

  Lemma we_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.

  Lemma we_HD : HD s -> HD s'.
  Proof. intros H o f o' He _. exact (H o f o' He (Hclean o)). Qed.

  Lemma we_UNQRT_a : UNQRT_a s -> UNQRT_a s'. Proof. exact (fun H => H). Qed.
  Lemma we_UNQR    : UNQR s    -> UNQR s'.    Proof. exact (fun H => H). Qed.

  Lemma we_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof. intros H p o lw' Hlk' Hr. discriminate Hlk'. Qed.

  Lemma we_WUNLK : WUNLK s -> WUNLK s'.
  Proof. intros H o t lw' Hlk' Hobs. discriminate Hlk'. Qed.

  Lemma we_WITR : WITR s -> WITR s'.
  Proof.
    intros H o t Hit.
    destruct (H o t (Hshrink _ _ Hit)) as [Hlk' | Hrd].
    - exfalso. rewrite Hlk in Hlk'. injection Hlk' as Ht.
      exact (we_not_w o t Hit (eq_sym Ht)).
    - by right.
  Qed.

  Theorem write_end_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact (we_OW HOW).
    - exact (we_RWOW HRWOW).
    - exact (we_AWRT HAWRT).
    - exact (we_IFL HIFL).
    - exact (we_ULKR HULKR).
    - exact HFLR.
    - exact (we_WULK HWULK).
    - exact (we_FR HFR).
    - exact (we_WFresh HWFresh).
    - exact (we_FNR HFNR).
    - exact (we_FPI HFPI).
    - exact (we_WNR HWNR).
    - exact (we_RITR HRITR).
    - exact (we_RINFL HRINFL).
    - exact (we_HD HHD).
    - exact (we_UNQRT_a HUa).
    - exact (we_UNQRT_b HUb).
    - exact (we_WUNLK HWU).
    - exact (we_WITR HWI).
    - exact (we_UNQR HUq).
  Qed.

End release.

Print Assumptions write_end_preserves_WellFormed.

(** ** WriteBegin, and what UNQRT_b costs it

    The last action, and the one that does not go through as written.

    \textsc{RCU-WBegin} takes the lock and changes nothing else.  But UNQRT$_b$
    says that while a writer holds the lock every reachable node carries that
    writer's [iterator] observation, and before the step there is no writer, so
    the invariant said nothing.  A thread that has just acquired the lock holds
    no references at all, so on any structure larger than the bare root
    UNQRT$_b$ is false immediately after a lock acquire that only takes the
    lock.

    The step therefore has to grant the incoming writer an [iterator]
    observation on every reachable node.  That is harmless -- the observation
    map is ghost state, and a writer inside its critical section may indeed
    reach anything from the root, so recording it asserts nothing new about the
    heap -- but it is not nothing either, and neither the semantics nor the
    invariant discussion says it happens.  [Hcover] below is that grant, and it
    is the only hypothesis here that is not read off a rule.

    Whether the right repair is this or a weaker UNQRT$_b$ is a question about
    the intended reading of the observation map, and we do not settle it.  What
    the mechanization establishes is that one of the two is needed: the
    invariant as published and the action as published cannot both stand. *)

Definition write_begin_ms (m : MState) (t : TID) : MState :=
  {| stk := stk m; hp := hp m; lk := Some t; rt := rt m;
     rds := rds m; bnd := bnd m |}.

Section acquire.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)) (lw : TID).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_begin_ms m lw) Og' U T F.

  Hypothesis Hlk_pre : lk m = None.
  Hypothesis Hnotrd  : ~ rds m lw.

  (** The grant UNQRT_b forces, and the two directions of the change. *)
  Hypothesis Hcover : forall p o,
    Reaches s p o -> obsv s' o (Oiter lw) \/ obsv s' o Oroot.
  Hypothesis Hnew : forall o ob,
    obsv s' o ob -> obsv s o ob \/ (ob = Oiter lw /\ exists p, Reaches s p o).
  Hypothesis Hkeep : forall o ob, obsv s o ob -> obsv s' o ob.

  (** The section is entered with nothing detached and nothing on the free list
      that is reachable -- what the previous WriteEnd left behind. *)
  Hypothesis Hclean : forall o, ~ Detached s o.
  Hypothesis Hreach_fl : forall p o, Reaches s p o -> flist s o = None.

  Lemma wb_back o ob : ob <> Oiter lw -> obsv s' o ob -> obsv s o ob.
  Proof.
    intros Hne H. destruct (Hnew o ob H) as [Y | [Hc _]];
      [exact Y | by contradiction].
  Qed.

  Lemma wb_no_det o t : ~ obsv s' o (Ounlk t) /\ ~ obsv s' o (Ofree t).
  Proof.
    split; intros H; apply (Hclean o); exists t.
    - left.  apply (wb_back o _); [discriminate | exact H].
    - right; left. apply (wb_back o _); [discriminate | exact H].
  Qed.

  Lemma wb_no_fresh o t : ~ obsv s' o (Ofresh t).
  Proof.
    intros H. apply (Hclean o). exists t. right; right.
    apply (wb_back o _); [discriminate | exact H].
  Qed.

  Lemma wb_OW : OW FType s -> OW FType s'.
  Proof.
    intros H o o' f f' x He He' Hf Hf'.
    destruct (H o o' f f' x He He' Hf Hf') as [Hs | [Hd | Hd]];
      [by left | exfalso; exact (Hclean o Hd) | exfalso; exact (Hclean o' Hd)].
  Qed.

  Lemma wb_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hnu.
    destruct (H x t o Hstk Hnu) as [Hit | [Hlk' _]];
      [left; exact (Hkeep o _ Hit) | exfalso; rewrite Hlk_pre in Hlk'; discriminate].
  Qed.

  Lemma wb_AWRT : AWRT s -> AWRT s'.
  Proof. intros H y t Hstk Hnu. exact (Hkeep _ _ (H y t Hstk Hnu)). Qed.

  Lemma wb_IFL : IFL s -> IFL s'.
  Proof.
    intros H t o Tr Hit Hfl.
    destruct (Hnew o _ Hit) as [Hit0 | [_ [p Hr]]].
    - exact (H t o Tr Hit0 Hfl).
    - exfalso. rewrite (Hreach_fl p o Hr) in Hfl. discriminate.
  Qed.

  Lemma wb_ULKR : ULKR s -> ULKR s'.
  Proof.
    intros H o o' f t Hobs He. exfalso.
    destruct Hobs as [X | X];
      [exact (proj1 (wb_no_det o t) X) | exact (proj2 (wb_no_det o t) X)].
  Qed.

  Lemma wb_WULK : WULK s -> WULK s'.
  Proof.
    intros H lw' o t Hlk' Hit.
    split; intros Hbad;
      [exact (proj1 (wb_no_det o t) Hbad) | exact (proj2 (wb_no_det o t) Hbad)].
  Qed.

  Lemma wb_FR : FR s -> FR s'.
  Proof. intros H t x o Hstk Hob. exfalso. exact (wb_no_fresh o t Hob). Qed.

  Lemma wb_WFresh : WFresh s -> WFresh s'.
  Proof. intros H t x o Hstk Hob. exfalso. exact (wb_no_fresh o t Hob). Qed.

  Lemma wb_FNR : FNR s -> FNR s'.
  Proof. intros H o t t' Hob. exfalso. exact (wb_no_fresh o t Hob). Qed.

  Lemma wb_FPI : FPI FType s -> FPI FType s'.
  Proof.
    intros H o f o' t lw' Hob He Hft Hlk'. exfalso. exact (wb_no_fresh o t Hob).
  Qed.

  Lemma wb_WNR : WNR s -> WNR s'.
  Proof. intros H t Hlk' Hrd. injection Hlk' as <-. exact (Hnotrd Hrd). Qed.

  Lemma wb_RITR : RITR s -> RITR s'.
  Proof.
    intros H o t Hrd. repeat apply conj; intros Hbad;
      [exact (proj1 (wb_no_det o t) Hbad) | exact (proj2 (wb_no_det o t) Hbad)
      |exact (wb_no_fresh o t Hbad)].
  Qed.

  Lemma wb_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.

  Lemma wb_HD : HD s -> HD s'.
  Proof. intros H o f o' He _. exact (H o f o' He (Hclean o)). Qed.

  Lemma wb_UNQRT_a : UNQRT_a s -> UNQRT_a s'. Proof. exact (fun H => H). Qed.
  Lemma wb_UNQR    : UNQR s    -> UNQR s'.    Proof. exact (fun H => H). Qed.

  (** The case the grant exists for. *)
  Lemma wb_UNQRT_b : UNQRT_b s'.
  Proof. intros p o lw' Hlk' Hr. injection Hlk' as <-. exact (Hcover p o Hr). Qed.

  Lemma wb_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t lw' Hlk' Hobs. exfalso.
    destruct Hobs as [X | X];
      [exact (proj1 (wb_no_det o t) X) | exact (proj2 (wb_no_det o t) X)].
  Qed.

  Lemma wb_WITR : WITR s -> WITR s'.
  Proof.
    intros H o t Hit. destruct (Hnew o _ Hit) as [Hit0 | [Hc _]].
    - destruct (H o t Hit0) as [Hlk' | Hrd];
        [exfalso; rewrite Hlk_pre in Hlk'; discriminate | by right].
    - injection Hc as Ht. left. by rewrite Ht.
  Qed.

  Theorem write_begin_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact (wb_OW HOW).
    - exact (wb_RWOW HRWOW).
    - exact (wb_AWRT HAWRT).
    - exact (wb_IFL HIFL).
    - exact (wb_ULKR HULKR).
    - exact HFLR.
    - exact (wb_WULK HWULK).
    - exact (wb_FR HFR).
    - exact (wb_WFresh HWFresh).
    - exact (wb_FNR HFNR).
    - exact (wb_FPI HFPI).
    - exact (wb_WNR HWNR).
    - exact (wb_RITR HRITR).
    - exact (wb_RINFL HRINFL).
    - exact (wb_HD HHD).
    - exact (wb_UNQRT_a HUa).
    - exact wb_UNQRT_b.
    - exact (wb_WUNLK HWU).
    - exact (wb_WITR HWI).
    - exact (wb_UNQR HUq).
  Qed.

End acquire.

Print Assumptions write_begin_preserves_WellFormed.

(** ** T-LinkF-Null

    The variant of T-Insert in which the fresh node's RCU fields are all null --
    appending at the end of a list, or inserting a leaf.  The paper mentions it
    and does not show it, and it is not an instance of T-Insert: [PointsOnlyAt]
    requires the fresh node to have exactly one outgoing edge, and here it has
    none.

    It is the easier of the two, and in exactly the place where T-Insert was
    hard.  The OW and HD cases that had to be re-discharged there -- because [n]
    was detached before the step and live after it, so a case OW settled by its
    detachment needed another argument -- are vacuous here, [n] having no
    outgoing edge to be the source of. *)

Section linking.

  Variable FType : FName -> FieldKind.
  Variables (m : MState) (Og Og' : ObsMap) (U : Var -> TID -> Prop)
            (T : gset TID) (F : gmap Loc (gset TID)).
  Variables (lw : TID) (op : Loc) (f : FName) (on : Loc) (rho : list FName).

  Let s  := to_LState_t m Og U T F.
  Let s' := to_LState_t (write_ms m op f (VLoc on)) Og' U T F.

  Hypothesis Hlk : lk m = Some lw.

  Hypothesis Hpromote : obsv s' on (Oiter lw).
  Hypothesis Hnofresh : forall t, ~ obsv s' on (Ofresh t).
  Hypothesis Hnew : forall o ob,
    obsv s' o ob -> obsv s o ob \/ (o = on /\ ob = Oiter lw).
  Hypothesis Hkeep : forall o ob,
    obsv s o ob -> (o, ob) <> (on, Ofresh lw) -> obsv s' o ob.

  Hypothesis Hfresh   : obsv s on (Ofresh lw).
  Hypothesis Hitr_op  : obsv s op (Oiter lw).
  Hypothesis Hpn      : PointsNowhere (hp m) on.
  Hypothesis Hno_in   : forall o g, hp m o g <> Some (VLoc on).
  Hypothesis Hin_on   : InHeap s on.
  Hypothesis Hnrt     : on <> rt m.
  Hypothesis Hfl_on   : flist s on = None.
  Hypothesis Hrho     : hstar (hp m) (rt m) rho = Some op.
  Hypothesis HU       : UNQR_h (hp m) (rt m).

  Lemma ln_unreach : forall sigma, hstar (hp m) (rt m) sigma <> Some on.
  Proof.
    apply (no_incoming_unreachable (hp m) (rt m) on Hno_in).
    intros Hc. exact (Hnrt (eq_sym Hc)).
  Qed.

  Lemma ln_np : on <> op.
  Proof. intros Hc. apply (ln_unreach rho). by rewrite Hrho Hc. Qed.

  Lemma ln_edge_split o g x :
    Edge s' o g x -> ((o, g) = (op, f) /\ x = on) \/ Edge s o g x.
  Proof.
    unfold Edge; simpl; intros He.
    destruct (edge_eq_dec o g op f) as [Heq | Hne].
    - left. injection Heq as -> ->. rewrite upd_same in He.
      injection He as <-. split; reflexivity.
    - right. by rewrite upd_other in He.
  Qed.

  Lemma ln_InHeap o : InHeap s o -> InHeap s' o.
  Proof.
    intros [g [v Hv]]. unfold InHeap; simpl.
    destruct (edge_eq_dec o g op f) as [Heq | Hne].
    - injection Heq as -> ->. exists f, (VLoc on). apply upd_same.
    - exists g, v. by rewrite upd_other.
  Qed.

  (** The fresh node is the source of no edge, before or after. *)
  Lemma ln_no_out g x : ~ Edge s' on g x.
  Proof.
    intros He. destruct (ln_edge_split on g x He) as [[Heq _] | Hold].
    - injection Heq as Hc _. exact (ln_np Hc).
    - exact (Hpn g x Hold).
  Qed.

  Lemma ln_keep_ob o ob : obsv s o ob -> ob <> Ofresh lw -> obsv s' o ob.
  Proof.
    intros Hob Hne. apply (Hkeep o ob Hob). intros Hc.
    injection Hc as _ Hc2. exact (Hne Hc2).
  Qed.

  Lemma ln_keep_iter o t : obsv s o (Oiter t) -> obsv s' o (Oiter t).
  Proof. intros H. apply (ln_keep_ob o _ H). discriminate. Qed.
  Lemma ln_keep_unlk o t : obsv s o (Ounlk t) -> obsv s' o (Ounlk t).
  Proof. intros H. apply (ln_keep_ob o _ H). discriminate. Qed.
  Lemma ln_keep_free o t : obsv s o (Ofree t) -> obsv s' o (Ofree t).
  Proof. intros H. apply (ln_keep_ob o _ H). discriminate. Qed.
  Lemma ln_keep_root o : obsv s o Oroot -> obsv s' o Oroot.
  Proof. intros H. apply (ln_keep_ob o _ H). discriminate. Qed.

  Lemma ln_keep_ne o ob : o <> on -> obsv s o ob -> obsv s' o ob.
  Proof. intros Hne Hob. apply (Hkeep o ob Hob). by injection 1 as ->. Qed.

  Lemma ln_back_ne o ob : o <> on -> obsv s' o ob -> obsv s o ob.
  Proof.
    intros Hne Hob. destruct (Hnew o ob Hob) as [X | [-> _]];
      [exact X | by contradiction].
  Qed.

  Lemma ln_detached_keep o : o <> on -> Detached s o -> Detached s' o.
  Proof.
    intros Hne [t0 [Hb | [Hb | Hb]]]; exists t0;
      [left | right; left | right; right]; exact (ln_keep_ne o _ Hne Hb).
  Qed.

  Lemma ln_fresh_inv o t : obsv s' o (Ofresh t) -> o <> on /\ obsv s o (Ofresh t).
  Proof.
    intros Hob.
    assert (Hne : o <> on) by (intros ->; exact (Hnofresh t Hob)).
    split; [exact Hne | exact (ln_back_ne o _ Hne Hob)].
  Qed.

  Lemma ln_op_not_fresh : FNR s -> forall t, ~ obsv s op (Ofresh t).
  Proof. intros HF t Hob. exact (proj1 (HF op t lw Hob) Hitr_op). Qed.

  Lemma ln_RWOW : RWOW s -> RWOW s'.
  Proof.
    intros H x t o Hstk Hnu.
    destruct (H x t o Hstk Hnu) as [Hit | [Hlk' [Hu | [Hfr | Hfs]]]].
    - left. exact (ln_keep_iter o t Hit).
    - right. split; [exact Hlk' |]. left. exact (ln_keep_unlk o t Hu).
    - right. split; [exact Hlk' |]. right; left. exact (ln_keep_free o t Hfr).
    - destruct (decide (o = on)) as [-> | Hne].
      + rewrite Hlk in Hlk'. injection Hlk' as <-. by left.
      + right. split; [exact Hlk' |]. right; right. exact (ln_keep_ne o _ Hne Hfs).
  Qed.

  Lemma ln_AWRT : AWRT s -> AWRT s'.
  Proof. intros H y t Hstk Hnu. exact (ln_keep_iter _ t (H y t Hstk Hnu)). Qed.

  Lemma ln_IFL : IFL s -> IFL s'.
  Proof.
    intros H t o Tr Hit Hfl.
    destruct (Hnew o _ Hit) as [Hit0 | [-> _]].
    - exact (H t o Tr Hit0 Hfl).
    - exfalso. rewrite Hfl_on in Hfl. discriminate.
  Qed.

  Lemma ln_WULK : FNR s -> WULK s -> WULK s'.
  Proof.
    intros HF H lw' o t Hlk' Hit.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (decide (o = on)) as [-> | Hne].
    - destruct (HF on lw t Hfresh) as (_ & Hnu & Hnf).
      split; intros Hbad; destruct (Hnew on _ Hbad) as [Y | [_ Hc]];
        try discriminate; [exact (Hnu Y) | exact (Hnf Y)].
    - destruct (H lw o t Hlk (ln_back_ne o _ Hne Hit)) as [Hnu Hnf].
      split; intros Hbad; [exact (Hnu (ln_back_ne o _ Hne Hbad))
                          | exact (Hnf (ln_back_ne o _ Hne Hbad))].
  Qed.

  Lemma ln_FR : FR s -> FR s'.
  Proof.
    intros H t x o Hstk Hob.
    destruct (ln_fresh_inv o t Hob) as [Hne Hob0].
    destruct (H t x o Hstk Hob0) as [Hin Hal].
    split; [| exact Hal].
    intros o' g He. destruct (ln_edge_split o' g o He) as [[_ Hx] | Hold].
    - exact (Hne Hx).
    - exact (Hin o' g Hold).
  Qed.

  Lemma ln_WFresh : WFresh s -> WFresh s'.
  Proof.
    intros H t x o Hstk Hob.
    exact (H t x o Hstk (proj2 (ln_fresh_inv o t Hob))).
  Qed.

  Lemma ln_FNR : FNR s -> FNR s'.
  Proof.
    intros H o t t' Hob.
    destruct (ln_fresh_inv o t Hob) as [Hne Hob0].
    destruct (H o t t' Hob0) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      [exact (H1 (ln_back_ne o _ Hne Hbad))
      |exact (H2 (ln_back_ne o _ Hne Hbad))
      |exact (H3 (ln_back_ne o _ Hne Hbad))].
  Qed.

  Lemma ln_RITR : RITR s -> RITR s'.
  Proof.
    intros H o t Hrd. destruct (H o t Hrd) as (H1 & H2 & H3).
    repeat apply conj; intros Hbad;
      destruct (Hnew o _ Hbad) as [X | [_ Hc]]; try discriminate.
    - exact (H1 X).
    - exact (H2 X).
    - exact (H3 X).
  Qed.

  Lemma ln_RINFL : RINFL s -> RINFL s'. Proof. exact (fun H => H). Qed.
  Lemma ln_WNR   : WNR s   -> WNR s'.   Proof. exact (fun H => H). Qed.

  (** OW: the case that was hard for T-Insert is vacuous here. *)
  Lemma ln_OW : OW FType s -> OW FType s'.
  Proof.
    intros H o o' g g' x He He' Hg Hg'.
    destruct (ln_edge_split o  g  x He)  as [[Heq  Hx ] | Hold ];
    destruct (ln_edge_split o' g' x He') as [[Heq' Hx'] | Hold'].
    - injection Heq as -> ->. injection Heq' as -> ->. by left.
    - exfalso. rewrite Hx in Hold'. exact (Hno_in o' g' Hold').
    - exfalso. rewrite Hx' in Hold. exact (Hno_in o g Hold).
    - assert (Hne  : o  <> on) by (intros ->; exact (Hpn g  x Hold)).
      assert (Hne' : o' <> on) by (intros ->; exact (Hpn g' x Hold')).
      destruct (H o o' g g' x Hold Hold' Hg Hg') as [Hsame | [Hd | Hd]].
      + by left.
      + right; left.  exact (ln_detached_keep o Hne Hd).
      + right; right. exact (ln_detached_keep o' Hne' Hd).
  Qed.

  Lemma ln_ULKR : FNR s -> ULKR s -> ULKR s'.
  Proof.
    intros HF H o o' g t Hobs He.
    assert (Hobs0 : obsv s o (Ounlk t) \/ obsv s o (Ofree t)).
    { destruct Hobs as [X | X].
      - destruct (Hnew o _ X) as [Y | [_ Hc]]; [by left | discriminate].
      - destruct (Hnew o _ X) as [Y | [_ Hc]]; [by right | discriminate]. }
    destruct (ln_edge_split o' g o He) as [[_ Hx] | Hold].
    - exfalso. subst o. destruct Hobs0 as [Y | Y];
        [exact (proj1 (proj2 (HF on lw t Hfresh)) Y)
        |exact (proj2 (proj2 (HF on lw t Hfresh)) Y)].
    - destruct (H o o' g t Hobs0 Hold) as [Y | Y];
        [left; exact (ln_keep_unlk o' t Y) | right; exact (ln_keep_free o' t Y)].
  Qed.

  Lemma ln_FLR : FLR s -> FLR s'.
  Proof.
    intros H o o' g Tr Hfl He.
    destruct (ln_edge_split o' g o He) as [[_ Hx] | Hold].
    - exfalso. subst o. rewrite Hfl_on in Hfl. discriminate.
    - exact (H o o' g Tr Hfl Hold).
  Qed.

  Lemma ln_FPI : FNR s -> FPI FType s -> FPI FType s'.
  Proof.
    intros HF H o g x t lw' Hob He Hft Hlk'.
    destruct (ln_fresh_inv o t Hob) as [Hne Hob0].
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (ln_edge_split o g x He) as [[Heq _] | Hold].
    - exfalso. injection Heq as -> ->. exact (ln_op_not_fresh HF t Hob0).
    - exact (ln_keep_iter x lw (H o g x t lw Hob0 Hold Hft Hlk)).
  Qed.

  Lemma ln_HD : HD s -> HD s'.
  Proof.
    intros H o g x He Hnd.
    destruct (ln_edge_split o g x He) as [[_ ->] | Hold].
    - exact (ln_InHeap on Hin_on).
    - assert (Hne : o <> on) by (intros ->; exact (Hpn g x Hold)).
      apply ln_InHeap. apply (H o g x Hold).
      intros Hd. exact (Hnd (ln_detached_keep o Hne Hd)).
  Qed.

  Lemma ln_UNQRT_a : UNQRT_a s -> UNQRT_a s'.
  Proof.
    intros H o g He.
    destruct (ln_edge_split o g (rt (ms s')) He) as [[_ Hx] | Hold].
    - exact (Hnrt (eq_sym Hx)).
    - exact (H o g Hold).
  Qed.

  Lemma ln_UNQRT_b : UNQRT_b s -> UNQRT_b s'.
  Proof.
    intros H p x lw' Hlk' Hr.
    simpl in Hlk'. rewrite Hlk in Hlk'. injection Hlk' as <-.
    destruct (hstar_link_null_char (hp m) (rt m) op f on p x Hpn ln_np Hr)
      as [Hpre | [-> _]].
    - destruct (H p x lw Hlk Hpre) as [Hit | Hrt].
      + left.  exact (ln_keep_iter x lw Hit).
      + right. exact (ln_keep_root x Hrt).
    - by left.
  Qed.

  Lemma ln_WUNLK : WUNLK s -> WUNLK s'.
  Proof.
    intros H o t lw' Hlk' Hobs. apply (H o t lw' Hlk').
    destruct Hobs as [X | X]; destruct (Hnew o _ X) as [Y | [_ Hc]];
      [by left | discriminate | by right | discriminate].
  Qed.

  Lemma ln_WITR : WITR s -> WITR s'.
  Proof.
    intros H o t Hit. destruct (Hnew o _ Hit) as [Y | [_ Hc]].
    - exact (H o t Y).
    - injection Hc as Ht. left. rewrite Ht. exact Hlk.
  Qed.

  Lemma ln_UNQR : UNQR s -> UNQR s'.
  Proof.
    intros _ p p' x H1 H2.
    exact (UNQR_link_null (hp m) (rt m) op f on HU Hpn ln_np ln_unreach
             p p' x H1 H2).
  Qed.

  (** *** The post-type environment: [n : rcuItr (rho.f) N1]

      Identical in shape to T-Insert's, the path being the same. *)
  Variables (xn : Var) (N1 : FieldMap).
  Hypothesis Hstk_n    : stk m xn lw = Some on.
  Hypothesis Hundf_n   : ~ undf s xn lw.
  Hypothesis Hfields_n : forall g v, N1 g = Some v -> FieldHolds s lw on g v.
  Hypothesis Hprefix   : forall rho1 rho2, rho1 ++ rho2 = rho ->
    exists o', hstar (hp m) (rt m) rho1 = Some o' /\ obsv s o' (Oiter lw).

  Lemma ln_avoids : avoids (hp m) (rt m) rho op f.
  Proof. exact (UNQR_avoids (hp m) (rt m) op f rho HU Hrho). Qed.

  Lemma ln_path : hstar (hp (ms s')) (rt m) (rho ++ [f]) = Some on.
  Proof.
    rewrite (hstar_upd_through (hp m) op f on rho [] (rt m) ln_avoids Hrho).
    reflexivity.
  Qed.

  Lemma ln_hp_n g : hp (ms s') on g = hp m on g.
  Proof.
    apply upd_other. intros Hc. injection Hc as Hc1 _. exact (ln_np Hc1).
  Qed.

  Lemma ln_FieldHolds g v : FieldHolds s lw on g v -> FieldHolds s' lw on g v.
  Proof.
    assert (Hg : hp (ms s') on g = hp (ms s) on g) by exact (ln_hp_n g).
    destruct v as [z|].
    - intros [oz (Hz & He & Hit & Hfl)]. unfold FieldHolds. rewrite Hg.
      exists oz. repeat apply conj;
        [exact Hz | exact He | exact (ln_keep_iter oz lw Hit) | exact Hfl].
    - intros He. unfold FieldHolds. rewrite Hg. exact He.
  Qed.

  Theorem link_null_post_env : D_rcuItr s' lw xn (rho ++ [f]) N1.
  Proof.
    exists on. repeat apply conj.
    - exact Hstk_n.
    - exact Hpromote.
    - intros Hc. exact (Hundf_n Hc).
    - intros g v HN. exact (ln_FieldHolds g v (Hfields_n g v HN)).
    - intros rho1 rho2 Heq.
      destruct (decide (rho1 = rho ++ [f])) as [-> | Hne].
      + exists on. split; [exact ln_path | exact Hpromote].
      + assert (Hne2 : rho2 <> []).
        { intros ->. apply Hne. by rewrite app_nil_r in Heq. }
        destruct (prefix_of_snoc rho1 rho2 rho f Heq Hne2) as [sigma Hs].
        destruct (Hprefix rho1 sigma Hs) as [o' [Hr Hit]].
        exists o'. split.
        * rewrite (hstar_upd_avoids (hp m) op f (VLoc on) rho1 (rt m)
                     (avoids_prefix (hp m) rho1 sigma (rt m) op f
                        ltac:(rewrite Hs; exact ln_avoids))).
          exact Hr.
        * exact (ln_keep_iter o' lw Hit).
    - exact ln_path.
    - exact Hlk.
    - exact Hfl_on.
  Qed.

  (** *** The parent: [p : rcuItr rho Np[f |-> n]] *)
  Variables (xp : Var) (Np : FieldMap).
  Hypothesis Hstk_p    : stk m xp lw = Some op.
  Hypothesis Hundf_p   : ~ undf s xp lw.
  Hypothesis Hfl_op    : flist s op = None.
  Hypothesis Hfields_p : forall g v, Np g = Some v -> FieldHolds s lw op g v.

  Definition LNparent : FieldMap :=
    fun g => if decide (g = f) then Some (FVar xn) else Np g.

  Lemma ln_hp_p g : g <> f -> hp (ms s') op g = hp m op g.
  Proof.
    intros Hne. apply upd_other. intros Hc. injection Hc as Hc2. exact (Hne Hc2).
  Qed.

  Lemma ln_FieldHolds_p g v :
    g <> f -> FieldHolds s lw op g v -> FieldHolds s' lw op g v.
  Proof.
    intros Hne.
    assert (Hg : hp (ms s') op g = hp (ms s) op g) by exact (ln_hp_p g Hne).
    destruct v as [z|].
    - intros [oz (Hz & He & Hit & Hfl)].
      assert (Hon : oz <> on) by (intros ->; exact (Hno_in op g He)).
      unfold FieldHolds. rewrite Hg. exists oz.
      repeat apply conj;
        [exact Hz | exact He | exact (ln_keep_ne oz _ Hon Hit) | exact Hfl].
    - intros He. unfold FieldHolds. rewrite Hg. exact He.
  Qed.

  Theorem link_null_post_env_parent : D_rcuItr s' lw xp rho LNparent.
  Proof.
    exists op. repeat apply conj.
    - exact Hstk_p.
    - exact (ln_keep_iter op lw Hitr_op).
    - intros Hc. exact (Hundf_p Hc).
    - intros g v HN. unfold LNparent in HN.
      destruct (decide (g = f)) as [-> | Hne].
      + injection HN as <-. unfold FieldHolds. exists on.
        repeat apply conj;
          [exact Hstk_n | apply upd_same | exact Hpromote | exact Hfl_on].
      + exact (ln_FieldHolds_p g v Hne (Hfields_p g v HN)).
    - intros rho1 rho2 Heq. destruct (Hprefix rho1 rho2 Heq) as [o' [Hr Hit]].
      exists o'. split.
      + rewrite (hstar_upd_avoids (hp m) op f (VLoc on) rho1 (rt m)
                   (avoids_prefix (hp m) rho1 rho2 (rt m) op f
                      ltac:(rewrite Heq; exact ln_avoids))).
        exact Hr.
      + exact (ln_keep_iter o' lw Hit).
    - rewrite (hstar_upd_avoids (hp m) op f (VLoc on) rho (rt m) ln_avoids).
      exact Hrho.
    - exact Hlk.
    - exact Hfl_op.
  Qed.

  Theorem link_null_preserves_WellFormed :
    WellFormed FType s -> WellFormed FType s'.
  Proof.
    intros (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR & HWFresh
            & HFNR & HFPI & HWNR & HRITR & HRINFL & HHD & HUa & HUb & HWU & HWI
            & HUq).
    repeat apply conj.
    - exact (ln_OW HOW).
    - exact (ln_RWOW HRWOW).
    - exact (ln_AWRT HAWRT).
    - exact (ln_IFL HIFL).
    - exact (ln_ULKR HFNR HULKR).
    - exact (ln_FLR HFLR).
    - exact (ln_WULK HFNR HWULK).
    - exact (ln_FR HFR).
    - exact (ln_WFresh HWFresh).
    - exact (ln_FNR HFNR).
    - exact (ln_FPI HFNR HFPI).
    - exact (ln_WNR HWNR).
    - exact (ln_RITR HRITR).
    - exact (ln_RINFL HRINFL).
    - exact (ln_HD HHD).
    - exact (ln_UNQRT_a HUa).
    - exact (ln_UNQRT_b HUb).
    - exact (ln_WUNLK HWU).
    - exact (ln_WITR HWI).
    - exact (ln_UNQR HUq).
  Qed.

End linking.

Print Assumptions link_null_preserves_WellFormed.
Print Assumptions link_null_post_env.
Print Assumptions link_null_post_env_parent.

(** * Executions

    Everything above is about a single step: fifteen theorems, each saying an
    action carries \textsf{WellFormed} across.  What a client cares about is a
    whole run, and the gap between the two is one induction -- but stating it
    is worth the space, because it is what turns ``no well-formed state has a
    dangling live reference'' into ``no \emph{reachable} state has one'', which
    is the property memory safety actually asserts.

    The step relation is a parameter here, and deliberately.  Its obligation is
    exactly the fifteen theorems above: any relation assembled from them
    discharges it by case analysis, and assembling it is transcription rather
    than proof.  What the section adds is that the invariants are inductive
    along executions and that safety then holds at every reachable state.
    [free_step] below is a concrete instance, so the parameterisation is not
    vacuous. *)

Section executions.
  Variable FType : FName -> FieldKind.
  Variable step : LState -> LState -> Prop.
  Hypothesis step_preserves :
    forall s s', step s s' -> WellFormed FType s -> WellFormed FType s'.

  Inductive reachable (s0 : LState) : LState -> Prop :=
  | reach_refl : reachable s0 s0
  | reach_step s s' : reachable s0 s -> step s s' -> reachable s0 s'.

  Theorem reachable_WellFormed s0 s :
    WellFormed FType s0 -> reachable s0 s -> WellFormed FType s.
  Proof.
    intros H0 Hr. induction Hr as [| s s' _ IH Hst];
      [exact H0 | exact (step_preserves s s' Hst IH)].
  Qed.

  (** And the property the whole development is for, over runs rather than
      states: at no point in any execution from a well-formed start does a
      thread other than the writer hold a live reference to a node the writer is
      about to reclaim. *)
  Theorem safety s0 s tw x o y t' :
    WellFormed FType s0 -> reachable s0 s ->
    D_freeable s tw x ->
    stk (ms s) x tw = Some o ->
    stk (ms s) y t' = Some o -> ~ undf s y t' ->
    t' = tw.
  Proof.
    intros H0 Hr Hfree Hd Hy Hnu.
    destruct (reachable_WellFormed s0 s H0 Hr)
      as (_ & HRWOW & _ & HIFL & _).
    exact (free_invalidates_nobody s tw x o y t'
             HIFL HRWOW Hfree Hd Hy Hnu).
  Qed.

End executions.

(** A concrete step relation, so that the section above is not vacuous.  Its
    obligation is [free_preserves_WellFormed] and nothing else. *)
Definition free_step (s s' : LState) : Prop :=
  exists m Og U T F d t,
    s = to_LState_t m Og U T F
    /\ s' = to_LState_t (free_ms m d) Og U T (delete d F)
    /\ obsv s d (Ofree t).

Lemma free_step_preserves FType s s' :
  free_step s s' -> WellFormed FType s -> WellFormed FType s'.
Proof.
  intros (m & Og & U & T & F & d & t & -> & -> & Hfree) Hwf.
  exact (free_preserves_WellFormed FType m Og U T F d t Hwf Hfree).
Qed.

(** So the safety theorem applies to it, and to any relation the other fourteen
    actions are assembled into in the same way. *)
Corollary free_runs_are_safe FType s0 s tw x o y t' :
  WellFormed FType s0 -> reachable free_step s0 s ->
  D_freeable s tw x ->
  stk (ms s) x tw = Some o ->
  stk (ms s) y t' = Some o -> ~ undf s y t' ->
  t' = tw.
Proof.
  exact (safety FType free_step (free_step_preserves FType) s0 s tw x o y t').
Qed.

Print Assumptions reachable_WellFormed.
Print Assumptions safety.
Print Assumptions free_step_preserves.
Print Assumptions free_runs_are_safe.

(** * The step relation, written out

    The [executions] section above takes the step relation as a parameter, and
    its obligation is exactly the fifteen preservation theorems.  This is the
    relation itself: one constructor per action, each carrying that action's
    hypotheses, so that [lstep_preserves] is fifteen applications and nothing
    else.  It adds no argument; what it adds is that [safety] can be stated at
    the whole system rather than at one action.

    Built in three groups, in the order the file proves them. *)

Inductive lstep (FType : FName -> FieldKind) : LState -> LState -> Prop :=
(** ** The reclamation chain *)
| L_free m Og U T F d t :
    obsv (to_LState_t m Og U T F) d (Ofree t) ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (free_ms m d) Og U T (delete d F))
| L_read_begin m Og U T F t :
    (forall lw, lk m = Some lw -> lw <> t) ->
    (forall o, ~ obsv (to_LState_t m Og U T F) o (Ounlk t)
            /\ ~ obsv (to_LState_t m Og U T F) o (Ofree t)
            /\ ~ obsv (to_LState_t m Og U T F) o (Ofresh t)) ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (read_begin_ms m t) Og U T F)
| L_read_end m Og Og' U U' T F t :
    (forall o ob, obs_tid ob = Some t ->
       ~ obsv (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t)) o ob) ->
    (forall o ob, obsv (to_LState_t m Og U T F) o ob -> obs_tid ob <> Some t ->
       obsv (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t)) o ob) ->
    (forall o ob,
       obsv (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t)) o ob ->
       obsv (to_LState_t m Og U T F) o ob) ->
    (forall x, undf (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t)) x t) ->
    (forall x t', undf (to_LState_t m Og U T F) x t' ->
       undf (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t)) x t') ->
    rds m t ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (read_end_ms m t) Og' U' T (read_end_F F t))
| L_sync_start m Og U T F F' Rs :
    (forall t, t ∈ Rs <-> rds m t) ->
    (forall o s0, F' !! o = Some s0 -> s0 = Rs) ->
    (forall o t, obsv (to_LState_t m Og U T F) o (Ounlk t)
              \/ obsv (to_LState_t m Og U T F) o (Ofree t) ->
       exists s0, F' !! o = Some s0) ->
    (forall o s0, F' !! o = Some s0 ->
       exists t, obsv (to_LState_t m Og U T F) o (Ounlk t)
              \/ obsv (to_LState_t m Og U T F) o (Ofree t)) ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (sync_start_ms m) Og U T F')
| L_sync_stop m Og U T F :
    (forall t, ~ bnd m t) ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (sync_stop_ms m) (sync_stop_Og Og) U T F)
| L_read m Og U T F t z sz :
    (forall S, Og !! (z, t) = Some S -> S ⊆ sz) ->
    (forall ob, ob ∈ sz -> exists S, Og !! (z, t) = Some S /\ ob ∈ S) ->
    rds m t ->
    (forall Tr, flist (to_LState_t m Og U T F) z = Some Tr -> Tr t) ->
    (forall t0, ~ obsv (to_LState_t m Og U T F) z (Ofresh t0)) ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t m (<[(z, t) := sz ∪ {[Oiter t]}]> Og) U T F)
(** ** Allocation and binding *)
| L_alloc m Og Og' U U' T F lw n x fs :
    lk m = Some lw ->
    obsv (to_LState_t (alloc_ms m n fs x lw) Og' U' T F) n (Ofresh lw) ->
    (forall o ob, obsv (to_LState_t (alloc_ms m n fs x lw) Og' U' T F) o ob ->
       obsv (to_LState_t m Og U T F) o ob \/ (o = n /\ ob = Ofresh lw)) ->
    (forall o ob, obsv (to_LState_t m Og U T F) o ob ->
       obsv (to_LState_t (alloc_ms m n fs x lw) Og' U' T F) o ob) ->
    (forall y t, (y, t) <> (x, lw) ->
       undf (to_LState_t (alloc_ms m n fs x lw) Og' U' T F) y t
       <-> undf (to_LState_t m Og U T F) y t) ->
    (forall g, hp m n g = None) ->
    (forall ob, ~ obsv (to_LState_t m Og U T F) n ob) ->
    (forall o g, hp m o g <> Some (VLoc n)) ->
    (forall y t, stk m y t <> Some n) ->
    n <> rt m ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (alloc_ms m n fs x lw) Og' U' T F)
| L_bind m Og Og' U U' T F tb y o :
    (lk m = Some tb \/ rds m tb) ->
    obsv (to_LState_t (bind_ms m y tb o) Og' U' T F) o (Oiter tb) ->
    (forall q ob, obsv (to_LState_t (bind_ms m y tb o) Og' U' T F) q ob ->
       obsv (to_LState_t m Og U T F) q ob \/ (q = o /\ ob = Oiter tb)) ->
    (forall q ob, obsv (to_LState_t m Og U T F) q ob ->
       obsv (to_LState_t (bind_ms m y tb o) Og' U' T F) q ob) ->
    (forall z t, (z, t) <> (y, tb) ->
       undf (to_LState_t (bind_ms m y tb o) Og' U' T F) z t
       <-> undf (to_LState_t m Og U T F) z t) ->
    ~ Detached (to_LState_t m Og U T F) o ->
    flist (to_LState_t m Og U T F) o = None ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (bind_ms m y tb o) Og' U' T F)
(** ** The heap mutations *)
| L_write_fresh m Og U T F lw on f oy :
    lk m = Some lw ->
    obsv (to_LState_t m Og U T F) on (Ofresh lw) ->
    obsv (to_LState_t m Og U T F) oy (Oiter lw) ->
    (forall p, hstar (hp m) (rt m) p <> Some on) ->
    InHeap (to_LState_t m Og U T F) oy ->
    flist (to_LState_t m Og U T F) oy = None ->
    oy <> rt m ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (write_ms m on f (VLoc oy)) Og U T F)
| L_link_null m Og Og' U T F lw op f on rho :
    lk m = Some lw ->
    obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) on (Oiter lw) ->
    (forall t, ~ obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F)
                 on (Ofresh t)) ->
    (forall o ob, obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) o ob ->
       obsv (to_LState_t m Og U T F) o ob \/ (o = on /\ ob = Oiter lw)) ->
    (forall o ob, obsv (to_LState_t m Og U T F) o ob ->
       (o, ob) <> (on, Ofresh lw) ->
       obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) o ob) ->
    obsv (to_LState_t m Og U T F) on (Ofresh lw) ->
    obsv (to_LState_t m Og U T F) op (Oiter lw) ->
    PointsNowhere (hp m) on ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    InHeap (to_LState_t m Og U T F) on ->
    on <> rt m ->
    flist (to_LState_t m Og U T F) on = None ->
    hstar (hp m) (rt m) rho = Some op ->
    UNQR_h (hp m) (rt m) ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (write_ms m op f (VLoc on)) Og' U T F)
| L_unlink m Og Og' U T F lw ox f1 oz f2 ow rho :
    lk m = Some lw ->
    obsv (to_LState_t (write_ms m ox f1 (VLoc ow)) Og' U T F) oz (Ounlk lw) ->
    ~ obsv (to_LState_t (write_ms m ox f1 (VLoc ow)) Og' U T F) oz (Oiter lw) ->
    (forall o ob, obsv (to_LState_t (write_ms m ox f1 (VLoc ow)) Og' U T F) o ob ->
       obsv (to_LState_t m Og U T F) o ob \/ (o = oz /\ ob = Ounlk lw)) ->
    (forall o ob, obsv (to_LState_t m Og U T F) o ob ->
       (o, ob) <> (oz, Oiter lw) ->
       obsv (to_LState_t (write_ms m ox f1 (VLoc ow)) Og' U T F) o ob) ->
    (forall o g o', hp m o g = Some (VLoc o') -> FType g = RCUField) ->
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
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (write_ms m ox f1 (VLoc ow)) Og' U T F)
| L_insert m Og Og' U T F lw op f on oo f4 rho :
    lk m = Some lw ->
    obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) on (Oiter lw) ->
    (forall t, ~ obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F)
                 on (Ofresh t)) ->
    (forall o ob, obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) o ob ->
       obsv (to_LState_t m Og U T F) o ob \/ (o = on /\ ob = Oiter lw)) ->
    (forall o ob, obsv (to_LState_t m Og U T F) o ob ->
       (o, ob) <> (on, Ofresh lw) ->
       obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) o ob) ->
    (forall o g o', hp m o g = Some (VLoc o') -> FType g = RCUField) ->
    hp m op f = Some (VLoc oo) ->
    obsv (to_LState_t m Og U T F) on (Ofresh lw) ->
    obsv (to_LState_t m Og U T F) op (Oiter lw) ->
    PointsOnlyAt (hp m) on f4 oo ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    InHeap (to_LState_t m Og U T F) on ->
    on <> rt m ->
    flist (to_LState_t m Og U T F) on = None ->
    hstar (hp m) (rt m) rho = Some op ->
    UNQR_h (hp m) (rt m) ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (write_ms m op f (VLoc on)) Og' U T F)
| L_replace m Og Og' U T F lw op f oo on rho :
    lk m = Some lw ->
    obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) on (Oiter lw) ->
    (forall t, ~ obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F)
                 on (Ofresh t)) ->
    obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) oo (Ounlk lw) ->
    ~ obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) oo (Oiter lw) ->
    (forall o ob, obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) o ob ->
       obsv (to_LState_t m Og U T F) o ob
       \/ (o = on /\ ob = Oiter lw) \/ (o = oo /\ ob = Ounlk lw)) ->
    (forall o ob, obsv (to_LState_t m Og U T F) o ob ->
       (o, ob) <> (on, Ofresh lw) -> (o, ob) <> (oo, Oiter lw) ->
       obsv (to_LState_t (write_ms m op f (VLoc on)) Og' U T F) o ob) ->
    (forall o g o', hp m o g = Some (VLoc o') -> FType g = RCUField) ->
    hp m op f = Some (VLoc oo) ->
    Mirrors (hp m) on oo ->
    obsv (to_LState_t m Og U T F) on (Ofresh lw) ->
    obsv (to_LState_t m Og U T F) op (Oiter lw) ->
    obsv (to_LState_t m Og U T F) oo (Oiter lw) ->
    (forall o g, hp m o g <> Some (VLoc on)) ->
    InHeap (to_LState_t m Og U T F) on ->
    on <> rt m ->
    flist (to_LState_t m Og U T F) on = None ->
    hstar (hp m) (rt m) rho = Some op ->
    UNQR_h (hp m) (rt m) ->
    (forall q t g, obsv (to_LState_t m Og U T F) q (Ofresh t) ->
       hp m q g <> Some (VLoc oo)) ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (write_ms m op f (VLoc on)) Og' U T F)
(** ** The write critical section's boundaries *)
| L_write_begin m Og Og' U T F lw :
    lk m = None ->
    ~ rds m lw ->
    (forall p o, Reaches (to_LState_t m Og U T F) p o ->
       obsv (to_LState_t (write_begin_ms m lw) Og' U T F) o (Oiter lw)
       \/ obsv (to_LState_t (write_begin_ms m lw) Og' U T F) o Oroot) ->
    (forall o ob, obsv (to_LState_t (write_begin_ms m lw) Og' U T F) o ob ->
       obsv (to_LState_t m Og U T F) o ob
       \/ (ob = Oiter lw /\ exists p, Reaches (to_LState_t m Og U T F) p o)) ->
    (forall o ob, obsv (to_LState_t m Og U T F) o ob ->
       obsv (to_LState_t (write_begin_ms m lw) Og' U T F) o ob) ->
    (forall o, ~ Detached (to_LState_t m Og U T F) o) ->
    (forall p o, Reaches (to_LState_t m Og U T F) p o ->
       flist (to_LState_t m Og U T F) o = None) ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (write_begin_ms m lw) Og' U T F)
| L_write_end m Og Og' U U' T F lw :
    lk m = Some lw ->
    (forall o ob, obs_tid ob = Some lw ->
       ~ obsv (to_LState_t (write_end_ms m) Og' U' T F) o ob) ->
    (forall o ob, obsv (to_LState_t m Og U T F) o ob ->
       obs_tid ob <> Some lw ->
       obsv (to_LState_t (write_end_ms m) Og' U' T F) o ob) ->
    (forall o ob, obsv (to_LState_t (write_end_ms m) Og' U' T F) o ob ->
       obsv (to_LState_t m Og U T F) o ob) ->
    (forall x, undf (to_LState_t (write_end_ms m) Og' U' T F) x lw) ->
    (forall x t, undf (to_LState_t m Og U T F) x t ->
       undf (to_LState_t (write_end_ms m) Og' U' T F) x t) ->
    (forall o, ~ Detached (to_LState_t m Og U T F) o) ->
    lstep FType (to_LState_t m Og U T F)
                (to_LState_t (write_end_ms m) Og' U' T F).

Lemma lstep_preserves FType s s' :
  lstep FType s s' -> WellFormed FType s -> WellFormed FType s'.
Proof.
  intros Hst Hwf. destruct Hst.
  - exact (free_preserves_WellFormed FType m Og U T F d t Hwf H).
  - exact (read_begin_preserves_WellFormed FType m Og U T F t H H0 Hwf).
  - exact (read_end_preserves_WellFormed FType m Og Og' U U' T F t
             H H0 H1 H2 H3 H4 Hwf).
  - exact (sync_start_preserves_WellFormed FType m Og U T F F' Rs
             H H0 H1 H2 Hwf).
  - exact (sync_stop_WellFormed FType m Og U T F H Hwf).
  - exact (reader_acquire_preserves_WellFormed FType m Og U T F t z sz
             H H0 H1 H2 H3 Hwf).
  - exact (alloc_preserves_WellFormed FType m Og Og' U U' T F lw n x fs
             H H0 H1 H2 H3 H4 H5 H6 H7 H8 Hwf).
  - exact (bind_preserves_WellFormed FType m Og Og' U U' T F tb y o
             H H0 H1 H2 H3 H4 H5 Hwf).
  - exact (write_fresh_preserves_WellFormed FType m Og U T F lw on f oy
             H H0 H1 H2 H3 H4 H5 Hwf).
  - exact (link_null_preserves_WellFormed FType m Og Og' U T F lw op f on rho
             H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Hwf).
  - exact (unlink_preserves_WellFormed FType m Og Og' U T F lw ox f1 oz f2 ow
             rho H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 Hwf).
  - exact (insert_preserves_WellFormed FType m Og Og' U T F lw op f on oo f4
             rho H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 Hwf).
  - exact (replace_preserves_WellFormed FType m Og Og' U T F lw op f oo on rho
             H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
             H18 Hwf).
  - exact (write_begin_preserves_WellFormed FType m Og Og' U T F lw
             H H0 H1 H2 H3 H4 H5 Hwf).
  - exact (write_end_preserves_WellFormed FType m Og Og' U U' T F lw
             H H0 H1 H2 H3 H4 H5 Hwf).
Qed.

Print Assumptions lstep_preserves.

(** And so the safety theorem holds of the whole system rather than of one
    action.  This is what [executions] was parameterised for; [free_step] was
    the placeholder while the relation was being written. *)
Corollary system_is_safe FType s0 s tw x o y t' :
  WellFormed FType s0 -> reachable (lstep FType) s0 s ->
  D_freeable s tw x ->
  stk (ms s) x tw = Some o ->
  stk (ms s) y t' = Some o -> ~ undf s y t' ->
  t' = tw.
Proof.
  exact (safety FType (lstep FType) (lstep_preserves FType) s0 s tw x o y t').
Qed.

(** A word on progress, because the obvious statement is not the right one.
    ``Some step is always possible'' is false and should be: a state in which no
    thread can move is a deadlock, and whether one is reachable is a question
    about the program, not about [LState].  [lstep] has no program counter --
    it relates states, not configurations -- so relation-level progress is not
    statable here and would not mean what it sounds like.

    What progress means for this system is per-thread and per-primitive: that a
    well-typed thread about to execute an RCU primitive finds that primitive's
    side condition true.  That is what the six [guard_*] propositions in
    [WellFormed.v] are, and it is discharged where a thread's own resources are
    available rather than here: [read_begin_guard] and [read_end_guard] in
    [Triples.v] for the reader's two, [write_end_unconditional] for the one that
    is trivial, and [writer_guards_are_not_invariants] for the proof that the
    writer's three cannot be discharged from the state at all, two of them being
    the blocking ones. *)

Print Assumptions lstep_preserves.
Print Assumptions system_is_safe.
