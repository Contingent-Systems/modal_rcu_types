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

(** ** A limitation of the observation camera, found by attempting FPI

    The next invariant to discharge for these actions is FPI, and it does not
    go through -- not because of the rules, which were repaired, but because of
    the ghost state chosen in [IrisGhost.v].

    Unlinking has to *revoke* an observation: the replaced node loses
    [iterator] and gains [unlinked], and WULK makes the two exclusive.  But the
    value camera is [gsetUR], whose operation is union.  Its elements are all
    [CoreId], so [obs_frag] is persistent -- an observation, once handed out,
    is held forever, and by [observes_mem] the authority must keep recording it
    forever too.

    The lemma below is that fact stated precisely: while any thread holds the
    iterator fragment for a location, WULK forbids that location from being
    observed unlinked.  Since the fragment is persistent it is still held in
    the post-state, so no action that unlinks such a location can re-establish
    the invariant.

    This is a real defect in milestone 3, not a missing lemma.  The union
    camera is right for a quantity that only grows; observations are not one.
    Fixing it is a design choice with consequences for how readers and the
    writer share observations -- an exclusive or fractional per-location entry
    would allow revocation but would stop readers sharing an observation
    freely, which is what [observes] is for -- so it is recorded here rather
    than guessed at. *)

Section limitation.
  Context `{!rcuG Σ}.

  Lemma iter_frag_blocks_unlink m O U T F γ o lw :
    lk m = Some lw ->
    WULK (to_LState m O U T F) ->
    obs_auth γ O -∗ observes γ o (Oiter lw) -∗
      ⌜forall t', ~ obsv (to_LState m O U T F) o (Ounlk t')⌝.
  Proof.
    iIntros (Hlk HW) "Ha Hf".
    iDestruct (observes_mem with "Ha Hf") as %[s [Hlkp Hin]].
    iPureIntro. intros t' Hunl.
    assert (Hiter : obsv (to_LState m O U T F) o (Oiter lw))
      by (simpl; rewrite Hlkp; exact Hin).
    destruct (HW lw o t' Hlk Hiter) as [Hno _].
    exact (Hno Hunl).
  Qed.

End limitation.

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
Print Assumptions iter_frag_blocks_unlink.
