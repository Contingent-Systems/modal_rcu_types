(** * Programs: the thing every theorem so far has been borrowing against

    Milestone 8.  Everything before this file relates *states*.  [lstep] is a
    relation on [LState], the fifteen action theorems are about one state and
    the next, and the safety theorem says "any state reachable by these steps".
    That is weaker than it sounds, and weaker than "verified" will be taken to
    mean: there is no command language anywhere in the development, no thread
    pool, no configurations, and so no way to quantify over the runs of a
    program at all.

    This file supplies them.  A command language whose primitives are the
    fifteen actions, a pool of threads, configurations, a thread-local step
    relation and its lift to an interleaving, a typing judgement over commands,
    and two theorems: subject reduction, and safety over the runs of any
    program from any well-formed start.

    Two deliberate abstractions, stated rather than hidden.

    Conditions are abstracted: [CIf] steps to either branch.  There is no
    expression language here, and the type system's branch refinement is the
    checker's business (Appendix B); for safety, taking either branch is the
    stronger statement, since it quantifies over more runs than a real
    condition would allow.

    The action's effect is a parameter, [Step], required only to be an [lstep].
    That is what lets this file be about programs without re-encoding fifteen
    actions' worth of side conditions: everything that pins down *which* state
    change an action makes is in [Actions.v] and [Triples.v], and what is added
    here is the quantification over threads and interleavings.  Safety needs
    nothing more.  Subject reduction needs the link between an action's typing
    and its effect, and that link is exactly axiom soundness, which
    [Triples.v] proves for all fifteen --- so it is taken as a hypothesis here
    and discharged there.

    Checked with Rocq 9.2, axiom-free. *)

From stdpp Require Import gmap sets.
From RCU Require Import WellFormed HeapPaths IrisGhost Denotations Actions.

(** ** The language *)

Inductive act :=
| AFree | AReadBegin | AReadEnd | ASyncStart | ASyncStop
| ARead | AAlloc | ABind | AWriteFresh | ALinkNull
| AUnlink | AInsert | AReplace | AWriteBegin | AWriteEnd.

Inductive cmd :=
| CSkip
| CAct (a : act)
| CSeq (c1 c2 : cmd)
| CIf (c1 c2 : cmd)
| CWhile (c : cmd).

(** The two block forms are derived rather than primitive, which is what the
    desugaring in the paper says they are. *)
Definition CReadBlock (c : cmd) : cmd :=
  CSeq (CAct AReadBegin) (CSeq c (CAct AReadEnd)).
Definition CWriteBlock (c : cmd) : cmd :=
  CSeq (CAct AWriteBegin) (CSeq c (CAct AWriteEnd)).

Definition Pool := gmap TID cmd.
Definition Conf : Type := Pool * LState.

Section semantics.
  Variable FType : FName -> FieldKind.

  (** What an action does.  Left a parameter, required only to be a step of the
      relation [Actions.v] defines. *)
  Variable Step : act -> LState -> LState -> Prop.
  Hypothesis Step_lstep : forall a s s', Step a s s' -> lstep FType s s'.

  (** ** One thread *)
  Inductive tstep : cmd -> LState -> cmd -> LState -> Prop :=
  | T_act a s s' :
      Step a s s' -> tstep (CAct a) s CSkip s'
  | T_seq c1 s c1' s' c2 :
      tstep c1 s c1' s' -> tstep (CSeq c1 c2) s (CSeq c1' c2) s'
  | T_seq_skip c s : tstep (CSeq CSkip c) s c s
  | T_if_l c1 c2 s : tstep (CIf c1 c2) s c1 s
  | T_if_r c1 c2 s : tstep (CIf c1 c2) s c2 s
  | T_while c s : tstep (CWhile c) s (CIf (CSeq c (CWhile c)) CSkip) s.

  (** ** All of them, interleaved *)
  Inductive cstep : Conf -> Conf -> Prop :=
  | CS (t : TID) (P : Pool) (s : LState) (c c' : cmd) (s' : LState) :
      P !! t = Some c -> tstep c s c' s' ->
      cstep (P, s) (<[t := c']> P, s').

  (** ** Safety

      Every step of every thread is a step of [lstep], so the invariants hold
      at every point of every interleaving.  This is the statement the earlier
      files could not make. *)
  Lemma tstep_preserves c s c' s' :
    tstep c s c' s' -> WellFormed FType s -> WellFormed FType s'.
  Proof.
    induction 1 as [a s s' Ha | | | | | ]; intros Hwf; try exact Hwf.
    - exact (lstep_preserves FType s s' (Step_lstep a s s' Ha) Hwf).
    - by apply IHtstep.
  Qed.

  Theorem cstep_preserves cf cf' :
    cstep cf cf' -> WellFormed FType (snd cf) -> WellFormed FType (snd cf').
  Proof.
    intros [t P s c c' s' Hlk Ht] Hwf. cbn in Hwf |- *.
    exact (tstep_preserves c s c' s' Ht Hwf).
  Qed.

  Theorem crun_preserves cf cf' :
    rtc cstep cf cf' -> WellFormed FType (snd cf) -> WellFormed FType (snd cf').
  Proof.
    induction 1 as [| a b d Hab Hbd IH]; intros Hwf; [exact Hwf |].
    exact (IH (cstep_preserves a b Hab Hwf)).
  Qed.

  (** And the property the whole development exists for, now said of programs:
      at no point in any interleaving of any program, from any well-formed
      start, does a thread other than the writer hold a live reference to a
      node the writer is about to reclaim. *)
  Theorem programs_are_memory_safe cf cf' tw x o :
    rtc cstep cf cf' -> WellFormed FType (snd cf) ->
    D_freeable (snd cf') tw x ->
    stk (ms (snd cf')) x tw = Some o ->
    forall y t', t' <> tw -> stk (ms (snd cf')) y t' = Some o ->
      ~ undf (snd cf') y t' -> False.
  Proof.
    intros Hrun Hwf Hfree Hstk.
    pose proof (crun_preserves cf cf' Hrun Hwf) as Hwf'.
    destruct Hwf' as (_ & HRWOW & _ & HIFL & _).
    exact (no_live_reference_to_a_freeable_node (snd cf') tw x o
             HIFL HRWOW Hfree Hstk).
  Qed.

End semantics.

Print Assumptions cstep_preserves.
Print Assumptions crun_preserves.
Print Assumptions programs_are_memory_safe.

(** ** Typing, and subject reduction

    The judgement is structural: sequencing threads the environment, a
    conditional requires both branches to agree because the condition is
    abstracted, and a loop requires its body to preserve the environment, which
    is what makes the invariant at a back edge an invariant.  The action case
    is a parameter, and the hypothesis tying it to the action's effect is
    exactly axiom soundness --- the post-state satisfies the denotation of the
    post-type environment --- which is what [Triples.v] proves for all fifteen.

    So this file does not re-prove the type system.  It says what the type
    system's per-action results add up to once there are programs. *)

Section typing.
  Variable FType : FName -> FieldKind.
  Variable Step : act -> LState -> LState -> Prop.
  Variable ActTyped : Env -> act -> Env -> Prop.

  (** Axiom soundness, per action. *)
  Hypothesis Act_sound : forall G a G' s s' t,
    ActTyped G a G' -> Step a s s' -> D_env FType s t G -> D_env FType s' t G'.

  Inductive Typed : Env -> cmd -> Env -> Prop :=
  | TySkip G : Typed G CSkip G
  | TyAct G a G' : ActTyped G a G' -> Typed G (CAct a) G'
  | TySeq G1 c1 G2 c2 G3 :
      Typed G1 c1 G2 -> Typed G2 c2 G3 -> Typed G1 (CSeq c1 c2) G3
  | TyIf G c1 c2 G' :
      Typed G c1 G' -> Typed G c2 G' -> Typed G (CIf c1 c2) G'
  | TyWhile G c : Typed G c G -> Typed G (CWhile c) G.

  (** The two block forms type as their desugaring, which is the point of
      deriving them. *)
  Lemma TyReadBlock G c G' :
    ActTyped G AReadBegin G -> Typed G c G -> ActTyped G AReadEnd G' ->
    Typed G (CReadBlock c) G'.
  Proof.
    intros Hb Hc He. unfold CReadBlock.
    apply (TySeq G _ G _ G'); [by apply TyAct |].
    apply (TySeq G _ G _ G'); [exact Hc | by apply TyAct].
  Qed.

  Lemma TyWriteBlock G c G' :
    ActTyped G AWriteBegin G -> Typed G c G -> ActTyped G AWriteEnd G' ->
    Typed G (CWriteBlock c) G'.
  Proof.
    intros Hb Hc He. unfold CWriteBlock.
    apply (TySeq G _ G _ G'); [by apply TyAct |].
    apply (TySeq G _ G _ G'); [exact Hc | by apply TyAct].
  Qed.

  (** A well-typed command stays well typed, and the environment its type says
      it has is the one the state satisfies. *)
  Theorem subject_reduction c s c' s' G G' t :
    tstep Step c s c' s' -> Typed G c G' -> D_env FType s t G ->
    exists G2, Typed G2 c' G' /\ D_env FType s' t G2.
  Proof.
    intros Hst. revert G G'.
    induction Hst as [a s s' Ha | c1 s c1' s' c2 Hst IH | c s | c1 c2 s
                      | c1 c2 s | c s];
      intros G G' Hty Henv.
    - inversion Hty as [| G0 a0 G1 Hact | | |]; subst.
      eexists. split;
        [apply TySkip | exact (Act_sound G a G' s s' t Hact Ha Henv)].
    - inversion Hty as [| | G1 d1 Gm d2 G3 H1 H2 | |]; subst.
      destruct (IH G Gm H1 Henv) as [G2 [Hty2 Henv2]].
      exists G2. split; [exact (TySeq G2 c1' Gm c2 G' Hty2 H2) | exact Henv2].
    - inversion Hty as [| | G1 d1 Gm d2 G3 H1 H2 | |]; subst.
      inversion H1; subst. eexists. split; [exact H2 | exact Henv].
    - inversion Hty as [| | | G0 d1 d2 G1 H1 H2 |]; subst.
      eexists. split; [exact H1 | exact Henv].
    - inversion Hty as [| | | G0 d1 d2 G1 H1 H2 |]; subst.
      eexists. split; [exact H2 | exact Henv].
    - inversion Hty as [| | | | G0 d0 H1]; subst.
      eexists. split; [| exact Henv].
      apply TyIf; [| apply TySkip].
      eapply TySeq; [exact H1 | apply TyWhile; exact H1].
  Qed.

  (** A well-typed pool: every thread's command is typed, and the state
      satisfies each thread's environment. *)
  Definition PoolTyped (P : Pool) (E : TID -> Env) (Ef : TID -> Env)
      (s : LState) : Prop :=
    forall t c, P !! t = Some c ->
      Typed (E t) c (Ef t) /\ D_env FType s t (E t).

  (** Whether that is preserved *pool-wide* is the framing question, and it is
      answered below rather than deferred: [Frames] says what a step must leave
      alone for another thread's environment to survive it, [Frames_D_env]
      proves that list is the right one, and [pool_ok_preserved] puts the two
      together.  The list is read off the denotations, so the proof is a
      transcription; the content is that nothing else in a logical state is
      mentioned by a type. *)

End typing.

Print Assumptions subject_reduction.

(** ** Framing

    Subject reduction is single-threaded: it advances the environment of the
    thread that stepped.  A pool has other threads, and their environments
    mention the same shared state.  So a pool-level preservation theorem needs
    to know what one thread's step may *not* do to another thread's types, and
    that is not a matter of taste --- the denotations say it exactly.

    Reading them off: a type's meaning for a thread [t] mentions [t]'s own stack
    slots, the observations tagged [t], the root observation, [t]'s scope [U],
    the free list, the heap, the lock and the root.  Nothing else.  [Frames] is
    that list.  It is deliberately *not* minimal per type --- a [TUndef]
    reference needs far less --- because a frame condition has to cover the
    environment, which may hold any of the six.

    Two things are worth noticing about the list.  It constrains the heap, the
    lock and the root as wholes, which is what makes the writer's actions
    non-framing and is correct: an unlink really can invalidate another
    writer's path, and that is why the lock exists.  And it constrains the free
    list as a whole rather than at [t]'s nodes, because [D_undef] and
    [D_freeable] quantify over entries the thread does not name. *)

Definition Frames (s s' : LState) (t : TID) : Prop :=
  (forall x, stk (ms s') x t = stk (ms s) x t)
  /\ (forall x, undf s' x t <-> undf s x t)
  /\ (forall o ob, obs_tid ob = Some t -> (obsv s o ob <-> obsv s' o ob))
  /\ (forall o, obsv s o Oroot <-> obsv s' o Oroot)
  /\ (forall o, flist s' o = flist s o)
  /\ hp (ms s') = hp (ms s)
  /\ lk (ms s') = lk (ms s)
  /\ rt (ms s') = rt (ms s).

Lemma Frames_refl s t : Frames s s t.
Proof.
  repeat apply conj; try reflexivity; intros; reflexivity.
Qed.

Lemma Frames_trans s1 s2 s3 t :
  Frames s1 s2 t -> Frames s2 s3 t -> Frames s1 s3 t.
Proof.
  intros (A1 & B1 & C1 & D1 & E1 & F1 & G1 & H1)
         (A2 & B2 & C2 & D2 & E2 & F2 & G2 & H2).
  repeat apply conj.
  - intros x. by rewrite A2, A1.
  - intros x. by rewrite B2, B1.
  - intros o ob Hob. by rewrite (C1 o ob Hob), (C2 o ob Hob).
  - intros o. by rewrite D1, D2.
  - intros o. by rewrite E2, E1.
  - by rewrite F2, F1.
  - by rewrite G2, G1.
  - by rewrite H2, H1.
Qed.

Section framing.
  Variable FType : FName -> FieldKind.

  (** The transcription.  Every conjunct of every denotation is one of the eight
      components, so each case is a rewrite. *)
  Lemma Frames_D_env s s' t G :
    Frames s s' t -> D_env FType s t G -> D_env FType s' t G.
  Proof.
    intros (Hstk & Hundf & Hobs & Hroot & Hfl & Hhp & Hlk & Hrt) Henv x T Hin.
    pose proof (Henv x T Hin) as Hty.
    assert (Hfield : forall o f v, FieldHolds s t o f v -> FieldHolds s' t o f v).
    { intros o f [y |] Hf; simpl in Hf |- *; [| by rewrite Hhp].
      destruct Hf as (oy & Hsy & Hcy & Hoy & Hfy).
      exists oy. rewrite Hstk, Hhp, Hfl.
      repeat apply conj; try assumption.
      by apply (Hobs oy (Oiter t) eq_refl). }
    destruct T; simpl in Hty |- *.
    - destruct Hty as [o (Hs & Ho & Hu & Hf & Hpre & Hpath & Hl & Hfo)].
      exists o. rewrite Hstk, Hhp, Hrt, Hlk, Hfl.
      repeat apply conj; try assumption.
      + by apply (Hobs o (Oiter t) eq_refl).
      + intros Hc. by apply Hu, Hundf.
      + intros f v Hv. exact (Hfield o f v (Hf f v Hv)).
      + intros rho1 rho2 Happ. destruct (Hpre rho1 rho2 Happ) as [o' [Hp Ho']].
        exists o'. split; [exact Hp |].
        by apply (Hobs o' (Oiter t) eq_refl).
    - destruct Hty as [o (Hs & Ho & Hu & Hfo & Hf & Hnull)].
      exists o. rewrite Hstk, Hhp, Hfl.
      repeat apply conj; try assumption.
      + by apply (Hobs o (Ofresh t) eq_refl).
      + intros Hc. by apply Hu, Hundf.
      + intros f v Hv. exact (Hfield o f v (Hf f v Hv)).
    - destruct Hty as [o (Hs & Ho & Hl & Hu)].
      exists o. rewrite Hstk, Hlk. repeat apply conj; try assumption.
      + by apply (Hobs o (Ounlk t) eq_refl).
      + intros Hc. by apply Hu, Hundf.
    - destruct Hty as [o (Hs & Ho & Hl & Hu & Hfo)].
      exists o. rewrite Hstk, Hlk, Hfl. repeat apply conj; try assumption.
      + by apply (Hobs o (Ofree t) eq_refl).
      + intros Hc. by apply Hu, Hundf.
    - destruct Hty as [Hu Hfo]. split; [by apply Hundf |].
      intros o Ho. rewrite Hstk in Ho. rewrite Hfl. exact (Hfo o Ho).
    - destruct Hty as [Hs Ho]. split.
      + rewrite Hstk, Hrt. exact Hs.
      + rewrite Hrt. by apply Hroot.
  Qed.

End framing.

Print Assumptions Frames_D_env.

(** ** The pool, typed

    The step relation is now indexed by the thread performing it, which the
    earlier sections did not need and this one does: soundness is about the
    stepping thread's environment, framing is about everybody else's, and
    saying so needs the two to be distinguishable.

    Both hypotheses have the same standing as [Step_lstep] and [Act_sound]
    before them --- properties of what the fifteen actions do, discharged where
    the actions are defined.  [Act_frames] is the per-action framing obligation,
    and it is [Triples.v]'s [EnvOK_cell], [EnvOK_obs], [EnvOK_stack],
    [EnvOK_fl], [EnvOK_scope], [EnvOK_free] and [EnvOK_syncstop] --- those
    lemmas are exactly the components of [Frames], proved one action at a
    time. *)

Section pool.
  Variable FType : FName -> FieldKind.
  Variable Step : TID -> act -> LState -> LState -> Prop.
  Variable ActTyped : Env -> act -> Env -> Prop.

  Hypothesis Step_lstep : forall t a s s', Step t a s s' -> lstep FType s s'.
  Hypothesis Act_sound : forall G a G' s s' t,
    ActTyped G a G' -> Step t a s s' -> D_env FType s t G -> D_env FType s' t G'.
  Hypothesis Act_frames : forall t a s s' t',
    Step t a s s' -> t' <> t -> Frames s s' t'.

  (** An interleaving in which each thread's actions are its own. *)
  Inductive pool_step : Conf -> Conf -> Prop :=
  | PS (t : TID) (P : Pool) (s : LState) (c c' : cmd) (s' : LState) :
      P !! t = Some c -> tstep (Step t) c s c' s' ->
      pool_step (P, s) (<[t := c']> P, s').

  (** A thread's step frames every other thread.  The control constructs do not
      touch the state at all, so only the action case has content. *)
  Lemma tstep_frames t c s c' s' t' :
    tstep (Step t) c s c' s' -> t' <> t -> Frames s s' t'.
  Proof.
    induction 1 as [a s0 s0' Ha | | | | | ]; intros Hne;
      try apply Frames_refl.
    - exact (Act_frames t a s0 s0' t' Ha Hne).
    - by apply IHtstep.
  Qed.

  (** Subject reduction for a named thread.  The sectioned version above
      quantifies its soundness hypothesis over all threads, which is more than
      a thread-indexed [Step] supplies; the induction is the same. *)
  Lemma tstep_typed t c s c' s' G G' :
    tstep (Step t) c s c' s' -> Typed ActTyped G c G' -> D_env FType s t G ->
    exists G2, Typed ActTyped G2 c' G' /\ D_env FType s' t G2.
  Proof.
    intros Hst. revert G G'.
    induction Hst as [a s0 s0' Ha | c1 s0 c1' s0' c2 Hst IH | c0 s0 | c1 c2 s0
                      | c1 c2 s0 | c0 s0];
      intros G G' Hty Henv.
    - inversion Hty as [| G0 a0 G1 Hact | | |]; subst.
      eexists. split;
        [apply TySkip | exact (Act_sound G a G' s0 s0' t Hact Ha Henv)].
    - inversion Hty as [| | G1 d1 Gm d2 G3 H1 H2 | |]; subst.
      destruct (IH G Gm H1 Henv) as [G2 [Hty2 Henv2]].
      exists G2. split; [exact (TySeq ActTyped G2 c1' Gm c2 G' Hty2 H2) | exact Henv2].
    - inversion Hty as [| | G1 d1 Gm d2 G3 H1 H2 | |]; subst.
      inversion H1; subst. eexists. split; [exact H2 | exact Henv].
    - inversion Hty as [| | | G0 d1 d2 G1 H1 H2 |]; subst.
      eexists. split; [exact H1 | exact Henv].
    - inversion Hty as [| | | G0 d1 d2 G1 H1 H2 |]; subst.
      eexists. split; [exact H2 | exact Henv].
    - inversion Hty as [| | | | G0 d0 H1]; subst.
      eexists. split; [| exact Henv].
      apply TyIf; [| apply TySkip].
      eapply TySeq; [exact H1 | apply TyWhile; exact H1].
  Qed.

  (** Every thread's command is typed from its current environment to the final
      one it was typed to reach, and the state satisfies every thread's current
      environment.  The final environments are shared across the step: a thread
      that steps does not change where it is going, and a thread that does not
      step does not change at all. *)
  Definition PoolOK (P : Pool) (E Ef : TID -> Env) (s : LState) : Prop :=
    forall t c, P !! t = Some c ->
      Typed ActTyped (E t) c (Ef t) /\ D_env FType s t (E t).

  Theorem pool_ok_preserved P E Ef s P' s' :
    pool_step (P, s) (P', s') -> PoolOK P E Ef s ->
    exists E', PoolOK P' E' Ef s'.
  Proof.
    intros Hst Hok.
    inversion Hst as [t0 P0 s0 c c' s0' Hlk Ht Heq1 Heq2]; subst.
    destruct (Hok t0 c Hlk) as [Hty Henv].
    destruct (tstep_typed t0 c s c' s' (E t0) (Ef t0) Ht Hty Henv)
      as [G2 [Hty2 Henv2]].
    exists (fun t => if Nat.eq_dec t t0 then G2 else E t).
    intros t d Hd. destruct (Nat.eq_dec t t0) as [-> | Hne].
    - rewrite (lookup_insert_eq P t0 c') in Hd. injection Hd as <-. by split.
    - rewrite (lookup_insert_ne P t0 t c') in Hd;
        [| exact (fun Hc => Hne (eq_sym Hc))].
      destruct (Hok t d Hd) as [Hty' Henv'].
      split; [exact Hty' |].
      exact (Frames_D_env FType s s' t (E t)
               (tstep_frames t0 c s c' s' t Ht Hne) Henv').
  Qed.

  (** ...and over a whole run.  This is the statement [PoolTyped] was a
      placeholder for: from a typed pool, every reachable configuration is a
      typed pool, with every thread still heading for the same final
      environment. *)
  Theorem pool_run_ok cf cf' E Ef :
    rtc pool_step cf cf' -> PoolOK (fst cf) E Ef (snd cf) ->
    exists E', PoolOK (fst cf') E' Ef (snd cf').
  Proof.
    intros Hrun. revert E. induction Hrun as [| a b d Hab _ IH]; intros E Hok.
    - by exists E.
    - destruct a as [Pa sa], b as [Pb sb].
      destruct (pool_ok_preserved Pa E Ef sa Pb sb Hab Hok) as [E1 Hok1].
      exact (IH E1 Hok1).
  Qed.

  (** And safety, for the same interleaving: every thread's step is an [lstep],
      so [WellFormed] holds throughout regardless of typing. *)
  Theorem pool_run_preserves cf cf' :
    rtc pool_step cf cf' -> WellFormed FType (snd cf) -> WellFormed FType (snd cf').
  Proof.
    induction 1 as [| a b d Hab _ IH]; intros Hwf; [exact Hwf |].
    apply IH. destruct Hab as [t P s0 c c' s0' Hlk Ht]. cbn in Hwf |- *.
    exact (tstep_preserves FType (Step t) (Step_lstep t) c s0 c' s0' Ht Hwf).
  Qed.

End pool.

Print Assumptions pool_ok_preserved.
Print Assumptions pool_run_ok.
Print Assumptions pool_run_preserves.
