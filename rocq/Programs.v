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

  (** ...which is not preserved as stated, and the reason is worth recording:
      one thread's step can change the shared state, and nothing here says the
      *other* threads' environments survive it.  That is the framing property,
      and it is [Triples.v]'s [EnvOK_cell], [EnvOK_obs] and [EnvOK_stack] --- a
      per-thread reading of exactly the condition a frame must satisfy.  What
      this file can say without them is the single-threaded case, which is
      subject reduction above, and the safety of any interleaving, which needs
      no environment at all. *)

End typing.

Print Assumptions subject_reduction.
