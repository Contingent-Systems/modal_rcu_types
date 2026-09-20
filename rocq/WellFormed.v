(** * WellFormed: the global invariants of the RCU type system.

    Mechanization of chapters/InvariantsRevised.tex, which supersedes the
    invariant figures in Section [sec:memaxioms] of the technical report.

    This is milestone 1 of the Iris development.  The invariants are pure
    propositions, so nothing here needs Iris yet: state components are plain
    functions and sets are predicates.  When the ghost state arrives, [obsv]
    becomes a [gmap loc (gset obs)] and [flist] a [gmap loc (gset TID)], and
    these definitions become the pure side condition of the Iris invariant
    [inv N (exists s, phys s * ghost s * |-WellFormed s-|)].  Keeping them
    dependency-free for now means they can be checked on their own.

    Besides stating the corrected invariants, this file mechanizes the claim
    that seven of the published ones are defective, by proving that the
    originals are vacuous, unsatisfiable, or too weak to support the uses the
    proofs make of them.  See [Section defects] and the four numbered sections
    after it.

    Checked with Rocq 9.0.  No axioms: see [Print Assumptions] at the bottom. *)

From Stdlib Require Import List Arith.
Import ListNotations.

(** ** Basic sorts *)

Definition Loc   := nat.
Definition TID   := nat.
Definition Var   := nat.
Definition FName := nat.

Inductive Val := VLoc (o : Loc) | VNull.

(** Only RCU-typed fields participate in the structure; scalar fields are
    excluded from the reachability and sharing invariants.  The published OW
    constrains only one of its two fields this way, which would permit a
    non-RCU field to alias a live node. *)
Inductive FieldKind := RCUField | ScalarField.

(** ** Observations

    Change C0 of InvariantsRevised.tex: every observation carries the observing
    thread.  The published grammar tags only [iterator], which leaves RITR
    unstatable (it is *about* which threads observe what) and forces WULK to
    write [undef notin O(o)] even though [undef] is not an observation at all --
    undefinedness lives in U.  [Oroot] stays anonymous: it is a property of the
    structure, not of an observer. *)
Inductive obs :=
| Oiter  (t : TID)
| Ounlk  (t : TID)
| Ofresh (t : TID)
| Ofree  (t : TID)
| Oroot.

(** ** States *)

Record MState := {
  stk : Var -> TID -> option Loc;
  hp  : Loc -> FName -> option Val;
  lk  : option TID;              (** [None] = unlocked *)
  rt  : Loc;
  rds : TID -> Prop;             (** R, the active readers *)
  bnd : TID -> Prop              (** B, the bounding threads *)
}.

Record LState := {
  ms    : MState;
  obsv  : Loc -> obs -> Prop;         (** O *)
  undf  : Var -> TID -> Prop;         (** U *)
  thrd  : TID -> Prop;                (** T *)
  flist : Loc -> option (TID -> Prop) (** F, partial *)
}.

(** [h^*] is partial, as declared in Figure [denotingtypeenviroment] but not
    respected by the published invariants: several quantify over all paths as
    though it were total, which makes them false for paths running off the
    structure (change C2). *)
Fixpoint hstar (h : Loc -> FName -> option Val) (o : Loc) (p : list FName)
  : option Loc :=
  match p with
  | []      => Some o
  | f :: p' => match h o f with
               | Some (VLoc o') => hstar h o' p'
               | _              => None
               end
  end.

Definition Edge (s : LState) (o : Loc) (f : FName) (o' : Loc) : Prop :=
  hp (ms s) o f = Some (VLoc o').

Definition InHeap (s : LState) (o : Loc) : Prop :=
  exists f v, hp (ms s) o f = Some v.

Definition Reaches (s : LState) (p : list FName) (o : Loc) : Prop :=
  hstar (hp (ms s)) (rt (ms s)) p = Some o.

(** A node the writer has detached or not yet published: exempt from the
    no-sharing invariant. *)
Definition Detached (s : LState) (o : Loc) : Prop :=
  exists t, obsv s o (Ounlk t) \/ obsv s o (Ofree t) \/ obsv s o (Ofresh t).

Section WellFormedness.

  (** Field kinds are static program information. *)
  Variable FType : FName -> FieldKind.

  (** ** The nineteen invariants *)

  (** 1. OW -- No Sharing.  In-degree at most one for live nodes.  (The
      published caption describes a different property entirely: "none of the
      heap nodes can be observed as undefined".) *)
  Definition OW (s : LState) : Prop :=
    forall o o' f f' x,
      hp (ms s) o  f  = Some (VLoc x) ->
      hp (ms s) o' f' = Some (VLoc x) ->
      FType f = RCUField -> FType f' = RCUField ->
      (o = o' /\ f = f') \/ Detached s o \/ Detached s o'.

  (** 2. RWOW -- Reader/Writer observation coexistence. *)
  Definition RWOW (s : LState) : Prop :=
    forall x t o,
      stk (ms s) x t = Some o -> ~ undf s x t ->
      obsv s o (Oiter t)
      \/ (lk (ms s) = Some t
          /\ (obsv s o (Ounlk t) \/ obsv s o (Ofree t) \/ obsv s o (Ofresh t))).

  (** 3. AWRT -- Alias with root. *)
  Definition AWRT (s : LState) : Prop :=
    forall y t,
      stk (ms s) y t = Some (rt (ms s)) -> ~ undf s y t ->
      obsv s (rt (ms s)) (Oiter t).

  (** 4. IFL -- Iterators in free list. *)
  Definition IFL (s : LState) : Prop :=
    forall t o Tr,
      obsv s o (Oiter t) -> flist s o = Some Tr -> Tr t.

  (** 5. ULKR -- Unlinked reachability, with the hypothesis closed under the
      disjunction (change 5 of InvariantsRevised.tex).  This is the corrected
      invariant, and it is the one WellFormed carries: the published one-step
      form is kept below as [ULKR_orig], where [ULKR_does_not_chain] shows it
      cannot support the reachability property the proofs appeal to.  The
      transitive form is the derived lemma [ULKR_closed_reaches], not a separate
      invariant. *)
  Definition ULKR (s : LState) : Prop :=
    forall o o' f' t,
      (obsv s o (Ounlk t) \/ obsv s o (Ofree t)) -> Edge s o' f' o ->
      obsv s o' (Ounlk t) \/ obsv s o' (Ofree t).

  (** 6. FLR -- Free-list reachability.

      The direction of the inclusion was previously left as a parameter, on the
      grounds that the temporal story argued against the published statement.
      It does not: the published direction is forced.

      [Edge s o' f' o] puts o' above o, and ULKR (child unlinked implies parent
      unlinked) means o' must already be unlinked when o becomes unlinked, so o'
      is unlinked no later than o.  Grace periods cannot overlap -- T-Sync types
      [SyncStart; SyncStop] as one compound statement, and there is a single
      writer -- so only two cases arise.  If o' and o were unlinked in different
      write critical sections, the earlier grace period has completed, o' is
      freeable and F(o') is empty.  If in the same one, both entries were
      populated at the same SyncStart from one snapshot and are equal.  Either
      way F(o') is contained in F(o), which is what the report writes.

      That also disposes of the worry that two entries created at different
      SyncStarts snapshot unrelated thread sets and need not nest: non-overlapping
      grace periods mean two live snapshots are never compared. *)
  Definition FLR (s : LState) : Prop :=
    forall o o' f' Tr,
      flist s o = Some Tr -> Edge s o' f' o ->
      exists Tr', flist s o' = Some Tr' /\ (forall t, Tr' t -> Tr t).

  (** 7. WULK -- Writer unlink.  [iterator] and [unlinked]/[freeable]
      observations of one location are mutually exclusive.  (The published
      caption claims the writer cannot observe a location as unlinked, which is
      both different from the formula and plainly false -- doing so is the whole
      point of the [unlinked] type.) *)
  Definition WULK (s : LState) : Prop :=
    forall lw o t,
      lk (ms s) = Some lw -> obsv s o (Oiter lw) ->
      ~ obsv s o (Ounlk t) /\ ~ obsv s o (Ofree t).

  (** 8. FR -- Fresh unreachable.  Two independent obligations, hence a
      conjunction; the published disjunction is satisfied by its own hypothesis
      (see [FR_orig_admits_writer_local_alias]). *)
  Definition FR (s : LState) : Prop :=
    forall t x o,
      stk (ms s) x t = Some o -> obsv s o (Ofresh t) ->
      (forall o' f', ~ Edge s o' f' o)
      /\ (forall y t', (y, t') <> (x, t) -> stk (ms s) y t' <> Some o).

  (** 9. WFresh -- allocation is the writer's. *)
  Definition WFresh (s : LState) : Prop :=
    forall t x o,
      stk (ms s) x t = Some o -> obsv s o (Ofresh t) -> lk (ms s) = Some t.

  (** 10. FNR -- a fresh node carries no other observation.

      The third conjunct is change 10b, and it is not cosmetic: without it the
      invariant set cannot prove that linking a fresh node preserves ULKR.  See
      [Section fresh_freeable] below, and [link_fresh_ULKR] in [Actions.v] for
      the use. *)
  Definition FNR (s : LState) : Prop :=
    forall o t t',
      obsv s o (Ofresh t) ->
      ~ obsv s o (Oiter t') /\ ~ obsv s o (Ounlk t') /\ ~ obsv s o (Ofree t').

  (** 11. FPI -- a fresh node's fields point at live nodes.  Both [f] and [o']
      are bound at the top (in the original [o'] escapes its existential), and
      the consequent is the writer's observation, not every thread's. *)
  Definition FPI (s : LState) : Prop :=
    forall o f o' t lw,
      obsv s o (Ofresh t) -> Edge s o f o' -> FType f = RCUField ->
      lk (ms s) = Some lw -> obsv s o' (Oiter lw).

  (** 12. WNR -- the writer is not a reader. *)
  Definition WNR (s : LState) : Prop :=
    forall t, lk (ms s) = Some t -> ~ rds (ms s) t.

  (** 13. RITR -- readers make only iterator observations.  Statable only
      because of C0. *)
  Definition RITR (s : LState) : Prop :=
    forall o t,
      rds (ms s) t ->
      ~ obsv s o (Ounlk t) /\ ~ obsv s o (Ofree t) /\ ~ obsv s o (Ofresh t).

  (** 14. RINFL -- free-list entries are bounding threads. *)
  Definition RINFL (s : LState) : Prop :=
    forall o Tr t, flist s o = Some Tr -> Tr t -> bnd (ms s) t.

  (** 15. HD -- heap domain closure, with the source restricted to nodes that
      are not detached (change 7).  The published form constrains every edge,
      which Free breaks: an unlinked node retains a pointer to its old child,
      and freeing that child leaves the pointer dangling.  It dangles harmlessly
      -- the node holding it is itself detached and unreachable -- and OW
      already carries exactly this exemption, so HD not carrying it was an
      oversight.  [HD_orig] below keeps the published form, where
      [HD_not_preserved_by_free] shows a legal Free violating it.

      This is also the invariant whose proof case is empty in four separate
      lemmas of the technical report, and dismissed as trivial in a fifth. *)
  Definition HD (s : LState) : Prop :=
    forall o f o', Edge s o f o' -> ~ Detached s o -> InHeap s o'.

  Definition HD_orig (s : LState) : Prop :=
    forall o f o', Edge s o f o' -> InHeap s o'.

  (** 16. UNQRT -- unique root, split into its two halves. *)
  Definition UNQRT_a (s : LState) : Prop :=
    forall o f, ~ Edge s o f (rt (ms s)).

  Definition UNQRT_b (s : LState) : Prop :=
    forall p o lw,
      lk (ms s) = Some lw -> Reaches s p o ->
      obsv s o (Oiter lw) \/ obsv s o Oroot.

  (** 17. WUNLK -- detaching observations are the writer's.

      New in the revision, and the counterpart of WFresh at the other end of a
      node's life: WFresh says an allocation is the lock holder's, and nothing
      said the same of an unlinking.  It is needed, and needed locally: the ULKR
      case of T-UnlinkH and T-Replace ends at a detached predecessor of the node
      being unlinked, and ULKR's conclusion names a thread, so the case does not
      close without knowing that the predecessor's [unlinked] observation is the
      writer's.  See [unlinked_observations_need_not_be_the_writers] below for a
      state satisfying the other eighteen in which it is not.

      Guarded by the lock, so it says nothing about a state with no writer --
      which is the weakest form that does the job. *)
  Definition WUNLK (s : LState) : Prop :=
    forall o t lw,
      lk (ms s) = Some lw ->
      (obsv s o (Ounlk t) \/ obsv s o (Ofree t)) -> t = lw.

  (** 18. WITR -- iterator observations are the writer's or a reader's.

      The third of a family, and the one that completes it.  Each kind of
      observation constrains who may hold it: WFresh does it for [fresh], WUNLK
      for [unlinked] and [freeable], and this for [iterator].  The published set
      had exactly one of the three.

      It is needed by SyncStart, whose IFL case is the obligation that a thread
      holding an [iterator] on a node about to be put on the free list is one of
      the readers the grace period will wait for.  WULK rules out the writer;
      nothing ruled out a thread that is neither writer nor reader.  See
      [iterators_need_not_be_active] below. *)
  Definition WITR (s : LState) : Prop :=
    forall o t, obsv s o (Oiter t) -> lk (ms s) = Some t \/ rds (ms s) t.

  (** 19. UNQR -- unique reachability: distinct paths reach distinct nodes.
      This is the tree-shape invariant on which every framing side condition in
      T-UnlinkH, T-Replace and T-Insert depends. *)
  Definition UNQR (s : LState) : Prop :=
    forall p p' o, Reaches s p o -> Reaches s p' o -> p = p'.

  (** ** WellFormed *)

  Definition WellFormed (s : LState) : Prop :=
    OW s /\ RWOW s /\ AWRT s /\ IFL s /\ ULKR s /\ FLR s /\ WULK s
    /\ FR s /\ WFresh s /\ FNR s /\ FPI s /\ WNR s /\ RITR s /\ RINFL s
    /\ HD s /\ UNQRT_a s /\ UNQRT_b s /\ WUNLK s /\ WITR s /\ UNQR s.

End WellFormedness.

(** * ULKR does not chain

    A fifth defect, found by attempting the mechanization rather than by reading.

    The technical report's caption for ULKR claims the reachability property --
    "all heap locations from which you can reach the unlinked one are also
    unlinked or in the free list" -- and the Unlink proof appeals to it in that
    form, arguing that a predecessor observed as [iterator] would conflict with
    UNQR.  But the formula is one step, with hypothesis [unlinked] and conclusion
    [unlinked \/ freeable].  The conclusion is weaker than the hypothesis, so the
    induction does not close: at a [freeable] predecessor there is no invariant
    left to apply.

    The repair is to close the hypothesis under the disjunction. *)

(** The published one-step form, retained only to exhibit the defect.  It is
    [ULKR] with the hypothesis *not* closed under the disjunction. *)
Definition ULKR_orig (s : LState) : Prop :=
  forall o o' f' t,
    obsv s o (Ounlk t) -> Edge s o' f' o ->
    obsv s o' (Ounlk t) \/ obsv s o' (Ofree t).

(** [ULKR_closed] is now just [ULKR]; kept as a name because the write-up cites
    [ULKR_closed_reaches]. *)
Definition ULKR_closed (s : LState) : Prop := ULKR s.

(** The reachability form, which is what the proofs actually use. *)
Definition ULKR_reach (s : LState) : Prop :=
  forall p o o' t,
    obsv s o' (Ounlk t) -> hstar (hp (ms s)) o p = Some o' -> p <> [] ->
    obsv s o (Ounlk t) \/ obsv s o (Ofree t).

(** Closed under the disjunction, it chains. *)
Lemma ULKR_closed_reaches : forall s, ULKR_closed s -> ULKR_reach s.
Proof.
  intros s HC p. induction p as [|f p IH]; intros o o' t Hunl Hreach Hne.
  - exfalso. apply Hne. reflexivity.
  - simpl in Hreach.
    destruct (hp (ms s) o f) as [[o1|]|] eqn:Hf; try discriminate.
    destruct p as [|g p'].
    + simpl in Hreach. injection Hreach as Heq. subst o1.
      apply (HC o' o f t (or_introl Hunl)). unfold Edge. exact Hf.
    + assert (Hne' : g :: p' <> []) by discriminate.
      apply (HC o1 o f t (IH o1 o' t Hunl Hreach Hne')). unfold Edge. exact Hf.
Qed.

(** * T-Replace and T-UnlinkH do not preserve FPI

    A sixth defect, again found by attempting a proof case rather than by
    reading -- the report calls this case "trivial" in both lemmas.

    This one is not confined to FPI.  The denotation of [rcuFresh N] itself
    requires every target in [codom(N)] to be observed as [iterator]; so if a
    fresh variable in Gamma points at the node being unlinked, the post-state
    fails the denotation of its *own* type environment, and the Axiom Soundness
    lemma for the action is false as stated.  FPI is simply where it shows up
    first.  The consequence it guards against is concrete: linking such a fresh
    node in afterwards would splice a node already scheduled for reclamation
    back into the structure.

    FPI says a fresh node's RCU fields point at locations the writer observes as
    [iterator].  T-Replace unlinks [o], which costs [o] its [iterator]
    observation (WULK makes [iterator] and [unlinked] exclusive).  So if any
    *fresh* node has a field pointing at [o], FPI held before the write and
    fails after it.

    Nothing in the published rules ruled that out.  The aliasing premise
    quantifies over
    [x:rcuItr rho N3([f1 |-> y])] and concludes [y <> o]; a variable typed
    [rcuFresh] is not an [rcuItr] and so is not covered.  Nor does the shape of
    the environment help: the denotation of a type environment is the
    *intersection* of the individual variables' denotations, not a separating
    conjunction, so two variables may denote overlapping structure.  And the
    state is reachable -- T-WriteFH sets a fresh node's field to an [rcuItr]
    target, which is exactly what [o] is until the replacement happens.

    Both rules that produce an [unlinked] observation were affected, and both
    now carry the repair: an extra premise excluding fresh predecessors of the
    node being unlinked ([y <> o] for T-Replace, [m' <> z] for T-UnlinkH),
    alongside the aliasing premise that covers only [rcuItr] variables.
    T-Insert needs nothing: it unlinks nothing, so no observation is lost.

    The state below is what those premises exclude, kept as the witness that
    they are not redundant.  The BST deletion still type checks under them: the
    fresh node it builds points at the children of the node being replaced,
    never at that node.

    Below, node 4 is fresh with an RCU edge to node 1; the write replaces 1 with
    2 under the root, unlinking 1. *)

Definition fpi_before : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o f => if Nat.eqb f 0
                                then (if Nat.eqb o 4 then Some (VLoc 1)
                                      else if Nat.eqb o 0 then Some (VLoc 1)
                                      else if Nat.eqb o 1 then Some VNull
                                      else None)
                                else None;
              lk  := Some 9;
              rt  := 0;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Oiter 9)
                          \/ (o = 1 /\ ob = Oiter 9)
                          \/ (o = 4 /\ ob = Ofresh 9);
     undf  := fun _ _ => False;
     thrd  := fun t => t = 9;
     flist := fun _ => None |}.

Definition fpi_after : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o f => if Nat.eqb f 0
                                then (if Nat.eqb o 4 then Some (VLoc 1)
                                      else if Nat.eqb o 0 then Some (VLoc 2)
                                      else if Nat.eqb o 1 then Some VNull
                                      else if Nat.eqb o 2 then Some VNull
                                      else None)
                                else None;
              lk  := Some 9;
              rt  := 0;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Oiter 9)
                          \/ (o = 1 /\ ob = Ounlk 9)
                          \/ (o = 2 /\ ob = Oiter 9)
                          \/ (o = 4 /\ ob = Ofresh 9);
     undf  := fun _ _ => False;
     thrd  := fun t => t = 9;
     flist := fun _ => None |}.

Lemma FPI_not_preserved_by_replace :
  FPI (fun _ => RCUField) fpi_before
  /\ ~ FPI (fun _ => RCUField) fpi_after.
Proof.
  split.
  - intros o f o' t lw Hfresh Hedge _ Hlk.
    simpl in Hlk. injection Hlk as <-.
    simpl in Hfresh.
    (* the only fresh node is 4, and its only edge goes to 1 *)
    destruct Hfresh as [[-> Heq] | [[-> Heq] | [-> Heq]]]; try discriminate.
    unfold Edge in Hedge. simpl in Hedge.
    destruct f as [|f0]; simpl in Hedge; [| discriminate].
    injection Hedge as <-.
    simpl. right; left. split; reflexivity.
  - intros HF.
    assert (Hfresh : obsv fpi_after 4 (Ofresh 9))
      by (simpl; right; right; right; split; reflexivity).
    assert (Hedge : Edge fpi_after 4 0 1) by reflexivity.
    destruct (HF 4 0 1 9 9 Hfresh Hedge eq_refl eq_refl)
      as [[H _] | [[_ H] | [[H _] | [H _]]]]; try discriminate.
Qed.

(** * FLR chains

    With the direction settled, FLR gives the free-list analogue of
    [ULKR_reach]: anything that reaches a free-list entry is itself a free-list
    entry, with a set contained in it.  Unlike ULKR the one-step form already
    chains -- its hypothesis and conclusion are the same predicate -- so no
    repair is needed, only the induction.

    This is the half of Section 6.4's claim that belongs to FLR: together with
    [ULKR_closed_reaches] it is what keeps a node awaiting reclamation
    unreachable from the root, since the root is on neither the free list nor
    the unlinked set. *)

Definition FLR_reach (s : LState) : Prop :=
  forall p a b Tb,
    flist s b = Some Tb -> hstar (hp (ms s)) a p = Some b -> p <> [] ->
    exists Ta, flist s a = Some Ta /\ (forall t, Ta t -> Tb t).

Lemma FLR_chains : forall s, FLR s -> FLR_reach s.
Proof.
  intros s HF p. induction p as [|f p IH]; intros a b Tb Hb Hreach Hne.
  - exfalso. apply Hne. reflexivity.
  - simpl in Hreach.
    destruct (hp (ms s) a f) as [[a1|]|] eqn:Hf; try discriminate.
    destruct p as [|g p'].
    + simpl in Hreach. injection Hreach as Heq. subst a1.
      destruct (HF b a f Tb Hb Hf) as [Ta [Hta Hsub]].
      exists Ta. split; [exact Hta | exact Hsub].
    + assert (Hne' : g :: p' <> []) by discriminate.
      destruct (IH a1 b Tb Hb Hreach Hne') as [Ta1 [Hta1 Hsub1]].
      destruct (HF a1 a f Ta1 Hta1 Hf) as [Ta [Hta Hsub]].
      exists Ta. split; [exact Hta | intros t Ht; exact (Hsub1 t (Hsub t Ht))].
Qed.

(** As published it does not.  Witness: a chain [2 -> 1 -> 0] in which 0 is
    unlinked, 1 is freeable -- which ULKR permits, since it offers exactly that
    disjunct -- and 2 is an ordinary iterator.  ULKR holds, because 1 is the only
    predecessor of the only unlinked node and 1 is freeable; nothing constrains
    2.  Yet 2 reaches the unlinked 0. *)
Definition chain : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o f => if Nat.eqb f 0
                                then (if Nat.eqb o 2 then Some (VLoc 1)
                                      else if Nat.eqb o 1 then Some (VLoc 0)
                                      else None)
                                else None;
              lk  := Some 9;
              rt  := 3;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Ounlk 0)
                          \/ (o = 1 /\ ob = Ofree 0)
                          \/ (o = 2 /\ ob = Oiter 0);
     undf  := fun _ _ => False;
     thrd  := fun t => t = 9;
     flist := fun _ => None |}.

Lemma ULKR_does_not_chain : ULKR_orig chain /\ ~ ULKR_reach chain.
Proof.
  split.
  - intros o o' f' t Hunl Hedge.
    (* the only unlinked node is 0, whose only predecessor is 1, which is freeable *)
    simpl in Hunl.
    destruct Hunl as [[-> Heq] | [[-> Heq] | [-> Heq]]]; try discriminate.
    injection Heq as ->.
    unfold Edge in Hedge. simpl in Hedge.
    destruct (Nat.eqb f' 0) eqn:Ef; [| discriminate].
    destruct (Nat.eqb o' 2) eqn:E2; [discriminate |].
    destruct (Nat.eqb o' 1) eqn:E1; [| discriminate].
    apply Nat.eqb_eq in E1. subst o'. right. simpl. right. left. split; reflexivity.
  - intros HR.
    assert (Hunl : obsv chain 0 (Ounlk 0)) by (simpl; left; split; reflexivity).
    assert (Hreach : hstar (hp (ms chain)) 2 [0; 0] = Some 0) by reflexivity.
    assert (Hne : [0; 0] <> ([] : list FName)) by discriminate.
    destruct (HR _ _ _ _ Hunl Hreach Hne) as [H | H]; simpl in H;
      destruct H as [[H1 H2] | [[H1 H2] | [H1 H2]]]; discriminate.
Qed.

(** * Defects in the published invariants
    <<
    Each lemma below is a mechanized version of a claim in
    InvariantsRevised.tex.  They are the concrete argument for mechanizing:
    all four survived publication and a soundness proof.
    >> *)

Section Defects.

  Variable FType : FName -> FieldKind.

  (** ** UNQR is vacuous

      Published (Figure [upath]): [h*(rt,p) <> h*(rt,p') -> p <> p'].  This is a
      theorem of equality -- if [p = p'] the two applications are equal by
      congruence -- so it holds of every function in every state, and constrains
      nothing at all. *)
  Definition UNQR_orig (s : LState) : Prop :=
    forall p p',
      hstar (hp (ms s)) (rt (ms s)) p <> hstar (hp (ms s)) (rt (ms s)) p' ->
      p <> p'.

  Lemma UNQR_orig_vacuous : forall s, UNQR_orig s.
  Proof. intros s p p' Hne Heq. subst. apply Hne. reflexivity. Qed.

  (** It is not merely weak: it is satisfied by states that are not trees, which
      is precisely what it was introduced to exclude.  Here every location's
      field 0 points to location 1, so [p = [0]] and [p' = [0;0]] both reach 1. *)
  Definition cyclic : LState :=
    {| ms := {| stk := fun _ _ => None;
                hp  := fun _ f => if Nat.eqb f 0 then Some (VLoc 1) else None;
                lk  := Some 0;
                rt  := 0;
                rds := fun _ => False;
                bnd := fun _ => False |};
       obsv  := fun _ _ => False;
       undf  := fun _ _ => False;
       thrd  := fun t => t = 0;
       flist := fun _ => None |}.

  Lemma UNQR_orig_admits_non_trees :
    UNQR_orig cyclic /\ ~ UNQR cyclic.
  Proof.
    split.
    - apply UNQR_orig_vacuous.
    - intros HU.
      assert (Reaches cyclic [0] 1) as H1 by reflexivity.
      assert (Reaches cyclic [0; 0] 1) as H2 by reflexivity.
      specialize (HU _ _ _ H1 H2). discriminate.
  Qed.

  (** ** RITR is unsatisfiable in the states it is needed for

      Published (Figure [riter]): [forall t in R, o. iterator t in O(o)] -- every
      reader observes *every* location as an iterator.  Combined with FNR, any
      state that has a reader and a fresh node is contradictory; and the writer
      allocates a fresh node in every [add]. *)
  Definition RITR_orig (s : LState) : Prop :=
    forall t o, rds (ms s) t -> obsv s o (Oiter t).

  Lemma RITR_orig_contradicts_fresh :
    forall s t o tf,
      RITR_orig s -> FNR s -> rds (ms s) t -> obsv s o (Ofresh tf) -> False.
  Proof.
    intros s t o tf Horig Hfnr Hrd Hfresh.
    destruct (Hfnr o tf t Hfresh) as [Hno _].
    exact (Hno (Horig t o Hrd)).
  Qed.

  (** ** FR does not rule out a second writer-local alias

      Published (Figure [freach]): a disjunction whose second disjunct,
      [s(y,tid) <> o], contradicts the hypothesis [s(x,tid) = o] when [y := x].
      Below, the writer holds the same fresh node in two distinct variables --
      exactly what T-Replace and T-Insert cite FR to exclude -- and the
      published version is satisfied anyway. *)
  Definition FR_orig (s : LState) : Prop :=
    forall t x o,
      stk (ms s) x t = Some o -> obsv s o (Ofresh t) ->
      forall y o' f' t',
        ~ Edge s o' f' o
        \/ stk (ms s) y t <> Some o
        \/ (t' <> t -> stk (ms s) y t' <> Some o).

  Definition two_aliases : LState :=
    {| ms := {| stk := fun x t => if andb (Nat.ltb x 2) (Nat.eqb t 0)
                                  then Some 5 else None;
                hp  := fun _ _ => None;
                lk  := Some 0;
                rt  := 0;
                rds := fun _ => False;
                bnd := fun _ => False |};
       obsv  := fun o ob => o = 5 /\ ob = Ofresh 0;
       undf  := fun _ _ => False;
       thrd  := fun t => t = 0;
       flist := fun _ => None |}.

  Lemma FR_orig_admits_writer_local_alias :
    FR_orig two_aliases /\ ~ FR two_aliases.
  Proof.
    split.
    - intros t x o _ _ y o' f' t'. left. unfold Edge. simpl. discriminate.
    - intros HFR.
      destruct (HFR 0 0 5 eq_refl (conj eq_refl eq_refl)) as [_ Halias].
      (* variable 1 of the same thread also holds the fresh node *)
      apply (Halias 1 0).
      + intros H. congruence.
      + reflexivity.
  Qed.

  (** ** FPI's consequent escapes its binder

      Published (Figure [fsinglefield]): [(fresh in O(o) /\ exists f o'. h(o,f) =
      o') -> forall tid. iterator tid in O(o')].  [o'] is bound by an
      existential inside the antecedent, so in the consequent it is free, i.e.
      universally quantified at the top.  Read literally, any fresh node with a
      field set forces *every* location to be observed as an iterator by *every*
      thread -- including the fresh node itself, which FNR forbids. *)
  Definition FPI_orig (s : LState) : Prop :=
    forall o o' t,
      obsv s o (Ofresh t) ->
      (exists f x, Edge s o f x) ->
      forall t', obsv s o' (Oiter t').

  Lemma FPI_orig_contradicts_FNR :
    forall s o t f x,
      FPI_orig s -> FNR s -> obsv s o (Ofresh t) -> Edge s o f x -> False.
  Proof.
    intros s o t f x Horig Hfnr Hfresh Hedge.
    destruct (Hfnr o t t Hfresh) as [Hno _].
    apply Hno. apply (Horig o o t Hfresh). exists f, x. exact Hedge.
  Qed.

End Defects.

(** * Satisfiability

    A guard against the failure mode RITR exhibits: an invariant set can be
    "corrected" into something no state satisfies, and every proof over it then
    goes through vacuously.  We exhibit a model -- the initial state of any RCU
    program, a root with null fields and the writer holding the lock -- and
    check it satisfies all nineteen, for any field typing and any reading of
    the open FLR direction. *)

Definition initial : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o _ => if Nat.eqb o 0 then Some VNull else None;
              lk  := Some 0;
              rt  := 0;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => o = 0 /\ ob = Oroot;
     undf  := fun _ _ => False;
     thrd  := fun t => t = 0;
     flist := fun _ => None |}.

Lemma initial_no_edges : forall o f o', ~ Edge initial o f o'.
Proof.
  intros o f o'. unfold Edge, initial. simpl.
  destruct (Nat.eqb o 0); discriminate.
Qed.

Lemma initial_reaches_only_root : forall p o, Reaches initial p o -> p = [] /\ o = 0.
Proof.
  intros [|f p] o H; unfold Reaches in H; simpl in H.
  - injection H as <-. split; reflexivity.
  - discriminate.
Qed.

(** One lemma per invariant, so a failure names the invariant that failed. *)

Lemma initial_OW : forall FType, OW FType initial.
Proof.
  intros FType o o' f f' x H1 H2 _ _. exfalso.
  simpl in H1. destruct (Nat.eqb o 0); discriminate H1.
Qed.

Lemma initial_RWOW : RWOW initial.
Proof. intros x t o H. simpl in H. discriminate H. Qed.

Lemma initial_AWRT : AWRT initial.
Proof. intros y t H. simpl in H. discriminate H. Qed.

Lemma initial_IFL : IFL initial.
Proof. intros t o Tr H1 H2. simpl in H2. discriminate H2. Qed.

Lemma initial_ULKR : ULKR initial.
Proof.
  intros o o' f' t H1 H2. simpl in H1.
  destruct H1 as [[_ H] | [_ H]]; discriminate H.
Qed.

Lemma initial_FLR : FLR initial.
Proof. intros o o' f' Tr H1 H2. simpl in H1. discriminate H1. Qed.

Lemma initial_WULK : WULK initial.
Proof. intros lw o t H1 H2. simpl in H2. destruct H2 as [_ H]. discriminate H. Qed.

Lemma initial_FR : FR initial.
Proof. intros t x o H1 H2. simpl in H1. discriminate H1. Qed.

Lemma initial_WFresh : WFresh initial.
Proof. intros t x o H1 H2. simpl in H1. discriminate H1. Qed.

Lemma initial_FNR : FNR initial.
Proof. intros o t t' H. simpl in H. destruct H as [_ H]. discriminate H. Qed.

Lemma initial_FPI : forall FType, FPI FType initial.
Proof.
  intros FType o f o' t lw H1 H2 H3 H4. exfalso.
  exact (initial_no_edges _ _ _ H2).
Qed.

Lemma initial_WNR : WNR initial.
Proof. intros t H1 H2. exact H2. Qed.

Lemma initial_RITR : RITR initial.
Proof. intros o t H. destruct H. Qed.

Lemma initial_RINFL : RINFL initial.
Proof. intros o Tr t H1 H2. simpl in H1. discriminate H1. Qed.

Lemma initial_HD : HD initial.
Proof. intros o f o' H _. exfalso. exact (initial_no_edges _ _ _ H). Qed.

Lemma initial_UNQRT_a : UNQRT_a initial.
Proof. intros o f. apply initial_no_edges. Qed.

Lemma initial_UNQRT_b : UNQRT_b initial.
Proof.
  intros p o lw H1 H2.
  destruct (initial_reaches_only_root _ _ H2) as [_ ->]. right.
  simpl. split; reflexivity.
Qed.

Lemma initial_WUNLK : WUNLK initial.
Proof.
  intros o t lw _ [H | H]; simpl in H; destruct H as [_ H]; discriminate H.
Qed.

Lemma initial_WITR : WITR initial.
Proof. intros o t H. simpl in H. destruct H as [_ H]. discriminate H. Qed.

Lemma initial_UNQR : UNQR initial.
Proof.
  intros p p' o H1 H2.
  destruct (initial_reaches_only_root _ _ H1) as [-> _].
  destruct (initial_reaches_only_root _ _ H2) as [-> _]. reflexivity.
Qed.

Theorem WellFormed_satisfiable :
  forall (FType : FName -> FieldKind), WellFormed FType initial.
Proof.
  intros FType. unfold WellFormed.
  (* [repeat split] is too eager: it descends through binders and splits the
     conjunction inside [obsv initial] itself.  [apply conj] matches only a
     literal [and] head, so it decomposes exactly the nineteen conjuncts. *)
  repeat apply conj;
    first [ apply initial_OW      | apply initial_RWOW  | apply initial_AWRT
          | apply initial_IFL     | apply initial_ULKR  | apply initial_FLR
          | apply initial_WULK    | apply initial_FR    | apply initial_WFresh
          | apply initial_FNR     | apply initial_FPI   | apply initial_WNR
          | apply initial_RITR    | apply initial_RINFL | apply initial_HD
          | apply initial_UNQRT_a | apply initial_UNQRT_b
          | apply initial_WUNLK    | apply initial_WITR
          | apply initial_UNQR ].
Qed.

(** The corrected set is satisfiable; the published RITR makes it not, in any
    state with a reader and a fresh node -- which every [add] produces. *)
Corollary corrected_but_not_published :
  (exists s FType, WellFormed FType s)
  /\ (forall s t o tf,
        RITR_orig s -> FNR s -> rds (ms s) t -> obsv s o (Ofresh tf) -> False).
Proof.
  split.
  - exists initial, (fun _ => RCUField).
    apply WellFormed_satisfiable.
  - intros s t o tf. apply (RITR_orig_contradicts_fresh s t o tf).
Qed.

Print Assumptions WellFormed_satisfiable.
Print Assumptions corrected_but_not_published.
Print Assumptions ULKR_closed_reaches.
Print Assumptions FLR_chains.
Print Assumptions FPI_not_preserved_by_replace.

(** * HD is too strong: Free breaks it

    A seventh defect, found the same way as the fifth and sixth -- by attempting
    a proof case, here the HD case of Free.

    HD as published constrains every edge in the heap.  But T-UnlinkH leaves the
    unlinked node still pointing at its old child through [f2] (the rule nulls
    its *other* fields, not that one), and Free sets only the freed node's own
    fields to undefined, not its predecessors'.  Nothing orders the reclamation
    of two unlinked nodes.  So a well-typed section may free a node while
    another node, unlinked and awaiting its own reclamation, still points at it,
    and HD fails in that state.

    It fails harmlessly: the dangling pointer sits in a node that is itself
    detached and unreachable, so nothing can follow it.  That is exactly the
    exemption OW already carries -- its conclusion is excused when either
    endpoint is [Detached] -- and HD should carry the same one.  That OW has it
    and HD does not looks like an oversight rather than a decision. *)

(** Node 0 is unlinked and still points at node 1, which is freeable.  Freeing
    1 leaves 0's pointer dangling. *)
Definition hd_before : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o f => if Nat.eqb f 0
                                then (if Nat.eqb o 0 then Some (VLoc 1)
                                      else if Nat.eqb o 1 then Some VNull
                                      else None)
                                else None;
              lk  := Some 9; rt := 2;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Ounlk 9) \/ (o = 1 /\ ob = Ofree 9);
     undf  := fun _ _ => False;
     thrd  := fun t => t = 9;
     flist := fun _ => None |}.

Definition hd_after : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o f => if Nat.eqb f 0
                                then (if Nat.eqb o 0 then Some (VLoc 1) else None)
                                else None;
              lk  := Some 9; rt := 2;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Ounlk 9) \/ (o = 1 /\ ob = Ofree 9);
     undf  := fun _ _ => False;
     thrd  := fun t => t = 9;
     flist := fun _ => None |}.

Lemma HD_not_preserved_by_free :
  HD_orig hd_before /\ ~ HD_orig hd_after /\ HD hd_after.
Proof.
  split; [| split].
  - (* before the free, both nodes are allocated *)
    intros o f o' Hedge. unfold Edge in Hedge. simpl in Hedge.
    destruct f; simpl in Hedge; [| discriminate].
    destruct o as [|o1]; simpl in Hedge.
    + injection Hedge as <-. exists 0, VNull. reflexivity.
    + destruct o1; simpl in Hedge; discriminate.
  - (* after it, node 0's pointer dangles *)
    intros HD.
    assert (Hedge : Edge hd_after 0 0 1) by reflexivity.
    destruct (HD 0 0 1 Hedge) as [f [v Hv]].
    simpl in Hv. destruct f; simpl in Hv; discriminate.
  - (* but the dangling pointer sits in a detached node *)
    intros o f o' Hedge Hlive. exfalso. apply Hlive.
    unfold Edge in Hedge. simpl in Hedge.
    destruct f; simpl in Hedge; [| discriminate].
    destruct o as [|o1]; simpl in Hedge.
    + exists 9. left. simpl. left. split; reflexivity.
    + discriminate.
Qed.

Print Assumptions HD_not_preserved_by_free.

(** * FNR does not exclude a freeable fresh node

    An eighth defect, found the same way as the fifth, sixth and seventh -- by
    attempting a proof case, here the ULKR case of the two rules that link a
    fresh node.

    The obligation is ULKR under the two rules that link a fresh node,
    T-Replace and T-Insert.  Both write [op.f := on] with [on] typed
    [rcuFresh]; the write creates the edge [op -> on], and ULKR asks that if
    [on] is unlinked or freeable then [op] is too.  The writer's [op] is an
    [rcuItr], so WULK denies it both observations -- which means the obligation
    can only be discharged by denying both to [on].

    FNR denies [on] the first.  Nothing in the published set denies it the
    second: [freeable] appears in Detached, RWOW, ULKR, WULK and RITR, and in
    none of them as a consequent that a [fresh] node could trigger.  So the
    proof does not close, and the missing step is an invariant rather than a
    side condition -- which is why the repair belongs in FNR.

    That the *reachable* states have no such node is beside the point, and is
    in fact the reason the omission survived.  A node acquires [freeable] only
    at SyncStop, from [unlinked], which FNR's second conjunct already denies to
    a fresh node; so the property holds inductively over whole executions.  But
    an invariant set earns its keep by making each action lemma provable from
    the invariants *alone*, and this one is not.  Adding the conjunct restores
    that, and costs nothing: [sync_stop_preserves_FNR] in [Actions.v] discharges
    it from the second conjunct, by exactly the argument just given.

    The witness below satisfies the other eighteen invariants and the published
    FNR, and has a node that is both fresh and freeable. *)

(** The published form: FNR without the third conjunct. *)
Definition FNR_pub (s : LState) : Prop :=
  forall o t t',
    obsv s o (Ofresh t) -> ~ obsv s o (Oiter t') /\ ~ obsv s o (Ounlk t').

Lemma FNR_stronger : forall s, FNR s -> FNR_pub s.
Proof.
  intros s H o t t' Hf. destruct (H o t t' Hf) as [H1 [H2 _]]. split; assumption.
Qed.

(** Two allocated nodes, no edges at all, the writer holding the lock and one
    variable pointing at node 1, which is observed both [fresh] and [freeable].
    Every invariant that mentions the heap is vacuous here, which is the point:
    the defect is about observations, so the witness carries no structure that
    could be blamed for it. *)
Definition fresh_freeable : LState :=
  {| ms := {| stk := fun x t => if Nat.eqb x 0
                                then (if Nat.eqb t 0 then Some 1 else None)
                                else None;
              hp  := fun o _ => if Nat.ltb o 2 then Some VNull else None;
              lk  := Some 0;
              rt  := 0;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Oroot)
                          \/ (o = 1 /\ (ob = Ofresh 0 \/ ob = Ofree 0));
     undf  := fun _ _ => False;
     thrd  := fun t => t = 0;
     flist := fun _ => None |}.

Lemma ff_no_edges : forall o f o', ~ Edge fresh_freeable o f o'.
Proof.
  intros o f o'. unfold Edge, fresh_freeable. simpl.
  destruct (Nat.ltb o 2); discriminate.
Qed.

Lemma ff_reaches_only_root :
  forall p o, Reaches fresh_freeable p o -> p = [] /\ o = 0.
Proof.
  intros [|f p] o H; unfold Reaches in H; simpl in H.
  - injection H as <-. split; reflexivity.
  - discriminate.
Qed.

Lemma ff_stk_inv :
  forall x t o, stk (ms fresh_freeable) x t = Some o -> x = 0 /\ t = 0 /\ o = 1.
Proof.
  intros x t o H. simpl in H.
  destruct (Nat.eqb x 0) eqn:Hx; [| discriminate].
  destruct (Nat.eqb t 0) eqn:Ht; [| discriminate].
  injection H as <-. apply Nat.eqb_eq in Hx. apply Nat.eqb_eq in Ht.
  repeat split; assumption.
Qed.

Lemma ff_fresh : obsv fresh_freeable 1 (Ofresh 0).
Proof. right. split; [reflexivity | left; reflexivity]. Qed.

Lemma ff_free : obsv fresh_freeable 1 (Ofree 0).
Proof. right. split; [reflexivity | right; reflexivity]. Qed.

(** One lemma per invariant, as for [initial], so a failure names the invariant
    that failed. *)

Lemma ff_OW : forall FType, OW FType fresh_freeable.
Proof.
  intros FType o o' f f' x H1 H2 _ _. exfalso.
  simpl in H1. destruct (Nat.ltb o 2); discriminate H1.
Qed.

Lemma ff_RWOW : RWOW fresh_freeable.
Proof.
  intros x t o H _.
  destruct (ff_stk_inv _ _ _ H) as [_ [-> ->]].
  right. split; [reflexivity |]. right. right. exact ff_fresh.
Qed.

Lemma ff_AWRT : AWRT fresh_freeable.
Proof.
  intros y t H _. destruct (ff_stk_inv _ _ _ H) as [_ [_ Hc]]. discriminate Hc.
Qed.

Lemma ff_IFL : IFL fresh_freeable.
Proof. intros t o Tr H1 H2. simpl in H2. discriminate H2. Qed.

Lemma ff_ULKR : ULKR fresh_freeable.
Proof. intros o o' f' t _ H. exfalso. exact (ff_no_edges _ _ _ H). Qed.

Lemma ff_FLR : FLR fresh_freeable.
Proof. intros o o' f' Tr H1 H2. simpl in H1. discriminate H1. Qed.

Lemma ff_WULK : WULK fresh_freeable.
Proof.
  intros lw o t _ H. simpl in H.
  destruct H as [[_ H] | [_ [H | H]]]; discriminate H.
Qed.

Lemma ff_FR : FR fresh_freeable.
Proof.
  intros t x o Hstk Hfresh.
  destruct (ff_stk_inv _ _ _ Hstk) as [-> [-> ->]]. split.
  - intros o' f'. apply ff_no_edges.
  - intros y t' Hne Hstk'.
    destruct (ff_stk_inv _ _ _ Hstk') as [-> [-> _]].
    apply Hne. reflexivity.
Qed.

Lemma ff_WFresh : WFresh fresh_freeable.
Proof.
  intros t x o Hstk _. destruct (ff_stk_inv _ _ _ Hstk) as [_ [-> _]].
  reflexivity.
Qed.

(** The published FNR holds -- both of its conjuncts are about observations
    node 1 does not carry. *)
Lemma ff_FNR_pub : FNR_pub fresh_freeable.
Proof.
  intros o t t' Hf. simpl in Hf.
  destruct Hf as [[_ H] | [-> _]]; [discriminate H |].
  split; intros H; destruct H as [[H _] | [_ [H | H]]]; discriminate H.
Qed.

Lemma ff_FPI : forall FType, FPI FType fresh_freeable.
Proof.
  intros FType o f o' t lw _ H _ _. exfalso. exact (ff_no_edges _ _ _ H).
Qed.

Lemma ff_WNR : WNR fresh_freeable.
Proof. intros t _ H. exact H. Qed.

Lemma ff_RITR : RITR fresh_freeable.
Proof. intros o t H. destruct H. Qed.

Lemma ff_RINFL : RINFL fresh_freeable.
Proof. intros o Tr t H1 H2. simpl in H1. discriminate H1. Qed.

Lemma ff_HD : HD fresh_freeable.
Proof. intros o f o' H _. exfalso. exact (ff_no_edges _ _ _ H). Qed.

Lemma ff_UNQRT_a : UNQRT_a fresh_freeable.
Proof. intros o f. apply ff_no_edges. Qed.

Lemma ff_UNQRT_b : UNQRT_b fresh_freeable.
Proof.
  intros p o lw _ H. destruct (ff_reaches_only_root _ _ H) as [_ ->].
  right. left. split; reflexivity.
Qed.

Lemma ff_WUNLK : WUNLK fresh_freeable.
Proof.
  intros o t lw Hlk [H | H]; simpl in Hlk; injection Hlk as <-;
    simpl in H; destruct H as [[_ H] | [_ [H | H]]]; try discriminate.
  injection H as H. exact H.
Qed.

Lemma ff_WITR : WITR fresh_freeable.
Proof.
  intros o t H. exfalso. simpl in H.
  destruct H as [[_ H] | [_ [H | H]]]; discriminate H.
Qed.

Lemma ff_UNQR : UNQR fresh_freeable.
Proof.
  intros p p' o H1 H2.
  destruct (ff_reaches_only_root _ _ H1) as [-> _].
  destruct (ff_reaches_only_root _ _ H2) as [-> _]. reflexivity.
Qed.

(** [WellFormed] with FNR replaced by the published form. *)
Definition WellFormed_pubFNR (FType : FName -> FieldKind) (s : LState) : Prop :=
  OW FType s /\ RWOW s /\ AWRT s /\ IFL s /\ ULKR s /\ FLR s /\ WULK s
  /\ FR s /\ WFresh s /\ FNR_pub s /\ FPI FType s /\ WNR s /\ RITR s /\ RINFL s
  /\ HD s /\ UNQRT_a s /\ UNQRT_b s /\ WUNLK s /\ WITR s /\ UNQR s.

Theorem ff_WellFormed_pubFNR :
  forall FType, WellFormed_pubFNR FType fresh_freeable.
Proof.
  intros FType. unfold WellFormed_pubFNR.
  repeat apply conj;
    first [ apply ff_OW      | apply ff_RWOW  | apply ff_AWRT
          | apply ff_IFL     | apply ff_ULKR  | apply ff_FLR
          | apply ff_WULK    | apply ff_FR    | apply ff_WFresh
          | apply ff_FNR_pub | apply ff_FPI   | apply ff_WNR
          | apply ff_RITR    | apply ff_RINFL | apply ff_HD
          | apply ff_UNQRT_a | apply ff_UNQRT_b
          | apply ff_WUNLK   | apply ff_WITR | apply ff_UNQR ].
Qed.

Lemma ff_not_FNR : ~ FNR fresh_freeable.
Proof.
  intros H. destruct (H 1 0 0 ff_fresh) as [_ [_ Hnf]]. exact (Hnf ff_free).
Qed.

(** The published set does not entail the conjunct, so no proof over it can use
    the conjunct -- and [link_fresh_ULKR] needs exactly that. *)
Theorem FNR_pub_admits_freeable_fresh :
  (forall FType, WellFormed_pubFNR FType fresh_freeable)
  /\ obsv fresh_freeable 1 (Ofresh 0)
  /\ obsv fresh_freeable 1 (Ofree 0)
  /\ ~ FNR fresh_freeable.
Proof.
  repeat apply conj;
    [ exact ff_WellFormed_pubFNR | exact ff_fresh | exact ff_free
    | exact ff_not_FNR ].
Qed.

Print Assumptions ff_WellFormed_pubFNR.
Print Assumptions FNR_pub_admits_freeable_fresh.

(** * Unlinking need not be the writer's

    A ninth defect, and the second of its kind: like FNR's missing conjunct it
    is a failure of locality rather than a false statement, and like that one it
    was found by attempting an action lemma -- here the ULKR case of T-UnlinkH
    and T-Replace, which is the case that keeps a node awaiting reclamation
    unreachable, so not a case one would want to leave waved through.

    The obligation is this.  Unlinking [z] leaves whatever detached predecessors
    OW allows it, and ULKR must then say they are unlinked or freeable *by the
    same thread* -- its conclusion is indexed by the thread its hypothesis is.
    OW gives detachment; the repaired premise of the two rules rules out a
    [fresh] predecessor; so the predecessor is unlinked or freeable by some
    thread.  Nothing in the published set says which.

    As with FNR, the executions have no such state: [unlinked] is produced only
    by the two writer rules and carried to [freeable] by SyncStop, so the thread
    is always the lock holder.  And as with FNR that is a property of whole
    executions rather than an invariant, so the action lemma does not close.
    WFresh already says the corresponding thing about the other end of a node's
    life -- an allocation is the lock holder's -- which is the strongest
    indication that its absence here was an oversight rather than a decision.

    The state below satisfies the other eighteen. *)

Definition WellFormed_noWUNLK (FType : FName -> FieldKind) (s : LState) : Prop :=
  OW FType s /\ RWOW s /\ AWRT s /\ IFL s /\ ULKR s /\ FLR s /\ WULK s
  /\ FR s /\ WFresh s /\ FNR s /\ FPI FType s /\ WNR s /\ RITR s /\ RINFL s
  /\ HD s /\ UNQRT_a s /\ UNQRT_b s /\ WITR s /\ UNQR s.

(** Node 1 is unlinked by thread 9, while the writer is thread 0. *)
Definition unlk_foreign : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o _ => if Nat.ltb o 2 then Some VNull else None;
              lk  := Some 0;
              rt  := 0;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Oroot) \/ (o = 1 /\ ob = Ounlk 9);
     undf  := fun _ _ => False;
     thrd  := fun t => t = 0 \/ t = 9;
     flist := fun _ => None |}.

Lemma uf_no_edges : forall o f o', ~ Edge unlk_foreign o f o'.
Proof.
  intros o f o'. unfold Edge, unlk_foreign. simpl.
  destruct (Nat.ltb o 2); discriminate.
Qed.

Lemma uf_reaches_only_root :
  forall p o, Reaches unlk_foreign p o -> p = [] /\ o = 0.
Proof.
  intros [|f p] o H; unfold Reaches in H; simpl in H.
  - injection H as <-. split; reflexivity.
  - discriminate.
Qed.

Lemma uf_WellFormed_noWUNLK : forall FType, WellFormed_noWUNLK FType unlk_foreign.
Proof.
  intros FType. unfold WellFormed_noWUNLK. repeat apply conj.
  - intros o o' f f' x H1. exfalso. simpl in H1.
    destruct (Nat.ltb o 2); discriminate H1.
  - intros x t o H. simpl in H. discriminate H.
  - intros y t H. simpl in H. discriminate H.
  - intros t o Tr H1 H2. simpl in H2. discriminate H2.
  - intros o o' f' t _ H. exfalso. exact (uf_no_edges _ _ _ H).
  - intros o o' f' Tr H1 H2. simpl in H1. discriminate H1.
  - intros lw o t _ H. simpl in H.
    destruct H as [[_ H] | [_ H]]; discriminate H.
  - intros t x o H. simpl in H. discriminate H.
  - intros t x o H. simpl in H. discriminate H.
  - intros o t t' H. simpl in H.
    destruct H as [[_ H] | [_ H]]; discriminate H.
  - intros o f o' t lw _ H. exfalso. exact (uf_no_edges _ _ _ H).
  - intros t H1 H2. exact H2.
  - intros o t H. destruct H.
  - intros o Tr t H1 H2. simpl in H1. discriminate H1.
  - intros o f o' H _. exfalso. exact (uf_no_edges _ _ _ H).
  - intros o f. apply uf_no_edges.
  - intros p o lw H1 H2.
    destruct (uf_reaches_only_root _ _ H2) as [_ ->].
    right. left. split; reflexivity.
  - intros o t H. exfalso. simpl in H.
    destruct H as [[_ H] | [_ H]]; discriminate H.
  - intros p p' o H1 H2.
    destruct (uf_reaches_only_root _ _ H1) as [-> _].
    destruct (uf_reaches_only_root _ _ H2) as [-> _]. reflexivity.
Qed.

Lemma uf_not_WUNLK : ~ WUNLK unlk_foreign.
Proof.
  intros H.
  assert (Hob : obsv unlk_foreign 1 (Ounlk 9))
    by (right; split; reflexivity).
  assert (Hc : 9 = 0) by exact (H 1 9 0 eq_refl (or_introl Hob)).
  discriminate Hc.
Qed.

Theorem unlinked_observations_need_not_be_the_writers :
  (forall FType, WellFormed_noWUNLK FType unlk_foreign)
  /\ lk (ms unlk_foreign) = Some 0
  /\ obsv unlk_foreign 1 (Ounlk 9)
  /\ ~ WUNLK unlk_foreign.
Proof.
  repeat apply conj;
    [ exact uf_WellFormed_noWUNLK | reflexivity
    | right; split; reflexivity | exact uf_not_WUNLK ].
Qed.

Print Assumptions uf_WellFormed_noWUNLK.
Print Assumptions unlinked_observations_need_not_be_the_writers.

(** * Iterators need not be held by an active thread

    A tenth defect, the third of the family, and the one that shows the family
    is a family.  Each kind of observation constrains who may hold it, and the
    published set says so for exactly one of the three: WFresh, that an
    allocation is the lock holder's.  Nothing said who may hold [unlinked] or
    [freeable] -- that is WUNLK, above -- and nothing said who may hold
    [iterator].

    This one is SyncStart's.  SyncStart puts every unlinked node on the free
    list with the current readers as its bounding set, and IFL then demands that
    every thread observing such a node as an [iterator] is in that set: it is
    the obligation that a grace period waits for everyone who could still be
    looking.  WULK rules out the writer.  Nothing rules out a thread that is
    neither the writer nor a current reader, and against such a thread the grace
    period would complete while a live reference remained -- which is precisely
    the accident the whole structure exists to prevent.

    So of the three this is the one whose absence is not merely a locality
    failure.  The other two hold of every reachable state and fail only to be
    provable locally; this one is what makes the reclamation safe, and it is
    unstated.  It is nonetheless just as cheap: every action preserves it, since
    an [iterator] is granted only to the writer by the two linking rules and
    only to a reader by a read, and ReadEnd drops a departing thread's
    observations in the same step as its readership.

    The state below satisfies the other eighteen. *)

Definition WellFormed_noWITR (FType : FName -> FieldKind) (s : LState) : Prop :=
  OW FType s /\ RWOW s /\ AWRT s /\ IFL s /\ ULKR s /\ FLR s /\ WULK s
  /\ FR s /\ WFresh s /\ FNR s /\ FPI FType s /\ WNR s /\ RITR s /\ RINFL s
  /\ HD s /\ UNQRT_a s /\ UNQRT_b s /\ WUNLK s /\ UNQR s.

(** Node 1 is observed as an iterator by thread 9, which is neither the writer
    (thread 0) nor a reader (there are none). *)
Definition itr_foreign : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o _ => if Nat.ltb o 2 then Some VNull else None;
              lk  := Some 0;
              rt  := 0;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Oroot) \/ (o = 1 /\ ob = Oiter 9);
     undf  := fun _ _ => False;
     thrd  := fun t => t = 0 \/ t = 9;
     flist := fun _ => None |}.

Lemma if_no_edges : forall o f o', ~ Edge itr_foreign o f o'.
Proof.
  intros o f o'. unfold Edge, itr_foreign. simpl.
  destruct (Nat.ltb o 2); discriminate.
Qed.

Lemma if_reaches_only_root :
  forall p o, Reaches itr_foreign p o -> p = [] /\ o = 0.
Proof.
  intros [|f p] o H; unfold Reaches in H; simpl in H.
  - injection H as <-. split; reflexivity.
  - discriminate.
Qed.

Lemma if_WellFormed_noWITR : forall FType, WellFormed_noWITR FType itr_foreign.
Proof.
  intros FType. unfold WellFormed_noWITR. repeat apply conj.
  - intros o o' f f' x H1. exfalso. simpl in H1.
    destruct (Nat.ltb o 2); discriminate H1.
  - intros x t o H. simpl in H. discriminate H.
  - intros y t H. simpl in H. discriminate H.
  - intros t o Tr H1 H2. simpl in H2. discriminate H2.
  - intros o o' f' t _ H. exfalso. exact (if_no_edges _ _ _ H).
  - intros o o' f' Tr H1 H2. simpl in H1. discriminate H1.
  - (* WULK: the writer is thread 0, and node 1's iterator is thread 9's *)
    intros lw o t H1 H2. simpl in H1. injection H1 as <-. simpl in H2.
    destruct H2 as [[_ H] | [_ H]]; discriminate H.
  - intros t x o H. simpl in H. discriminate H.
  - intros t x o H. simpl in H. discriminate H.
  - intros o t t' H. simpl in H.
    destruct H as [[_ H] | [_ H]]; discriminate H.
  - intros o f o' t lw _ H. exfalso. exact (if_no_edges _ _ _ H).
  - intros t H1 H2. exact H2.
  - intros o t H. destruct H.
  - intros o Tr t H1 H2. simpl in H1. discriminate H1.
  - intros o f o' H _. exfalso. exact (if_no_edges _ _ _ H).
  - intros o f. apply if_no_edges.
  - intros p o lw H1 H2.
    destruct (if_reaches_only_root _ _ H2) as [_ ->].
    right. left. split; reflexivity.
  - intros o t lw _ [H | H]; simpl in H;
      destruct H as [[_ H] | [_ H]]; discriminate H.
  - intros p p' o H1 H2.
    destruct (if_reaches_only_root _ _ H1) as [-> _].
    destruct (if_reaches_only_root _ _ H2) as [-> _]. reflexivity.
Qed.

Lemma if_not_WITR : ~ WITR itr_foreign.
Proof.
  intros H.
  assert (Hob : obsv itr_foreign 1 (Oiter 9)) by (right; split; reflexivity).
  destruct (H 1 9 Hob) as [Hc | Hc]; [discriminate Hc | exact Hc].
Qed.

Theorem iterators_need_not_be_active :
  (forall FType, WellFormed_noWITR FType itr_foreign)
  /\ obsv itr_foreign 1 (Oiter 9)
  /\ lk (ms itr_foreign) = Some 0
  /\ ~ rds (ms itr_foreign) 9
  /\ ~ WITR itr_foreign.
Proof.
  repeat apply conj;
    [ exact if_WellFormed_noWITR | right; split; reflexivity | reflexivity
    | intros H; exact H | exact if_not_WITR ].
Qed.

Print Assumptions if_WellFormed_noWITR.
Print Assumptions iterators_need_not_be_active.

(** ** Defect 11: the free list's domain is unconstrained

    Three conjuncts mention [flist] -- IFL, FLR and RINFL -- and all three are
    conditional on an entry existing.  None of them says where entries may
    exist.  So nothing in the nineteen rules out an entry at a node that is not
    detached, not reachable, and not even in the heap.

    That is not a curiosity.  SyncStart's specification says the grace period
    covers *exactly* the detached nodes, and re-establishing "exactly" needs to
    know that the entries already there were at detached nodes too.  It is the
    one hypothesis of the snapshot step that no invariant supplies, and the
    witness below is why: the state satisfies all nineteen and has an entry at
    a location with no observations at all.

    The repair is a twentieth conjunct,

      FLD s := forall o Tr, flist s o = Some Tr ->
                 exists t, obsv s o (Ounlk t) \/ obsv s o (Ofree t)

    which SyncStart establishes and every other action either preserves
    trivially or -- Free and ReadEnd -- preserves because it only shrinks the
    free list.  It is stated here and used as an explicit hypothesis where it is
    needed rather than being folded into [WellFormed], because adding a
    conjunct means re-proving fifteen actions and that is a change to make
    deliberately. *)

Definition FLD (s : LState) : Prop :=
  forall o Tr, flist s o = Some Tr ->
    exists t, obsv s o (Ounlk t) \/ obsv s o (Ofree t).

Definition fl_stray : LState :=
  {| ms    := ms initial;
     obsv  := obsv initial;
     undf  := undf initial;
     thrd  := thrd initial;
     flist := fun o => if Nat.eqb o 1 then Some (fun _ => False) else None |}.

Lemma fl_stray_entry : flist fl_stray 1 = Some (fun _ => False).
Proof. reflexivity. Qed.

Lemma fl_stray_entry_inv o Tr :
  flist fl_stray o = Some Tr -> Tr = (fun _ => False).
Proof.
  simpl. destruct (Nat.eqb o 1); [| discriminate]. intros H.
  injection H as <-. reflexivity.
Qed.

Lemma fl_stray_IFL : IFL fl_stray.
Proof. intros t o Tr Hit _. destruct Hit as [_ Hc]. discriminate. Qed.

Lemma fl_stray_FLR : FLR fl_stray.
Proof.
  intros o o' f' Tr _ He. exfalso. exact (initial_no_edges o' f' o He).
Qed.

Lemma fl_stray_RINFL : RINFL fl_stray.
Proof.
  intros o Tr t Hfl Hin. rewrite (fl_stray_entry_inv o Tr Hfl) in Hin.
  destruct Hin.
Qed.

Theorem fl_stray_WellFormed : forall FType, WellFormed FType fl_stray.
Proof.
  intros FType. unfold WellFormed.
  repeat apply conj;
    first [ apply initial_OW      | apply initial_RWOW  | apply initial_AWRT
          | apply fl_stray_IFL    | apply initial_ULKR  | apply fl_stray_FLR
          | apply initial_WULK    | apply initial_FR    | apply initial_WFresh
          | apply initial_FNR     | apply initial_FPI   | apply initial_WNR
          | apply initial_RITR    | apply fl_stray_RINFL | apply initial_HD
          | apply initial_UNQRT_a | apply initial_UNQRT_b
          | apply initial_WUNLK   | apply initial_WITR
          | apply initial_UNQR ].
Qed.

(** The entry is at a node with no observations, so it is not detached, and
    FLD is not a consequence of the nineteen. *)
Theorem free_list_domain_is_unconstrained :
  (forall FType, WellFormed FType fl_stray) /\ ~ FLD fl_stray.
Proof.
  split; [exact fl_stray_WellFormed |].
  intros H. destruct (H 1 (fun _ => False) fl_stray_entry) as [t [Hc | Hc]];
    destruct Hc as [_ Hd]; discriminate.
Qed.

Print Assumptions fl_stray_WellFormed.
Print Assumptions free_list_domain_is_unconstrained.

(** ** Defects 13 and 14: two observations that constrain nobody

    Found the same way as FLD, by attempting the last of the linking rules
    against the Iris invariant.  T-LinkF-Null needs to know that no thread other
    than the writer has an observation of the node being linked in.  Two
    invariants ought to supply it between them, and neither does.

    The first is that [root] marks the root.  Nothing says so.  [Oroot] is the
    anonymous observation, and the nineteen constrain where every *tagged*
    observation may sit but say nothing about this one -- so a well-formed state
    may record the root observation at a location that is not the root.  That
    also weakens UNQRT-b, whose conclusion is "iterator or root" and which is
    read as "reachable nodes are the writer's, except the root itself".

    The second is that a [fresh] observation belongs to the lock holder.
    WFresh is stated with a stack reference in its hypothesis -- a thread that
    *names* a fresh node holds the lock -- so a fresh observation whose variable
    has left scope constrains nobody.  That makes WFresh weaker than its own
    caption, and weaker than WUNLK and WITR, the two added above, which are the
    same statement for the other two kinds of observation.  The family the
    response describes is right; the member it already had was the weak one.

    One witness does for both: a state satisfying all nineteen in which the root
    observation sits at a non-root location and a fresh observation belongs to a
    thread that does not hold the lock. *)

Definition RTO (s : LState) : Prop :=
  forall o, obsv s o Oroot -> o = rt (ms s).

Definition WFreshW (s : LState) : Prop :=
  forall o t, obsv s o (Ofresh t) -> lk (ms s) = Some t.

(** Defect 18: WUNLK is guarded just tightly enough not to be usable.

    Found the same way WFreshW was, and it is the same defect one invariant
    along.  WUNLK says detaching observations are the writer's, but only *while
    a writer holds the lock*: in an unlocked state it says nothing, so nothing
    rules out a stray [unlinked] or [freeable] observation belonging to an
    arbitrary thread.

    That is exactly what 	extsc{ReadBegin} needs ruled out.  A thread entering a
    read-side critical section must hold no detaching observation -- otherwise
    RITR fails the moment it becomes a reader -- and the action lemma
    [read_begin_preserves_WellFormed] has carried this as the hypothesis
    [Hclean] for want of an invariant that supplies it.  With the lock held it
    does follow, from WUNLK and the entering thread not being the writer.  With
    the lock free nothing supplies it, and the unlocked state is precisely when
    a thread starts reading.

    The repair is WFreshW's, transposed: state it unguarded.  It is true of
    every reachable state for the reason WriteEnd already records -- the
    critical section leaves nothing detached, which is the hypothesis [Hclean]
    of [write_end_preserves_WellFormed]. *)
Definition WUNLKW (s : LState) : Prop :=
  forall o t,
    obsv s o (Ounlk t) \/ obsv s o (Ofree t) -> lk (ms s) = Some t.

(** Guarded, it does not survive an unlocked state: the witness is the same
    kind of thing as [obs_stray], and the point is that WUNLK holds of it. *)
Definition unlk_stray : LState :=
  {| ms    := {| stk := stk (ms initial); hp := hp (ms initial);
                 lk  := None;             rt := rt (ms initial);
                 rds := rds (ms initial); bnd := bnd (ms initial) |};
     obsv  := fun o ob => (o = 0 /\ ob = Oroot) \/ (o = 1 /\ ob = Ounlk 9);
     undf  := undf initial;
     thrd  := thrd initial;
     flist := flist initial |}.

Lemma unlk_stray_WUNLK : WUNLK unlk_stray.
Proof. intros o t lw Hc. discriminate Hc. Qed.

Lemma unlk_stray_no_edges : forall o f o', ~ Edge unlk_stray o f o'.
Proof.
  intros o f o'. unfold Edge, unlk_stray. simpl.
  destruct (Nat.eqb o 0); discriminate.
Qed.

Lemma unlk_stray_reaches : forall p o, Reaches unlk_stray p o -> p = [] /\ o = 0.
Proof.
  intros [|f p] o H; unfold Reaches in H; simpl in H.
  - injection H as <-. split; reflexivity.
  - discriminate.
Qed.

(** All nineteen hold.  Almost every case is vacuous -- no edges, no stack, no
    free list, no readers -- which is the point: the state is unremarkable, and
    the stray observation is what the invariants do not see. *)
Lemma unlk_stray_WellFormed : forall FType, WellFormed FType unlk_stray.
Proof.
  intros FType. unfold WellFormed. repeat apply conj.
  - intros o o' f f' x H1. exfalso. exact (unlk_stray_no_edges _ _ _ H1).
  - intros x t o H. simpl in H. discriminate H.
  - intros y t H. simpl in H. discriminate H.
  - intros t o Tr H1 H2. simpl in H2. discriminate H2.
  - intros o o' f' t _ H. exfalso. exact (unlk_stray_no_edges _ _ _ H).
  - intros o o' f' Tr H1 H2. simpl in H1. discriminate H1.
  - intros lw o t H1. discriminate H1.
  - intros t x o H1 H2. simpl in H1. discriminate H1.
  - intros t x o H1 H2. simpl in H1. discriminate H1.
  - intros o t t' H. simpl in H.
    destruct H as [[_ H] | [_ H]]; discriminate H.
  - intros o f o' t lw _ H. exfalso. exact (unlk_stray_no_edges _ _ _ H).
  - intros t H1. discriminate H1.
  - intros o t H. destruct H.
  - intros o Tr t H1 H2. simpl in H1. discriminate H1.
  - intros o f o' H _. exfalso. exact (unlk_stray_no_edges _ _ _ H).
  - intros o f. apply unlk_stray_no_edges.
  - intros p o lw H1. discriminate H1.
  - intros o t lw H1. discriminate H1.
  - intros o t H. simpl in H.
    destruct H as [[_ H] | [_ H]]; discriminate H.
  - intros p p' o H1 H2.
    destruct (unlk_stray_reaches _ _ H1) as [-> _].
    destruct (unlk_stray_reaches _ _ H2) as [-> _]. reflexivity.
Qed.

Theorem detaching_observations_survive_the_lock :
  (forall FType, WellFormed FType unlk_stray)
  /\ WUNLK unlk_stray
  /\ obsv unlk_stray 1 (Ounlk 9)
  /\ lk (ms unlk_stray) = None
  /\ ~ WUNLKW unlk_stray.
Proof.
  repeat apply conj;
    [ exact unlk_stray_WellFormed | exact unlk_stray_WUNLK
    | right; split; reflexivity | reflexivity |].
  intros H. assert (Hc : @None TID = Some 9).
  { apply (H 1 9). left. right. split; reflexivity. }
  discriminate Hc.
Qed.

Print Assumptions unlk_stray_WellFormed.
Print Assumptions detaching_observations_survive_the_lock.

Definition obs_stray : LState :=
  {| ms    := ms initial;
     obsv  := fun o ob => (ob = Oroot /\ (o = 0 \/ o = 1))
                          \/ (o = 2 /\ ob = Ofresh 5);
     undf  := undf initial;
     thrd  := thrd initial;
     flist := flist initial |}.

Lemma os_OW : forall FType, OW FType obs_stray.
Proof.
  intros FType o o' f f' x H1 H2 _ _. exfalso.
  exact (initial_no_edges _ _ _ H1).
Qed.

Lemma os_RWOW : RWOW obs_stray.
Proof. intros x t o H. simpl in H. discriminate H. Qed.

Lemma os_AWRT : AWRT obs_stray.
Proof. intros y t H. simpl in H. discriminate H. Qed.

Lemma os_IFL : IFL obs_stray.
Proof. intros t o Tr H1 H2. simpl in H2. discriminate H2. Qed.

Lemma os_ULKR : ULKR obs_stray.
Proof.
  intros o o' f' t H1 H2. exfalso. simpl in H1.
  destruct H1 as [H | H];
    destruct H as [[Hc _] | [_ Hc]]; discriminate Hc.
Qed.

Lemma os_FLR : FLR obs_stray.
Proof. intros o o' f' Tr H1 H2. simpl in H1. discriminate H1. Qed.

Lemma os_WULK : WULK obs_stray.
Proof.
  intros lw o t H1 H2. simpl in H2.
  destruct H2 as [[H _] | [_ H]]; discriminate H.
Qed.

Lemma os_FR : FR obs_stray.
Proof. intros t x o H1 H2. simpl in H1. discriminate H1. Qed.

Lemma os_WFresh : WFresh obs_stray.
Proof. intros t x o H1 H2. simpl in H1. discriminate H1. Qed.

Lemma os_FNR : FNR obs_stray.
Proof.
  intros o t t' H. split; [| split];
    intros [[Hc _] | [_ Hc]]; discriminate Hc.
Qed.

Lemma os_FPI : forall FType, FPI FType obs_stray.
Proof.
  intros FType o f o' t lw H1 H2 H3 H4. exfalso.
  exact (initial_no_edges _ _ _ H2).
Qed.

Lemma os_WNR : WNR obs_stray.
Proof. intros t H1 H2. exact H2. Qed.

Lemma os_RITR : RITR obs_stray.
Proof. intros o t H. destruct H. Qed.

Lemma os_RINFL : RINFL obs_stray.
Proof. intros o Tr t H1 H2. simpl in H1. discriminate H1. Qed.

Lemma os_HD : HD obs_stray.
Proof. intros o f o' H _. exfalso. exact (initial_no_edges _ _ _ H). Qed.

Lemma os_UNQRT_a : UNQRT_a obs_stray.
Proof. intros o f. apply initial_no_edges. Qed.

Lemma os_UNQRT_b : UNQRT_b obs_stray.
Proof.
  intros p o lw H1 H2.
  destruct (initial_reaches_only_root _ _ H2) as [_ ->]. right.
  simpl. left. split; [reflexivity | left; reflexivity].
Qed.

Lemma os_WUNLK : WUNLK obs_stray.
Proof.
  intros o t lw _ [H | H]; simpl in H;
    destruct H as [[Hc _] | [_ Hc]]; discriminate Hc.
Qed.

Lemma os_WITR : WITR obs_stray.
Proof.
  intros o t H. simpl in H.
  destruct H as [[Hc _] | [_ Hc]]; discriminate Hc.
Qed.

Lemma os_UNQR : UNQR obs_stray.
Proof.
  intros p p' o H1 H2.
  destruct (initial_reaches_only_root _ _ H1) as [-> _].
  destruct (initial_reaches_only_root _ _ H2) as [-> _]. reflexivity.
Qed.

Theorem obs_stray_WellFormed : forall FType, WellFormed FType obs_stray.
Proof.
  intros FType. unfold WellFormed.
  repeat apply conj;
    first [ apply os_OW      | apply os_RWOW  | apply os_AWRT
          | apply os_IFL     | apply os_ULKR  | apply os_FLR
          | apply os_WULK    | apply os_FR    | apply os_WFresh
          | apply os_FNR     | apply os_FPI   | apply os_WNR
          | apply os_RITR    | apply os_RINFL | apply os_HD
          | apply os_UNQRT_a | apply os_UNQRT_b
          | apply os_WUNLK   | apply os_WITR
          | apply os_UNQR ].
Qed.

Theorem root_observation_is_unpinned :
  (forall FType, WellFormed FType obs_stray) /\ ~ RTO obs_stray.
Proof.
  split; [exact obs_stray_WellFormed |].
  intros H. assert (Hc : (1 : Loc) = 0).
  { apply H. simpl. left. split; [reflexivity | right; reflexivity]. }
  discriminate Hc.
Qed.

Theorem fresh_observations_need_not_be_the_writers :
  (forall FType, WellFormed FType obs_stray) /\ ~ WFreshW obs_stray.
Proof.
  split; [exact obs_stray_WellFormed |].
  intros H. assert (Hc : lk (ms obs_stray) = Some 5).
  { apply (H 2). simpl. right. split; reflexivity. }
  simpl in Hc. discriminate Hc.
Qed.

Print Assumptions obs_stray_WellFormed.
Print Assumptions root_observation_is_unpinned.
Print Assumptions fresh_observations_need_not_be_the_writers.

(** ** Defect 17: the bounding set is unconstrained

    Found the same way as FLD, and it is the same kind of gap at the other end
    of the reclamation.  Exactly one of the nineteen mentions [B]: RINFL says
    every thread in a free-list entry is a bounding thread.  That bounds the
    entries above by [B] and says nothing whatever about [B] itself.

    [B] is not decoration.  SyncStop blocks until it is empty, and the only
    action that removes a thread from it is ReadEnd, which is a *reader's*
    action.  So a bounding thread that is not a reader can never be removed, and
    the grace period never completes.  Nothing in the nineteen rules that out.

    The missing invariant is the one SyncStart in fact establishes -- it sets
    [B] to the current readers -- and which every action preserves: ReadEnd
    narrows [R] and [B] together, SyncStop empties [B], and no other action
    touches either.  It is the exact counterpart of WITR: that one says who may
    hold an observation, this one says who may hold up a reclamation. *)

Definition BR (s : LState) : Prop :=
  forall t, bnd (ms s) t -> rds (ms s) t.

(** Why it matters beyond termination in general: with BR, the thread running
    the grace period is never one of the threads it waits for.  WNR says the
    writer is not a reader; without BR that leaves the writer free to sit in
    [B], waiting on itself. *)
Lemma writer_not_bounding s t :
  WNR s -> BR s -> lk (ms s) = Some t -> ~ bnd (ms s) t.
Proof. intros HW HB Hlk Hb. exact (HW t Hlk (HB t Hb)). Qed.

(** The witness: the initial state with thread 9 in the bounding set.  Thread 9
    is not a reader -- there are none -- and holds no observation, so the other
    nineteen are exactly the initial state's. *)
Definition bnd_ms : MState :=
  {| stk := stk (ms initial); hp := hp (ms initial); lk := lk (ms initial);
     rt  := rt (ms initial);  rds := rds (ms initial);
     bnd := fun t => t = 9 |}.

Definition bnd_stray : LState :=
  {| ms    := bnd_ms;
     obsv  := obsv initial;
     undf  := undf initial;
     thrd  := thrd initial;
     flist := flist initial |}.

Lemma bnd_stray_RINFL : RINFL bnd_stray.
Proof. intros o Tr t H1 H2. simpl in H1. discriminate H1. Qed.

Theorem bnd_stray_WellFormed : forall FType, WellFormed FType bnd_stray.
Proof.
  intros FType. unfold WellFormed.
  repeat apply conj;
    first [ apply initial_OW      | apply initial_RWOW   | apply initial_AWRT
          | apply initial_IFL     | apply initial_ULKR   | apply initial_FLR
          | apply initial_WULK    | apply initial_FR     | apply initial_WFresh
          | apply initial_FNR     | apply initial_FPI    | apply initial_WNR
          | apply initial_RITR    | apply bnd_stray_RINFL | apply initial_HD
          | apply initial_UNQRT_a | apply initial_UNQRT_b
          | apply initial_WUNLK   | apply initial_WITR
          | apply initial_UNQR ].
Qed.

Theorem bounding_threads_need_not_be_readers :
  (forall FType, WellFormed FType bnd_stray)
  /\ bnd (ms bnd_stray) 9
  /\ ~ rds (ms bnd_stray) 9
  /\ ~ BR bnd_stray.
Proof.
  repeat apply conj;
    [ exact bnd_stray_WellFormed | reflexivity | intros H; exact H |].
  intros H. exact (H 9 eq_refl).
Qed.

Print Assumptions bnd_stray_WellFormed.
Print Assumptions bounding_threads_need_not_be_readers.

(** ** Defect 19: free-list entries need not agree

    \textsc{SyncStart} takes one snapshot, so every entry it writes holds the
    same set.  That is a hypothesis of [sync_start_FLR] -- it is what makes FLR
    hold with equality rather than mere inclusion along a chain of detached
    nodes -- and it is stated there as a condition on the step.  It is also what
    the *reader's* read needs, and there it has to be an invariant.

    The obligation IFL puts on a reader following an edge is that a reader
    taking a reference to a node already on the free list is one of the threads
    its grace period waits for.  The reader is at [o] and follows an edge to
    [z].  If [z] is on the free list, FLR says its predecessor [o] is too, with
    a set containing [z]'s; IFL applied to [o], which the reader observes as an
    iterator, says the reader is in [o]'s set.  What is wanted is that it is in
    [z]'s, and the inclusion runs the wrong way.  With the entries equal it
    follows at once ([read_bound] below); without it, it does not follow at all.

    Nothing in the nineteen forces the entries to agree.  [snap_split] is the
    witness: a state satisfying all of them, and BR besides, with two entries
    holding different sets. *)

Definition SameSnap (s : LState) : Prop :=
  forall a b Ta Tb, flist s a = Some Ta -> flist s b = Some Tb ->
    forall x, Ta x <-> Tb x.

(** The reader's read, discharged.  Four lines, given the entries agree. *)
Lemma read_bound (s : LState) t o f z Tr :
  IFL s -> FLR s -> SameSnap s ->
  obsv s o (Oiter t) -> Edge s o f z -> flist s z = Some Tr -> Tr t.
Proof.
  intros HIFL HFLR Hsame Hit Hedge Hfl.
  destruct (HFLR z o f Tr Hfl Hedge) as [Tr' [Hfl' _]].
  apply (Hsame o z Tr' Tr Hfl' Hfl).
  exact (HIFL t o Tr' Hit Hfl').
Qed.

Definition snap_ms : MState :=
  {| stk := stk (ms initial); hp := hp (ms initial); lk := lk (ms initial);
     rt  := rt (ms initial);
     rds := fun t => t = 1 \/ t = 2;
     bnd := fun t => t = 1 \/ t = 2 |}.

Definition snap_split : LState :=
  {| ms    := snap_ms;
     obsv  := obsv initial;
     undf  := undf initial;
     thrd  := thrd initial;
     flist := fun o => if Nat.eqb o 1 then Some (fun t => t = 1)
                       else if Nat.eqb o 2 then Some (fun t => t = 2)
                       else None |}.

Lemma snap_entry_inv o Tr :
  flist snap_split o = Some Tr ->
  (Tr = (fun t => t = 1)) \/ (Tr = (fun t => t = 2)).
Proof.
  simpl. destruct (Nat.eqb o 1).
  - intros H. injection H as <-. left; reflexivity.
  - destruct (Nat.eqb o 2); [| discriminate].
    intros H. injection H as <-. right; reflexivity.
Qed.

Lemma snap_RINFL : RINFL snap_split.
Proof.
  intros o Tr t Hfl Hin. destruct (snap_entry_inv o Tr Hfl) as [-> | ->];
    simpl in Hin; simpl; [left; exact Hin | right; exact Hin].
Qed.

Lemma snap_split_WellFormed : forall FType, WellFormed FType snap_split.
Proof.
  intros FType. unfold WellFormed. repeat apply conj.
  - intros o o' f f' x H1. exfalso. simpl in H1.
    destruct (Nat.eqb o 0); discriminate H1.
  - intros x t o H. simpl in H. discriminate H.
  - intros y t H. simpl in H. discriminate H.
  - (* IFL: no iterator observations at all *)
    intros t o Tr H1 H2. exfalso. simpl in H1.
    destruct H1 as [_ Hc]. discriminate Hc.
  - intros o o' f' t H1. simpl in H1.
    destruct H1 as [[_ H] | [_ H]]; discriminate H.
  - intros o o' f' Tr H1 H2. exfalso.
    unfold Edge in H2. simpl in H2. destruct (Nat.eqb o' 0); discriminate H2.
  - intros lw o t H1 H2. simpl in H2. destruct H2 as [_ H]. discriminate H.
  - intros t x o H1 H2. simpl in H1. discriminate H1.
  - intros t x o H1 H2. simpl in H1. discriminate H1.
  - intros o t t' H. simpl in H. destruct H as [_ H]. discriminate H.
  - intros o f o' t lw H1 H2. exfalso.
    unfold Edge in H2. simpl in H2. destruct (Nat.eqb o 0); discriminate H2.
  - intros t H1 H2. simpl in H1. injection H1 as <-.
    destruct H2 as [H | H]; discriminate H.
  - intros o t H. repeat apply conj; intros [_ Hc]; discriminate Hc.
  - exact snap_RINFL.
  - intros o f o' H _. exfalso.
    unfold Edge in H. simpl in H. destruct (Nat.eqb o 0); discriminate H.
  - intros o f H. unfold Edge in H. simpl in H.
    destruct (Nat.eqb o 0); discriminate H.
  - intros p o lw H1 H2.
    destruct (initial_reaches_only_root p o H2) as [_ ->].
    right. split; reflexivity.
  - intros o t lw H1 [H | H]; simpl in H;
      destruct H as [_ H]; discriminate H.
  - intros o t H. simpl in H. destruct H as [_ H]. discriminate H.
  - intros p p' o H1 H2.
    destruct (initial_reaches_only_root p o H1) as [-> _].
    destruct (initial_reaches_only_root p' o H2) as [-> _]. reflexivity.
Qed.

Theorem free_list_entries_need_not_agree :
  (forall FType, WellFormed FType snap_split)
  /\ BR snap_split
  /\ ~ SameSnap snap_split.
Proof.
  repeat apply conj; [exact snap_split_WellFormed | intros t H; exact H |].
  intros H. assert (Hc : (1 : TID) = 2).
  { apply (H 1 2 (fun t => t = 1) (fun t => t = 2) eq_refl eq_refl 1).
    reflexivity. }
  discriminate Hc.
Qed.

Print Assumptions read_bound.
Print Assumptions snap_split_WellFormed.
Print Assumptions free_list_entries_need_not_agree.

(** ** Defect 20: fresh-reachability is guarded by the stack

    The fifth of the family, and the reader's read found it the way the reader's
    read found the fourth.

    \textsc{T-ReadH} gives a reader an [iterator] observation on the node it has
    just reached.  If that node were [fresh], FNR would fail at once -- a fresh
    node holds no iterator observation.  So the read needs to know that the node
    it reaches is not fresh, and what ought to supply that is FR: a fresh node
    has no incoming edge, so a node reached by following one is not fresh.

    FR does not supply it.  It is stated with a stack reference in its
    hypothesis -- a thread that *names* a fresh node -- exactly as WFresh was
    before the revision unguarded it, and for the same reason it is unusable:
    the observation outlives the variable.  A fresh node whose variable has been
    rebound constrains nobody, and nothing then stops an edge pointing at it.

    [fresh_may_be_pointed_at] is the witness: a state satisfying all nineteen in
    which a detached node points at a fresh one.  The repair is the one WFresh
    got -- state it unguarded -- and it is true of every reachable state because
    a node stops being fresh at the moment it is published. *)

Definition FRW (s : LState) : Prop :=
  forall o t, obsv s o (Ofresh t) -> forall o' f', ~ Edge s o' f' o.

Definition fr_stray : LState :=
  {| ms := {| stk := fun _ _ => None;
              hp  := fun o f => if Nat.eqb o 1
                                then (if Nat.eqb f 0 then Some (VLoc 2) else None)
                                else if Nat.eqb o 0 then Some VNull
                                else if Nat.eqb o 2 then Some VNull
                                else None;
              lk  := Some 0;
              rt  := 0;
              rds := fun _ => False;
              bnd := fun _ => False |};
     obsv  := fun o ob => (o = 0 /\ ob = Oroot)
                          \/ (o = 1 /\ ob = Ounlk 0)
                          \/ (o = 2 /\ ob = Ofresh 0);
     undf  := fun _ _ => False;
     thrd  := fun t => t = 0;
     flist := fun _ => None |}.

Lemma fr_stray_edge : Edge fr_stray 1 0 2.
Proof. reflexivity. Qed.

Lemma fr_stray_edge_inv o f o' :
  Edge fr_stray o f o' -> o = 1 /\ f = 0 /\ o' = 2.
Proof.
  unfold Edge. simpl. destruct (Nat.eqb o 1) eqn:E1.
  - destruct (Nat.eqb f 0) eqn:E0; [| discriminate].
    intros H. injection H as <-.
    apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E0.
    repeat apply conj; [exact E1 | exact E0 | reflexivity].
  - destruct (Nat.eqb o 0); [discriminate |].
    destruct (Nat.eqb o 2); discriminate.
Qed.

Lemma fr_stray_reaches q o : Reaches fr_stray q o -> q = [] /\ o = 0.
Proof.
  destruct q as [|f q]; intros H; unfold Reaches in H; simpl in H.
  - injection H as <-. split; reflexivity.
  - exfalso. simpl in H. destruct (Nat.eqb f 0); discriminate H.
Qed.

Lemma fr_stray_detached_1 : Detached fr_stray 1.
Proof. exists 0. left. simpl. right; left. split; reflexivity. Qed.

Lemma fr_stray_WellFormed : forall FType, WellFormed FType fr_stray.
Proof.
  intros FType. unfold WellFormed. repeat apply conj.
  - (* OW: the only edge has a detached source, which is the exemption *)
    intros o o' f f' x H1 H2 H3 H4.
    destruct (fr_stray_edge_inv o f x H1) as (-> & _ & _).
    right. left. exact fr_stray_detached_1.
  - intros x t o H. simpl in H. discriminate H.
  - intros y t H. simpl in H. discriminate H.
  - intros t o Tr H1 H2. simpl in H2. discriminate H2.
  - (* ULKR: nothing points at the unlinked node *)
    intros o o' f' t H1 H2.
    destruct (fr_stray_edge_inv o' f' o H2) as (_ & _ & ->).
    exfalso. destruct H1 as [Hc | Hc]; simpl in Hc;
      destruct Hc as [[Hd _] | [[Hd _] | [_ Hd]]]; discriminate Hd.
  - intros o o' f' Tr H1 H2. simpl in H1. discriminate H1.
  - (* WULK: there is no iterator observation to conflict with *)
    intros lw o t H1 H2. exfalso. simpl in H2.
    destruct H2 as [[_ Hd] | [[_ Hd] | [_ Hd]]]; discriminate Hd.
  - intros t x o H1 H2. simpl in H1. discriminate H1.
  - intros t x o H1 H2. simpl in H1. discriminate H1.
  - (* FNR: the fresh node holds no other observation *)
    intros o t t' H. simpl in H.
    destruct H as [[_ Hd] | [[_ Hd] | [-> Hd]]]; try discriminate Hd.
    repeat apply conj; intros Hbad; simpl in Hbad;
      destruct Hbad as [[Hc _] | [[Hc _] | [_ Hc]]]; discriminate Hc.
  - (* FPI: the edge's source is the unlinked node, not a fresh one *)
    intros o f o' t lw H1 H2 H3 H4.
    destruct (fr_stray_edge_inv o f o' H2) as (-> & _ & _).
    exfalso. simpl in H1.
    destruct H1 as [[Hd _] | [[_ Hd] | [Hd _]]]; discriminate Hd.
  - intros t H1 H2. exact H2.
  - intros o t H. destruct H.
  - intros o Tr t H1 H2. simpl in H1. discriminate H1.
  - (* HD: the only edge's source is detached, so it is exempt *)
    intros o f o' H1 H2. exfalso.
    destruct (fr_stray_edge_inv o f o' H1) as (-> & _ & _).
    exact (H2 fr_stray_detached_1).
  - intros o f H. destruct (fr_stray_edge_inv o f 0 H) as (_ & _ & Hc).
    discriminate Hc.
  - intros p o lw H1 H2.
    destruct (fr_stray_reaches p o H2) as [_ ->].
    right. simpl. left. split; reflexivity.
  - (* WUNLK: the same, unguarded in the thread *)
    intros o t lw H1 H2. simpl in H1. injection H1 as <-.
    destruct H2 as [Hc | Hc]; simpl in Hc;
      destruct Hc as [[_ Hd] | [[_ Hd] | [_ Hd]]]; try discriminate Hd;
      injection Hd as <-; reflexivity.
  - intros o t H. simpl in H.
    destruct H as [[_ Hc] | [[_ Hc] | [_ Hc]]]; discriminate Hc.
  - intros p p' o H1 H2.
    destruct (fr_stray_reaches p o H1) as [-> _].
    destruct (fr_stray_reaches p' o H2) as [-> _]. reflexivity.
Qed.

Theorem fresh_may_be_pointed_at :
  (forall FType, WellFormed FType fr_stray)
  /\ obsv fr_stray 2 (Ofresh 0)
  /\ Edge fr_stray 1 0 2
  /\ ~ FRW fr_stray.
Proof.
  repeat apply conj;
    [exact fr_stray_WellFormed
     | simpl; right; right; split; reflexivity
     | exact fr_stray_edge |].
  intros H. exact (H 2 0 (or_intror (or_intror (conj eq_refl eq_refl)))
                     1 0 fr_stray_edge).
Qed.

(** And with it, the node a reader reaches by following an edge is not fresh. *)
Lemma read_not_fresh (s : LState) o f z :
  FRW s -> Edge s o f z -> forall t, ~ obsv s z (Ofresh t).
Proof. intros HF He t Hbad. exact (HF z t Hbad o f He). Qed.

Print Assumptions fr_stray_WellFormed.
Print Assumptions fresh_may_be_pointed_at.
Print Assumptions read_not_fresh.

(** * Alglave et al.'s publish-subscribe requirement

    The second of the fundamental requirements: a freshly allocated node cannot
    be observed by a reader until it is published.  The paper argues this in
    prose from the shape of the type rules -- a new location can only be
    referenced by a variable of type [fresh], and becomes [rcuItr] on being
    published.  Here it is as a property of the state, and what is worth
    reporting is which invariants it needs.

    It needs two, and one of them is the invariant the reader's read forced
    (\S the FR defect above).  FNR gives that a fresh node carries no iterator
    observation, so no reader observes it; FRW gives that a fresh node has no
    incoming edge, so no reader can reach it by traversing.  Without the second
    the guarantee is half of itself: a reader could not be *holding* an
    unpublished node, but nothing said it could not walk to one. *)

Theorem readers_cannot_see_unpublished (s : LState) o t :
  FNR s -> FRW s ->
  obsv s o (Ofresh t) ->
  (* no thread observes it as an iterator ... *)
  (forall t', ~ obsv s o (Oiter t'))
  (* ... and nothing points at it, so none can reach it *)
  /\ (forall o' f', ~ Edge s o' f' o).
Proof.
  intros HFNR HFRW Hfr. split.
  - intros t'. exact (proj1 (HFNR o t t' Hfr)).
  - exact (HFRW o t Hfr).
Qed.

(** And the third requirement, that the RCU primitives execute unconditionally
    rather than failing and retrying, is a property of the *shape* of the
    semantics rather than of any state: the four primitives that are not
    blocking are total functions on the machine state, so each is enabled
    everywhere.  The two that are blocking -- WriteBegin and SyncStop -- block
    rather than fail, which is what the requirement asks.  There is nothing to
    prove about the four beyond their being functions, which is how they are
    defined; we record the observation rather than dress it as a theorem.

    The fourth requirement, read-to-write upgrade, this system does not provide,
    and we say so rather than argue about it: it is a performance optimisation
    and is orthogonal to memory safety. *)

Print Assumptions readers_cannot_see_unpublished.

(** * Alglave et al.'s third requirement, which is not nothing

    We said the third requirement -- that the RCU primitives execute
    unconditionally, rather than failing and retrying -- needed no proof, on the
    grounds that the primitives are total functions on the machine state.  That
    was wrong, and reading the semantics again is what shows it.  Five of the
    six primitives carry a side condition:

      ReadBegin  is written with [tid <> l] and with [R uplus {tid}] on the
                 right, so it requires the thread to be neither the writer nor
                 already a reader;
      ReadEnd    is written with [R uplus {tid}] on the *left*, so it requires
                 the thread to be a reader, and with [tid <> l] again;
      SyncStart  is written with an empty bounding set on the left, so it
                 requires no grace period to be in progress;
      WriteBegin requires the lock to be free;
      SyncStop   requires the bounding set to be empty.

    Only WriteEnd is unguarded.  So there is something to prove, and it is the
    right thing to prove: the requirement is not that the guards are trivial but
    that a *well-typed* thread never finds one false.  Below are the guards as
    propositions; which of them are discharged, and by what, is in [Triples.v],
    where a thread's own registration is a resource. *)

Definition guard_ReadBegin (m : MState) (t : TID) : Prop :=
  lk m <> Some t /\ ~ rds m t.

Definition guard_ReadEnd (m : MState) (t : TID) : Prop :=
  lk m <> Some t /\ rds m t.

Definition guard_SyncStart (m : MState) : Prop := forall t, ~ bnd m t.

Definition guard_SyncStop (m : MState) : Prop := forall t, ~ bnd m t.

Definition guard_WriteBegin (m : MState) : Prop := lk m = None.

(** The one that really is nothing. *)
Definition guard_WriteEnd (m : MState) : Prop := True.

Theorem write_end_unconditional : forall m, guard_WriteEnd m.
Proof. intros m. exact I. Qed.

(** The three the type system does not discharge are genuinely not discharged,
    and not because we have failed to: a state can satisfy every invariant with
    the lock held and a grace period running, and then all three are false at
    once.  [initial] with a lock holder and a bounding thread is such a state;
    [bnd_stray] above already is one. *)
Theorem writer_guards_are_not_invariants :
  (forall FType, WellFormed FType bnd_stray)
  /\ ~ guard_SyncStart (ms bnd_stray)
  /\ ~ guard_SyncStop (ms bnd_stray)
  /\ ~ guard_WriteBegin (ms bnd_stray).
Proof.
  repeat apply conj; [exact bnd_stray_WellFormed | | |].
  - intros H. exact (H 9 eq_refl).
  - intros H. exact (H 9 eq_refl).
  - intros H. discriminate H.
Qed.

Print Assumptions write_end_unconditional.
Print Assumptions writer_guards_are_not_invariants.
