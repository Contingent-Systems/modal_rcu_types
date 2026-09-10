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

  (** ** The eighteen invariants *)

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
      state satisfying the other seventeen in which it is not.

      Guarded by the lock, so it says nothing about a state with no writer --
      which is the weakest form that does the job. *)
  Definition WUNLK (s : LState) : Prop :=
    forall o t lw,
      lk (ms s) = Some lw ->
      (obsv s o (Ounlk t) \/ obsv s o (Ofree t)) -> t = lw.

  (** 18. UNQR -- unique reachability: distinct paths reach distinct nodes.
      This is the tree-shape invariant on which every framing side condition in
      T-UnlinkH, T-Replace and T-Insert depends. *)
  Definition UNQR (s : LState) : Prop :=
    forall p p' o, Reaches s p o -> Reaches s p' o -> p = p'.

  (** ** WellFormed *)

  Definition WellFormed (s : LState) : Prop :=
    OW s /\ RWOW s /\ AWRT s /\ IFL s /\ ULKR s /\ FLR s /\ WULK s
    /\ FR s /\ WFresh s /\ FNR s /\ FPI s /\ WNR s /\ RITR s /\ RINFL s
    /\ HD s /\ UNQRT_a s /\ UNQRT_b s /\ WUNLK s /\ UNQR s.

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
    check it satisfies all eighteen, for any field typing and any reading of
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
     literal [and] head, so it decomposes exactly the eighteen conjuncts. *)
  repeat apply conj;
    first [ apply initial_OW      | apply initial_RWOW  | apply initial_AWRT
          | apply initial_IFL     | apply initial_ULKR  | apply initial_FLR
          | apply initial_WULK    | apply initial_FR    | apply initial_WFresh
          | apply initial_FNR     | apply initial_FPI   | apply initial_WNR
          | apply initial_RITR    | apply initial_RINFL | apply initial_HD
          | apply initial_UNQRT_a | apply initial_UNQRT_b
          | apply initial_WUNLK    | apply initial_UNQR ].
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

    The witness below satisfies the other seventeen invariants and the published
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
  /\ HD s /\ UNQRT_a s /\ UNQRT_b s /\ WUNLK s /\ UNQR s.

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
          | apply ff_WUNLK   | apply ff_UNQR ].
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

    The state below satisfies the other seventeen. *)

Definition WellFormed_noWUNLK (FType : FName -> FieldKind) (s : LState) : Prop :=
  OW FType s /\ RWOW s /\ AWRT s /\ IFL s /\ ULKR s /\ FLR s /\ WULK s
  /\ FR s /\ WFresh s /\ FNR s /\ FPI FType s /\ WNR s /\ RITR s /\ RINFL s
  /\ HD s /\ UNQRT_a s /\ UNQRT_b s /\ UNQR s.

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
