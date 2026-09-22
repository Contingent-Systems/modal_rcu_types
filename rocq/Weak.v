(** * Weak memory: which invariants survive a per-thread heap

    Milestone 7, and it is the first task of a piece of work that is a paper
    rather than a file.  What is settled here is the partition, and it is
    settled mechanically; what is not settled is anything about an operational
    model, which is where the rest of that work lives.

    Everything before this file is sequentially consistent: there is one heap,
    and every thread sees it.  Tassarotti et al. verify RCU under
    release-acquire, where that is false -- each thread has its own view, and a
    view is a *sub-heap* of what has been written, since a thread sees a subset
    of the writes that have happened and never something that has not been
    written.  So the question a weak reading asks of an invariant is exactly:

      does it still hold when the heap shrinks?

    An invariant that survives shrinking transfers from the strongest view --
    the union of what all threads can see, which is what the writer maintains
    --- to every thread's own view, for free, and a weak-memory account never
    has to re-prove it per thread.  One that does not is an obligation
    synchronisation has to buy.

    The answer is sharp, and it is not the one we expected.  Of the twenty-six
    conjuncts the development carries, sixteen do not mention the heap at all
    and so survive trivially --- eleven of the published nineteen, and five of
    the ones this work adds; nine mention it and survive shrinking; and exactly
    one does not.  That one is \textbf{HD}, heap-domain closure --
    which is also the one invariant the published set got outright wrong, and
    the repair it needed is unrelated to this.  Read as an obligation, what it
    asks for is that a thread which can see an edge can also see the node at
    the end of it, and that is precisely the publish-subscribe guarantee:
    Alglave et al.'s second requirement, and the release-acquire pair
    Tassarotti et al. call Release-Acquire-1.  So the single place a per-thread
    heap bites is the single place the literature says synchronisation is
    required, which is the outcome that would make the rest of the work worth
    doing.

    Checked with Rocq 9.2, axiom-free. *)

From stdpp Require Import gmap sets.
From RCU Require Import WellFormed HeapPaths IrisGhost Denotations Actions
                        Epochs.

(** ** A thread's view

    A view is a sub-heap: what a thread can see is some of what has been
    written, and nothing that has not been.  [swap_hp] puts a given view in
    place of the global heap, and [sub_heap] is the ordering. *)

Definition swap_hp (s : LState) (h : Loc -> FName -> option Val) : LState :=
  {| ms := {| stk := stk (ms s); hp := h; lk := lk (ms s); rt := rt (ms s);
              rds := rds (ms s); bnd := bnd (ms s) |};
     obsv := obsv s; undf := undf s; thrd := thrd s; flist := flist s |}.

Definition sub_heap (h h' : Loc -> FName -> option Val) : Prop :=
  forall o f v, h o f = Some v -> h' o f = Some v.

(** Paths are monotone: a path that a thread can walk, the union can walk. *)
Lemma hstar_sub h h' o p q :
  sub_heap h h' -> hstar h o p = Some q -> hstar h' o p = Some q.
Proof.
  intros Hsub. revert o. induction p as [|f p IH]; intros o Hp; [exact Hp |].
  simpl in Hp |- *. destruct (h o f) as [[o1|]|] eqn:E; try discriminate.
  rewrite (Hsub o f (VLoc o1) E). exact (IH o1 Hp).
Qed.

Lemma edge_sub s h o f o' :
  sub_heap h (hp (ms s)) -> Edge (swap_hp s h) o f o' -> Edge s o f o'.
Proof. intros Hsub He. exact (Hsub o f (VLoc o') He). Qed.

(** ** The sixteen that do not mention the heap

    These survive any change to it whatever, shrinking or not, and the proof of
    each is [exact].  Under a weak reading they are the same statement in every
    thread's view because they do not look at a heap to begin with --- which is
    the observation map being per-thread already, and is the reason to think a
    weak account is approachable. *)
Theorem heap_free_invariants s h :
  (RWOW s -> RWOW (swap_hp s h))
  /\ (AWRT s -> AWRT (swap_hp s h))
  /\ (IFL s -> IFL (swap_hp s h))
  /\ (WULK s -> WULK (swap_hp s h))
  /\ (WFresh s -> WFresh (swap_hp s h))
  /\ (FNR s -> FNR (swap_hp s h))
  /\ (WNR s -> WNR (swap_hp s h))
  /\ (RITR s -> RITR (swap_hp s h))
  /\ (RINFL s -> RINFL (swap_hp s h))
  /\ (WUNLK s -> WUNLK (swap_hp s h))
  /\ (WITR s -> WITR (swap_hp s h))
  (* and the added conjuncts that mention no heap either *)
  /\ (FLD s -> FLD (swap_hp s h))
  /\ (BR s -> BR (swap_hp s h))
  /\ (WUNLKW s -> WUNLKW (swap_hp s h))
  /\ (WFreshW s -> WFreshW (swap_hp s h))
  /\ (SameSnap s -> SameSnap (swap_hp s h)).
Proof. repeat apply conj; intros H; exact H. Qed.

Print Assumptions heap_free_invariants.

(** ** The nine that survive shrinking

    Each of these mentions the heap, and each mentions it in a position where
    having *fewer* edges is easier: the heap occurs in a hypothesis, or under a
    negation in the conclusion.  So an invariant established of the union holds
    in every thread's view, and a weak reading costs nothing. *)
Theorem shrinking_is_harmless FType s h :
  sub_heap h (hp (ms s)) ->
  (OW FType s -> OW FType (swap_hp s h))
  /\ (ULKR s -> ULKR (swap_hp s h))
  /\ (FLR s -> FLR (swap_hp s h))
  /\ (FR s -> FR (swap_hp s h))
  /\ (FPI FType s -> FPI FType (swap_hp s h))
  /\ (UNQRT_a s -> UNQRT_a (swap_hp s h))
  /\ (UNQRT_b s -> UNQRT_b (swap_hp s h))
  /\ (UNQR s -> UNQR (swap_hp s h))
  /\ (FRW s -> FRW (swap_hp s h)).
Proof.
  intros Hsub. repeat apply conj.
  - intros H o o' f f' x H1 H2 Hf Hf'.
    exact (H o o' f f' x (Hsub o f _ H1) (Hsub o' f' _ H2) Hf Hf').
  - intros H o o' f' t Hob He.
    exact (H o o' f' t Hob (edge_sub s h o' f' o Hsub He)).
  - intros H o o' f' Tr Hfl He.
    exact (H o o' f' Tr Hfl (edge_sub s h o' f' o Hsub He)).
  - intros H t x o Hstk Hfr. destruct (H t x o Hstk Hfr) as [Hne Hstk'].
    split; [| exact Hstk'].
    intros o' f' He. exact (Hne o' f' (edge_sub s h o' f' o Hsub He)).
  - intros H o f o' t lw Hfr He Hft Hlk.
    exact (H o f o' t lw Hfr (edge_sub s h o f o' Hsub He) Hft Hlk).
  - intros H o f He. exact (H o f (edge_sub s h o f _ Hsub He)).
  - intros H p o lw Hlk Hr.
    exact (H p o lw Hlk (hstar_sub h (hp (ms s)) _ p o Hsub Hr)).
  - intros H p p' o Hr Hr'.
    exact (H p p' o (hstar_sub h (hp (ms s)) _ p o Hsub Hr)
             (hstar_sub h (hp (ms s)) _ p' o Hsub Hr')).
  - intros H o t Hfr o' f' He.
    exact (H o t Hfr o' f' (edge_sub s h o' f' o Hsub He)).
Qed.

Print Assumptions shrinking_is_harmless.

(** ** The one that does not

    \textbf{HD} says that if a node is not detached and has an edge, the node
    at the end of that edge is in the heap.  Every other invariant reads the
    heap only to rule something out; this one reads it to require something,
    and a thread that has seen the edge but not the node it points at breaks
    it.

    That is not an artificial state.  It is the publication race: the writer
    initialises a node and then links it, a reader acquires the link without
    acquiring the initialisation, and the reader can now follow a pointer to a
    node it cannot see.  The witness below is that state written down. *)

Definition pub_hp (o : Loc) (f : FName) : option Val :=
  if Nat.eqb o 0 then Some (VLoc 1%nat)
  else if Nat.eqb o 1 then Some VNull
  else None.

(* what the reader has acquired: the link, but not the node it points at *)
Definition pub_view (o : Loc) (f : FName) : option Val :=
  if Nat.eqb o 0 then Some (VLoc 1%nat) else None.

Definition pub_s : LState :=
  {| ms    := {| stk := fun _ _ => None; hp := pub_hp; lk := None;
                 rt := 0%nat; rds := fun _ => False; bnd := fun _ => False |};
     obsv  := fun _ _ => False;
     undf  := fun _ _ => True;
     thrd  := fun _ => True;
     flist := fun _ => None |}.

Lemma pub_sub : sub_heap pub_view pub_hp.
Proof.
  intros o f v Hv. unfold pub_view in Hv. unfold pub_hp.
  destruct (Nat.eqb o 0); [exact Hv | discriminate].
Qed.

Theorem publication_is_the_obligation :
  sub_heap pub_view pub_hp
  /\ HD (swap_hp pub_s pub_hp)
  /\ ~ HD (swap_hp pub_s pub_view).
Proof.
  repeat apply conj; [exact pub_sub | |].
  - intros o f o' He _. unfold Edge in He. simpl in He.
    unfold pub_hp in He.
    destruct (Nat.eqb o 0) eqn:E0.
    + injection He as <-. exists 0%nat, VNull. reflexivity.
    + destruct (Nat.eqb o 1) eqn:E1; discriminate.
  - intros H.
    assert (He : Edge (swap_hp pub_s pub_view) 0%nat 0%nat 1%nat)
      by reflexivity.
    assert (Hnd : ~ Detached (swap_hp pub_s pub_view) 0%nat)
      by (intros [t [Hc | [Hc | Hc]]]; exact Hc).
    destruct (H 0%nat 0%nat 1%nat He Hnd) as [f [v Hv]].
    unfold pub_view in Hv. simpl in Hv. discriminate.
Qed.

Print Assumptions publication_is_the_obligation.

(** ** What this settles, and what it does not

    It settles the partition the first task of this work asks for, and settles
    it mechanically rather than by reading.  Twenty-five of the twenty-six
    conjuncts are indifferent to a per-thread heap: sixteen do not mention one,
    and nine mention it only to rule something out, so an invariant proved of
    the union holds in every view.  The twenty-sixth is \textbf{HD}, and what
    it asks for under a weak reading is a publication guarantee.

    Two things follow that are worth having before the rest of the work starts.

    First, the synchronisation points the plan guessed at --- SyncStart's
    snapshot and ReadEnd's registration clear --- are the protocol's, and this
    says the type system needs one more: the *link*, where a writer publishes a
    node.  That is the release-acquire pair Tassarotti et al. name first, and
    it is the one our sequentially consistent model gets for free and a weak
    one does not.

    Second, the memory-safety argument is untouched by any of it.  It uses IFL
    and RWOW, both of which are in the heap-free eleven, and
    [readers_cannot_see_unpublished] --- our proof of the publish-subscribe
    requirement --- uses FNR and FRW, one heap-free and one that survives
    shrinking.  So none of the three has anything to say about views, and a
    weak account does not have to revisit them.  What it has to do is buy
    \textbf{HD} at the link.

    What is *not* settled is everything an operational model would settle.
    There is no weak-memory semantics here, no notion of a release or an
    acquire, and no theorem relating a run under one to a run under sequential
    consistency.  The reading of a view as a sub-heap is an assumption about
    what a weak model would provide, not a consequence of one; it is the right
    assumption for release-acquire, where a thread's knowledge only grows and
    is always of writes that happened, and it would be the wrong one for a
    model admitting out-of-thin-air reads.  We state the partition because it
    is checkable and because it says where the work goes, not because it is the
    work. *)

(** * Task two: where the synchronisation goes

    Task one said which invariants a per-thread heap endangers, and the answer
    was one.  This section says what follows: a state in which every thread has
    its own view, and the single condition under which the whole invariant set
    holds in every one of them.

    The point of stating it this way is that it is a *closed* obligation.  It
    does not say "and now re-prove the invariants per thread"; it says the
    invariants transfer wholesale, given one thing, and names the thing. *)

Record WState := MkW {
  w_base : LState;                                  (** the union of the views *)
  w_view : TID -> (Loc -> FName -> option Val);     (** what each thread sees *)
}.

(** A view is a sub-heap of the union: a thread sees some of the writes that
    have happened and never one that has not. *)
Definition w_ok (w : WState) : Prop :=
  forall t, sub_heap (w_view w t) (hp (ms (w_base w))).

Definition w_at (w : WState) (t : TID) : LState :=
  swap_hp (w_base w) (w_view w t).

(** The obligation, named.  Every thread that can reach a node can see it. *)
Definition Published (w : WState) : Prop :=
  forall t, HD (w_at w t).

(** And the theorem.  Nineteen of the twenty conjuncts of [WellFormed] transfer
    from the union to every view with no hypothesis at all -- eleven because
    they never look at a heap, eight because looking at a smaller one is easier
    -- and the twentieth is [Published].  So a weak-memory account of this
    system does not have to revisit the invariants; it has to establish one
    property at the moment a node is linked. *)
Theorem views_are_well_formed FType w :
  w_ok w -> Published w -> WellFormed FType (w_base w) ->
  forall t, WellFormed FType (w_at w t).
Proof.
  intros Hok Hpub Hwf t.
  destruct (shrinking_is_harmless FType (w_base w) (w_view w t) (Hok t))
    as (HOW' & HULKR' & HFLR' & HFR' & HFPI' & HUa' & HUb' & HUq' & _).
  destruct Hwf as (HOW & HRWOW & HAWRT & HIFL & HULKR & HFLR & HWULK & HFR
                   & HWFresh & HFNR & HFPI & HWNR & HRITR & HRINFL & _
                   & HUa & HUb & HWU & HWI & HUq).
  repeat apply conj.
  - exact (HOW' HOW).
  - exact HRWOW.
  - exact HAWRT.
  - exact HIFL.
  - exact (HULKR' HULKR).
  - exact (HFLR' HFLR).
  - exact HWULK.
  - exact (HFR' HFR).
  - exact HWFresh.
  - exact HFNR.
  - exact (HFPI' HFPI).
  - exact HWNR.
  - exact HRITR.
  - exact HRINFL.
  - exact (Hpub t).
  - exact (HUa' HUa).
  - exact (HUb' HUb).
  - exact HWU.
  - exact HWI.
  - exact (HUq' HUq).
Qed.

Print Assumptions views_are_well_formed.

(** So the heap's synchronisation is exactly one release-acquire pair, at the
    link.  Nothing the reader does needs one: a read walks an edge in the
    reader's own view, and everything the walk relies on -- the free-list
    chaining that discharges the bounding obligation, the fresh-reachability
    that says the target is not fresh -- is in the nineteen that transfer.  And
    reclamation needs none either, which is the part worth noticing: the
    memory-safety argument uses IFL and RWOW, both of which never look at a
    heap, so a reader holding a stale view cannot be made unsafe by a free.
    What it can be made unsafe by is a link it half-sees, which is
    [Published]. *)

(** * Task three: the protocol state goes the other way

    The heap is not the only shared state.  The registrations are shared too,
    and [Sim] in [Epochs.v] relates them to the published model's reader set.
    Restating that against a weak reading turns up the opposite character, and
    the contrast is the useful part of this section.

    For the heap, a thread that sees less is safe: twenty-five of the
    twenty-six conjuncts survive shrinking, and the exception is about
    publication.  For the registrations it is reversed.  A writer that sees
    *fewer* registrations than exist concludes a grace period has ended when it
    has not, and frees a node a reader is still holding.  Seeing less is
    exactly the hazard.

    So the two kinds of shared state in this system need synchronisation for
    opposite reasons, and that is why they need it at different places: the
    heap at the write that publishes, the registrations at the read that
    decides the wait is over. *)

Definition sub_reg (r r' : gmap TID nat) : Prop :=
  forall t e, r !! t = Some e -> r' !! t = Some e.

(** A reader registered at epoch 0, inside the grace period for a node stamped
    at 0.  The truth is that the grace period has not ended. *)
Definition wq_true : EState :=
  {| egen := 1; ereg := {[ 7%nat := 0 ]}; estamp := {[ 0%nat := 0 ]} |}.

(** The writer's stale view: it has not acquired the reader's registration. *)
Definition wq_view : EState :=
  {| egen := 1; ereg := ∅; estamp := {[ 0%nat := 0 ]} |}.

Theorem stale_registrations_are_unsafe :
  (* the view is a sub-map of the truth: the writer has missed a write *)
  sub_reg (ereg wq_view) (ereg wq_true)
  (* and both are well formed, so nothing else is wrong with either *)
  /\ EWF wq_true /\ EWF wq_view
  (* the grace period has not ended *)
  /\ ~ e_quiescent wq_true 0
  (* the writer's view says it has *)
  /\ e_quiescent wq_view 0
  (* so the writer takes the certificate and frees *)
  /\ e_F wq_view !! 0%nat = Some ∅
  (* while the node's snapshot really still contains the reader *)
  /\ e_F wq_true !! 0%nat = Some {[ 7%nat ]}.
Proof.
  assert (Hst : estamp wq_true !! 0%nat = Some 0) by apply lookup_singleton_eq.
  assert (Hsv : estamp wq_view !! 0%nat = Some 0) by apply lookup_singleton_eq.
  assert (Hstamps : forall (r : gmap TID nat),
            forall o e, ({[ 0%nat := 0 ]} : gmap Loc nat) !! o = Some e -> e < 1).
  { intros r o e Ho. destruct (decide (o = 0%nat)) as [-> | Hne].
    - rewrite lookup_singleton_eq in Ho. injection Ho as <-. apply Nat.lt_0_1.
    - rewrite lookup_singleton_ne in Ho;
        [discriminate | exact (fun Hc => Hne (eq_sym Hc))]. }
  repeat apply conj.
  - intros t e He. simpl in He. by rewrite lookup_empty in He.
  - exact (Hstamps ∅).
  - intros t e Ht. simpl in Ht.
    destruct (decide (t = 7%nat)) as [-> | Hne].
    + rewrite lookup_singleton_eq in Ht. injection Ht as <-. apply Nat.le_0_l.
    + rewrite lookup_singleton_ne in Ht;
        [discriminate | exact (fun Hc => Hne (eq_sym Hc))].
  - exact (Hstamps ∅).
  - intros t e Ht. simpl in Ht. by rewrite lookup_empty in Ht.
  - intros Hq.
    assert (Hr : ereg wq_true !! 7%nat = Some 0) by apply lookup_singleton_eq.
    exact (Nat.lt_irrefl 0 (Hq 7%nat 0 Hr)).
  - intros t e Ht. simpl in Ht. by rewrite lookup_empty in Ht.
  - apply (e_free_premise wq_view 0%nat 0 Hsv).
    intros t e Ht. simpl in Ht. by rewrite lookup_empty in Ht.
  - unfold e_F. rewrite lookup_fmap. rewrite Hst. simpl.
    apply f_equal. apply set_eq. intros t. rewrite elem_of_singleton.
    unfold e_snapshot. rewrite elem_of_dom. split.
    + intros [e He]. apply map_lookup_filter_Some in He as [He _].
      simpl in He.
      destruct (decide (t = 7%nat)) as [-> | Hne]; [reflexivity |].
      rewrite lookup_singleton_ne in He;
        [discriminate | exact (fun Hc => Hne (eq_sym Hc))].
    + intros ->. exists 0.
      apply map_lookup_filter_Some.
      split; [apply (lookup_singleton_eq 7%nat 0) |].
      simpl. apply Nat.le_refl.
Qed.

Print Assumptions stale_registrations_are_unsafe.

(** ** What that does to [Sim]

    [Sim] says the two models agree on who is reading, who is bounding, and
    what the free list is, and the first of those is an *iff*.  Under a weak
    reading that is the whole content: a sub-map view gives one direction of it
    and not the other, and the direction it loses is the one the wait depends
    on.  So the refinement obligation under weak memory is not a weakened
    version of the sequentially consistent one -- it is the same obligation,
    with the reads that establish it required to be acquires.

    That places the protocol's two synchronisation points exactly where
    Tassarotti et al. put them, which is the check on this section: the
    registration write at ReadBegin and ReadEnd must be a release, and the scan
    that decides the wait must acquire each one, which are their
    Release-Acquire-2 and Release-Acquire-3.  Their first pair is the link,
    which is [Published] above.  Three pairs, and we arrive at the same three
    from the invariants rather than from the algorithm.

    What remains, and it is the part that is genuinely a paper: an operational
    model in which "view", "release" and "acquire" are defined rather than
    assumed, and a theorem that a run under it is matched by a run of [lstep].
    Everything above is about the *statement* of that theorem -- which
    invariants it would have to re-establish (one), where it would have to
    synchronise (three places), and what it would have to assume about views (
    that they are sub-heaps and sub-maps).  We would rather publish the
    obligations than an account that quietly assumed them. *)
