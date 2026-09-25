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


(** * The model itself: release, acquire, and what a run guarantees

    Everything above is about the *statement* of a weak-memory result.  This
    section stops assuming and defines, and the first thing defining does is
    correct the assumption.

    We read a view as a sub-heap, and for the invariant partition that is the
    right reading: what an invariant faces is a thread that has seen fewer
    writes.  It is *not* the right reading of a run, and the reason is
    overwriting.  A thread that read a link before the writer re-pointed it
    holds a value the current heap no longer has, so its view is not a sub-heap
    of the current heap; it is a sub-heap of the heap as it was.  A model that
    cannot say that cannot say anything about RCU, where re-pointing a link is
    the operation.

    So the state here is a history.  Each cell carries the values written to it
    in order, a view is a timestamp per cell saying how far along each one a
    thread has got, and what a thread sees at a cell is the value at its own
    timestamp.  That is release-acquire in its standard view form.

    One thing is worth getting right rather than nearly right: the released
    view belongs to the *message*, not to the location.  Attaching it to the
    location is the obvious simplification and it is wrong -- publishing a
    location a second time would retroactively change what an earlier reader is
    obliged to have acquired, and the invariant below would not be preserved.
    Per-message is what makes the transitivity argument go through, and it is
    also what the real semantics does.

    Three steps, and they are the three the C API has.  A write, releasing or
    not: [rcu_assign_pointer] is the releasing one and a field initialisation
    is the other.  And a read, which acquires: [rcu_dereference]. *)

Definition View := Loc -> FName -> nat.
Definition Hist := Loc -> FName -> nat -> option Val.
Definition bot : View := fun _ _ => 0.

Definition vle (V W : View) : Prop := forall o f, V o f <= W o f.

Definition set_at (V : View) (o : Loc) (f : FName) (k : nat) : View :=
  fun q g => if decide ((q, g) = (o, f)) then k else V q g.

(** What a read does to a view: move to the message read, and take the maximum
    with what that message released. *)
Definition after_read (V W : View) (o : Loc) (f : FName) (k : nat) : View :=
  fun q g => if decide ((q, g) = (o, f)) then k else Nat.max (V q g) (W q g).

Record RAConf := MkRA {
  ra_h    : Hist;                        (** the value written at each timestamp *)
  ra_c    : View;                        (** how far each cell has been written *)
  ra_v    : TID -> View;                 (** how far each thread has got *)
  ra_relm : Loc -> FName -> nat -> View; (** the view released with each message *)
}.

(** What a thread sees at a cell. *)
Definition seen (c : RAConf) (t : TID) (o : Loc) (f : FName) : option Val :=
  ra_h c o f (ra_v c t o f).

(** And the heap it is looking at, which is what the invariants of the earlier
    sections are read against. *)
Definition ra_heap (c : RAConf) (t : TID) : Heap := seen c t.

Definition upd_v (V : TID -> View) (t : TID) (W : View) : TID -> View :=
  fun t' => if Nat.eq_dec t' t then W else V t'.

Definition upd_m (R : Loc -> FName -> nat -> View)
    (o : Loc) (f : FName) (k : nat) (W : View)
  : Loc -> FName -> nat -> View :=
  fun q g j => if decide ((q, g, j) = (o, f, k)) then W else R q g j.

Definition write (H : Hist) (o : Loc) (f : FName) (k : nat) (v : Val) : Hist :=
  fun q g j => if decide ((q, g, j) = (o, f, k)) then Some v else H q g j.

(** ** The bookkeeping

    Nobody is past what has been written; nothing published is; and a message's
    released view does not claim to be past that message at its own cell, which
    is what makes an acquiring read land where it should.  The last clause is
    the one that is easy to leave out and is load-bearing. *)
Definition ra_ok (c : RAConf) : Prop :=
  (forall t, vle (ra_v c t) (ra_c c))
  /\ (forall o f k, vle (ra_relm c o f k) (ra_c c))
  /\ (forall o f k, ra_relm c o f k o f <= k)
  /\ (forall o f, ra_relm c o f 0 = bot).

(** ** The steps *)
Inductive rastep : TID -> RAConf -> RAConf -> Prop :=
(** A write.  [b] says whether it releases: [rcu_assign_pointer] does, a field
    initialisation does not.  What a releasing write publishes is the writer's
    knowledge at the moment it publishes. *)
| RA_write t o f v (b : bool) c :
    rastep t c
      (MkRA (write (ra_h c) o f (S (ra_c c o f)) v)
            (set_at (ra_c c) o f (S (ra_c c o f)))
            (upd_v (ra_v c) t (set_at (ra_v c t) o f (S (ra_c c o f))))
            (upd_m (ra_relm c) o f (S (ra_c c o f))
               (if b then set_at (ra_v c t) o f (S (ra_c c o f)) else bot)))
(** A read, which acquires.  The thread may see any message at or after where
    it already is, and takes on what that message released. *)
| RA_read t o f k v c :
    ra_v c t o f <= k ->
    k <= ra_c c o f ->
    ra_h c o f k = Some v ->
    rastep t c
      (MkRA (ra_h c) (ra_c c)
            (upd_v (ra_v c) t
               (after_read (ra_v c t) (ra_relm c o f k) o f k))
            (ra_relm c)).

Lemma vle_refl V : vle V V.
Proof. intros o f. apply Nat.le_refl. Qed.

Lemma vle_trans U V W : vle U V -> vle V W -> vle U W.
Proof. intros H1 H2 o f. exact (Nat.le_trans _ _ _ (H1 o f) (H2 o f)). Qed.

Lemma vle_bot V : vle bot V.
Proof. intros o f. apply Nat.le_0_l. Qed.

Lemma vle_set_both V W o f k : vle V W -> vle (set_at V o f k) (set_at W o f k).
Proof.
  intros Hle q g. unfold set_at.
  destruct (decide ((q, g) = (o, f))); [apply Nat.le_refl | apply Hle].
Qed.

Lemma vle_set_r V W o f k : vle V W -> V o f <= k -> vle V (set_at W o f k).
Proof.
  intros Hle Hk q g. unfold set_at.
  destruct (decide ((q, g) = (o, f))) as [He | He];
    [injection He as -> ->; exact Hk | apply Hle].
Qed.

Lemma set_at_here V o f k : set_at V o f k o f = k.
Proof. unfold set_at. by rewrite decide_True. Qed.

Lemma set_at_there V o f k q g :
  (q, g) <> (o, f) -> set_at V o f k q g = V q g.
Proof. intros Hne. unfold set_at. by rewrite decide_False. Qed.

Theorem rastep_ok t c c' : rastep t c c' -> ra_ok c -> ra_ok c'.
Proof.
  intros Hst (Hv & Hm & Hself & Hzero). destruct Hst; unfold ra_ok;
    cbn [ra_h ra_c ra_v ra_relm]; unfold upd_v, upd_m.
  - (* a write.  The new message is at a timestamp past everything. *)
    assert (Hlt : forall (W : View), vle W (ra_c c) -> W o f <= S (ra_c c o f))
      by (intros W Hle; exact (Nat.le_trans _ _ _ (Hle o f)
                                 (Nat.le_succ_diag_r _))).
    repeat apply conj.
    + intros t'. destruct (Nat.eq_dec t' t) as [-> | Hne].
      * exact (vle_set_both _ _ o f _ (Hv t)).
      * exact (vle_set_r _ _ o f _ (Hv t') (Hlt _ (Hv t'))).
    + intros q g j. case_decide as He.
      * destruct b; [exact (vle_set_both _ _ o f _ (Hv t)) | apply vle_bot].
      * exact (vle_set_r _ _ o f _ (Hm q g j) (Hlt _ (Hm q g j))).
    + intros q g j. case_decide as He; [| exact (Hself q g j)].
      injection He as -> -> ->.
      destruct b; [rewrite set_at_here; apply Nat.le_refl | apply Nat.le_0_l].
    + intros q g. case_decide as He; [| exact (Hzero q g)].
      exfalso. injection He as -> -> Hk.
      exact (Nat.neq_succ_0 _ (eq_sym Hk)).
  - (* a read *)
    repeat apply conj; [| exact Hm | exact Hself | exact Hzero].
    intros t'. destruct (Nat.eq_dec t' t) as [-> | Hne]; [| exact (Hv t')].
    intros q g. unfold after_read. case_decide as He;
      [injection He as -> ->; exact H0
       | apply Nat.max_lub; [apply Hv | apply Hm]].
Qed.

Print Assumptions rastep_ok.

(** ** The invariant that makes publication work

    A view is *closed* when, at every cell, it has already acquired what was
    released with the message it is at.  The invariant is that every thread's
    view is closed and so is every published one --- the second clause being
    the transitivity release-acquire exists for, and what carries knowledge
    along a chain of links rather than one link only. *)
Definition Closed (c : RAConf) (V : View) : Prop :=
  forall q g, vle (ra_relm c q g (V q g)) V.

Definition RAClosed (c : RAConf) : Prop :=
  (forall t, Closed c (ra_v c t)) /\ (forall o f k, Closed c (ra_relm c o f k)).

(** A write lands at a timestamp past everything, so it cannot change what any
    existing view or published view is closed against. *)
Lemma relm_untouched c o f k X (W : View) :
  ra_c c o f < k -> vle W (ra_c c) ->
  forall q g, upd_m (ra_relm c) o f k X q g (W q g) = ra_relm c q g (W q g).
Proof.
  intros Hlt Hle q g. unfold upd_m. case_decide as He; [| reflexivity].
  injection He as -> -> Hk. exfalso.
  pose proof (Hle o f) as Hb. rewrite Hk in Hb.
  exact (Nat.lt_irrefl _ (Nat.le_lt_trans _ _ _ Hb Hlt)).
Qed.

Theorem rastep_closed t c c' :
  rastep t c c' -> ra_ok c -> RAClosed c -> RAClosed c'.
Proof.
  intros Hst (Hv & Hm & Hself & Hzero) [Hcv Hcm]. destruct Hst;
    unfold RAClosed, Closed; cbn [ra_h ra_c ra_v ra_relm].
  - (* a write *)
    set (k := S (ra_c c o f)).
    set (V' := set_at (ra_v c t) o f k).
    assert (HVle : vle (ra_v c t) V').
    { apply vle_set_r; [apply vle_refl |].
      exact (Nat.le_trans _ _ _ (Hv t o f) (Nat.le_succ_diag_r _)). }
    (* the writer's new view is closed against whatever it published, provided
       what it published is no further along than the view itself *)
    assert (HclV : forall (X : View), vle X V' ->
              forall q g, vle (upd_m (ra_relm c) o f k X q g (V' q g)) V').
    { intros X HXle q g. destruct (decide ((q, g) = (o, f))) as [He | He].
      - injection He as -> ->. unfold V' at 1. rewrite set_at_here.
        assert (Hh : upd_m (ra_relm c) o f k X o f k = X)
          by (unfold upd_m; by rewrite decide_True).
        rewrite Hh. exact HXle.
      - unfold V' at 1. rewrite (set_at_there (ra_v c t) o f k q g He).
        rewrite (relm_untouched c o f k X (ra_v c t)
                   (Nat.lt_succ_diag_r _) (Hv t) q g).
        intros a b0. exact (Nat.le_trans _ _ _ (Hcv t q g a b0) (HVle a b0)). }
    split.
    + intros t'. unfold upd_v. destruct (Nat.eq_dec t' t) as [-> | Hne].
      * apply HclV. destruct b; [apply vle_refl | apply vle_bot].
      * intros q g. rewrite (relm_untouched c o f k (if b then V' else bot)
                               (ra_v c t') (Nat.lt_succ_diag_r _) (Hv t') q g).
        exact (Hcv t' q g).
    + intros q g j. destruct (decide ((q, g, j) = (o, f, k))) as [He | He].
      * injection He as -> -> ->.
        assert (Hh : upd_m (ra_relm c) o f k (if b then V' else bot) o f k
                     = (if b then V' else bot))
          by (unfold upd_m; by rewrite decide_True).
        rewrite Hh. destruct b; cbn iota.
        -- apply HclV. apply vle_refl.
        -- intros a b0.
           rewrite (relm_untouched c o f k bot bot
                      (Nat.lt_succ_diag_r _) (vle_bot _) a b0).
           unfold bot at 1. rewrite (Hzero a b0). apply vle_bot.
      * assert (Hq : upd_m (ra_relm c) o f k (if b then V' else bot) q g j
                     = ra_relm c q g j)
          by (unfold upd_m; by rewrite decide_False).
        rewrite Hq. intros a b0.
        rewrite (relm_untouched c o f k (if b then V' else bot)
                   (ra_relm c q g j) (Nat.lt_succ_diag_r _) (Hm q g j) a b0).
        exact (Hcm q g j a b0).
  - (* a read.  The reader's new view is closed because the message's view is,
       and because the message does not claim to be past itself. *)
    set (W := ra_relm c o f k). set (V' := after_read (ra_v c t) W o f k).
    assert (HW : vle W V').
    { intros q g. unfold V', after_read. case_decide as He;
        [injection He as -> ->; exact (Hself o f k) | apply Nat.le_max_r]. }
    assert (HVV : vle (ra_v c t) V').
    { intros q g. unfold V', after_read. case_decide as He;
        [injection He as -> ->; exact H | apply Nat.le_max_l]. }
    split; [| exact Hcm].
    intros t'. unfold upd_v. destruct (Nat.eq_dec t' t) as [-> | Hne];
      [| exact (Hcv t')].
    intros q g. unfold V' at 1. unfold after_read. case_decide as He.
    + injection He as -> ->. exact HW.
    + destruct (Nat.max_spec (ra_v c t q g) (W q g)) as [[_ Hmx] | [_ Hmx]];
        rewrite Hmx.
      * intros a b0. exact (Nat.le_trans _ _ _ (Hcm o f k q g a b0) (HW a b0)).
      * intros a b0. exact (Nat.le_trans _ _ _ (Hcv t q g a b0) (HVV a b0)).
Qed.

Print Assumptions rastep_closed.

(** ** Runs *)
Definition rastep_any (c c' : RAConf) : Prop := exists t, rastep t c c'.

Theorem rarun c c' :
  rtc rastep_any c c' -> ra_ok c -> RAClosed c -> ra_ok c' /\ RAClosed c'.
Proof.
  induction 1 as [| a b0 d [t Hab] Hbd IH]; intros Hok Hcl; [by split |].
  exact (IH (rastep_ok t a b0 Hab Hok) (rastep_closed t a b0 Hab Hok Hcl)).
Qed.

(** The initial configuration: every cell holds null at timestamp zero, nobody
    has gone anywhere, and nothing has been published. *)
Definition ra0 : RAConf :=
  MkRA (fun _ _ k => if Nat.eqb k 0 then Some VNull else None)
       bot (fun _ => bot) (fun _ _ _ => bot).

Lemma ra0_ok : ra_ok ra0.
Proof.
  repeat apply conj; try (intros; apply vle_refl); [| intros; reflexivity].
  intros o f k. apply Nat.le_0_l.
Qed.

Lemma ra0_closed : RAClosed ra0.
Proof. split; intros; intros q g; apply vle_refl. Qed.

Print Assumptions rarun.

(** ** Publication, as a theorem about runs

    A thread that has read a message is at least as far along as whoever wrote
    it was.  That is the whole of release-acquire, and here it is the
    invariant, so the theorem is immediate and the work was in showing the
    steps preserve it. *)
Theorem ra_publication c t o f :
  RAClosed c -> vle (ra_relm c o f (ra_v c t o f)) (ra_v c t).
Proof. intros [Hcv _]. exact (Hcv t o f). Qed.

(** And what a reader gets out of it.  The two extra hypotheses are the
    programmer's, and naming them is half the point: the publisher had
    initialised the field, and nothing has rewritten it since.  The second is
    RCU's own discipline --- a node's fields are written while it is \frsh{}
    and not after --- so both are conditions the type system already enforces
    on the write side. *)
Corollary ra_reader_sees c t o f n g v :
  ra_ok c -> RAClosed c ->
  seen c t o f = Some (VLoc n) ->
  ra_h c n g (ra_relm c o f (ra_v c t o f) n g) = Some v ->
  (forall j, ra_relm c o f (ra_v c t o f) n g <= j -> j <= ra_c c n g ->
     ra_h c n g j = Some v) ->
  seen c t n g = Some v.
Proof.
  intros (Hv & _ & _ & _) Hcl Hsee Hpub Hstable. unfold seen.
  exact (Hstable (ra_v c t n g) (ra_publication c t o f Hcl n g) (Hv t n g)).
Qed.

Print Assumptions ra_publication.
Print Assumptions ra_reader_sees.

(** ** That the release is necessary, and not by argument

    The same run twice, differing in one bit: whether the link is published
    with a releasing write or a relaxed one.  The writer initialises node 5's
    field, links it at 3.0, and a reader follows the link.  With the release
    the reader sees the initialised field; without it the reader sees the link
    and the node's field as it was before initialisation.

    That second run is a well-formed run of the semantics.  Nothing about it is
    ruled out by the model; it is ruled out by the discipline, which is what
    [rcu_assign_pointer] is for. *)
Definition step_w (c : RAConf) (t : TID) (o : Loc) (f : FName) (v : Val)
    (b : bool) : RAConf :=
  MkRA (write (ra_h c) o f (S (ra_c c o f)) v)
       (set_at (ra_c c) o f (S (ra_c c o f)))
       (upd_v (ra_v c) t (set_at (ra_v c t) o f (S (ra_c c o f))))
       (upd_m (ra_relm c) o f (S (ra_c c o f))
          (if b then set_at (ra_v c t) o f (S (ra_c c o f)) else bot)).

Definition step_r (c : RAConf) (t : TID) (o : Loc) (f : FName) (k : nat)
  : RAConf := MkRA (ra_h c) (ra_c c)
       (upd_v (ra_v c) t (after_read (ra_v c t) (ra_relm c o f k) o f k))
       (ra_relm c).

Lemma step_w_step t c o f v b : rastep t c (step_w c t o f v b).
Proof. exact (RA_write t o f v b c). Qed.

Lemma step_r_step t c o f k v :
  ra_v c t o f <= k -> k <= ra_c c o f -> ra_h c o f k = Some v ->
  rastep t c (step_r c t o f k).
Proof. intros H1 H2 H3. exact (RA_read t o f k v c H1 H2 H3). Qed.

(* writer 0 initialises node 5's field 0, then links it at 3.0; reader 1
   follows the link *)
Definition rc1 : RAConf := step_w ra0 0%nat 5%nat 0%nat (VLoc 9%nat) false.
Definition rc2 (b : bool) : RAConf :=
  step_w rc1 0%nat 3%nat 0%nat (VLoc 5%nat) b.
Definition run (b : bool) : RAConf := step_r (rc2 b) 1%nat 3%nat 0%nat 1.

Theorem release_is_necessary :
  (* both are runs of the semantics *)
  (forall b, rtc rastep_any ra0 (run b))
  (* with the release, the reader sees the initialised field *)
  /\ seen (run true) 1%nat 5%nat 0%nat = Some (VLoc 9%nat)
  (* without it, it sees the link and the field as it was before *)
  /\ seen (run false) 1%nat 5%nat 0%nat = Some VNull
  (* and in both it does see the link *)
  /\ (forall b, seen (run b) 1%nat 3%nat 0%nat = Some (VLoc 5%nat)).
Proof.
  assert (Hrun : forall b, rtc rastep_any ra0 (run b)).
  { intros b.
    eapply rtc_l with (y := rc1);
      [exists 0%nat; unfold rc1; apply step_w_step |].
    eapply rtc_l with (y := rc2 b);
      [exists 0%nat; unfold rc2; apply step_w_step |].
    eapply rtc_l with (y := run b); [| apply rtc_refl].
    exists 1%nat. unfold run.
    apply (step_r_step 1%nat (rc2 b) 3%nat 0%nat 1 (VLoc 5%nat));
      [apply Nat.le_0_l | apply Nat.le_refl | destruct b; reflexivity]. }
  repeat apply conj; [exact Hrun | reflexivity | reflexivity |].
  intros b. destruct b; reflexivity.
Qed.

Print Assumptions release_is_necessary.

(** ** From a weak run to the sequentially consistent invariants

    The last step is the one the earlier sections were owed: a theorem relating
    a run of this semantics to the invariants of the rest of the development.

    It needs one restriction.  That restriction is lifted further down, once
    the *discipline* is in the picture rather than the bare semantics, and the
    version below is superseded by
    [weak_run_is_sound_under_the_discipline]; we keep it because the two
    together say what the discipline is worth.  A thread's view is a sub-heap
    of the *current* heap only where nothing has been overwritten since the
    thread last looked.  For a cell written once ---
    a node's fields, which RCU writes while the node is \frsh{} and not after
    --- that holds, and it is exactly the class of cells publication is about.
    For a cell written twice --- a link, which is the operation --- it fails,
    and what protects a reader holding the old link is not the memory model at
    all but the grace period.  That half is already proved, sequentially, and
    the whole design of RCU is that it has to be: no amount of synchronisation
    makes a stale link safe; only not reclaiming does.

    So the theorem below is about the write-once cells, and the division of
    labour it makes explicit is the one the system actually has. *)

Definition ra_now (c : RAConf) : Heap := fun o f => ra_h c o f (ra_c c o f).

(** A cell all of whose messages agree: written once, or rewritten with what
    was already there. *)
Definition WriteOnce (c : RAConf) (o : Loc) (f : FName) : Prop :=
  forall j k, j <= ra_c c o f -> k <= ra_c c o f -> ra_h c o f j = ra_h c o f k.

Theorem stable_cells_are_shared c t :
  ra_ok c -> (forall o f, WriteOnce c o f) ->
  sub_heap (ra_heap c t) (ra_now c).
Proof.
  intros (Hv & _ & _ & _) Hw o f v Hv'. unfold ra_now.
  rewrite <- (Hw o f (ra_v c t o f) (ra_c c o f) (Hv t o f) (Nat.le_refl _)).
  exact Hv'.
Qed.

(** The programmer's obligation, as a condition on the configuration: whatever
    a thread can see a link to, the publisher of that link had already written
    a field of.  That is initialise-before-publish, which is what the
    \frsh{} discipline enforces on the write side. *)
Definition InitBeforePublish (c : RAConf) : Prop :=
  forall t o f n, ra_heap c t o f = Some (VLoc n) ->
    exists g v, ra_h c n g (ra_relm c o f (ra_v c t o f) n g) = Some v.

(** And then publication holds of every thread's view: the obligation task one
    isolated, discharged by the semantics rather than assumed. *)
Theorem publication_holds c s :
  ra_ok c -> RAClosed c -> (forall o f, WriteOnce c o f) ->
  InitBeforePublish c ->
  Published (MkW s (ra_heap c)).
Proof.
  intros Hok Hcl Hw Hinit t o f n He _.
  pose proof Hok as (Hv & Hm & _ & _).
  destruct (Hinit t o f n He) as [g [v Hpub]].
  exists g, v.
  change (ra_heap c t n g = Some v). unfold ra_heap, seen.
  rewrite (Hw n g (ra_v c t n g) (ra_relm c o f (ra_v c t o f) n g)
             (Hv t n g) (Hm o f (ra_v c t o f) n g)).
  exact Hpub.
Qed.

Print Assumptions stable_cells_are_shared.
Print Assumptions publication_holds.

(** The theorem.  A run of the release-acquire semantics, under the discipline,
    reaches a configuration in which every thread's own view satisfies every
    invariant --- given that the sequentially consistent state whose heap is
    what has been written satisfies them.

    Nineteen of the twenty conjuncts come from the partition of task one and
    cost nothing.  The twentieth is publication, and it comes from the
    semantics.  Nothing is assumed about views here: [ra_ok] and [RAClosed] are
    established at [ra0] and preserved by every step. *)
Theorem weak_run_is_sound FType (s : LState) c :
  rtc rastep_any ra0 c ->
  (forall o f, WriteOnce c o f) ->
  InitBeforePublish c ->
  hp (ms s) = ra_now c ->
  WellFormed FType s ->
  forall t, WellFormed FType (swap_hp s (ra_heap c t)).
Proof.
  intros Hrun Hw Hinit Hhp Hwf t.
  destruct (rarun ra0 c Hrun ra0_ok ra0_closed) as [Hok Hcl].
  apply (views_are_well_formed FType (MkW s (ra_heap c))).
  - intros t'. cbn [w_view w_base]. rewrite Hhp.
    exact (stable_cells_are_shared c t' Hok Hw).
  - exact (publication_holds c s Hok Hcl Hw Hinit).
  - exact Hwf.
Qed.

Print Assumptions weak_run_is_sound.

(** ** What is now proved, and what a fuller account would still add

    Proved: the semantics, with release, acquire and view defined rather than
    assumed ([rastep]); that its bookkeeping is preserved ([rastep_ok]); that
    the closure release-acquire turns on is preserved ([rastep_closed]), which
    is the part with content; that a reader is therefore at least as far along
    as the publisher of anything it can see ([ra_publication]) and sees what
    the publisher wrote ([ra_reader_sees]); that the release is necessary, by
    exhibiting the same run without it ([release_is_necessary]); and that a run
    under the discipline satisfies every invariant in every thread's view
    ([weak_run_is_sound]).

    Not proved, and worth being exact about rather than leaving as "future
    work".

    First, the restriction to write-once cells in the last theorem.  It is the
    right fragment for publication and the wrong one for links, and the reason
    a link needs no fragment is the grace period, which is proved elsewhere and
    sequentially.  Joining the two --- a reader holding a stale link, protected
    by reclamation rather than by memory ordering --- needs the invariants to
    be carried along a *pair* of runs, the weak one and the SC one it refines,
    and that is the simulation this file does not build.

    Second, the protocol state.  [stale_registrations_are_unsafe] above shows
    the registrations need synchronisation for the opposite reason to the heap,
    and the semantics here is only over the heap.  A registration is a cell
    like any other, so the same three steps would carry it; what is missing is
    the argument that the scan which ends a grace period must acquire each
    registration it reads, which is the mirror of [ra_publication] and which we
    state rather than prove.

    Third, the memory model is release-acquire and not weaker.  Every read here
    acquires and every view only grows, so there is nothing out of thin air to
    rule out, and nothing here would survive a relaxed model unchanged.

    What we would claim is narrower than "RCU is verified under weak memory"
    and, we think, more useful: the single invariant a weak memory model
    endangers is publication, publication is what the releasing write buys, and
    the buying can be written down. *)

(** * The registrations, in the same semantics

    The heap is not the only shared state, and
    [stale_registrations_are_unsafe] above shows the other kind needs
    synchronisation for the opposite reason.  A registration is a cell like any
    other, so the three steps already carry it: the generation counter lives at
    one cell, each thread's registration at another, a reader publishes its
    registration with a releasing write, and the writer's scan reads them with
    acquiring reads.

    What this section settles is which half of that is doing the work.  The
    answer is not the half we expected when we wrote the guess above, and it is
    worth stating because it makes the remaining obligation smaller rather than
    larger. *)

(** Counters live in cells, encoded as locations because that is what a cell
    holds. *)
Definition ctr (c : RAConf) (t : TID) (o : Loc) (f : FName) : nat :=
  match seen c t o f with Some (VLoc k) => k | _ => 0 end.

(** The two cells the protocol uses.  Which they are does not matter; that they
    are ordinary cells is the point. *)
Definition gcell : Loc * FName := (100%nat, 0%nat).
Definition rcell (t : TID) : Loc * FName := (200%nat + t, 0%nat)%nat.

(** A grace period for epoch [e] must wait for a reader that registered at or
    before [e] and has not left.  This is the published model's bounding set,
    read off the counters. *)
Definition overlaps (c : RAConf) (w t : TID) (e : nat) : Prop :=
  ctr c w (rcell t).1 (rcell t).2 <= e.

(** ** A stale generation read is safe

    A reader reads the generation and registers at what it read.  Under a weak
    model it may read a stale generation, and the question is which way that
    errs.  It errs safe: a smaller generation is an *earlier* registration, so
    the reader looks older than it is and a grace period that need not have
    waited for it waits anyway.

    This is the first half of the obligation, and it is discharged by the
    direction of the staleness rather than by any ordering. *)
Theorem stale_generation_is_conservative (gseen gtrue e : nat) :
  gseen <= gtrue -> gtrue <= e -> gseen <= e.
Proof. intros Hle Htrue. exact (Nat.le_trans _ _ _ Hle Htrue). Qed.

Print Assumptions stale_generation_is_conservative.

(** ** A stale registration read is not

    The other direction is the hazard, and it is the operational form of
    [stale_registrations_are_unsafe].  The reader registers; the writer's view
    of that cell is still at the message before, which says the reader was not
    there; the writer concludes the grace period is over.

    The run below is a run of the semantics.  Nothing in the memory model
    forbids it. *)
Definition reg_run : RAConf :=
  (* the reader registers at generation 0 *)
  step_w ra0 1%nat (rcell 1%nat).1 (rcell 1%nat).2 (VLoc 0%nat) true.

Theorem stale_scan_misses_the_reader :
  (* it is a run *)
  rtc rastep_any ra0 reg_run
  (* the reader has registered at generation 0, which a grace period for 0
     must wait for *)
  /\ ctr reg_run 1%nat (rcell 1%nat).1 (rcell 1%nat).2 = 0%nat
  (* and the writer, which has not caught up, sees the cell as it was *)
  /\ seen reg_run 0%nat (rcell 1%nat).1 (rcell 1%nat).2 = Some VNull.
Proof.
  repeat apply conj.
  - eapply rtc_l with (y := reg_run); [| apply rtc_refl].
    exists 1%nat. unfold reg_run. apply step_w_step.
  - reflexivity.
  - reflexivity.
Qed.

Print Assumptions stale_scan_misses_the_reader.

(** ** So the scan has to catch up, and catching up is the assumption we
       already had

    The writer's position at a cell only ever moves forward --- that is
    coherence, and it is built into the read step, which requires the new
    timestamp to be at or after the old.  So a scan that keeps reading has a
    monotonically advancing position at each registration cell, and the only
    thing it needs is to reach the last message.

    That is exactly the fairness assumption the sequentially consistent
    development already reduces the *termination* of the wait to.  So weak
    memory adds no new obligation here: the same assumption that makes
    \textsc{SyncStop} terminate makes it sound.  That is the useful outcome of
    this section, and it is why the earlier guess --- that the registrations
    would need a synchronisation argument of their own --- was wrong in an
    informative way. *)
Theorem reads_only_move_forward t c c' o f :
  ra_ok c -> rastep t c c' -> ra_v c t o f <= ra_v c' t o f.
Proof.
  intros (Hv & _ & _ & _) Hst. destruct Hst; cbn [ra_v]; unfold upd_v;
    destruct (Nat.eq_dec t t) as [_ | Hne]; try (by destruct Hne).
  - unfold set_at. case_decide as He;
      [injection He as -> ->;
       exact (Nat.le_trans _ _ _ (Hv t o0 f0) (Nat.le_succ_diag_r _))
      | apply Nat.le_refl].
  - unfold after_read. case_decide as He;
      [injection He as -> ->; exact H | apply Nat.le_max_l].
Qed.

Print Assumptions reads_only_move_forward.

(** And the scan is sound once it has caught up: if the writer's position at a
    registration cell is the last message, what it reads is what is there. *)
Theorem scan_is_sound_when_current c w t :
  ra_v c w (rcell t).1 (rcell t).2 = ra_c c (rcell t).1 (rcell t).2 ->
  seen c w (rcell t).1 (rcell t).2 = ra_now c (rcell t).1 (rcell t).2.
Proof. intros Hcur. unfold seen, ra_now. by rewrite Hcur. Qed.

Print Assumptions scan_is_sound_when_current.

(** * Reclamation, and the one place weak memory is not the problem

    The memory-safety property is about references held, not about a node's
    own cells: reclaiming [n] is safe when no thread's view contains a link to
    [n].  So the question this semantics has to answer is what it takes for
    that to be true, and the answer separates cleanly into a part the memory
    model supplies and a part it cannot.

    What it supplies: a view contains only values that were written, and a
    thread that has caught up past the unlink does not see the link the unlink
    replaced.  Both are below and both are small.

    What it cannot: a thread that has *not* caught up does see the old link,
    and no amount of synchronisation changes that --- the value was really
    written and the thread really read it.  That is not a defect of the model.
    It is the situation RCU exists for, and the thing that makes it safe is
    that reclamation waits.  The witness at the end is that state, and it is
    worth having because it is the one place in this file where the answer to
    "what does the release buy" is "nothing, and it should not". *)

(** A view holds only what was written. *)
Theorem views_hold_only_written c t o f v :
  ra_ok c -> seen c t o f = Some v ->
  exists k, k <= ra_c c o f /\ ra_h c o f k = Some v.
Proof.
  intros (Hv & _ & _ & _) Hs. exists (ra_v c t o f). split; [apply Hv | exact Hs].
Qed.

(** No message at or after [k] links [o.f] to [n]: the unlink happened at [k]
    and has not been undone. *)
Definition unlinked_since (c : RAConf) (o : Loc) (f : FName) (n : Loc)
    (k : nat) : Prop :=
  forall j, k <= j -> j <= ra_c c o f -> ra_h c o f j <> Some (VLoc n).

(** A thread that has caught up past the unlink cannot see the old link. *)
Theorem caught_up_sees_no_stale_link c t o f n k :
  ra_ok c -> unlinked_since c o f n k -> k <= ra_v c t o f ->
  seen c t o f <> Some (VLoc n).
Proof.
  intros (Hv & _ & _ & _) Hun Hk. unfold seen. apply Hun; [exact Hk | apply Hv].
Qed.

Definition NoLinkTo (c : RAConf) (n : Loc) : Prop :=
  forall t o f, seen c t o f <> Some (VLoc n).

(** And so reclamation is safe exactly when every thread has caught up past
    every unlink of the node.  This is the weak-memory form of what the grace
    period is for, and the quantifier over threads is where the waiting lives. *)
Theorem reclamation_safe_when_caught_up c n (K : Loc -> FName -> nat) :
  ra_ok c ->
  (forall o f, unlinked_since c o f n (K o f)) ->
  (forall t o f, K o f <= ra_v c t o f) ->
  NoLinkTo c n.
Proof.
  intros Hok Hun Hcaught t o f.
  exact (caught_up_sees_no_stale_link c t o f n (K o f) Hok (Hun o f)
           (Hcaught t o f)).
Qed.

Print Assumptions views_hold_only_written.
Print Assumptions caught_up_sees_no_stale_link.
Print Assumptions reclamation_safe_when_caught_up.

(** ** The witness: a stale reader really does hold the old link

    The writer links 5 at 3.0 and then replaces it with 6, both with releasing
    writes --- the strongest thing the model has.  A reader that read the cell
    before the replacement holds a reference to 5, and 5 is now unreachable
    from the current heap.  Reclaiming it at this point would be unsafe, and
    nothing about the memory model says so.

    That is the division of labour the whole development is about, made
    visible in one run: publication is bought with a release, and reclamation
    is bought by waiting. *)
Definition unlink_run : RAConf :=
  step_w (step_w ra0 0%nat 3%nat 0%nat (VLoc 5%nat) true)
         0%nat 3%nat 0%nat (VLoc 6%nat) true.

Definition stale_reader : RAConf := step_r unlink_run 1%nat 3%nat 0%nat 1.

Theorem the_grace_period_is_what_makes_this_safe :
  (* it is a run *)
  rtc rastep_any ra0 stale_reader
  (* the current heap has the new link *)
  /\ ra_now stale_reader 3%nat 0%nat = Some (VLoc 6%nat)
  (* and the reader is holding the old one *)
  /\ seen stale_reader 1%nat 3%nat 0%nat = Some (VLoc 5%nat)
  (* so node 5 is referenced by a thread although nothing reachable points at
     it, which is precisely the state reclamation must not act on *)
  /\ ~ NoLinkTo stale_reader 5%nat.
Proof.
  repeat apply conj.
  - eapply rtc_l with (y := step_w ra0 0%nat 3%nat 0%nat (VLoc 5%nat) true);
      [exists 0%nat; apply step_w_step |].
    eapply rtc_l with (y := unlink_run);
      [exists 0%nat; unfold unlink_run; apply step_w_step |].
    eapply rtc_l with (y := stale_reader); [| apply rtc_refl].
    exists 1%nat. unfold stale_reader.
    apply (step_r_step 1%nat unlink_run 3%nat 0%nat 1 (VLoc 5%nat));
      [apply Nat.le_0_l | apply Nat.le_succ_diag_r | reflexivity].
  - reflexivity.
  - reflexivity.
  - intros H. exact (H 1%nat 3%nat 0%nat eq_refl).
Qed.

Print Assumptions the_grace_period_is_what_makes_this_safe.


(** * The discipline, and what it buys

    [weak_run_is_sound] is restricted to write-once cells, and the obvious next
    move is to lift the restriction by finding a run whose reader holds a view
    that was never the heap.  We tried, and it cannot be done --- which is the
    better outcome, and this section is why.

    A view selects, per cell, one of the values that cell has held, and nothing
    in the semantics makes that selection coherent across cells.  But the
    semantics is not what RCU runs under.  RCU runs under a discipline: one
    writer at a time, holding the lock; every link it writes published with a
    releasing write; readers that only read, and acquire when they do.  Under
    that discipline a releasing write publishes the writer's *whole* knowledge,
    so a reader acquiring any message becomes current on everything the writer
    knew at that moment --- and since there is only one writer, those moments
    are totally ordered.

    The consequence is the theorem below: **every reader's view is one of the
    writer's past views**.  A reader is therefore always looking at a heap the
    writer really had, not at a mixture, and every invariant transfers with no
    restriction on which cells are written twice.

    That is what lets the bridge be stated properly.  The write-once
    restriction was an artefact of proving the wrong thing. *)

Definition veq (V W : View) : Prop := forall o f, V o f = W o f.

(** The discipline as a step relation: writes are the writer's and release,
    reads are the readers' and acquire. *)
Inductive dstep (w : TID) : RAConf -> RAConf -> Prop :=
| D_write o f v c :
    dstep w c
      (MkRA (write (ra_h c) o f (S (ra_c c o f)) v)
            (set_at (ra_c c) o f (S (ra_c c o f)))
            (upd_v (ra_v c) w (set_at (ra_v c w) o f (S (ra_c c o f))))
            (upd_m (ra_relm c) o f (S (ra_c c o f))
               (set_at (ra_v c w) o f (S (ra_c c o f)))))
| D_read t o f k v c :
    t <> w ->
    ra_v c t o f <= k -> k <= ra_c c o f -> ra_h c o f k = Some v ->
    dstep w c
      (MkRA (ra_h c) (ra_c c)
            (upd_v (ra_v c) t
               (after_read (ra_v c t) (ra_relm c o f k) o f k))
            (ra_relm c)).

Lemma dstep_rastep w c c' : dstep w c c' -> exists t, rastep t c c'.
Proof.
  intros [o f v c0 | t o f k v c0 Hne Hle Hk Hh].
  - exists w. exact (RA_write w o f v true c0).
  - exists t. exact (RA_read t o f k v c0 Hle Hk Hh).
Qed.

Definition dstep_any (w : TID) (c c' : RAConf) : Prop := dstep w c c'.

(** The invariant.  Four clauses, and each is a sentence about the discipline:
    every published view is one the writer has already reached; the published
    views are totally ordered, there being one writer; a published view is at
    its own message; and every reader is at one of them. *)
Definition Disc (w : TID) (c : RAConf) : Prop :=
  (forall o f k, vle (ra_relm c o f k) (ra_v c w))
  /\ (forall o f k o' f' k', vle (ra_relm c o f k) (ra_relm c o' f' k')
                          \/ vle (ra_relm c o' f' k') (ra_relm c o f k))
  /\ (forall o f k, k <= ra_c c o f -> ra_relm c o f k o f = k)
  /\ (forall t, t <> w ->
        exists o f k, k <= ra_c c o f /\ veq (ra_v c t) (ra_relm c o f k)).

Lemma ra0_disc w : Disc w ra0.
Proof.
  repeat apply conj.
  - intros o f k. apply vle_refl.
  - intros o f k o' f' k'. left. apply vle_refl.
  - intros o f k Hk. cbn in Hk |- *. by apply Nat.le_0_r in Hk.
  - intros t _. exists 0%nat, 0%nat, 0%nat.
    split; [apply Nat.le_refl | intros o f; reflexivity].
Qed.

Theorem dstep_disc w c c' :
  dstep w c c' -> ra_ok c -> Disc w c -> Disc w c'.
Proof.
  intros Hst (Hv & Hm & Hself & Hzero) (D1 & D2 & D3 & D4). destruct Hst.
  - (* the writer publishes *)
    set (k := S (ra_c c o f)). set (V' := set_at (ra_v c w) o f k).
    assert (HwV : vle (ra_v c w) V').
    { apply vle_set_r; [apply vle_refl |].
      exact (Nat.le_trans _ _ _ (Hv w o f) (Nat.le_succ_diag_r _)). }
    assert (Hall : forall q g j, vle (upd_m (ra_relm c) o f k V' q g j) V').
    { intros q g j. unfold upd_m. case_decide as He; [apply vle_refl |].
      exact (vle_trans _ _ _ (D1 q g j) HwV). }
    assert (Hgrow : forall q g, ra_c c q g <= set_at (ra_c c) o f k q g).
    { intros q g. unfold set_at. case_decide as He;
        [injection He as -> ->; apply Nat.le_succ_diag_r | apply Nat.le_refl]. }
    repeat apply conj; cbn [ra_v ra_relm ra_c].
    + intros q g j. unfold upd_v.
      destruct (Nat.eq_dec w w) as [_ | Hc]; [| by destruct Hc].
      exact (Hall q g j).
    + intros q g j q' g' j'. unfold upd_m. case_decide as He1; case_decide as He2.
      * left. apply vle_refl.
      * right. exact (vle_trans _ _ _ (D1 q' g' j') HwV).
      * left. exact (vle_trans _ _ _ (D1 q g j) HwV).
      * exact (D2 q g j q' g' j').
    + intros q g j Hj. unfold upd_m. case_decide as He.
      * injection He as -> -> ->. unfold V'. apply set_at_here.
      * apply D3. unfold set_at in Hj. case_decide as He2; [| exact Hj].
        injection He2 as -> ->.
        assert (Hlt : j < k).
        { destruct (Nat.lt_ge_cases j k) as [Hl | Hg]; [exact Hl |].
          exfalso. apply He. by rewrite (Nat.le_antisymm j k Hj Hg). }
        exact (proj1 (Nat.lt_succ_r j (ra_c c o f)) Hlt).
    + intros t Hne. unfold upd_v.
      destruct (Nat.eq_dec t w) as [-> | _]; [by destruct (Hne eq_refl) |].
      destruct (D4 t Hne) as [q [g [j [Hj Heq]]]].
      exists q, g, j.
      assert (Hne' : (q, g, j) <> (o, f, k)).
      { intros He. injection He as -> -> ->. unfold k in Hj.
        exact (Nat.nle_succ_diag_l _ Hj). }
      split; [exact (Nat.le_trans _ _ _ Hj (Hgrow q g)) |].
      intros a b0. rewrite (Heq a b0). unfold upd_m.
      by rewrite decide_False.
  - (* a reader acquires *)
    repeat apply conj; cbn [ra_v ra_relm ra_c]; [| exact D2 | exact D3 |].
    + intros q g j. unfold upd_v.
      destruct (Nat.eq_dec w t) as [-> | _]; [by destruct (H eq_refl) |].
      exact (D1 q g j).
    + intros t' Hne'. unfold upd_v.
      destruct (Nat.eq_dec t' t) as [-> | Hne2]; [| exact (D4 t' Hne')].
      destruct (D4 t H) as [q [g [j [Hj Heq]]]].
      destruct (D2 o f k q g j) as [Hle | Hle].
      * (* the reader was already at least as late as the message *)
        exists q, g, j. split; [exact Hj |].
        intros a b0. unfold after_read. case_decide as He.
        -- injection He as -> ->. rewrite <- (Heq o f).
           apply Nat.le_antisymm; [| exact H0].
           rewrite <- (D3 o f k H1). rewrite (Heq o f). exact (Hle o f).
        -- rewrite <- (Heq a b0). apply Nat.max_l.
           rewrite (Heq a b0). exact (Hle a b0).
      * (* the message is at least as late as where the reader was *)
        exists o, f, k. split; [exact H1 |].
        intros a b0. unfold after_read. case_decide as He.
        -- injection He as -> ->. by rewrite (D3 o f k H1).
        -- apply Nat.max_r. rewrite (Heq a b0). exact (Hle a b0).
Qed.

Print Assumptions dstep_disc.

Lemma drun_disc w c c' :
  rtc (dstep w) c c' -> ra_ok c -> Disc w c -> ra_ok c' /\ Disc w c'.
Proof.
  induction 1 as [| a b0 d Hab Hbd IH]; intros Hok Hd; [by split |].
  destruct (dstep_rastep w a b0 Hab) as [t Ht].
  exact (IH (rastep_ok t a b0 Ht Hok) (dstep_disc w a b0 Hab Hok Hd)).
Qed.

(** The heap a view is looking at. *)
Definition heap_at (c : RAConf) (V : View) : Heap :=
  fun o f => ra_h c o f (V o f).

(** The theorem: under the discipline, a reader is always looking at a heap the
    writer really had. *)
Theorem reader_views_are_past_writer_views w c t :
  rtc (dstep w) ra0 c -> t <> w ->
  exists o f k, k <= ra_c c o f
             /\ forall q g, ra_heap c t q g = heap_at c (ra_relm c o f k) q g.
Proof.
  intros Hrun Hne.
  destruct (drun_disc w ra0 c Hrun ra0_ok (ra0_disc w)) as [Hok Hd].
  destruct Hd as (_ & _ & _ & D4).
  destruct (D4 t Hne) as [o [f [k [Hk Heq]]]].
  exists o, f, k. split; [exact Hk |].
  intros q g. unfold ra_heap, seen, heap_at. by rewrite (Heq q g).
Qed.

Print Assumptions reader_views_are_past_writer_views.

(** Well-formedness does not distinguish pointwise-equal heaps.  Stated rather
    than obtained by extensionality, which this development does not assume. *)
Lemma wf_veq FType s h1 h2 :
  (forall o f, h1 o f = h2 o f) ->
  WellFormed FType (swap_hp s h2) -> WellFormed FType (swap_hp s h1).
Proof.
  intros Heq Hwf.
  assert (Hok : w_ok (MkW (swap_hp s h2) (fun _ => h1)))
    by (intros t' o f v Hv; cbn [w_view w_base]; by rewrite <- Heq).
  assert (Hpub : Published (MkW (swap_hp s h2) (fun _ => h1))).
  { intros t' o f o' He Hnd.
    pose proof Hwf as Hwf2.
    destruct Hwf2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & HD & _).
    destruct (HD o f o') as [g [v Hv]].
    - unfold Edge in He |- *. cbn in He |- *. by rewrite <- Heq.
    - exact Hnd.
    - exists g, v. cbn in Hv |- *. by rewrite Heq. }
  exact (views_are_well_formed FType (MkW (swap_hp s h2) (fun _ => h1))
           Hok Hpub Hwf 0%nat).
Qed.

Print Assumptions wf_veq.

(** And the bridge, without the write-once restriction.  What has to be assumed
    is that the states the writer passed through are well formed --- which is
    the sequentially consistent development's business and is what it proves.
    What is *not* assumed is anything about views. *)
Theorem weak_run_is_sound_under_the_discipline FType w (s : LState) c t :
  rtc (dstep w) ra0 c -> t <> w ->
  (forall o f k, k <= ra_c c o f ->
     WellFormed FType (swap_hp s (heap_at c (ra_relm c o f k)))) ->
  WellFormed FType (swap_hp s (ra_heap c t)).
Proof.
  intros Hrun Hne Hpast.
  destruct (reader_views_are_past_writer_views w c t Hrun Hne)
    as [o [f [k [Hk Heq]]]].
  exact (wf_veq FType s (ra_heap c t) (heap_at c (ra_relm c o f k)) Heq
           (Hpast o f k Hk)).
Qed.

Print Assumptions weak_run_is_sound_under_the_discipline.

(** ** What this replaced

    The earlier bridge asked that no cell be written twice, and said what it
    could about a fragment.  This one asks nothing about cells at all.  The
    difference is not a better proof of the same thing; it is a different
    hypothesis, and the reason the better one is available is that RCU's
    discipline is stronger than the memory model.  A releasing write publishes
    the writer's whole knowledge, and with a single writer those publications
    are totally ordered, so a reader that acquires any of them lands on one of
    them rather than on a mixture.

    That also explains the counterexample we could not build.  We set out to
    show a reader holding a view that was never the heap, and every attempt
    failed at the same step: the acquire pulled the reader forward everywhere,
    not just at the cell it read.  The theorem is why.

    It is worth being clear about what it does not extend to.  Two writers, and
    the publications are no longer a chain; a relaxed write, and the reader
    acquires nothing.  Both are outside the discipline, and both are outside
    what \textsc{ToRCUWrite} permits --- which is the point.  The type system
    is what enforces the hypothesis of this theorem. *)

(** * The kernel's read: dependency ordering rather than acquire

    The semantics above is stronger than Linux, and the difference is not a
    simplification but a defect, so this section repairs it.

    [RA_read] unconditionally unions in the message's release view: every read
    acquires, and there is no relaxed load in the model at all.  Linux is not
    that.  [rcu_assign_pointer] *is* a release store, so the publishing half
    matches; but [rcu_dereference] is [READ_ONCE] plus a compiler barrier, and
    what orders the access is the **address dependency** between loading the
    pointer and loading through it.  An acquire orders the load against
    everything the publisher knew.  A dependency orders it only against
    accesses that use the value --- which is to say, against the target's own
    cells and nothing else.

    So the relation below has three steps: the same releasing write, a relaxed
    read, and a dependency-ordered read that acquires *at the target only*.
    The release-acquire relation is kept beside it rather than replaced,
    because having both is what lets the difference be stated.

    A relaxed read here is of a non-pointer.  That is the discipline, not a
    limitation of the model: reading a pointer without [rcu_dereference] is the
    bug [rcu_dereference] exists to prevent, and in a language with scalars the
    condition would read "scalars may be loaded relaxed, pointers may not". *)

(** Acquire, restricted to one node's cells. *)
Definition at_node (V W : View) (n : Loc) : View :=
  fun q g => if decide (q = n) then Nat.max (V q g) (W q g) else V q g.

Inductive kstep : TID -> RAConf -> RAConf -> Prop :=
(** The same write, releasing or not. *)
| K_write t o f v (b : bool) c :
    kstep t c
      (MkRA (write (ra_h c) o f (S (ra_c c o f)) v)
            (set_at (ra_c c) o f (S (ra_c c o f)))
            (upd_v (ra_v c) t (set_at (ra_v c t) o f (S (ra_c c o f))))
            (upd_m (ra_relm c) o f (S (ra_c c o f))
               (if b then set_at (ra_v c t) o f (S (ra_c c o f)) else bot)))
(** [READ_ONCE] of a non-pointer: the position moves and nothing is acquired. *)
| K_rlx t o f k c :
    ra_v c t o f <= k -> k <= ra_c c o f -> ra_h c o f k = Some VNull ->
    kstep t c
      (MkRA (ra_h c) (ra_c c)
            (upd_v (ra_v c) t (set_at (ra_v c t) o f k))
            (ra_relm c))
(** [rcu_dereference]: the position moves, and the accesses that depend on the
    value --- the target's own cells --- are ordered after the publication.
    Nothing else is. *)
| K_dep t o f k n c :
    ra_v c t o f <= k -> k <= ra_c c o f ->
    ra_h c o f k = Some (VLoc n) ->
    kstep t c
      (MkRA (ra_h c) (ra_c c)
            (upd_v (ra_v c) t
               (at_node (set_at (ra_v c t) o f k) (ra_relm c o f k) n))
            (ra_relm c)).

Theorem kstep_ok t c c' : kstep t c c' -> ra_ok c -> ra_ok c'.
Proof.
  intros Hst (Hv & Hm & Hself & Hzero). destruct Hst; unfold ra_ok;
    cbn [ra_h ra_c ra_v ra_relm]; unfold upd_v.
  - (* a write: the same argument as for the release-acquire relation *)
    assert (Hlt : forall (W : View), vle W (ra_c c) -> W o f <= S (ra_c c o f))
      by (intros W Hle; exact (Nat.le_trans _ _ _ (Hle o f)
                                 (Nat.le_succ_diag_r _))).
    repeat apply conj.
    + intros t'. destruct (Nat.eq_dec t' t) as [-> | Hne];
        [exact (vle_set_both _ _ o f _ (Hv t))
         | exact (vle_set_r _ _ o f _ (Hv t') (Hlt _ (Hv t')))].
    + intros q g j. unfold upd_m. case_decide as He.
      * destruct b; [exact (vle_set_both _ _ o f _ (Hv t)) | apply vle_bot].
      * exact (vle_set_r _ _ o f _ (Hm q g j) (Hlt _ (Hm q g j))).
    + intros q g j. unfold upd_m. case_decide as He; [| exact (Hself q g j)].
      injection He as -> -> ->.
      destruct b; [rewrite set_at_here; apply Nat.le_refl | apply Nat.le_0_l].
    + intros q g. unfold upd_m. case_decide as He; [| exact (Hzero q g)].
      exfalso. injection He as -> -> Hk.
      exact (Nat.neq_succ_0 _ (eq_sym Hk)).
  - (* a relaxed read *)
    repeat apply conj; [| exact Hm | exact Hself | exact Hzero].
    intros t'. destruct (Nat.eq_dec t' t) as [-> | Hne]; [| exact (Hv t')].
    intros q g. unfold set_at. case_decide as He;
      [injection He as -> ->; exact H0 | apply Hv].
  - (* a dependency-ordered read *)
    repeat apply conj; [| exact Hm | exact Hself | exact Hzero].
    intros t'. destruct (Nat.eq_dec t' t) as [-> | Hne]; [| exact (Hv t')].
    intros q g. unfold at_node. case_decide as Hn.
    + apply Nat.max_lub; [| apply Hm].
      unfold set_at. case_decide as He;
        [injection He as -> ->; exact H0 | apply Hv].
    + unfold set_at. case_decide as He;
        [injection He as -> ->; exact H0 | apply Hv].
Qed.

Print Assumptions kstep_ok.

(** ** What dependency ordering gives, and what it does not

    The release-acquire invariant said a thread is at least as far along as the
    publisher of anything it *can see*.  That is not available here, and the
    reason is not a weakness of the proof: under dependency ordering a thread
    may come to hold a link it never dereferenced --- it can be carried forward
    at one cell as a side effect of dereferencing another --- and nothing
    orders the target of a pointer that was never followed.  So the guarantee
    is not a property of a configuration at all.  It is a property of the
    *step*: what a dereference orders is the node it dereferenced.

    That is the right shape and not a concession.  Heap-domain closure, the one
    invariant a weak model endangers, says a thread that can see an edge can
    see the node at the end of it --- and a thread that has not followed the
    edge has no business seeing the node.  The per-dereference statement is
    exactly the obligation, with nothing left over. *)

Lemma k_dep_position (V W : View) n g :
  W n g <= at_node V W n n g.
Proof. unfold at_node. rewrite decide_True by reflexivity. apply Nat.le_max_r. Qed.

(** After a [rcu_dereference] of [n], the reader sees whatever the publisher of
    that pointer had already written into [n].  The two side conditions are the
    programmer's, and they are the same two the release-acquire account needed:
    initialise before publishing, and do not rewrite afterwards. *)
Theorem k_dereference_sees c t o f k n g v :
  ra_ok c ->
  ra_v c t o f <= k -> k <= ra_c c o f -> ra_h c o f k = Some (VLoc n) ->
  ra_h c n g (ra_relm c o f k n g) = Some v ->
  (forall j, ra_relm c o f k n g <= j -> j <= ra_c c n g ->
     ra_h c n g j = Some v) ->
  seen (MkRA (ra_h c) (ra_c c)
          (upd_v (ra_v c) t
             (at_node (set_at (ra_v c t) o f k) (ra_relm c o f k) n))
          (ra_relm c)) t n g = Some v.
Proof.
  intros (Hv & Hm & _ & _) Hle Hk Hlink Hpub Hstable.
  unfold seen. cbn [ra_h ra_v]. unfold upd_v.
  destruct (Nat.eq_dec t t) as [_ | Hc]; [| by destruct Hc].
  apply Hstable; [apply k_dep_position |].
  unfold at_node. case_decide as Hn; [| unfold set_at; case_decide as He;
    [injection He as -> ->; exact Hk | apply Hv]].
  apply Nat.max_lub; [| apply Hm].
  unfold set_at. case_decide as He;
    [injection He as -> ->; exact Hk | apply Hv].
Qed.

Print Assumptions k_dereference_sees.

(** ** What the weaker read costs

    Under release-acquire we could not build a reader whose view had never been
    the heap: every attempt failed because the acquire pulled the reader
    forward everywhere.  Under dependency ordering it builds immediately, and
    that is the precise statement of what acquire was buying.

    The writer points the root's second field at 5, then at 6, then points the
    first field at 5.  At every moment the two fields point at different nodes,
    so unique-paths holds throughout.  A reader that dereferences the second
    field while it still reads 5, and then dereferences the first, is carried
    forward only at node 5's own cells --- not at the root's --- so it keeps
    the stale second field.  Its view has both fields pointing at 5, which no
    state ever had, and in it 5 has two paths. *)

Definition vs (h : Heap) : LState :=
  {| ms    := {| stk := fun _ _ => None; hp := h; lk := None; rt := 0%nat;
                 rds := fun _ => False; bnd := fun _ => False |};
     obsv  := fun _ _ => False;
     undf  := fun _ _ => True;
     thrd  := fun _ => True;
     flist := fun _ => None |}.

Definition kstep_d (c : RAConf) (t : TID) (o : Loc) (f : FName) (k : nat)
    (n : Loc) : RAConf :=
  MkRA (ra_h c) (ra_c c)
       (upd_v (ra_v c) t
          (at_node (set_at (ra_v c t) o f k) (ra_relm c o f k) n))
       (ra_relm c).

Definition kstep_any (c c' : RAConf) : Prop := exists t, kstep t c c'.

Lemma kstep_w_step t c o f v b : kstep t c (step_w c t o f v b).
Proof. exact (K_write t o f v b c). Qed.

Lemma kstep_d_step t c o f k n :
  ra_v c t o f <= k -> k <= ra_c c o f -> ra_h c o f k = Some (VLoc n) ->
  kstep t c (kstep_d c t o f k n).
Proof. intros H1 H2 H3. exact (K_dep t o f k n c H1 H2 H3). Qed.

Definition kw1 : RAConf := step_w ra0 0%nat 0%nat 1%nat (VLoc 5%nat) true.
Definition kw2 : RAConf := step_w kw1 0%nat 0%nat 1%nat (VLoc 6%nat) true.
Definition kw3 : RAConf := step_w kw2 0%nat 0%nat 0%nat (VLoc 5%nat) true.
Definition kd1 : RAConf := kstep_d kw3 1%nat 0%nat 1%nat 1 5%nat.
Definition kv  : RAConf := kstep_d kd1 1%nat 0%nat 0%nat 1 5%nat.

Lemma kv_run : rtc kstep_any ra0 kv.
Proof.
  eapply rtc_l with (y := kw1); [exists 0%nat; unfold kw1; apply kstep_w_step |].
  eapply rtc_l with (y := kw2); [exists 0%nat; unfold kw2; apply kstep_w_step |].
  eapply rtc_l with (y := kw3); [exists 0%nat; unfold kw3; apply kstep_w_step |].
  eapply rtc_l with (y := kd1).
  { exists 1%nat. unfold kd1. apply kstep_d_step;
      [apply Nat.le_0_l | apply Nat.le_succ_diag_r | reflexivity]. }
  eapply rtc_l with (y := kv); [| apply rtc_refl].
  exists 1%nat. unfold kv. apply kstep_d_step;
    [apply Nat.le_0_l | apply Nat.le_refl | reflexivity].
Qed.

Lemma kv_view_f : ra_heap kv 1%nat 0%nat 0%nat = Some (VLoc 5%nat).
Proof. reflexivity. Qed.

Lemma kv_view_g : ra_heap kv 1%nat 0%nat 1%nat = Some (VLoc 5%nat).
Proof. reflexivity. Qed.

Lemma kv_now_f : ra_now kv 0%nat 0%nat = Some (VLoc 5%nat).
Proof. reflexivity. Qed.

Lemma kv_now_g : ra_now kv 0%nat 1%nat = Some (VLoc 6%nat).
Proof. reflexivity. Qed.

Lemma kv_other (q g : nat) :
  (q, g) <> (0%nat, 0%nat) -> (q, g) <> (0%nat, 1%nat) ->
  ra_now kv q g = Some VNull /\ ra_heap kv 1%nat q g = Some VNull.
Proof.
  intros H1 H2. unfold ra_now, ra_heap, seen, kv, kd1, kw3, kw2, kw1, ra0,
    kstep_d, step_w, write, set_at, at_node, upd_v, upd_m, bot.
  cbn [ra_h ra_c ra_v ra_relm].
  destruct (Nat.eq_dec 1%nat 1%nat) as [_ | Hc]; [| by destruct Hc].
  repeat (rewrite decide_False by congruence).
  destruct (decide (q = 5%nat)) as [-> | Hq].
  - rewrite decide_True by reflexivity.
    repeat (rewrite decide_False by congruence). by split.
  - rewrite decide_False by exact Hq.
    repeat (rewrite decide_False by congruence). by split.
Qed.

Theorem dependency_ordering_loses_the_whole_view :
  rtc kstep_any ra0 kv
  /\ ~ UNQR (vs (ra_heap kv 1%nat))
  /\ UNQR (vs (ra_now kv)).
Proof.
  repeat apply conj; [exact kv_run | |].
  - intros H.
    assert (Hf : Reaches (vs (ra_heap kv 1%nat)) [0%nat] 5%nat)
      by (unfold Reaches; cbn [hstar ms hp rt vs];
          by rewrite (kv_view_f : ra_heap kv 1%nat 0%nat 0%nat = _)).
    assert (Hg : Reaches (vs (ra_heap kv 1%nat)) [1%nat] 5%nat)
      by (unfold Reaches; cbn [hstar ms hp rt vs];
          by rewrite (kv_view_g : ra_heap kv 1%nat 0%nat 1%nat = _)).
    pose proof (H [0%nat] [1%nat] 5%nat Hf Hg) as Hc. discriminate.
  - assert (Hpath : forall p o, hstar (ra_now kv) 0%nat p = Some o ->
              (p = [] /\ o = 0%nat) \/ (p = [0%nat] /\ o = 5%nat)
              \/ (p = [1%nat] /\ o = 6%nat)).
    { intros [| a [| b p]] o Hp; cbn [hstar] in Hp.
      - injection Hp as <-. by left.
      - destruct (decide (a = 0%nat)) as [-> | Ha];
          [rewrite kv_now_f in Hp; injection Hp as <-; right; by left |].
        destruct (decide (a = 1%nat)) as [-> | Hb];
          [rewrite kv_now_g in Hp; injection Hp as <-; right; by right |].
        rewrite (proj1 (kv_other 0%nat a ltac:(congruence) ltac:(congruence)))
          in Hp. discriminate.
      - destruct (decide (a = 0%nat)) as [-> | Ha]; [rewrite kv_now_f in Hp |].
        + rewrite (proj1 (kv_other 5%nat b ltac:(congruence) ltac:(congruence)))
            in Hp. discriminate.
        + destruct (decide (a = 1%nat)) as [-> | Hb];
            [rewrite kv_now_g in Hp |].
          * rewrite (proj1 (kv_other 6%nat b ltac:(congruence)
                              ltac:(congruence))) in Hp. discriminate.
          * rewrite (proj1 (kv_other 0%nat a ltac:(congruence)
                              ltac:(congruence))) in Hp. discriminate. }
    intros p p' o Hp Hp'.
    destruct (Hpath p o Hp) as [[Hp1 Ho1] | [[Hp1 Ho1] | [Hp1 Ho1]]];
      destruct (Hpath p' o Hp') as [[Hp2 Ho2] | [[Hp2 Ho2] | [Hp2 Ho2]]];
      subst; try reflexivity; discriminate.
Qed.

Print Assumptions dependency_ordering_loses_the_whole_view.
