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

    It needs one restriction, and being exact about it is the point.  A
    thread's view is a sub-heap of the *current* heap only where nothing has
    been overwritten since the thread last looked.  For a cell written once ---
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
