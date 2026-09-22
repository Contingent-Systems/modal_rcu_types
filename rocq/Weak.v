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
From RCU Require Import WellFormed HeapPaths Denotations.

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

Lemma edge_sub s h h' o f o' :
  sub_heap h h' -> Edge (swap_hp s h) o f o' -> Edge (swap_hp s h') o f o'.
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
Theorem shrinking_is_harmless FType s h h' :
  sub_heap h h' ->
  (OW FType (swap_hp s h') -> OW FType (swap_hp s h))
  /\ (ULKR (swap_hp s h') -> ULKR (swap_hp s h))
  /\ (FLR (swap_hp s h') -> FLR (swap_hp s h))
  /\ (FR (swap_hp s h') -> FR (swap_hp s h))
  /\ (FPI FType (swap_hp s h') -> FPI FType (swap_hp s h))
  /\ (UNQRT_a (swap_hp s h') -> UNQRT_a (swap_hp s h))
  /\ (UNQRT_b (swap_hp s h') -> UNQRT_b (swap_hp s h))
  /\ (UNQR (swap_hp s h') -> UNQR (swap_hp s h))
  /\ (FRW (swap_hp s h') -> FRW (swap_hp s h)).
Proof.
  intros Hsub. repeat apply conj.
  - intros H o o' f f' x H1 H2 Hf Hf'.
    exact (H o o' f f' x (Hsub o f _ H1) (Hsub o' f' _ H2) Hf Hf').
  - intros H o o' f' t Hob He.
    exact (H o o' f' t Hob (edge_sub s h h' o' f' o Hsub He)).
  - intros H o o' f' Tr Hfl He.
    exact (H o o' f' Tr Hfl (edge_sub s h h' o' f' o Hsub He)).
  - intros H t x o Hstk Hfr. destruct (H t x o Hstk Hfr) as [Hne Hstk'].
    split; [| exact Hstk'].
    intros o' f' He. exact (Hne o' f' (edge_sub s h h' o' f' o Hsub He)).
  - intros H o f o' t lw Hfr He Hft Hlk.
    exact (H o f o' t lw Hfr (edge_sub s h h' o f o' Hsub He) Hft Hlk).
  - intros H o f He. exact (H o f (edge_sub s h h' o f _ Hsub He)).
  - intros H p o lw Hlk Hr.
    exact (H p o lw Hlk (hstar_sub h h' _ p o Hsub Hr)).
  - intros H p p' o Hr Hr'.
    exact (H p p' o (hstar_sub h h' _ p o Hsub Hr)
             (hstar_sub h h' _ p' o Hsub Hr')).
  - intros H o t Hfr o' f' He.
    exact (H o t Hfr o' f' (edge_sub s h h' o' f' o Hsub He)).
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
