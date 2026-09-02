(** * HeapPaths: reachability under a single field update.

    Milestone 2 of the Iris development, on the raw-heap-plus-[hstar] encoding.

    Because the structure is carried as a raw heap rather than a representation
    predicate, UNQR, UNQRT_a, OW and HD stay *assumed* invariants: every atomic
    action must re-establish them by hand.  Each of the three heap-mutating type
    rules -- T-UnlinkH, T-Replace, T-Insert -- performs exactly one field write,
    so the reasoning they all need is the same: how does [hstar] change when one
    edge changes?

    This file answers that once.  The central result is [hstar_upd_dichotomy]:
    after a single write, every path either behaves exactly as it did before, or
    it factors through the written edge.  Everything the action lemmas need
    about path preservation should follow from it, rather than being re-derived
    per rule -- which is what the technical report does, and where its UNQR
    cases wave.

    Checked with Rocq 9.0, axiom-free. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From RCU Require Import WellFormed.

(** ** Single-field update *)

Definition Heap := Loc -> FName -> option Val.

Definition upd (h : Heap) (o : Loc) (f : FName) (v : Val) : Heap :=
  fun o' f' =>
    if Nat.eq_dec o' o then
      if Nat.eq_dec f' f then Some v else h o' f'
    else h o' f'.

Lemma upd_same : forall h o f v, upd h o f v o f = Some v.
Proof.
  intros. unfold upd.
  destruct (Nat.eq_dec o o); [| congruence].
  destruct (Nat.eq_dec f f); [reflexivity | congruence].
Qed.

Lemma upd_other : forall h ou fu v o f,
  (o, f) <> (ou, fu) -> upd h ou fu v o f = h o f.
Proof.
  intros h ou fu v o f Hne. unfold upd.
  destruct (Nat.eq_dec o ou) as [->|]; [| reflexivity].
  destruct (Nat.eq_dec f fu) as [->|]; [| reflexivity].
  congruence.
Qed.

Lemma edge_eq_dec : forall (o f ou fu : nat),
  {(o, f) = (ou, fu)} + {(o, f) <> (ou, fu)}.
Proof. intros. decide equality; apply Nat.eq_dec. Qed.

(** ** Composing paths *)

Lemma hstar_app : forall h p q o,
  hstar h o (p ++ q) =
    match hstar h o p with
    | Some o' => hstar h o' q
    | None    => None
    end.
Proof.
  intros h p. induction p as [|f p IH]; intros q o; simpl.
  - reflexivity.
  - destruct (h o f) as [[o1|]|]; try reflexivity. apply IH.
Qed.

(** ** Avoiding an edge

    [avoids h o p ou fu] says the walk from [o] along [p] in [h] never traverses
    the edge [(ou, fu)].  Stated relative to the *old* heap, which is what makes
    it usable as a hypothesis about an update yet to be performed. *)

Fixpoint avoids (h : Heap) (o : Loc) (p : list FName) (ou : Loc) (fu : FName)
  : Prop :=
  match p with
  | []      => True
  | f :: p' => (o, f) <> (ou, fu)
               /\ match h o f with
                  | Some (VLoc o') => avoids h o' p' ou fu
                  | _              => True
                  end
  end.

Lemma avoids_dec : forall h o p ou fu,
  {avoids h o p ou fu} + {~ avoids h o p ou fu}.
Proof.
  intros h o p. revert o.
  induction p as [|f p IH]; intros o ou fu.
  - left. exact I.
  - destruct (edge_eq_dec o f ou fu) as [Eq|Hne].
    + right. simpl. intros [H _]. contradiction.
    + destruct (h o f) as [[o1|]|] eqn:E.
      * destruct (IH o1 ou fu) as [Y|N].
        -- left.  simpl. rewrite E. split; assumption.
        -- right. simpl. rewrite E. intros [_ HA]. contradiction.
      * left. simpl. rewrite E. split; [assumption | exact I].
      * left. simpl. rewrite E. split; [assumption | exact I].
Qed.

(** A path that avoids the written edge walks identically in the updated heap.
    Note this holds for *any* written value: the path never looks at it. *)
Lemma hstar_upd_avoids : forall h ou fu v p o,
  avoids h o p ou fu -> hstar (upd h ou fu v) o p = hstar h o p.
Proof.
  intros h ou fu v p. induction p as [|f p IH]; intros o Hav.
  - reflexivity.
  - destruct Hav as [Hne Hrest]. simpl.
    rewrite (upd_other h ou fu v o f Hne).
    destruct (h o f) as [[o1|]|]; try reflexivity.
    apply IH. exact Hrest.
Qed.

(** ** Factoring through the written edge *)

Lemma avoids_cons_inv : forall h o f p ou fu,
  (o, f) <> (ou, fu) ->
  ~ avoids h o (f :: p) ou fu ->
  exists o1, h o f = Some (VLoc o1) /\ ~ avoids h o1 p ou fu.
Proof.
  intros h o f p ou fu Hne Hna.
  destruct (h o f) as [[o1|]|] eqn:E.
  - exists o1. split; [reflexivity |].
    intros Hav. apply Hna. simpl. rewrite E. split; assumption.
  - exfalso. apply Hna. simpl. rewrite E. split; [assumption | exact I].
  - exfalso. apply Hna. simpl. rewrite E. split; [assumption | exact I].
Qed.

(** A path that does *not* avoid the edge splits at its first traversal of it.
    No reachability hypothesis is needed: if the walk dies before reaching the
    edge then it avoids it vacuously.

    The prefix [p1] is the walk up to the *first* traversal, so it avoids the
    edge itself.  That extra conjunct is what lets the factored case be walked
    in the updated heap as well as the old one, which [hstar_upd_through] needs. *)
Lemma avoids_false_factors : forall h ou fu p o,
  ~ avoids h o p ou fu ->
  exists p1 p2, p = p1 ++ fu :: p2
                /\ hstar h o p1 = Some ou
                /\ avoids h o p1 ou fu.
Proof.
  intros h ou fu p. induction p as [|f p IH]; intros o Hna.
  - exfalso. apply Hna. exact I.
  - destruct (edge_eq_dec o f ou fu) as [Eq|Hne].
    + injection Eq as -> ->. exists [], p.
      split; [reflexivity | split; [reflexivity | exact I]].
    + destruct (avoids_cons_inv h o f p ou fu Hne Hna) as [o1 [Hf Hna1]].
      destruct (IH o1 Hna1) as [p1 [p2 [-> [Hreach Hav1]]]].
      exists (f :: p1), p2. split; [reflexivity | split].
      * simpl. rewrite Hf. exact Hreach.
      * simpl. rewrite Hf. split; assumption.
Qed.

(** ** The dichotomy

    After a single field write, every path either behaves exactly as before, or
    factors through the written edge.  This is the lemma the three heap-mutation
    rules should be discharged against. *)
Theorem hstar_upd_dichotomy : forall h ou fu v p o,
  hstar (upd h ou fu v) o p = hstar h o p
  \/ (exists p1 p2, p = p1 ++ fu :: p2
                    /\ hstar h o p1 = Some ou
                    /\ avoids h o p1 ou fu).
Proof.
  intros h ou fu v p o.
  destruct (avoids_dec h o p ou fu) as [Y|N].
  - left.  apply hstar_upd_avoids. exact Y.
  - right. apply avoids_false_factors. exact N.
Qed.

(** ** Consequences

    The immediate payoff: writing to a node that the root cannot reach leaves
    reachability wholly unchanged. *)
Corollary hstar_upd_unreachable : forall h root ou fu v,
  (forall p, hstar h root p <> Some ou) ->
  forall p, hstar (upd h ou fu v) root p = hstar h root p.
Proof.
  intros h root ou fu v Hunreach p.
  destruct (hstar_upd_dichotomy h ou fu v p root) as [Heq | [p1 [p2 [_ [Hr _]]]]].
  - exact Heq.
  - exfalso. exact (Hunreach p1 Hr).
Qed.

(** UNQR at the level of heaps, which is what the LState-level UNQR of
    WellFormed.v unfolds to once [rt] and [hp] are projected. *)
Definition UNQR_h (h : Heap) (root : Loc) : Prop :=
  forall p p' o, hstar h root p = Some o -> hstar h root p' = Some o -> p = p'.

(** The tree shape survives a write to an unreachable node.  This is exactly the
    T-WriteFH case: the writer sets a field of a [rcuFresh] object, which FR
    guarantees no heap edge reaches.  It is the one heap mutation for which UNQR
    preservation is unconditional. *)
Corollary UNQR_h_upd_unreachable : forall h root ou fu v,
  UNQR_h h root ->
  (forall p, hstar h root p <> Some ou) ->
  UNQR_h (upd h ou fu v) root.
Proof.
  intros h root ou fu v HU Hunreach p p' o H1 H2.
  rewrite (hstar_upd_unreachable h root ou fu v Hunreach p)  in H1.
  rewrite (hstar_upd_unreachable h root ou fu v Hunreach p') in H2.
  exact (HU p p' o H1 H2).
Qed.

(** Connecting FR to the side condition above: FR's first clause says no heap
    edge targets a fresh node, and [hstar] can only land on a node that some
    edge targets -- unless the path is empty, i.e. the node is the root itself.
    So a fresh node distinct from the root is unreachable. *)
Lemma no_incoming_unreachable : forall h root ou,
  (forall o f, h o f <> Some (VLoc ou)) ->
  root <> ou ->
  forall p, hstar h root p <> Some ou.
Proof.
  intros h root ou Hno Hne p. revert root Hne.
  induction p as [|f p IH]; intros root Hne Hcontra.
  - simpl in Hcontra. injection Hcontra as ->. contradiction.
  - simpl in Hcontra.
    destruct (h root f) as [[o1|]|] eqn:E; try discriminate.
    destruct (Nat.eq_dec o1 ou) as [->|Hne1].
    + exact (Hno root f E).
    + exact (IH o1 Hne1 Hcontra).
Qed.

(** ** The suffix rewrite

    The statement common to all three heap-mutation rules: once a path is known
    to factor through the written edge, its walk in the updated heap continues
    from the newly written target.  Each rule then differs only in what that
    target is and how the remaining suffix relates to the old heap. *)

Lemma hstar_upd_through : forall h ou fu w p1 p2 o,
  avoids h o p1 ou fu ->
  hstar h o p1 = Some ou ->
  hstar (upd h ou fu (VLoc w)) o (p1 ++ fu :: p2)
    = hstar (upd h ou fu (VLoc w)) w p2.
Proof.
  intros h ou fu w p1 p2 o Hav Hp1.
  rewrite hstar_app.
  rewrite (hstar_upd_avoids h ou fu (VLoc w) p1 o Hav), Hp1.
  simpl. rewrite upd_same. reflexivity.
Qed.

(** Combining the dichotomy with the rewrite: the full characterisation of
    reachability after one field write.  Every heap-mutation rule should be
    discharged against this, rather than re-deriving a path argument. *)
Theorem hstar_upd_char : forall h ou fu w p o,
  hstar (upd h ou fu (VLoc w)) o p = hstar h o p
  \/ exists p1 p2,
       p = p1 ++ fu :: p2
       /\ hstar h o p1 = Some ou
       /\ hstar (upd h ou fu (VLoc w)) o p
          = hstar (upd h ou fu (VLoc w)) w p2.
Proof.
  intros h ou fu w p o.
  destruct (hstar_upd_dichotomy h ou fu (VLoc w) p o)
    as [Heq | [p1 [p2 [-> [Hp1 Hav]]]]].
  - left. exact Heq.
  - right. exists p1, p2. split; [reflexivity | split; [exact Hp1 |]].
    apply hstar_upd_through; assumption.
Qed.

(** ** T-Replace

    [p.f := n] with [n] fresh and [n]'s fields mirroring [o]'s.  Below the
    replacement point the two walks coincide, so paths through the edge are
    preserved in length with [n] substituted for [o]. *)

(** The mirroring hypothesis.

    The type rule's [N1 = N2] is equality of the two *field maps*, which on its
    own is weaker than what is needed here: a field map records only the fields
    that have been read or set, and neither [[| rcuItr rho N |]] nor
    [[| rcuFresh N |]] constrains a field outside [dom(N)], so the subtrees
    could differ on an untracked field.

    T-Replace therefore carries the side condition
    [forall f', FType(f') = RCU -> f' in dom(N1)].  With it, [N1 = N2] pins the
    entire RCU footprint of both nodes and [Mirrors] follows from the
    denotations.  It is not a burden in practice: writing a field of the fresh
    node with T-WriteFH already requires that field to be in the replaced node's
    map, so any replacement that copies every RCU field satisfies it by
    construction -- the BST deletion does.

    [Mirrors] stays a hypothesis here only because this file models the heap and
    not the type system; it is supplied by the rule, not assumed away.  Note
    also that [Heap] carries RCU fields only, so the [forall g] below is the
    quantification over RCU fields that the side condition delivers. *)
Definition Mirrors (h : Heap) (n o : Loc) : Prop := forall g, h n g = h o g.

Lemma hstar_replace_step : forall h P f o n g p,
  Mirrors h n o ->
  n <> P ->
  avoids h o (g :: p) P f ->
  hstar (upd h P f (VLoc n)) n (g :: p) = hstar h o (g :: p).
Proof.
  intros h P f o n g p Hmir Hne Hav.
  destruct Hav as [Hedge Hrest]. simpl.
  rewrite (upd_other h P f (VLoc n) n g)
    by (intro HH; injection HH as HH1 _; contradiction).
  rewrite Hmir.
  destruct (h o g) as [[o1|]|]; try reflexivity.
  apply hstar_upd_avoids. exact Hrest.
Qed.

(** After the replacement, every reachable node is either reached by exactly the
    same path as before, or is [n] itself, reached by the old path to [P]
    extended by [f].

    [Hnoback] -- [P] is not reachable from [o] -- is the tree condition; it is
    what stops the walk below the replacement point from re-entering the written
    edge.  It follows from UNQR (two distinct paths would reach [P]); we take it
    as a hypothesis here and derive it in [UNQR_replace] below. *)
Theorem hstar_replace_char : forall h root P f o n sigma x,
  Mirrors h n o ->
  n <> P ->
  h P f = Some (VLoc o) ->
  (forall tau, hstar h o tau <> Some P) ->
  hstar (upd h P f (VLoc n)) root sigma = Some x ->
  hstar h root sigma = Some x
  \/ (x = n /\ exists p1, sigma = p1 ++ [f] /\ hstar h root p1 = Some P).
Proof.
  intros h root P f o n sigma x Hmir Hne HPf Hnoback Hreach.
  destruct (avoids_dec h root sigma P f) as [Hav|Hna].
  - left. rewrite <- (hstar_upd_avoids h P f (VLoc n) sigma root Hav). exact Hreach.
  - destruct (avoids_false_factors h P f sigma root Hna)
      as [p1 [p2 [-> [Hp1 Hav1]]]].
    rewrite (hstar_upd_through h P f n p1 p2 root Hav1 Hp1) in Hreach.
    destruct p2 as [|g tau].
    + simpl in Hreach. injection Hreach as <-.
      right. split; [reflexivity |].
      exists p1. split; [reflexivity | exact Hp1].
    + left.
      assert (Hav2 : avoids h o (g :: tau) P f).
      { destruct (avoids_dec h o (g :: tau) P f) as [Y|N]; [exact Y | exfalso].
        destruct (avoids_false_factors h P f (g :: tau) o N) as [q1 [_ [_ [Hq _]]]].
        exact (Hnoback q1 Hq). }
      rewrite (hstar_replace_step h P f o n g tau Hmir Hne Hav2) in Hreach.
      rewrite hstar_app, Hp1. simpl. rewrite HPf. exact Hreach.
Qed.

(** UNQR is preserved by T-Replace.

    The two side conditions come from the type rule: [n] is [rcuFresh], so by the
    corrected FR nothing in the heap points to it and it is unreachable; and [P]
    is not reachable from [o] because the structure was a tree. *)
Theorem UNQR_replace : forall h root P f o n,
  UNQR_h h root ->
  Mirrors h n o ->
  n <> P ->
  h P f = Some (VLoc o) ->
  (forall tau, hstar h o tau <> Some P) ->
  (forall sigma, hstar h root sigma <> Some n) ->
  UNQR_h (upd h P f (VLoc n)) root.
Proof.
  intros h root P f o n HU Hmir Hne HPf Hnoback Hfresh sigma sigma' x H1 H2.
  destruct (hstar_replace_char h root P f o n sigma  x Hmir Hne HPf Hnoback H1)
    as [Ha | [Hx1 [q1 [Hs1 Hq1]]]];
  destruct (hstar_replace_char h root P f o n sigma' x Hmir Hne HPf Hnoback H2)
    as [Hb | [Hx2 [q2 [Hs2 Hq2]]]].
  - (* both reached by the same path as before *) exact (HU _ _ _ Ha Hb).
  - (* sigma' reaches the fresh node, sigma reaches it in the old heap too *)
    exfalso. subst x. exact (Hfresh sigma Ha).
  - exfalso. subst x. exact (Hfresh sigma' Hb).
  - (* both are the replaced edge; the path to P is unique *)
    subst sigma sigma'. rewrite (HU q1 q2 P Hq1 Hq2). reflexivity.
Qed.

(** [Hnoback] really does follow from the tree shape, so it is not an extra
    assumption on the caller. *)
Lemma UNQR_no_back_edge : forall h root P f o rho,
  UNQR_h h root ->
  hstar h root rho = Some P ->
  h P f = Some (VLoc o) ->
  forall tau, hstar h o tau <> Some P.
Proof.
  intros h root P f o rho HU Hrho HPf tau Hcontra.
  (* P is reached both by rho and by rho.f.tau, which differ in length. *)
  assert (Hlong : hstar h root (rho ++ f :: tau) = Some P).
  { rewrite hstar_app, Hrho. simpl. rewrite HPf. exact Hcontra. }
  assert (Heq : rho = rho ++ f :: tau) by exact (HU _ _ _ Hrho Hlong).
  assert (Hlen : length rho = length (rho ++ f :: tau)) by (rewrite <- Heq; reflexivity).
  rewrite length_app in Hlen. simpl in Hlen.
  (* length rho = length rho + S (length tau) is impossible *)
  lia.
Qed.

(** ** T-Insert

    [p.f := n] with [n] fresh and one field of [n], namely [f4], already
    pointing back at [o].  Unlike Replace, the path to everything under [o] is
    *lengthened* by one segment: what was reached by [rho.f.tau] is now reached
    by [rho.f.f4.tau].  So the unchanged-path case and the lengthened-path case
    are genuinely different, and ruling out a collision between them needs to
    know that an unchanged path does not traverse the written edge.  Hence: *)

Lemma avoids_app_edge_false : forall h ou fu p1 p2 o,
  hstar h o p1 = Some ou -> ~ avoids h o (p1 ++ fu :: p2) ou fu.
Proof.
  intros h ou fu p1. induction p1 as [|g q IH]; intros p2 o Hp1 Hav.
  - simpl in Hp1. injection Hp1 as <-. destruct Hav as [Hne _]. apply Hne. reflexivity.
  - simpl in Hp1. destruct (h o g) as [[o1|]|] eqn:E; try discriminate.
    destruct Hav as [_ Hrest]. rewrite E in Hrest.
    exact (IH p2 o1 Hp1 Hrest).
Qed.

(** [n]'s only outgoing RCU edge is [f4], pointing at [o].

    The rule supplies [forall f2 in dom(N1). f4 <> f2 -> N1(f2) = null], which
    on its own constrains only the *tracked* fields, leaving a field outside
    [dom(N1)] free to point anywhere and give the inserted node a second child.

    Unlike [Mirrors], this one is closed in the denotation rather than the rule:
    [[| rcuFresh N |]] now also requires every RCU field outside [dom(N)] to be
    null.  That is an invariant of the fresh-node lifecycle rather than a new
    obligation -- T-Alloc establishes it (fresh object, all fields null, empty
    map) and T-WriteFH, the only rule that writes a fresh object's field,
    preserves it by moving exactly the written field into [dom(N)].  Together
    with the rule's null condition it gives [PointsOnlyAt] outright.

    The split is deliberate: T-Insert's obligation is about the *fresh* node, so
    a denotation invariant reaches it, whereas [Mirrors] also constrains the
    pre-existing node, whose untracked fields are legitimately non-null. *)
Definition PointsOnlyAt (h : Heap) (n : Loc) (f4 : FName) (o : Loc) : Prop :=
  h n f4 = Some (VLoc o)
  /\ forall g x, g <> f4 -> h n g <> Some (VLoc x).

Lemma hstar_insert_step : forall h P f o n f4 tau,
  PointsOnlyAt h n f4 o ->
  n <> P ->
  avoids h o tau P f ->
  hstar (upd h P f (VLoc n)) n (f4 :: tau) = hstar h o tau.
Proof.
  intros h P f o n f4 tau [Hf4 _] Hne Hav. simpl.
  rewrite (upd_other h P f (VLoc n) n f4)
    by (intro HH; injection HH as HH1 _; contradiction).
  rewrite Hf4. apply hstar_upd_avoids. exact Hav.
Qed.

(** Any other field of [n] is null, so the walk dies there. *)
Lemma hstar_insert_dead : forall h P f o n f4 g tau,
  PointsOnlyAt h n f4 o ->
  n <> P ->
  g <> f4 ->
  hstar (upd h P f (VLoc n)) n (g :: tau) = None.
Proof.
  intros h P f o n f4 g tau [_ Hnull] Hne Hg. simpl.
  rewrite (upd_other h P f (VLoc n) n g)
    by (intro HH; injection HH as HH1 _; contradiction).
  destruct (h n g) as [[x|]|] eqn:E; try reflexivity.
  exfalso. exact (Hnull g x Hg E).
Qed.

Theorem hstar_insert_char : forall h root P f o n f4 sigma x,
  PointsOnlyAt h n f4 o ->
  n <> P ->
  h P f = Some (VLoc o) ->
  (forall tau, hstar h o tau <> Some P) ->
  hstar (upd h P f (VLoc n)) root sigma = Some x ->
  (hstar h root sigma = Some x /\ avoids h root sigma P f)
  \/ (x = n /\ exists p1, sigma = p1 ++ [f] /\ hstar h root p1 = Some P)
  \/ (exists p1 tau, sigma = p1 ++ f :: f4 :: tau
                     /\ hstar h root p1 = Some P
                     /\ hstar h root (p1 ++ f :: tau) = Some x).
Proof.
  intros h root P f o n f4 sigma x Hn Hne HPf Hnoback Hreach.
  destruct (avoids_dec h root sigma P f) as [Hav|Hna].
  - left. split; [| exact Hav].
    rewrite <- (hstar_upd_avoids h P f (VLoc n) sigma root Hav). exact Hreach.
  - destruct (avoids_false_factors h P f sigma root Hna)
      as [p1 [p2 [-> [Hp1 Hav1]]]].
    rewrite (hstar_upd_through h P f n p1 p2 root Hav1 Hp1) in Hreach.
    destruct p2 as [|g tau].
    + simpl in Hreach. injection Hreach as <-.
      right; left. split; [reflexivity |].
      exists p1. split; [reflexivity | exact Hp1].
    + destruct (Nat.eq_dec g f4) as [->|Hg].
      * right; right.
        assert (Hav2 : avoids h o tau P f).
        { destruct (avoids_dec h o tau P f) as [Y|N]; [exact Y | exfalso].
          destruct (avoids_false_factors h P f tau o N) as [q1 [_ [_ [Hq _]]]].
          exact (Hnoback q1 Hq). }
        rewrite (hstar_insert_step h P f o n f4 tau Hn Hne Hav2) in Hreach.
        exists p1, tau. split; [reflexivity | split; [exact Hp1 |]].
        rewrite hstar_app, Hp1. simpl. rewrite HPf. exact Hreach.
      * exfalso.
        rewrite (hstar_insert_dead h P f o n f4 g tau Hn Hne Hg) in Hreach.
        discriminate.
Qed.

Theorem UNQR_insert : forall h root P f o n f4,
  UNQR_h h root ->
  PointsOnlyAt h n f4 o ->
  n <> P ->
  h P f = Some (VLoc o) ->
  (forall tau, hstar h o tau <> Some P) ->
  (forall sigma, hstar h root sigma <> Some n) ->
  UNQR_h (upd h P f (VLoc n)) root.
Proof.
  intros h root P f o n f4 HU Hn Hne HPf Hnoback Hfresh sigma sigma' x H1 H2.
  destruct (hstar_insert_char h root P f o n f4 sigma  x Hn Hne HPf Hnoback H1)
    as [[Ha Hav] | [[Hx1 [q1 [Hs1 Hq1]]] | [q1 [t1 [Hs1 [Hq1 Hr1]]]]]];
  destruct (hstar_insert_char h root P f o n f4 sigma' x Hn Hne HPf Hnoback H2)
    as [[Hb Hav'] | [[Hx2 [q2 [Hs2 Hq2]]] | [q2 [t2 [Hs2 [Hq2 Hr2]]]]]].
  - (* unchanged / unchanged *) exact (HU _ _ _ Ha Hb).
  - (* unchanged / reaches n *) exfalso. subst x. exact (Hfresh sigma Ha).
  - (* unchanged / lengthened: the unchanged path would have to cross the edge *)
    exfalso. rewrite (HU sigma (q2 ++ f :: t2) x Ha Hr2) in Hav.
    exact (avoids_app_edge_false h P f q2 t2 root Hq2 Hav).
  - exfalso. subst x. exact (Hfresh sigma' Hb).
  - (* both reach n: the path to P is unique *)
    subst sigma sigma'. rewrite (HU q1 q2 P Hq1 Hq2). reflexivity.
  - (* reaches n / lengthened: n would be reachable in the old heap *)
    exfalso. subst x. exact (Hfresh (q2 ++ f :: t2) Hr2).
  - exfalso. rewrite (HU sigma' (q1 ++ f :: t1) x Hb Hr1) in Hav'.
    exact (avoids_app_edge_false h P f q1 t1 root Hq1 Hav').
  - exfalso. subst x. exact (Hfresh (q1 ++ f :: t1) Hr1).
  - (* both lengthened *)
    subst sigma sigma'.
    assert (Hq : q1 = q2) by exact (HU q1 q2 P Hq1 Hq2). subst q2.
    assert (Heq : q1 ++ f :: t1 = q1 ++ f :: t2) by exact (HU _ _ x Hr1 Hr2).
    apply app_inv_head in Heq. injection Heq as ->. reflexivity.
Qed.

(** ** T-UnlinkH

    Writes [x.f1 := r] where [x.f1 = z] and [z.f2 = r], so paths through the
    written edge are *shortened* by one segment: what was reached by
    [rho.f1.f2.tau] is now reached by [rho.f1.tau].

    Structurally this is the mirror image of Insert, and needs strictly fewer
    hypotheses -- there is no fresh node, so nothing to mirror and no
    fields-are-null side condition.  The rule's
    [forall f in dom(N1). f <> f2 -> N1(f) = null] is not needed here: it
    constrains how much of the structure becomes unreachable (one node, not a
    subtree), which is ULKR's business, not UNQR's. *)

(** The general no-back-edge lemma: nothing below a node can reach back to it.
    [UNQR_no_back_edge] above is the one-step instance; unlinking needs the
    two-step one, for [X] against its grandchild [r]. *)
Lemma UNQR_no_back : forall h root X rho delta r,
  UNQR_h h root ->
  hstar h root rho = Some X ->
  delta <> [] ->
  hstar h root (rho ++ delta) = Some r ->
  forall tau, hstar h r tau <> Some X.
Proof.
  intros h root X rho delta r HU Hrho Hd Hr tau Hcontra.
  assert (Hxd : hstar h X delta = Some r)
    by (rewrite hstar_app, Hrho in Hr; exact Hr).
  assert (Hlong : hstar h root (rho ++ delta ++ tau) = Some X)
    by (rewrite hstar_app, Hrho, hstar_app, Hxd; exact Hcontra).
  assert (Heq : rho = rho ++ delta ++ tau) by exact (HU _ _ _ Hrho Hlong).
  assert (Hlen : length rho = length (rho ++ delta ++ tau))
    by (rewrite <- Heq; reflexivity).
  rewrite length_app in Hlen.
  destruct delta as [|d0 dr]; [contradiction | simpl in Hlen]. lia.
Qed.

Theorem hstar_unlink_char : forall h root X f1 z f2 r sigma x,
  h X f1 = Some (VLoc z) ->
  h z f2 = Some (VLoc r) ->
  (forall tau, hstar h r tau <> Some X) ->
  hstar (upd h X f1 (VLoc r)) root sigma = Some x ->
  (hstar h root sigma = Some x /\ avoids h root sigma X f1)
  \/ (exists p1 s2, sigma = p1 ++ f1 :: s2
                    /\ hstar h root p1 = Some X
                    /\ hstar h root (p1 ++ f1 :: f2 :: s2) = Some x).
Proof.
  intros h root X f1 z f2 r sigma x HXf1 Hzf2 Hnoback Hreach.
  destruct (avoids_dec h root sigma X f1) as [Hav|Hna].
  - left. split; [| exact Hav].
    rewrite <- (hstar_upd_avoids h X f1 (VLoc r) sigma root Hav). exact Hreach.
  - destruct (avoids_false_factors h X f1 sigma root Hna)
      as [p1 [s2 [-> [Hp1 Hav1]]]].
    rewrite (hstar_upd_through h X f1 r p1 s2 root Hav1 Hp1) in Hreach.
    assert (Hav2 : avoids h r s2 X f1).
    { destruct (avoids_dec h r s2 X f1) as [Y|N]; [exact Y | exfalso].
      destruct (avoids_false_factors h X f1 s2 r N) as [q1 [_ [_ [Hq _]]]].
      exact (Hnoback q1 Hq). }
    rewrite (hstar_upd_avoids h X f1 (VLoc r) s2 r Hav2) in Hreach.
    right. exists p1, s2. split; [reflexivity | split; [exact Hp1 |]].
    rewrite hstar_app, Hp1. simpl. rewrite HXf1. simpl. rewrite Hzf2. exact Hreach.
Qed.

Theorem UNQR_unlink : forall h root X f1 z f2 r,
  UNQR_h h root ->
  h X f1 = Some (VLoc z) ->
  h z f2 = Some (VLoc r) ->
  (forall tau, hstar h r tau <> Some X) ->
  UNQR_h (upd h X f1 (VLoc r)) root.
Proof.
  intros h root X f1 z f2 r HU HXf1 Hzf2 Hnoback sigma sigma' x H1 H2.
  destruct (hstar_unlink_char h root X f1 z f2 r sigma  x HXf1 Hzf2 Hnoback H1)
    as [[Ha Hav] | [q1 [s1 [Hs1 [Hq1 Hr1]]]]];
  destruct (hstar_unlink_char h root X f1 z f2 r sigma' x HXf1 Hzf2 Hnoback H2)
    as [[Hb Hav'] | [q2 [s2 [Hs2 [Hq2 Hr2]]]]].
  - (* unchanged / unchanged *) exact (HU _ _ _ Ha Hb).
  - (* unchanged / shortened: the unchanged path would have to cross the edge *)
    exfalso. rewrite (HU sigma (q2 ++ f1 :: f2 :: s2) x Ha Hr2) in Hav.
    exact (avoids_app_edge_false h X f1 q2 (f2 :: s2) root Hq2 Hav).
  - exfalso. rewrite (HU sigma' (q1 ++ f1 :: f2 :: s1) x Hb Hr1) in Hav'.
    exact (avoids_app_edge_false h X f1 q1 (f2 :: s1) root Hq1 Hav').
  - (* both shortened *)
    subst sigma sigma'.
    assert (Hq : q1 = q2) by exact (HU q1 q2 X Hq1 Hq2). subst q2.
    assert (Hs : s1 = s2).
    { assert (Heq : q1 ++ f1 :: f2 :: s1 = q1 ++ f1 :: f2 :: s2)
        by exact (HU _ _ x Hr1 Hr2).
      apply app_inv_head in Heq. congruence. }
    rewrite Hs. reflexivity.
Qed.

(** ** Discharging the no-back-edge side conditions

    [UNQR_insert] and [UNQR_unlink] both take a "nothing below the write can
    reach back above it" hypothesis.  Neither is an extra obligation on the
    caller: both follow from the tree shape together with the fact that the
    written node is reachable, which is what the type rules supply.  Stating the
    theorems that way keeps the composition machine-checked rather than
    asserted. *)

Corollary UNQR_insert_reachable : forall h root P f o n f4 rho,
  UNQR_h h root ->
  PointsOnlyAt h n f4 o ->
  hstar h root rho = Some P ->
  h P f = Some (VLoc o) ->
  (forall sigma, hstar h root sigma <> Some n) ->
  UNQR_h (upd h P f (VLoc n)) root.
Proof.
  intros h root P f o n f4 rho HU Hn Hrho HPf Hfresh.
  apply (UNQR_insert h root P f o n f4 HU Hn).
  - (* n <> P: n is unreachable, P is reached by rho *)
    intros <-. exact (Hfresh rho Hrho).
  - exact HPf.
  - exact (UNQR_no_back_edge h root P f o rho HU Hrho HPf).
  - exact Hfresh.
Qed.

Corollary UNQR_unlink_reachable : forall h root X f1 z f2 r rho,
  UNQR_h h root ->
  hstar h root rho = Some X ->
  h X f1 = Some (VLoc z) ->
  h z f2 = Some (VLoc r) ->
  UNQR_h (upd h X f1 (VLoc r)) root.
Proof.
  intros h root X f1 z f2 r rho HU Hrho HXf1 Hzf2.
  apply (UNQR_unlink h root X f1 z f2 r HU HXf1 Hzf2).
  apply (UNQR_no_back h root X rho [f1; f2] r HU Hrho).
  - discriminate.
  - rewrite hstar_app, Hrho. simpl. rewrite HXf1. simpl. rewrite Hzf2.
    reflexivity.
Qed.

(** ** Status

    All three heap-mutating rules preserve the tree shape, each discharged
    against [hstar_upd_char] plus one statement about how the factored suffix is
    rewritten:

      - T-Replace  length-preserving   ([hstar_replace_step])
      - T-Insert   lengthened by one   ([hstar_insert_step])
      - T-UnlinkH  shortened by one    (no step lemma needed)

    What remains for the atomic-action lemmas is the rest of WellFormed --
    the observation map, the free list, and the grace-period invariants -- which
    is ghost state rather than reachability, and belongs with the Iris
    instantiation. *)

Print Assumptions hstar_upd_char.
Print Assumptions UNQR_replace.
Print Assumptions UNQR_insert.
Print Assumptions UNQR_unlink.
Print Assumptions UNQR_insert_reachable.
Print Assumptions UNQR_unlink_reachable.
Print Assumptions UNQR_no_back.
Print Assumptions UNQR_h_upd_unreachable.
