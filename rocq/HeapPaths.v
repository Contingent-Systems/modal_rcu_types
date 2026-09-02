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

    NOTE: the type rule states [N1 = N2], equality of the two *field maps*.
    That is weaker than what is needed here.  A field map records only the
    fields that have been read or set, and neither
    [[| rcuItr rho N |]] nor [[| rcuFresh N |]] constrains a field outside
    [dom(N)] -- so [N1 = N2] does not by itself give [forall g, h n g = h o g],
    and the subtrees could differ on an untracked field.  Section 4 says "we
    presume all objects contain all fields", which suggests the intended reading
    is that [N] is total on RCU fields at the point of the rule, but nothing in
    the system enforces it.  Either the rule needs that side condition or the
    denotation needs strengthening.  We take the semantic property as a
    hypothesis and flag the gap. *)
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

(** ** Next targets

    [T-Replace] is done.  The other two mutations differ only in how the
    factored suffix relates to the old heap:

      - T-UnlinkH  writes [x.f1 := r] where [x.f1 = z] and [z.f2 = r].  Paths
        through the written edge are *shortened* by one segment, which is why
        the rule must exclude descendants of [r] -- their recorded paths would
        otherwise go stale.  The analogue of [hstar_replace_step] should say the
        walk from [r] is unchanged; the extra work is that the path *image* is
        no longer the identity, so UNQR needs injectivity of segment deletion.

      - T-Insert   writes [p.f := n] with [n] fresh and one field of [n] already
        pointing back into the structure.  Paths through the edge are
        *lengthened* by one, the case the rule's final implication guards.  This
        should be closest to Replace, with [hstar_replace_step] replaced by a
        version that takes one extra step through [n]. *)

Print Assumptions hstar_upd_char.
Print Assumptions UNQR_replace.
Print Assumptions UNQR_no_back_edge.
Print Assumptions UNQR_h_upd_unreachable.
