Set Implicit Arguments.

Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Aniceto.List.
Section LISTS.

Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.

Fixpoint as_set (l:list A) :=
  match l with
    | cons x l' =>
      if set_mem eq_dec x l'
      then as_set l'
      else x :: (as_set l')
    | nil => nil
  end.

Definition set_length (l:list A) := length (as_set l).

Lemma as_set_simpl:
  forall a l,
  In a l ->
  as_set (a :: l) = as_set l.
Proof.
  intros.
  simpl.
  remember (set_mem eq_dec a l) as x.
  destruct x.
  trivial.
  symmetry in Heqx.
  apply set_mem_correct2 with (Aeq_dec := eq_dec) in H.
  rewrite H in Heqx.
  inversion Heqx.
Qed.

Lemma as_set_in1:
  forall a l,
  In a l ->
  In a (as_set l).
Proof.
  intros.
  induction l.
  - inversion H.
  - simpl.
    remember (set_mem eq_dec a0 l) as x.
    destruct x.
    symmetry in Heqx.
    apply set_mem_correct1 in Heqx.
    inversion H.
    subst.
    apply IHl. assumption.
    apply IHl. assumption.
    symmetry in Heqx.
    simpl.
    inversion H.
    subst.
    intuition.
    right.
    apply IHl.
    assumption.
Qed.

Lemma as_set_in2:
  forall a l,
  In a (as_set l) ->
  In a l.
Proof.
  intros.
  induction l.
  inversion H.
  simpl in *.
  remember (set_mem eq_dec a0 l) as x. symmetry in Heqx.
  destruct x.
  - right. apply IHl.
    assumption.
  - inversion H.
    intuition.
    right. apply IHl.
    assumption.
Qed.

Lemma as_set_def1:
  forall l,
  incl l (as_set l).
Proof.
  intros.
  unfold incl.
  intros.
  apply as_set_in1.
  assumption.
Qed.

Lemma as_set_def2:
  forall l,
  incl (as_set l) l.
Proof.
  intros.
  unfold incl. intros.
  apply as_set_in2.
  assumption.
Qed.

Lemma as_set_no_dup:
  forall l,
  NoDup (as_set l).
Proof.
  intros.
  induction l.
  - apply NoDup_nil.
  - simpl.
    remember (set_mem eq_dec a l) as x. symmetry in Heqx.
    destruct x.
    + assumption.
    + assert (a_nin_l: ~ In a l).
      intuition.
      apply set_mem_correct2 with (Aeq_dec := eq_dec) in H.
      rewrite H in *.
      inversion Heqx.
      apply NoDup_cons.
      intuition.
      apply as_set_in2 in H.
      apply a_nin_l.
      assumption.
      assumption.
Qed.

Lemma as_set_no_dup_simpl:
  forall l,
  NoDup l ->
  as_set l = l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    inversion H; subst.
    remember (set_mem eq_dec a l).
    destruct b.
    + symmetry in Heqb.
      apply (set_mem_complete2 eq_dec)  in H2.
      rewrite H2 in Heqb.
      inversion Heqb.
    + apply IHl in H3.
      rewrite H3.
      auto.
Qed.


(***************************************) 

Definition set_eq (l1:list A) (l2:list A) := (forall x, In x l1 <-> In x l2).

Lemma set_eq_nil:
  set_eq nil nil.
Proof.
  unfold set_eq.
  split; auto.
Qed.

Lemma set_eq_spec:
  forall l1 l2,
  set_eq l1 l2 ->
  (forall x, In x l1 <-> In x l2).
Proof.
  unfold set_eq.
  auto.
Qed.


  Lemma set_eq_refl:
    forall (l:list A),
    set_eq l l.
  Proof.
    intros.
    unfold set_eq.
    intros.
    tauto.
  Qed.

  Lemma set_eq_symm:
    forall (l1 l2:list A),
    set_eq l1 l2 ->
    set_eq l2 l1.
  Proof.
    unfold set_eq; intuition; apply H in H0; eauto.
  Qed.

  Lemma set_eq_def:
    forall (l1 l2:list A),
    incl l1 l2 ->
    incl l2 l1 ->
    set_eq l1 l2.
  Proof.
    unfold incl, set_eq.
    split; intros; eauto.
  Qed.

  Lemma set_eq_to_incl:
    forall (l1 l2:list A),
    set_eq l1 l2 ->
    incl l1 l2.
  Proof.
    unfold set_eq, incl.
    intros.
    apply H in H0.
    assumption.
  Qed.

  Lemma set_eq_to_incl_alt:
    forall (l1 l2:list A),
    set_eq l1 l2 ->
    incl l2 l1.
  Proof.
    unfold set_eq, incl.
    intros.
    apply H in H0.
    assumption.
  Qed.

Theorem exists_no_dup:
  forall l, exists l', set_eq l l' /\ NoDup l'.
Proof.
  intros.
  exists (as_set l).
  split.
  - unfold set_eq.
    intuition.
    apply as_set_def1; assumption.
    apply as_set_def2; assumption.
  - apply as_set_no_dup.
Qed.

Lemma set_eq_perm:
  forall l1 l2,
  NoDup l1 ->
  NoDup l2 ->
  set_eq l1 l2 ->
  length l1 = length l2.
Proof.
  intros.
  unfold set_eq in H1.
  assert (p: Permutation l1 l2).
  apply NoDup_Permutation; repeat auto.
  apply Permutation_length ; repeat auto.
Qed.

Lemma set_length_le:
  forall l1 l2,
  incl l1 l2 ->
  set_length l1 <= set_length l2. 
Proof.
  intros.
  assert (NoDup (as_set l1)) by apply as_set_no_dup.
  assert (NoDup (as_set l2)) by apply as_set_no_dup.
  unfold set_length.
  remember (as_set l1) as l1'.
  remember (as_set l2) as l2'.
  apply no_dup_length_le; auto.
  assert (incl (as_set l1) l1) by apply as_set_def2.
  assert (incl l2 (as_set l2)) by apply as_set_def1.
  subst.
  eauto using incl_tran.
Qed.

Lemma set_length_succ:
  forall a l,
  ~ In a l ->
  set_length (a :: l) = S (set_length l).
Proof.
  intros.
  unfold set_length.
  simpl.
  remember (set_mem eq_dec a l).
  destruct b.
  - symmetry in Heqb.
    apply set_mem_correct1 in Heqb.
    contradiction Heqb.
  - auto.
Qed.

Let minus_lt_compat:
  forall n m : nat,
  (S m) <= n ->
  n - (S m) < n - m.
Proof.
  induction n, m; eauto using Le.le_S_n; intuition.
Qed.

Lemma set_length_minus:
  forall a l1 l2,
  ~ In a l1 ->
  incl (a :: l1) l2 ->
  set_length l2 - set_length (a :: l1) <
  set_length l2 - set_length l1.
Proof.
  intros.
  apply set_length_le in H0.
  rewrite set_length_succ in *; repeat auto.
Qed.

End LISTS.
