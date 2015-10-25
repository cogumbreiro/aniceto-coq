Set Implicit Arguments.

Lemma opt_neq_none:
  forall {A:Type} (o:option A),
  o <> None ->
  exists v, o = Some v.
Proof.
  intros.
  destruct o.
  - exists a.
    auto.
  - contradiction H. auto.
Qed.

Lemma opt_some_neq:
  forall {A:Type} v (o:option A),
  o = Some v ->
  o <> None.
Proof.
  intros.
  intuition.
  subst.
  inversion H0.
Qed.

Lemma opt_some:
  forall {A:Type} (o:option A),
  o <> None <->
  exists v, o = Some v.
Proof.
  intros.
  split.
  apply opt_neq_none.
  intros.
  destruct H.
  apply opt_some_neq in H.
  assumption.
Qed.

Definition is_some {A:Type} (o:option A) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Lemma is_some_true:
  forall {A:Type} (o:option A),
  is_some o = true ->
  exists v, o = Some v.
Proof.
  intros.
  destruct o.
  - exists a; trivial.
  - inversion H.
Qed.

Lemma some_to_is_some:
  forall {A:Type} o (x:A),
  o = Some x ->
  is_some o = true.
Proof.
  intros.
  subst; simpl; trivial.
Qed.

Lemma is_some_rw:
  forall {A:Type} (o:option A),
  is_some o = true <->
  exists v, o = Some v.
Proof.
  split; intros.
  - auto using is_some_true.
  - destruct H; eauto using some_to_is_some.
Qed.

Lemma is_some_false:
  forall {A:Type} (o:option A),
  is_some o = false ->
  o = None.
Proof.
  intros.
  destruct o.
  - inversion H.
  - trivial.
Qed.

Lemma is_some_none:
  forall {A:Type} (o:option A),
  o = None ->
  is_some o = false.
Proof.
  intros.
  destruct o.
  - inversion H.
  - auto.
Qed.

Lemma is_some_rw_none:
  forall {A:Type} (o:option A),
  is_some o = false <-> o = None.
Proof.
  split;intros; auto using is_some_false, is_some_none.
Qed.

Lemma is_some_dec:
  forall {A:Type} (o:option A),
  { is_some o = true /\ exists v, o = Some v } + { is_some o = false /\ o = None }.
Proof.
  intros.
  remember (is_some o).
  symmetry in Heqb.
  destruct b.
  - left.
    apply is_some_true in Heqb.
    intuition.
  - right.
    apply is_some_false in Heqb; intuition.
Qed.
