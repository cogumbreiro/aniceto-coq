Section EqDec.

  Variable A:Type.

  Variable eq_dec: forall (x y:A), { x = y } + { x <> y }.

  Definition eq_dec_to_bool x y := if eq_dec x y then true else false.

  Lemma eq_dec_inv_true:
    forall x y,
    eq_dec_to_bool x y = true -> x = y.
  Proof.
    intros.
    unfold eq_dec_to_bool in *.
    destruct (eq_dec x y); auto; try inversion H.
  Qed.

  Lemma eq_dec_inv_false:
    forall x y,
    eq_dec_to_bool x y = false -> x <> y.
  Proof.
    intros.
    unfold eq_dec_to_bool in *.
    destruct (eq_dec x y); auto; try inversion H.
  Qed.

  Lemma eq_dec_rw:
    forall x y,
    { eq_dec_to_bool x y = true /\ x = y } +
    { eq_dec_to_bool x y = false /\ x <> y }.
  Proof.
    intros.
    unfold eq_dec_to_bool.
    destruct (eq_dec x y).
    - left; intuition.
    - right; intuition.
  Qed.

  Lemma eq_dec_refl:
    forall x,
    eq_dec_to_bool x x = true.
  Proof.
    intros.
    destruct eq_dec_rw with (x:=x) (y:=x) as [(?,?)|(?,?)].
    - trivial.
    - contradiction H0.
      trivial.
  Qed.

End EqDec.
