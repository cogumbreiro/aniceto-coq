Require Coq.FSets.FSetFacts.
Require Coq.FSets.FSetInterface.
Require Coq.FSets.FSetProperties.
Require Import Coq.Lists.SetoidList.

Module SetUtil (Import M:FSetInterface.WS).
  Module P := FSetProperties.Properties M.
  Lemma in_elements_impl_in:
    forall e s,
    List.In e (elements s) ->
    In e s.
  Proof.
    intros.
    apply elements_2.
    apply In_InA.
    + apply Build_Setoid_Theory.
      * unfold Reflexive.
        auto.
      * unfold Symmetric.
        auto.
      * unfold Transitive.
        intros.
        apply E.eq_trans with (y:=y); repeat assumption.
    + assumption.
  Qed.

  Lemma in_impl_in_elements:
    forall e s,
    In e s ->
    exists e', E.eq e e' /\ List.In e' (elements s).
  Proof.
    intros.
    apply elements_1 in H.
    apply InA_alt in H.
    assumption.
  Qed.

  Lemma in_iff_in_elements:
    forall e s,
    (forall e1 e2, E.eq e1 e2 -> e1 = e2) ->
    (In e s <-> List.In e (elements s)).
  Proof.
    intros.
    split.
    - intros. apply in_impl_in_elements in H0.
      destruct H0 as (k', (Heq, Hin)).
      apply H in Heq.
      subst.
      assumption.
    - apply in_elements_impl_in.
  Qed.

  Lemma nonempty_in:
    forall s,
    ~ Empty s ->
    exists e, In e s.
  Proof.
    remember ((fun (s:t) => ~ Empty s ->
    exists e, In e s) <: t -> Type) as P.
    assert (X:= P.set_induction (P:=P)).
    subst.
    apply X.
    - intros.
      contradiction H0.
    - intros.
      exists x.
      apply P.Add_Equal in H1.
      assert (In x (add x s)). {
        auto using add_1.
      }
      unfold Equal in *.
      apply H1.
      assumption.
  Qed.
End SetUtil.
