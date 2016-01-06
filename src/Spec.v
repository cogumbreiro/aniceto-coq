Set Implicit Arguments.

Require Import Aniceto.Option.

(**
  The result class establishes an isomorphism between a property [R]
  and an optional value: [R] holds iff there is some value.

  This class is useful to obtain facts about propositions that behave like functions.
 *)
  

Class Result {A:Type} (R: A->Prop) := {
  result_impl: option A; 
  
  result_to_impl:
    forall x, R x -> result_impl = Some x;

  impl_to_result:
    forall x, result_impl = Some x -> R x
}.

Section Result.
  Variable A:Type.
  Variable R: A -> Prop.
  Context `{s: Result A R}.

  Lemma result_rw:
    forall x,
    (result_impl = Some x <-> R x).
  Proof.
    intros.
    split; auto using impl_to_result, result_to_impl.
  Qed.

  Lemma impl_none_to_not_result:
    result_impl = None -> forall x, ~ R x.
  Proof.
    intuition. apply result_to_impl in H0.
    rewrite H0 in H; inversion H.
  Qed.

  Lemma not_result_to_impl_none:
    (forall x, ~ R x) -> result_impl = None.
  Proof.
    intros.
    remember (result_impl).
    symmetry in Heqo.
    destruct o.
    + apply result_rw in Heqo.
      contradiction (H a); trivial.
    + trivial.
  Qed.

  Lemma result_rw_none:
    (result_impl = None <-> forall x, ~ R x).
  Proof.
    split; intros; auto using impl_none_to_not_result, not_result_to_impl_none.
  Qed.

  Lemma result_dec:
    { exists x, R x } + { forall x, ~ R x }.
  Proof.
    intros.
    remember result_impl.
    symmetry in Heqo.
    destruct o.
    - left.
      exists a.
      auto using impl_to_result.
    - right.
      apply result_rw_none; assumption.
  Qed.

  Lemma result_fun:
    forall x y,
    R x ->
    R y ->
    x  = y.
  Proof.
    intros.
    apply result_to_impl in H.
    apply result_to_impl in H0.
    rewrite H in H0.
    inversion H0; trivial.
  Qed.

End Result.

(* TODO: REMOVE ME WHEN Coq >= 8.5 *)

Class Decidable (P : Prop) := {
  Decidable_witness : bool;
  Decidable_spec : Decidable_witness = true <-> P
}.


Lemma Decidable_sound : forall P (H : Decidable P),
  Decidable_witness = true -> P.
Proof.
  intros.
  apply Decidable_spec; assumption.
Qed.

Lemma Decidable_complete : forall P (H : Decidable P),
  P -> Decidable_witness = true.
Proof.
  intros.
  apply Decidable_spec; assumption.
Qed.  

Lemma Decidable_sound_alt : forall P (H : Decidable P),
   ~ P -> Decidable_witness = false.
Proof.
  intros.
  remember (Decidable_witness).
  symmetry in Heqb.
  destruct b.
  - apply Decidable_spec in Heqb.
    contradiction H0.
  - trivial.
Qed.

Lemma Decidable_complete_alt : forall P (H : Decidable P),
  Decidable_witness = false -> ~ P.
Proof.
  intros.
  remember (Decidable_witness).
  symmetry in Heqb.
  destruct b.
  - inversion H0.
  - intuition.
    apply Decidable_spec in H1.
    rewrite H1 in Heqb.
    inversion Heqb.
Qed.

Definition decide P {H : Decidable P} := Decidable_witness (Decidable:=H).

Lemma decide_sumbool P `{D:Decidable P}:
  { P } + { ~ P }.
Proof.
  remember (Decidable_witness).
  symmetry in Heqb.
  destruct b.
  - left; eauto using (Decidable_sound D).
  - right; eauto using (Decidable_complete_alt D).
Qed.

Class HasResult (A:Type) (R:A->Prop) (P:Prop) := {
  pack_result:
    forall x, R x -> P;

  unpack_result:
    P -> exists x, R x
}.

Require Coq.Setoids.Setoid.

Section HasResult.

  Variable A:Type.
  Variable R:A -> Prop.
  Variable P:Prop.

  Context `{q:HasResult A R P}.

  Lemma has_result_rw:
    (exists x, R x) <-> P.
  Proof.
    split; intros.
    - destruct H; eauto using pack_result.
    - eauto using unpack_result.
  Qed.

  Context `{s:Result A R}.

  Program Instance Decidable_HasResult: Decidable P := {
    Decidable_witness := is_some result_impl
  }.
  Next Obligation.
    split; intros.
    - apply is_some_true in H.
      destruct H.
      eauto using impl_to_result, pack_result.
    - rewrite is_some_rw.
      apply unpack_result in H.
      destruct H as (x, ?).
      exists x.
      rewrite result_rw; trivial.
  Qed.

  Lemma has_result_dec:
    { P } + { ~ P}.
  Proof.
    destruct result_dec with (A:=A) (R:=R); auto.
    - left; apply has_result_rw; assumption.
    - right.
      intuition.
      apply unpack_result in H.
      destruct H.
      eauto using n.
  Qed.

End HasResult.
