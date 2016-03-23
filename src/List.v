Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.funind.Recdef. (* Required by Function *)
Require Import Coq.Arith.Wf_nat. (* Required implicitly by measure obligations *)

Section LISTS.

Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.
Variable f : A -> bool.

Lemma in_cons_neq:
  forall {A:Type} (x y:A) l,
  In x (y :: l) ->
  x <> y ->
  In x l.
Proof.
  intros.
  inversion H.
  contradiction H0.
  auto.
  assumption.
Qed.

Lemma filter_length:
  forall l,
  length (filter f l) <= length l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    destruct (f a); simpl; auto with *.
Qed.

Lemma filter_inv:
  forall l,
  {l = filter f l} + {length l > length (filter f l)}.
Proof.
  intros.
  induction l.
  - left.
    auto.
  - destruct IHl.
    + simpl.
      rewrite <- e in *; clear e.
      destruct (f a).
      * left.
        auto.
      * right.
        auto with *.
    + simpl.
      destruct (f a);(
        right;
        simpl;
        auto with *
      ).
Qed.

Lemma filter_incl:
  forall l,
  incl (filter f l) l.
Proof.
  intros.
  unfold incl.
  intros.
  rewrite filter_In in H.
  intuition.
Qed.

Lemma filter_in:
  forall x l,
  In x (filter f l) ->
  In x l.
Proof.
  intros.
  assert (f_i := filter_incl l).
  unfold incl in f_i.
  auto.
Qed.

Lemma filter_refl:
  forall l,
  filter f l = l ->
  incl l (filter f l).
Proof.
  intros.
  induction l.
  - simpl.
    unfold incl.
    intros.
    inversion H0.
  - simpl in *.
    destruct (f a); (
      rewrite H;
      apply incl_refl).
Qed.

Lemma filter_forallb:
  forall l,
  filter f l = l <->
  forallb f l = true.
Proof.
  intros.
  split.
  - intros.
    induction l.
    + auto.
    + assert (Hfa : f a = true).
      assert (Ha : In a (filter f (a :: l))).
      rewrite H.
      apply in_eq.
      rewrite filter_In in Ha.
      intuition.
      simpl in *.
      destruct (f a).
      * inversion H.
        rewrite H1.
        auto.
      * inversion Hfa. (*absurd *)
  - intros. induction l.
    auto.
    simpl in *.
    rewrite Bool.andb_true_iff in H.
    destruct H as (Hl, Hr).
    apply IHl in Hr.
    destruct (f a).
    + rewrite Hr. trivial.
    + inversion Hl.
Qed.


  Lemma notin_contract:
    forall (x y:A) l,
    ~ In x (y :: l) ->
    ~ In x l.
  Proof.
    intros.
    intuition.
  Qed.

  Lemma filter_notin_to_false:
    forall l (x:A),
    In x l ->
    ~ In x (filter f l) ->
    f x = false.
  Proof.
    induction l; intros.
    - inversion H.
    - simpl in *.
      destruct H. {
        subst.
        destruct (f x). {
          contradiction H0.
          auto using in_eq.
        }
        trivial.
      }
      destruct (f a). {
        apply notin_contract in H0.
        auto.
      }
      auto.
  Qed.

  Lemma filter_in_to_true:
    forall l (x:A),
    In x l ->
    In x (filter f l) ->
    f x = true.
  Proof.
    induction l; intros.
    - inversion H.
    - simpl in *.
      destruct H. {
        subst.
        remember (f x).
        destruct b; auto.
        assert (In x l) by auto using filter_in.
        assert (Hx: f x = true) by eauto.
        rewrite Hx in Heqb.
        inversion Heqb.
      }
      remember (f a).
      destruct b. {
        destruct H0; subst; auto.
      }
      auto.
  Qed.

  Lemma filter_false_to_notin:
    forall l (x:A),
    In x l ->
    f x = false ->
    ~ In x (filter f l).
  Proof.
    intros.
    induction l. {
      inversion H.
    }
    inversion H; subst. {
      simpl.
      rewrite H0.
      intuition.
      assert (incl (filter f l) l). {
        auto using filter_incl.
      }
      unfold incl in *.
      assert (Hx := H1).
      apply H2 in H1.
      apply (IHl H1 Hx).
    }
    simpl.
    apply IHl in H1; clear IHl.
    remember (f a).
    destruct b. {
      intuition.
      inversion H2. {
        subst.
        rewrite H0 in Heqb.
        inversion Heqb.
      }
      auto.
    }
    auto.
  Qed.

  Lemma filter_true_to_in:
    forall l (x:A),
    In x l ->
    f x = true ->
    In x (filter f l).
  Proof.
    intros l.
    induction l; intros. {
      inversion H.
    }
    simpl.
    remember (f a).
    symmetry in Heqb.
    destruct H.
    - destruct b. {
        subst; eauto using in_eq.
      }
      subst.
      rewrite H0 in Heqb.
      inversion Heqb.
    - destruct b; eauto using in_cons.
  Qed.


Lemma existsb_inv:
  forall {B:Type} (a:B) l g,
  existsb g (a :: l) = true ->
  g a = false ->
  existsb g l = true.
Proof.
  intros.
  simpl in H.
  rewrite H0 in H.
  auto.
Qed.

Lemma forallb_existsb:
  forall l,
  forallb f l = negb (existsb (fun x => negb (f x)) l).
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    rewrite negb_orb.
    rewrite negb_involutive.
    rewrite <- IHl.
    auto.
Qed.

Lemma Forall_forallb:
  forall l,
  Forall (fun x => Is_true (f x)) l <->
  forallb f l = true.
Proof.
  split.
  + intro.
    rewrite forallb_forall.
    intros.
    rewrite Forall_forall in H.
    auto using Is_true_eq_true.
  + intros.
    rewrite forallb_forall in H.
    rewrite Forall_forall.
    intros.
    auto using Is_true_eq_left.
Qed.

End LISTS.

Implicit Arguments filter_inv.

Section FEEDBACK.
Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.
Variable f : list A -> A -> bool.

Function feedback_filter (l:list A) {measure length l} :=
  let fl := filter (f l) l in
  if list_eq_dec eq_dec l fl then l
  else feedback_filter fl.
Proof.
  intros.
  destruct (filter_inv (f l) l).
  - contradiction anonymous.
  - auto.
Defined.

Lemma feedback_filter_incl:
  forall l,
  incl (feedback_filter l) l.
Proof.
  intros.
  elim l using feedback_filter_rec.
  - auto using incl_refl.
  - intros. clear l. rename l0 into l.
    remember (filter (f l) l) as l'.
    assert (Hx : incl l' l). {
      rewrite Heql'.
      apply filter_incl.
    }
    eauto using incl_tran.
Qed.

Lemma feedback_filter_simpl:
  forall l,
  filter (f l) l = l ->
  feedback_filter l = l.
Proof.
  intros.
  rewrite feedback_filter_equation.
  destruct (list_eq_dec eq_dec l (filter (f l) l)).
  - auto.
  - contradiction n.
    auto.
Qed.

Let if_list_eq_dec_eq:
  forall {B:Type} l (a b:B),
  (if list_eq_dec eq_dec l l then a else b) = a.
Proof.
  intros.
  destruct (list_eq_dec eq_dec l l); (
    try (contradiction n); auto
  ).
Qed.

Let if_list_eq_filter_forallb:
  forall {B:Type} l (a b:B),
  (if list_eq_dec eq_dec l (filter (f l) l) then a else b)
  = (if forallb (f l) l then a else b).
Proof.
  intros.
  remember (filter (f l) l) as fl.
  symmetry in Heqfl.
  remember (forallb (f l) l) as flb.
  symmetry in Heqflb.
  destruct flb.
  - rewrite <- filter_forallb in Heqflb.
    rewrite Heqfl in Heqflb.
    rewrite Heqflb.
    apply if_list_eq_dec_eq.
  - destruct (list_eq_dec eq_dec l fl).
    + rewrite <- e in Heqfl.
      rewrite filter_forallb in Heqfl.
      rewrite Heqfl in Heqflb.
      inversion Heqflb.
    + auto.
Qed.

Let feedback_filter_equation2:
  forall l : list A,
  feedback_filter l =
  (if forallb (f l) l
  then l
  else feedback_filter (filter (f l) l)).
Proof.
  intros.
  rewrite feedback_filter_equation.
  rewrite if_list_eq_filter_forallb.
  auto.
Qed.

Lemma feedback_filter_prop:
  forall l fl,
  feedback_filter l = fl <->
  (Forall (fun x=>Is_true (f l x)) l /\ fl = l)
  \/
  (exists x, In x l /\ Is_true (negb (f l x)) /\ fl = feedback_filter (filter (f l) l)).
Proof.
  intros.
  split.
  - intros.
    rewrite feedback_filter_equation2 in H.
    remember (forallb (f l) l) as flb.
    symmetry in Heqflb.
    destruct flb.
    + rewrite forallb_forall in Heqflb.
      left.
      rewrite Forall_forall.
      intuition.
      auto using Is_true_eq_left.
    + right.
      rewrite forallb_existsb in Heqflb.
      rewrite negb_false_iff in Heqflb.
      rewrite existsb_exists in Heqflb.
      destruct Heqflb as (x, (x_in, flx)).
      exists x.
      apply Is_true_eq_left in flx.
      intuition.
   - intros.
     rewrite feedback_filter_equation2.
     destruct H as [(H1,H2)|(x, (H1, (H2, H3)))].
     + apply Forall_forallb in H1.
       rewrite H1.
       auto.
     + rewrite <- H3.
       remember (forallb (f l) l) as c.
       symmetry in Heqc.
       destruct c.
       * rewrite forallb_forall in Heqc.
         apply Heqc in H1.
         apply Is_true_eq_true in H2.
         rewrite negb_true_iff in H2.
         rewrite H1 in H2.
         inversion H2.
       * auto.
Qed.


Lemma feedback_filter_in_f:
  forall x l,
  In x (feedback_filter l) -> f (feedback_filter l) x = true.
Proof.
  intros.
  functional induction (feedback_filter l); auto.
  assert (Hf := _x).
  symmetry in Hf.
  rewrite filter_forallb in Hf.
  rewrite forallb_forall in Hf.
  auto.
Qed.

Lemma feedback_filter_in:
  forall x l,
  In x (feedback_filter l) ->
  In x l.
Proof.
  intros.
  assert (Hx := feedback_filter_incl l).
  unfold incl in Hx.
  apply Hx; assumption.
Qed.
End FEEDBACK.

Section PARTITION.
Variable A : Type.
Variable f : A -> bool.

Lemma partition_iff_1 :
  forall x l,
  (In x (fst (partition f l)) <-> In x l /\ f x = true).
Proof.
  intros.
  split.
  - intros.
    induction l.
    simpl in *.
    inversion H.
    simpl in H.
    remember (f a) as fa.
    symmetry in Heqfa.
    remember (partition f l) as pf.
    symmetry in Heqpf.
    destruct pf as (pfl, pfr).
    destruct fa.
    + simpl in *.
      destruct H.
      * subst.
        intuition.
      * apply IHl in H; clear IHl.
        destruct H.
        intuition.
    + simpl in *.
      apply IHl in H; clear IHl.
      destruct H.
      intuition.
 - intros.
   destruct H.
   induction l.
   auto.
   simpl in *.
   remember (f a).
   destruct H, b.
   + subst.
     remember (partition f l).
     destruct p.
     simpl.
     auto.
   + subst.
     rewrite H0 in Heqb.
     inversion Heqb.
   + remember (partition f l).
     destruct p.
     simpl in *.
     apply IHl in H.
     intuition.
   + apply IHl in H.
     remember (partition f l).
     destruct p.
     auto.
Qed.

Lemma partition_iff_2 :
  forall x l,
  (In x (snd (partition f l)) <-> In x l /\ f x = false).
Proof.
  intros.
  split.
  - intros.
    induction l.
    simpl in *.
    inversion H.
    simpl in H.
    remember (f a) as fa.
    symmetry in Heqfa.
    remember (partition f l) as pf.
    symmetry in Heqpf.
    destruct pf as (pfl, pfr).
    destruct fa.
    + simpl in *.
      apply IHl in H; clear IHl.
      destruct H.
      intuition.
    + simpl in *.
      destruct H.
      * subst.
        intuition.
      * apply IHl in H; clear IHl.
        destruct H.
        intuition.
 - intros.
   destruct H.
   induction l.
   auto.
   simpl in *.
   remember (f a).
   destruct H, b.
   + subst.
     rewrite H0 in Heqb.
     inversion Heqb.
   + subst.
     remember (partition f l).
     destruct p.
     simpl.
     auto.
   + remember (partition f l).
     destruct p.
     simpl in *.
     auto.
   + apply IHl in H.
     remember (partition f l).
     destruct p.
     simpl in *.
     auto with *.
Qed.

Lemma partition_in :
  forall x l,
  In x l ->
  {In x (fst (partition f l)) /\ f x = true} +
  {In x (snd (partition f l)) /\ f x = false}.
Proof.
  intros.
  remember (f x).
  symmetry in Heqb.
  destruct b.
  - left.
    intuition.
    apply partition_iff_1.
    auto.
  - right.
    intuition.
    apply partition_iff_2.
    auto.
Qed.

Lemma partition_length:
  forall l,
  length (snd (partition f l)) <= length l.
Proof.
  intros.
  induction l.
  auto.
  simpl.
  remember (partition f l) as p.
  symmetry in Heqp.
  destruct p as (pl, pr).
  simpl in *.
  remember (f a) as fa.
  destruct fa; simpl; auto with *.
Qed.

End PARTITION.

Lemma split_in_r:
  forall {L R:Type} (r:R) (lst:list (L * R)),
  In r (snd (split lst)) ->
  exists (l:L), In (l, r) lst.
Proof.
  intros.
  induction lst.
  inversion H.
  destruct a.
  simpl in *.
  remember (split lst).
  destruct p as (ll, lr).
  simpl in *.
  destruct H.
  - subst.
    eauto.
  - apply IHlst in H.
    destruct H as (l', Hin).
    eauto.
Qed.

Lemma split_in_l:
  forall {L R:Type} (l:L) (lst:list (L * R)),
  In l (fst (split lst)) ->
  exists (r:R), In (l, r) lst.
Proof.
  intros.
  induction lst.
  inversion H.
  destruct a.
  simpl in *.
  remember (split lst).
  destruct p as (ll, lr).
  simpl in *.
  destruct H.
  - subst.
    exists r.
    intuition.
  - apply IHlst in H.
    destruct H as (r', Hin).
    exists r'.
    intuition.
Qed.


Fixpoint split_alt {A:Type} {B:Type} (l:list (A*B) %type) : (list A * list B) % type:=
  match l with
    | nil => (nil, nil)
    | (x, y) :: l => (x :: (fst (split_alt l)), y :: (snd (split_alt l)))
  end.

Lemma split_alt_spec:
  forall {A:Type} {B:Type} (l:list (A*B) %type),
  split l = split_alt l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl. intuition.
    rewrite IHl.
    remember (split_alt l) as l'.
    destruct l' as (lhs, rhs).
    auto.
Qed.

Lemma in_fst_split:
  forall {A:Type} {B:Type} (l:list (A*B)%type) (lhs:A),
  List.In lhs (fst (split l)) ->
  exists rhs, List.In (lhs, rhs) l.
Proof.
  intros.
  induction l.
  { inversion H. (* absurd *) }
  destruct a.
  rewrite split_alt_spec in H.
  simpl in H.
  destruct H.
  + subst.
    eauto using in_eq.
  + rewrite <- split_alt_spec in H.
    apply IHl in H; clear IHl.
    destruct H as (r, Hin).
    eauto using in_cons.
Qed.

Lemma in_snd_split:
  forall {A:Type} {B:Type} (l:list (A*B)%type) (rhs:B),
  List.In rhs (snd (split l)) ->
  exists (lhs:A), List.In (lhs, rhs) l.
Proof.
  intros.
  induction l.
  { inversion H. (* absurd *) }
  destruct a.
  rewrite split_alt_spec in H.
  simpl in H.
  destruct H.
  + subst.
    exists a.
    apply in_eq.
  + rewrite <- split_alt_spec in H.
    apply IHl in H; clear IHl.
    destruct H as (r, Hin).
    exists r.
    apply in_cons; assumption.
Qed.

Require Import Coq.Lists.SetoidList.

Section INA_IN.
  Let ina_to_in:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) (a:A) l,
    InA P a l ->
    List.In a l.
  Proof.
    intros. induction l.
    + inversion H.
    + inversion H; subst; clear H.
      * apply P_eq in H1.
        subst.
        apply in_eq.
      * auto using in_cons.
  Qed.

  Let in_to_ina:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) (a:A) l,
    List.In a l ->
    InA P a l.
  Proof.
    intros. induction l.
    + inversion H.
    + inversion H; subst; clear H.
      * apply InA_cons_hd.
        rewrite P_eq; auto.
      * auto using InA_cons_tl.
  Qed.

  Lemma ina_in_iff:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) (a:A) l,
    InA P a l <-> List.In a l.
  Proof.
    intros.
    split; eauto using ina_to_in, in_to_ina.
  Qed.
End INA_IN.

Section NODUPA_NODUP.
  Let nodupa_to_nodup:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) l,
    NoDupA P l ->
    NoDup l.
  Proof.
    intros.
    induction l.
    - apply NoDup_nil.
    - apply NoDup_cons.
      + intuition.
        inversion H; clear H; subst.
        rewrite ina_in_iff in H3.
        contradiction H0.
        assumption.
      + inversion H; clear H; subst.
        auto.
  Qed.

  Let nodup_to_nodupa:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) l,
    NoDup l ->
    NoDupA P l.
  Proof.
    intros.
    induction l.
    - apply NoDupA_nil.
    - inversion H; clear H; subst.
      apply IHl in H3; clear IHl.
      apply NoDupA_cons; auto.
      intuition.
      rewrite ina_in_iff in H; auto.
  Qed.

  Lemma nodupa_nodup_iff:
    forall {A:Type} (P: A -> A -> Prop) (P_eq: forall x y, P x y <-> x = y) l,
    NoDupA P l <-> NoDup l.
  Proof.
    intros.
    split; eauto using nodupa_to_nodup, nodup_to_nodupa.
  Qed.
End NODUPA_NODUP.
Implicit Arguments filter_incl.
Implicit Arguments feedback_filter.
Implicit Arguments feedback_filter_equation.


Section FindProps.

Variable A: Type.
Variable f: A -> bool.

Lemma find_some_impl_existsb:
  forall l x,
  find f l = Some x -> existsb f l = true.
Proof.
  intros.
  induction l; simpl in *.
  { inversion H. }
  destruct (f a); auto.
Qed.

Lemma existsb_impl_find_some:
  forall l,
  existsb f l = true ->
  exists x, find f l = Some x.
Proof.
  intros.
  induction l.
  { inversion H. }
  simpl in *.
  destruct (f a); eauto.
Qed.

Lemma find_existsb_spec_true:
  forall l,
  (exists x, find f l = Some x) <-> existsb f l = true.
Proof.
  intros.
  split.
  - intros.
    destruct H.
    eauto using find_some_impl_existsb.
  - apply existsb_impl_find_some.
Qed.

Lemma find_none_impl_existsb:
  forall l,
  find f l = None -> existsb f l = false.
Proof.
  intros.
  induction l.
  { auto. }
  simpl in *.
  destruct (f a).
  - inversion H.
  - auto.
Qed.

Lemma existsb_false_impl_find:
  forall l,
  existsb f l = false ->
  find f l = None.
Proof.
  intros.
  induction l.
  { auto. }
  simpl in *.
  destruct (f a).
  - inversion H.
  - auto.
Qed.

Lemma find_existsb_spec_false:
  forall l,
  find f l = None <-> existsb f l = false.
Proof.
  split.
  - apply find_none_impl_existsb.
  - apply existsb_false_impl_find.
Qed.

Lemma find_inv_eq:
  forall x l,
  f x = true ->
  find f (x :: l) = Some x.
Proof.
  intros.
  simpl.
  rewrite H.
  trivial.
Qed.

Lemma existsb_forallb:
  forall l,
  existsb f l = negb (forallb (fun x : A => negb (f x)) l).
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    destruct (f a); auto.
Qed.

Lemma find_none_incl:
  forall x l,
  find f (x::l) = None ->
  find f l = None.
Proof.
  intros.
  rewrite find_existsb_spec_false in *.
  rewrite existsb_forallb in *.
  rewrite negb_false_iff in *.
  apply Forall_forallb.
  apply Forall_forallb in H.
  inversion H; auto.
Qed.

Lemma find_some_spec:
  forall x l,
  find f l = Some x ->
  In x l /\ f x = true.
Proof.
  intros.
  induction l.
  { inversion H. }
  simpl in H.
  remember (f a).
  destruct b.
  - inversion H.
    subst.
    split; auto using in_eq.
  - apply IHl in H.
    destruct H.
    split; auto.
    auto using in_cons.
Qed.

End FindProps.

Set Implicit Arguments.

Section Sum.
  Variable A: Type.
  Variable weight: A -> nat.
  Let aux := (fun (n:nat) (a:A) => n + weight a). 
  Definition summation (l:list A) : nat := fold_left aux l 0.
  
  Let fold_left_aux_lift:
    forall l n,
    fold_left aux l n = n + fold_left aux l 0.
  Proof.
    intros l.
    induction l.
    { intros; auto. }
    intros.
    simpl.
    assert (rw1 : aux n a = n + weight a) by auto.
    rewrite rw1.
    assert (rw2 : aux 0 a = weight a) by auto.
    rewrite rw2.
    assert (rw3 := IHl (n+ weight a)).
    rewrite rw3.
    assert (rw4 := IHl (weight a)).
    rewrite rw4.
    auto with *.
  Qed.
  
  Lemma summation_rw_cons:
    forall l x,
    summation (x::l) = weight x + summation l.
  Proof.
    intros l.
    induction l.
    - intros.
      auto.
    - assert (Hx := IHl a).
      intros.
      rewrite Hx.
      unfold summation.
      simpl.
      assert (rw : aux 0 x = weight x) by auto.
      rewrite rw.
      assert (rw2 : aux (weight x) a = weight x + weight a) by auto.
      rewrite rw2.
      rewrite fold_left_aux_lift.
      auto with *.
  Qed.

  Lemma summation_rw_app:
    forall l1 l2,
    summation (l1 ++ l2) = summation l1 + summation l2.
  Proof.
    intros l1.
    induction l1.
    { intros; auto. }
    intros.
    simpl.
    rewrite summation_rw_cons.
    rewrite summation_rw_cons.
    rewrite IHl1.
    auto with *.
  Qed.
End Sum.

Section OMap.
  Set Implicit Arguments.
  (** Defines an optional map function. *)
  Variable A:Type.

  Variable B:Type.

  Variable f : A -> option B.

  Definition omap l :=
    flat_map
    (fun x =>
      match f x with
      | Some x => cons x nil
      | None => nil
      end)
    l.

  Lemma in_omap_1:
    forall l x y,
    In x l ->
    f x = Some y ->
    In y (omap l).
  Proof.
    intros.
    unfold omap.
    rewrite in_flat_map.
    exists x.
    intuition.
    rewrite H0.
    auto using in_eq.
  Qed.

  Lemma in_omap_2:
    forall l y,
    In y (omap l) ->
    exists x, (In x l /\ f x = Some y).
  Proof.
    unfold omap.
    intros.
    rewrite in_flat_map in *.
    destruct H as (x, (Hin1, Hin2)).
    remember (f x).
    destruct o.
    - inversion Hin2.
      + subst.
        eauto.
      + inversion H.
    - inversion Hin2.
  Qed.

End OMap.
