Require Aniceto.Graphs.Bipartite.Bipartite.

Module C := Aniceto.Graphs.Bipartite.Bipartite.

Require Import Aniceto.Graphs.Graph.

Set Implicit Arguments.

Section CycleAAtoBB.
  Variable A : Type.
  Variable B : Type.
  Variable AB : A -> B -> Prop.
  Variable BA : B -> A -> Prop.

  Notation b_edge := (B * B) % type.
  Notation a_edge := (A * A) % type.
  Notation a_walk := (list a_edge).
  Notation b_walk := (list b_edge).
  Notation AA := (Bipartite.AA AB BA).
  Notation BB := (Bipartite.BB AB BA).
  Notation BWalk := (Walk BB).
  Notation AWalk := (Walk AA).
  Notation ACycle := (Cycle AA).
  Notation BCycle := (Cycle BB).
  Notation ABA := (Bipartite.ABA AB BA).
  Notation BAB := (Bipartite.BAB AB BA).

  (**
    In a bi-partite graph, any two A-edges can be "contracted" two a B-edge, as
    there is a B-vertex connecting any A-edge in the AB-graph.
    
    We can depict the relation between the A-edges and the B-edges as:
    ```
    (a1) ~~ (a2) ~~ (a3)
       \    /  \   /
        (b1) ~~ (b2)
    ```
   *)

  Inductive edge_a_to_b : a_edge -> a_edge -> b_edge -> Prop :=
    edge_a_to_b_def:
      forall a1 a2 a3 b1 b2,
      ABA a1 b1 a2 ->
      ABA a2 b2 a3 ->
      edge_a_to_b (a1, a2) (a2, a3) (b1, b2).

  (**
    The proposition [edge_a_to_b] relates two AB-edges, but by using the
    definitions of A-edges and B-edges we can arrive in both the A-graph and
    B-graph.
   *)

  Let a_to_b_b_edge:
    forall e1 e2 e3,
    edge_a_to_b e1 e2 e3 ->
    BB e3.
  Proof.
    intros.
    inversion H.
    subst.
    eauto using C.bab_to_b, C.aba_to_bab.
  Qed.

  Let edge_a_to_b_total:
    forall a1 a2 a3,
    AA (a1, a2) ->
    AA (a2, a3) ->
    exists b1 b2,
    edge_a_to_b (a1, a2) (a2, a3) (b1, b2).
  Proof.
    intros.
    apply C.a_edge_to_bi_edge in H.
    apply C.a_edge_to_bi_edge in H0.
    destruct H as (b1, (H1, H2)).
    destruct H0 as (b2, (H3, H4)).
    exists b1.
    exists b2.
    intuition.
    auto using edge_a_to_b_def, C.ab_ba_to_aba, C.ba_ab_to_bab.
  Qed.


  Let a_walk_to_edge_a_to_b:
    forall a1 a2 a3 aw,
    AWalk ((a1, a2) :: ((a2, a3) :: aw)%list) ->
    exists b1 b2, edge_a_to_b (a1, a2) (a2, a3) (b1, b2).
  Proof.
    intros.
    inversion H; subst.
    inversion H2; subst.
    auto using edge_a_to_b_total.
  Qed.

  Let edge_a_to_b_inv1:
    forall a1 a2 a3 b1 b2,
    edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
    ABA a1 b1 a2.
  Proof.
    intros. inversion H.
    assumption.
  Qed.

  Let edge_a_to_b_inv2:
    forall a1 a2 a3 b1 b2,
    edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
    ABA a2 b2 a3.
  Proof.
    intros. inversion H.
    assumption.
  Qed.

  Let edge_a_to_b_inv3:
    forall a1 a2 a3 b1 b2,
    edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
    BAB b1 a2 b2.
  Proof.
    intros. inversion H.
    eauto using C.aba_to_bab.
  Qed.

  (**
    Using [edge_a_to_b] we can "contract" an A-walk to a B-walk.

    The depiction of the two walks can be found next.
    
    ```
    (a1) ~~ (a2) ~~ (a3) ~~ .... ~~ (an) 
       \    /  \    /  \    /  \   / 
        (b1) ~~ (b2) ~~ .... ~~ (bn)
    ```
   *)

  Inductive a_to_b : a_walk -> b_walk -> Prop :=
    | a_to_b_nil:
      a_to_b nil nil
    | a_to_b_edge_nil:
      forall e,
      a_to_b (e::nil)%list nil
    | a_to_b_cons:
      forall e1 e2 e aw bw,
      a_to_b (e2 :: aw)%list bw ->
      edge_a_to_b e1 e2 e ->
      a_to_b (e1 :: e2 :: aw)%list (e :: bw)%list.

  Let a_to_b_total_nil:
    exists bw : b_walk, a_to_b nil bw /\ BWalk bw.
  Proof.
    exists nil.
    split; auto using a_to_b_nil, walk_nil.
  Qed.

  Let a_to_b_total_edge:
    forall a1 a2,
    AWalk ((a1, a2) :: nil) ->
    exists bw : b_walk, a_to_b ((a1, a2) :: nil)%list bw /\ BWalk bw.
  Proof.
    exists nil.
    split; auto using walk_nil, a_to_b_edge_nil.
  Qed.

  Let edge_a_to_b_to_a_to_b:
    forall a1 a2 a3 b1 b2,
    edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
    a_to_b ((a1, a2) :: ((a2, a3) :: nil)%list)%list ((b1, b2) :: nil)%list.
  Proof.
    intros.
    inversion H.
    auto using a_to_b_cons, a_to_b_edge_nil, edge_a_to_b_def.
  Qed.

  Let b_walk_cons_aba:
    forall b1 b2 b3 a1 a2 a3 bw,
    ABA a1 b1 a2 ->
    ABA a2 b2 a3 ->
    BWalk ((b2, b3) :: bw) ->
    BWalk ((b1, b2) :: ((b2, b3) :: bw)%list).
  Proof.
    intros.
    inversion H0; subst.
    eauto using walk_cons, C.aba_to_b, linked_eq.
  Qed.

  Let a_to_b_cons_aba:
    forall a1 a2 a3 a4 aw b1 b2 b3 bw,
    ABA a1 b1 a2 ->
    ABA a2 b2 a3 ->
    a_to_b ((a2, a3) :: ((a3, a4) :: aw)%list)%list ((b2, b3) :: bw)%list
    ->
    a_to_b ((a1, a2) :: ((a2, a3) :: (a3, a4) :: aw)%list)%list
    ((b1, b2) :: ((b2, b3) :: bw)%list)%list.
  Proof.
    intros.
    eauto using edge_a_to_b_def, a_to_b_cons.
  Qed.

  Let a_to_b_b_walk_cons:
    forall a1 a2 a3 a4 aw b1 b2 b3 bw,
    ABA a1 b1 a2 ->
    ABA a2 b2 a3 ->
    BWalk ((b2, b3) :: bw) ->
    edge_a_to_b (a2, a3) (a3, a4) (b2, b3) ->
    a_to_b ((a2, a3) :: ((a3, a4) :: aw))%list ((b2, b3) :: bw)%list
    ->
    a_to_b ((a1, a2) :: ((a2, a3) :: (a3, a4) :: aw)%list)%list
    ((b1, b2) :: ((b2, b3) :: bw)%list)%list
    /\
    BWalk ((b1, b2) :: ((b2, b3) :: bw)%list).
  Proof.
    intuition.
    apply edge_a_to_b_inv1 in H2.
    eauto using b_walk_cons_aba.
  Qed.

  Let edge_a_to_b_to_b_walk:
    forall a1 a2 a3 b1 b2,
    edge_a_to_b (a1, a2) (a2, a3) (b1, b2) ->
    BWalk ((b1, b2) :: nil).
  Proof.
    intros.
    eauto using walk_cons, linked_nil, walk_nil, a_to_b_b_edge.
  Qed.

  Let a_to_b_total_step:
    forall a1 a2 a3 aw bw,
    AWalk ((a1, a2) :: ((a2, a3) :: aw)%list) ->
    a_to_b ((a2, a3) :: aw)%list bw ->
    BWalk bw ->
    exists bw' : b_walk,
    a_to_b ((a1, a2) :: ((a2, a3) :: aw)%list)%list bw' /\ BWalk bw'.
  Proof.
    intros.
    assert (H3: AA (a1, a2)).
    inversion H; subst; assumption.
    inversion H0.
    - (* Case 1: *)
      subst.
      assert (Hr := H).
      apply a_walk_to_edge_a_to_b in Hr.
      destruct Hr as (b1, (b2, Hr)).
      exists (cons (b1, b2) nil).
      intuition.
      eauto using edge_a_to_b_to_b_walk.
    - (* Case 2: *)
      subst.
      destruct e2 as (a3', a4).
      inversion H7; subst. (* a3 = a3' *)
      apply C.a_to_aba in H3; destruct H3.
      eauto using a_to_b_b_walk_cons.
  Qed.

  (**
    The main property we want to show is that we can always "contract" a A-walk [aw]
    to obtain a B-walk [bw] such that proposition [a_to_b aw bw] holds. 

    The proof follows by induction on the structure of [aw].
    The base case is trivial, consider [bw] to be an empty B-walk.
    For the induction case let [aw = e :: aw'].
    The induction hypothesis can be readily applied if we invert [AWalk (e::aw')],
    so we know that there exists a [bw] such that [a_to_b aw' bw] and [BWalk bw].
    If we consider the structure of [a_to_b] there are two more cases to consider, by
    inspecting [aw'].
    If [aw'] is [nil], we can conlude by applying [a_to_b_edge_nil], so the resulting
    B-walk is empty.
    Otherwise, we conclude using [a_to_b_cons].
   *)

  Let a_to_b_total:
    forall aw,
    AWalk aw ->
    exists bw, a_to_b aw bw /\ BWalk bw.
  Proof.
    intros.
    induction aw.
    - apply a_to_b_total_nil.
    - inversion H.
      subst.
      apply IHaw in H2; clear IHaw.
      destruct H2 as (bw, (H1, H2)).
      destruct a as (a1, a2).
      destruct aw.
      + auto using a_to_b_total_edge.
      + destruct p as (a2', a3).
        (* a2 = a2' *)
        apply linked_inv in H4; rewrite H4 in *; clear H4.
        eauto using a_to_b_total_step.
  Qed.

  Let a_to_b_step:
    forall aw b1 b2 bw,
    AWalk aw ->
    a_to_b aw ((b1,b2)::bw)%list ->
    BWalk ((b1,b2)::bw) ->
    exists a1 a2 a3 aw',
    (aw = ((a1,a2)::(a2,a3)::aw')%list /\
    ABA a1 b1 a2 /\ ABA a2 b2 a3).
  Proof.
    intros.
    inversion H0.
    - subst.
      destruct e1 as (a1,a2).
      destruct e2 as (a2',a3).
      exists a1;
      exists a2;
      exists a3;
      exists aw0.
      intuition.
      + inversion H.
        apply linked_inv in H8.
        subst.
        auto.
      + inversion H6.
        auto.
      + inversion H6.
        auto.
  Qed.

  Let a_to_b_mk_nil:
    forall a1 a2 a3 b1 b2,
    a_to_b ((a1,a2)::(a2,a3)::nil)%list ((b1,b2)::nil)%list ->
    (ABA a1 b1 a2 /\ ABA a2 b2 a3).
  Proof.
    intros.
    inversion H.
    subst.
    inversion H6.
    subst.
    auto.
  Qed.

  Let a_to_b_nil_inv:
    forall aw b1 b2,
    a_to_b aw ((b1, b2) :: nil)%list ->
    exists a1 a2 a3,
    aw = ((a1, a2) :: (a2, a3) :: nil)%list /\
    edge_a_to_b (a1, a2) (a2, a3) (b1, b2).
  Proof.
    intros.
    inversion H.
    subst.
    destruct e1 as (a1, a2').
    destruct e2 as (a2, a3).
    inversion H4.
    subst.
    exists a1; exists a2; exists a3.
    intuition.
    inversion H3.
    auto.
  Qed.

  (**
    An important result 
    The proof follows by induction on the derivation tree of [a_to_b aw bw].
    The base-cases are simple as they lead to the absurd.
    In the inductive step, we can perform a case analysis.
    The interesting case is when we have [bw = e::bw'].
    By inverting [End bw (b1,b2)], we can apply the induction hypothesis to 
    [End bw' (b1,b2)] we can trivially conclude our proof.
  *)

  Let a_to_b_end:
    forall aw bw b1 b2,
    End bw (b1,b2) ->
    a_to_b aw bw ->
    exists a1 a2 a3,
    ABA a1 b1 a2 /\ ABA a2 b2 a3 /\ End aw (a2, a3).
  Proof.
    intros.
    induction H0.
    - inversion H.
    - inversion H.
    - destruct bw.
      + inversion H0.
        subst.
        destruct e1 as (a1, a2'); destruct e2 as (a2, a3); destruct e as (b1', b2').
        inversion H1.
        subst.
        apply end_inv in H.
        inversion H. subst; clear H.
        exists a1; exists a2; exists a3.
        intuition.
        auto using end_cons, end_nil.
      + inversion H; subst; clear H.
        apply IHa_to_b in H5.
        destruct H5 as (a1, (a2, (a3, (Ha, (Hb, Hd))))).
        exists a1; exists a2; exists a3.
        intuition.
        auto using end_cons.
  Qed.

  Let cycle_a_to_b1:
    forall t,
    AA (t, t) ->
    exists w', BCycle w'.
  Proof.
    intros.
    apply C.a_to_aba in H.
    destruct H as (r, H).
    apply C.aba_refl in H.
    apply C.bab_to_b in H.
    exists ((r,r) :: nil)%list.
    simpl in *.
    auto using edge_to_cycle.
  Qed.

  (**
    Given a [ACycle aw] we can obtain a B-walk [bw] such that
    [a_to_b aw bw], by using lemma [a_to_b_total].
    By inverting [a_to_b aw bw] there are two cases to consider.
    The case where [aw = (a,a)::nil], we have that there exists a vertex [b] such that
    we have (a,b) and (b,a) in the AB-graph, thus (b,b) is a cycle in in the B-graph.
    The other case, we lemma [a_to_b_end] to obtain three AB-edges: (bi)-(an), (an)-(bn),
    and (bn)-(a1).
    ```
    (a1) ~~ .... ~~ (ai) ~~ (an) ~~ (a1) 
       \    /  \    /  \    /  \   /
        (b1) ~~ .... ~~ (bi) ~~ (bn) 
    ```
    From (bn)-(a1) and (a1)-(b1) we get that (bn)-(b1) is an edge in the B-graph, thus
    we have a B-cycle in the B-graph.
    ```
        (a1) ~~ .... ~~ (ai) ~~ (an) ~~ (a1) 
        /  \    /  \    /  \    /  \   / 
    (bn) ~~ (b1) ~~ .... ~~ (bi) ~~ (bn)
    ```
   *)

  Theorem cycle_a_to_b:
    forall aw,
    ACycle aw ->
    exists bw, BCycle bw.
  Proof.
    intros.
    inversion H; subst; clear H. (* ACycle w *)
    rename v1 into a1;
    rename v2 into a2;
    rename vn into an.
    inversion H1; subst. (* AWalk ((v1, v2) :: w0) *)
    apply a_to_b_total in H1.
    destruct H1 as (bw, (H1, H2)).
    inversion H1.
    - (* Case: (t,t)::nil *)
      subst.
      apply end_inv in H0; inversion H0; subst.
      eauto using cycle_a_to_b1.
    - (* Case: (a1,a2) :: aw *)
      subst.
      destruct e2 as (a2', a3).
      compute in H5; subst; rename a2' into a2. (* a2' = a2 *)
      destruct e as (b1, b2).
      (* Fun begins *)
      rename bw0 into bw.
      assert (Hre: exists b bn, End ((b1, b2) :: bw) (b, bn) ). {
        assert (H':= end_total (b1, b2) bw).
        destruct H' as ((?,?), ?).
        eauto.
      }
      destruct Hre as (b, (bn, Hre)).
      assert (Hre' := Hre).
      apply a_to_b_end with (aw := ((a1, a2) :: ((a2, a3) :: aw))%list) in Hre; auto.
      destruct Hre as (?, (an', (a1', (Hb, (Hc, Hd))))).
      assert (rw: (an', a1') = (an, a1)) by eauto using end_det.
      inversion rw; subst; destruct rw.
      assert (Hs: BAB bn a1 b1)
      by eauto using C.aba_to_bab, edge_a_to_b_inv1.
      (* Ready to build the path *)
      exists ((bn,b1)::(b1,b2)::bw)%list.
      eauto using cycle_def, end_cons.
  Qed.

End CycleAAtoBB.

Section B_TO_A.
  Variable A: Type.
  Variable B: Type.
  Variable AB : A -> B -> Prop.
  Variable BA : B -> A -> Prop.
  Variable w: list (B*B)%type.
  Lemma cycle_b_to_a:
    forall w,
    Cycle (Bipartite.BB AB BA) w ->
    exists w', Cycle (Bipartite.AA AB BA) w'.
  Proof.
    intros.
    apply Bipartite.cycle_aa_eq_rev_bb in H.
    apply cycle_a_to_b in H.
    destruct H as (w', H).
    exists w'.
    apply Bipartite.cycle_aa_eq_rev_bb.
    assumption.
  Qed.
End B_TO_A.
