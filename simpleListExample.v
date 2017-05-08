Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import SepLogic.
Require Import SepLogic_bigStep.
Require Import HoareLogic_bas_withSepLogic.

(** Here is definition of list **)
(* Because of the element in a list has at least two parts, so we
have to extend definition of pto as e |-> e1 e2  *)
Definition pto2 (e e1 e2 : aexp) : sass :=
  fun st : sstate =>
    match st with
    | (s, h) => h = h_update
                  (h_update emp_heap (aeval s e) (aeval s e1))
                  ((aeval s e) + 1) (aeval s e2)
    end.
Notation "e '|-->' e1 ',' e2" := (pto2 e e1 e2) (at level 60).

Definition pto2_any (e : aexp) : sass :=
  fun st => (exists e1 e2, pto2 e e1 e2 st).
Notation "e '|-->' -,-" := (pto2_any e) (at level 60).

Lemma union_heap_cell : forall l1 l2 n1 n2,
  l1 =? l2 = false ->
  h_union (h_update emp_heap l1 n1) (h_update emp_heap l2 n2) =
  h_update (h_update emp_heap l1 n1) l2 n2.
Proof.
  intros. unfold h_union. apply functional_extensionality. intro.
  destruct (in_not_in_dec x (h_update emp_heap l1 n1)).
  unfold in_dom in i. destruct i as [n].
  unfold h_update, eq_nat_dec in H0. destruct (l1 =? x) eqn:Heqe.
  inversion H0; subst. unfold h_update, eq_nat_dec.
  rewrite Heqe. destruct (l2 =? x) eqn:Heqe2; auto.
  apply beq_nat_true_iff in Heqe2.  apply beq_nat_true_iff in Heqe.
  rewrite <- Heqe in Heqe2. apply beq_nat_false_iff in H.
  omega. unfold emp_heap in H0. inversion H0.
  unfold not_in_dom in n. unfold h_update, eq_nat_dec in *.
  destruct (l1 =? x) eqn:Heqe. inversion n.
  destruct (l2 =? x) eqn:Heqe2; auto.
Qed.

Theorem loc2_loc_seq : forall e e1 e2,
    (e |--> e1, e2) ->> ((e |-> e1) ** ((APlus e (ANum 1)) |-> e2)).
Proof.
  unfold assert_implies. intros. destruct st as [s h].
  unfold pto2 in H. simpl.
  exists (h_update emp_heap (aeval s e) (aeval s e1)),
  (h_update emp_heap (aeval s e + 1) (aeval s e2)).
  split. unfold disjoint. intros.
  destruct
    (in_not_in_dec l (h_update emp_heap (aeval s e) (aeval s e1)));
    auto.
  unfold in_dom in i. destruct i as [n]. unfold not_in_dom.
  right. unfold h_update, eq_nat_dec in H0.
  destruct (aeval s e =? l) eqn:Heqe. apply beq_nat_true_iff in Heqe.
  unfold h_update, eq_nat_dec. destruct (aeval s e + 1 =? l) eqn:Heqe2;
                                 auto.
  apply beq_nat_true_iff in Heqe2. rewrite Heqe in Heqe2. omega.
  unfold emp_heap in H0. inversion H0.
  split. rewrite H. apply union_heap_cell. apply beq_nat_false_iff.
  omega. repeat (split; auto).
Qed.

Theorem loc_any : forall e e1 e2,
   ((e |-> e1) ** ((APlus e (ANum 1)) |-> e2)) ->> (e |--> -,-).
Proof.
  intros. unfold assert_implies. intros. destruct st as [s h].
  unfold star in H. unfold pto2_any.
  destruct H as [h1 [h2 [Hdisj [Hunion [H1 H2]]]]].
  exists e1, e2. unfold pto2. unfold pto in *. simpl in *.
  rewrite H1 in Hunion. rewrite H2 in Hunion.
  rewrite <- Hunion. apply union_heap_cell. apply beq_nat_false_iff.
  omega.
Qed.

Theorem loc_seq : forall e e1 e2,
    ((e |-> e1) ** ((APlus e (ANum 1)) |-> e2)) ->>
                                                (e |--> e1 , e2).
Proof.
  unfold assert_implies. intros. destruct st as [s h].
  unfold star in H.
  destruct H as [h1 [h2 [Hdisj [Hunion [H1 H2]]]]].
  unfold pto in *. unfold pto2. simpl in *.
  rewrite H1 in Hunion. rewrite H2 in Hunion. rewrite <- Hunion.
  apply union_heap_cell. apply beq_nat_false_iff. omega.
Qed.

(* To make the proof simple, we change the form of some hoare_triple *)
Lemma union_not_in_update : forall h l1 l2 n1 n2,
    not_in_dom l1 h /\ not_in_dom l2 h ->
    h_union h (h_update (h_update emp_heap l1 n1) l2 n2) =
    h_update (h_update h l1 n1) l2 n2.
Proof.
  intros. destruct H.
  unfold h_union. apply functional_extensionality. intros.
  destruct (in_not_in_dec x h). unfold h_update, eq_nat_dec.
  destruct (l2 =? x) eqn:Heqe. apply beq_nat_true_iff in Heqe. subst.
  unfold in_dom in i. unfold not_in_dom in H0. destruct i as [n].
  rewrite H0 in H1. inversion H1. destruct (l1 =? x) eqn:Heqe1.
  apply beq_nat_true_iff in Heqe1. subst. unfold in_dom in i.
  unfold not_in_dom in H. destruct i as [n]. rewrite H in H1.
  inversion H1. reflexivity. unfold h_update, eq_nat_dec.
  destruct (l2 =? x) eqn:Heqe; auto. destruct (l1 =? x) eqn:Heqe2; auto.
Qed.
  
Theorem hoare_cons_bkr : forall e1 e2 p v,
    {{ fun st => (forall v',
                     (((ANum v') |--> e1, e2)
                       --*(p [v --> (ANum v')])) st) }}
      (SCCons v e1 e2)
    {{ p }}.
Proof.
  unfold hoare_triple. intros. destruct st as [s h].
  split. unfold safeAt_bs, not. intros. inversion H0.
  intros. inversion H0; subst.
  assert ((ANum l |--> e1, e2 --* p [v --> ANum l]) (s, h)) by
      apply H.
  unfold simp in H1.
  assert (disjoint
            (h_update
               (h_update emp_heap l (aeval s e1))
               (l+1) (aeval s e2)) h).
  {
    unfold disjoint. intros. unfold not_in_dom.
    unfold h_update, eq_nat_dec. destruct (l+1 =? l0) eqn:Heqe.
    apply beq_nat_true_iff in Heqe. unfold not_in_dom in H8.
    rewrite Heqe in H8. auto. destruct (l =? l0) eqn:Heqe1.
    apply beq_nat_true_iff in Heqe1. unfold not_in_dom in H5.
    rewrite Heqe1 in H5. auto. unfold emp_heap. auto.
  }
  apply H1 in H2. unfold assertion_var_sub in H2. simpl in *.
  rewrite union_not_in_update in H2. assumption. auto.
  unfold pto2. reflexivity.
Qed.

Theorem hoare_lookup_bkr : forall e v p,
    {{ fun st => (exists v',
        ((e |-> (ANum v')) **
            ((e |-> (ANum v')) --* (p [v --> ANum v']))) st) }}
      (SCLookup v e)
    {{ p }}.
Proof.
  unfold hoare_triple. intros. split.
  unfold safeAt_bs, not. intros. inversion H0; subst.
  destruct H as [v']. simpl in H.
  destruct H as [h1 [h2 [Hdisj [Hunion [Hh1 H]]]]].
  unfold not_in_dom in H5. rewrite <- Hunion in H5.
  unfold h_union in H5. destruct (in_not_in_dec (aeval s e) h1).
  unfold in_dom in i. destruct i as [n]. rewrite H1 in H5.
  inversion H5. unfold not_in_dom in n. rewrite Hh1 in n.
  unfold h_update, eq_nat_dec in n. rewrite <- beq_nat_refl in n.
  inversion n.
  intros. inversion H0; subst. destruct H as [v'].
  simpl in H. destruct H as [h1 [h2 [Hdisj [Hunion [Hh1 H]]]]].
  assert (Hdisj1 : disjoint h1 h2) by assumption.
  apply H in Hdisj; auto. clear H.
  assert (h_union h1 h2 = h_union h2 h1).
  {
    apply disj_union_symmetry; auto.
  }
  rewrite <- H in Hdisj. rewrite Hunion in Hdisj.
  assert (Hin : h1 (aeval s e) = Some v').
  {
    rewrite Hh1. unfold h_update, eq_nat_dec.
    rewrite <- beq_nat_refl. reflexivity.
  }
  subst h. unfold h_union in H7.
  assert (in_dom (aeval s e) h1).
  {
    unfold in_dom. exists v'; auto.
  }
  destruct (in_not_in_dec (aeval s e) h1).
  rewrite Hin in H7. inversion H7; subst; auto.
  unfold not_in_dom in n0. rewrite n0 in Hin. inversion Hin.
Qed.

(* Some times we don't want to process entire list, so it will be good to define an other structure called segment *)
Inductive lseg : list nat -> aexp -> aexp -> sass :=
| emp_seg : forall s h i j,
    emp (s, h) -> aeval s i = aeval s j -> lseg nil i j (s, h)
| seg_extend : forall s h i j k a l n,
    ((i |--> a,j) ** (lseg l j k)) (s, h) -> aeval s a = n ->
    lseg (n :: l) i k (s, h).

Lemma lseg_eq : forall l i j s1 p s2 h,
    aeval s1 i = aeval s2 p -> aeval s1 j = aeval s2 j ->
    lseg l i j (s1, h) -> lseg l p j (s2, h).
Proof.
  intros l. induction l; intros.
  - inversion H1; subst. constructor. unfold emp in *.
    simpl in *. assumption. rewrite <- H. rewrite <- H0. assumption.
  - inversion H1; subst. unfold star in H7.
    destruct H7 as [h1 [h2 [Hdisj [Hunion [Hcell Hseg]]]]].
    rewrite <- Hunion.
    apply seg_extend with (ANum (aeval s1 j0)) (ANum (aeval s1 a0));
                         auto.
    unfold star. exists h1, h2. repeat (split; auto).
    unfold pto2 in *. simpl in *. rewrite Hcell.
    rewrite H. reflexivity. apply IHl with j0 s1; auto.
Qed.

Lemma disjoint_symmetry : forall h1 h2,
    disjoint h1 h2 -> disjoint h2 h1.
Proof.
  unfold disjoint in *. intros.
  destruct (H l); auto.
Qed.

Lemma union_emp_heap : forall h,
    h_union emp_heap h = h.
Proof.
  intros. unfold h_union. apply functional_extensionality.
  intros. destruct (in_not_in_dec x emp_heap); auto.
  unfold in_dom in i. destruct i as [n]. unfold emp_heap in H.
  inversion H.
Qed.

SearchAbout disjoint.

Lemma disjoint_union_still : forall h1 h2 h3,
    disjoint h1 h2 -> disjoint h1 h3 ->
    disjoint h1 (h_union h2 h3).
Proof.
  intros. unfold disjoint in *. intros.
  destruct (H l); auto.
  destruct (H0 l); auto.
  right. unfold not_in_dom in *. unfold h_union.
  destruct (in_not_in_dec l h2); auto.
Qed.

Lemma disjoint_union_sep : forall h1 h2 h3,
    disjoint (h_union h1 h2) h3 ->
    disjoint h1 h3 /\ disjoint h2 h3.
Proof.
  intros. unfold disjoint in *. split.
  - intros. destruct (H l); auto. left. unfold not_in_dom in H0.
    unfold not_in_dom. unfold h_union in H0.
    destruct (in_not_in_dec l h1); auto.
  - intros. destruct (H l); auto. left. unfold not_in_dom in H0.
    unfold h_union in H0. unfold not_in_dom.
    destruct (in_not_in_dec l h1); auto. unfold in_dom in i.
    destruct i as [n]. rewrite H1 in H0. inversion H0.
Qed.

Lemma union_association : forall h1 h2 h3,
    h_union (h_union h1 h2) h3 = h_union h1 (h_union h2 h3).
Proof.
  intros. unfold h_union. apply functional_extensionality.
  intros. destruct (in_not_in_dec x
           (fun l : nat => if in_not_in_dec l h1 then h1 l else h2 l)).
  unfold in_dom in i. destruct i as [n].
  destruct (in_not_in_dec x h1); auto.
  destruct (in_not_in_dec x h2); auto.
  unfold not_in_dom in n1. rewrite H in n1. inversion n1.
  unfold not_in_dom in n.
  destruct (in_not_in_dec x h1); auto.
  unfold in_dom in i. destruct i. rewrite n in H. inversion H.
  destruct (in_not_in_dec x h2); auto. unfold in_dom in i.
  destruct i. rewrite n in H. inversion H.
Qed.

Lemma lseg_add_tail : forall l i j a t,
    ((lseg l i j) ** (j |--> (ANum a), t))
      ->> (lseg (l ++ (a :: nil)) i t).
Proof.
  intros l. induction l; unfold assert_implies; intros.
  - destruct st as [s h]. simpl in *.
    destruct H as [h1 [h2 [Hdisj [Hunion [Hlseg Hh2]]]]].
    inversion Hlseg; subst. unfold emp in H1. simpl in H1.
    subst h1. rewrite union_emp_heap.
    apply seg_extend with (ANum (aeval s t)) (ANum a); auto.
    simpl. exists  (h_update (h_update emp_heap (aeval s j) a) 
                             (aeval s j + 1) (aeval s t)).
    exists emp_heap. split. apply disjoint_symmetry; auto.
    split. apply disj_union_symmetry; auto. apply disjoint_symmetry;
                                              auto.
    split. rewrite H4. reflexivity. constructor; auto.
    unfold emp; reflexivity.
  - simpl in *. destruct st as [s h]. inversion H; subst.
    destruct H0 as [h2 [Hdisj [Hunion [Hseg Hj]]]].
    inversion Hseg; subst. simpl in H5.
    destruct H5 as [h1 [h3 [Hdisj1 [Hunion1 [Hh1 Hseg1]]]]].
    apply seg_extend with j0 (ANum (aeval s a1)); auto.
    simpl. exists h1, (h_union h3 h2).
    split. apply disjoint_union_still; auto. simpl in Hj.
    rewrite <- Hunion1 in Hdisj. apply disjoint_union_sep in Hdisj.
    destruct Hdisj; auto. split. rewrite <- Hunion1.
    symmetry. apply union_association. split.
    rewrite Hh1. reflexivity.
    assert (((lseg l j0 j) ** (j |--> ANum a0, t)) (s, h_union h3 h2)).
    {
      simpl. exists h3, h2. rewrite <- Hunion1 in Hdisj.
      apply disjoint_union_sep in Hdisj. destruct Hdisj.
      repeat (split; auto).
    }
    apply IHl in H0. assumption.
Qed.

Section SimpleExample.

  Definition k : id := Id 0.
  Definition i : id := Id 1.
  Definition j : id := Id 2.
  Definition a : nat := 2.
  
  Example List_extend :=
    (SCCons k (ANum a) (AId i) ;; i ::= (AId k)).

  Example proofListExtend : forall l,
      {{ lseg l (AId i) (AId j) }}
        List_extend
      {{ lseg (a :: l) (AId i) (AId j) }}.
  Proof.
    unfold List_extend. intro. eapply hoare_seq.
    apply hoare_asgn. eapply hoare_consquence_pre.
    apply hoare_cons_bkr. unfold assert_implies. intros.
    destruct st as [s h]. unfold simp. intros. simpl in *.
    apply seg_extend with (ANum (s i)) (ANum a); auto.
    unfold star. exists h', h. repeat (split; auto).
    apply disj_union_symmetry. assumption.
    assert (st_update s k v' k = v').
    {
      unfold st_update, eq_id_dec. reflexivity.  
    }
    rewrite H2. apply lseg_eq with (AId i) s; auto.
  Qed.

  Example ListExtendConcise : forall l,
      {{ lseg l (AId i) (AId k) }}
        (SCCons i (ANum a) (AId i))
      {{ lseg (a :: l) (AId i) (AId k) }}.
  Proof.
    intros. eapply hoare_consquence_pre. apply hoare_cons_bkr.
    unfold assert_implies. intros. destruct st as [s h].
    simpl in *. intros. apply seg_extend with (ANum (s i)) (ANum a);
                          auto.
    unfold star. exists h', h.
    repeat (split; auto). apply disj_union_symmetry; auto.
    apply lseg_eq with (AId i) s; auto.
  Qed.

  Definition b : nat := 3.
  Definition t := Id 3.

  Example List_extend_tail :=
    (SCCons t (ANum b) (AId k) ;;
            [(APlus (AId j) (ANum 1))] ::= (AId t)).
  
  Example ListExtendTail : forall l,
      {{ (lseg l (AId i) (AId j))
           ** ((AId j) |--> (ANum a), (AId k)) }}
        List_extend_tail
      {{ lseg (l ++ (a :: nil) ++ (b :: nil)) (AId i) (AId k) }}.
  Proof.
    unfold List_extend_tail. intros. eapply hoare_seq. 
    apply hoare_mubr. 
    apply hoare_consquence_post with
    (lseg l (AId i) (AId j) ** AId j |--> ANum a, AId k
                         ** AId t |--> (ANum b), (AId k)). 
    eapply hoare_consquence_pre. apply hoare_cons_bkr.
    {
      unfold assert_implies. destruct st as [s h]. intros.
      simpl in *. intros.
      destruct H as [h1 [h2 [Hdisj [Hunion [Hlseg Hh2]]]]].
      exists h, h'. split. apply disjoint_symmetry; auto.
      split. auto. split. exists h1, h2. split; auto.
      split; auto. split.
      apply lseg_eq with (AId i) s; auto.
      assert (st_update s t v' j = s j).
      {
        unfold st_update, eq_id_dec. reflexivity.
      }
      rewrite H. 
      assert (st_update s t v' k = s k).
      {
        unfold st_update, eq_id_dec. reflexivity.
      }
      rewrite H2. assumption.
      unfold st_update, eq_id_dec; simpl. assumption.
    }
    unfold assert_implies; intros. destruct st as [s h].
    unfold star in H.
    destruct H as [h1 [h2 [Hdisj [Hunion [H Ht]]]]].
    destruct H as [h3 [h4 [Hdisj1 [Hunion1 [Hlseg Hj]]]]].
    apply loc2_loc_seq in Hj. unfold star in Hj.
    destruct Hj as [h5 [h6 [Hdisj2 [Hunion2 [Hj Hj1]]]]].
    unfold star. exists h6, (h_union h2 (h_union h3 h5)).
    split. rewrite <- Hunion2 in Hunion1.
    rewrite <- Hunion1 in Hdisj. apply disjoint_union_sep in Hdisj.
    destruct Hdisj. apply disjoint_union_sep in H0. destruct H0.
    apply disjoint_union_still; auto. apply disjoint_union_still.
    rewrite <- Hunion2 in Hdisj1. apply disjoint_symmetry in Hdisj1.
    apply disjoint_union_sep in Hdisj1. destruct Hdisj1. auto.
    apply disjoint_symmetry; auto. split.
    rewrite disj_union_symmetry. rewrite union_association.
    rewrite union_association. rewrite Hunion2. rewrite Hunion1.
    rewrite <- Hunion. apply disj_union_symmetry; auto.
    apply disjoint_symmetry; auto. apply disjoint_union_still.
    rewrite <- Hunion2 in Hunion1. rewrite <- Hunion1 in Hdisj.
    apply disjoint_union_sep in Hdisj. destruct Hdisj.
    apply disjoint_union_sep in H0; auto. destruct H0; auto.
    apply disjoint_union_still. rewrite <- Hunion2 in Hdisj1.
    apply disjoint_symmetry in Hdisj1.
    apply disjoint_union_sep in Hdisj1. destruct Hdisj1; auto.
    apply disjoint_symmetry; auto. split.
    simpl in Hj1. simpl. exists (s k); auto. simpl. intros. 
    assert (lseg (l ++ (a :: nil)) (AId i) (AId t)
                 (s, h_union (h_union h3 h5) h')).
    {
      apply lseg_add_tail with (AId j). unfold star.
      exists h3, (h_union h' h5). split. apply disjoint_symmetry in H.
      apply disjoint_union_sep in H. destruct H.
      apply disjoint_union_sep in H1. destruct H1.
      apply disjoint_union_still; auto. rewrite <- Hunion2 in Hdisj1.
      apply disjoint_symmetry in Hdisj1.
      apply disjoint_union_sep in Hdisj1. destruct Hdisj1.
      apply disjoint_symmetry; auto. split.
      assert (h_union h' h5 = h_union h5 h').
      {
        apply disj_union_symmetry. apply disjoint_symmetry in H.
        apply disjoint_union_sep in H. destruct H.
        apply disjoint_union_sep in H1. destruct H1.
        apply disjoint_symmetry; auto.
      } 
      rewrite H1. rewrite union_association. reflexivity. split.
      auto. simpl. rewrite <- union_heap_cell.
      rewrite H0. simpl in Hj. rewrite Hj. apply disj_union_symmetry.
      apply disjoint_symmetry in H. apply disjoint_union_sep in H.
      destruct H. apply disjoint_union_sep in H1. destruct H1.
      rewrite <- Hj. rewrite <- H0. apply disjoint_symmetry; auto.
      apply beq_nat_false_iff; omega.
    }
    assert ((lseg (l ++ a :: nil) (AId i) (AId t) ** ((AId t) |--> ANum b, AId k)) (s, h_union h2 (h_union (h_union h3 h5) h'))).
    {
      unfold star. exists (h_union (h_union h3 h5) h'), h2.
      split. apply disjoint_symmetry.
      apply disjoint_union_still. rewrite <- Hunion1 in Hdisj.
      rewrite <- Hunion2 in Hdisj. apply disjoint_union_sep in Hdisj.
      destruct Hdisj. apply disjoint_union_sep in H3. destruct H3.
      apply disjoint_union_still; (apply disjoint_symmetry; auto).
      apply disjoint_symmetry in H.  apply disjoint_union_sep in H.
      destruct H; auto. split. rewrite disj_union_symmetry. auto.
      apply disjoint_symmetry; apply disjoint_union_still.
      apply disjoint_union_still. rewrite <- Hunion1 in Hdisj.
      apply disjoint_union_sep in Hdisj. destruct Hdisj.
      apply disjoint_symmetry; auto. subst h1. subst h4.
      apply disjoint_union_sep in Hdisj. destruct Hdisj.
      apply disjoint_union_sep in H3. destruct H3.
      apply disjoint_symmetry; auto. apply disjoint_symmetry in H.
      apply disjoint_union_sep in H. destruct H; auto.
      split; auto.
    }
    apply lseg_add_tail in H2. rewrite union_association.
    simpl in H2. 
    rewrite <- app_assoc in H2. simpl in H2. auto.
  Qed.

  Example DeleteTail :=
    [APlus (AId j) (ANum 1)] ::= (AId t) ;;
    Dispose (AId k) ;; Dispose (APlus (AId k) (ANum 1)).

  Example proofDeleteTail : forall l,
      {{ (lseg l (AId i) (AId j)) ** ((AId j) |--> (ANum a), (AId k))
                      ** ((AId k) |--> (ANum b), (AId t)) }}
        DeleteTail
      {{ lseg (l ++ (a :: nil)) (AId i) (AId t) }}.
  Proof.
    intros. unfold DeleteTail. eapply hoare_seq.
    eapply hoare_seq. apply hoare_dispose_gb.
    apply hoare_dispose_gb.
    apply hoare_consquence_post with
    (((AId k) |--> -,-) ** (lseg (l ++ a :: nil) (AId i) (AId t))).
    {
      eapply hoare_consquence_pre. apply hoare_mubr.
      unfold assert_implies; intros. destruct st as [s h].
      unfold star in H.
      destruct H as [h1 [h2 [Hdisj [Hunion [H Hk]]]]].
      destruct H as [h3 [h4 [Hdisj1 [Hunion1 [Hlseg Hj]]]]].
      simpl. apply loc2_loc_seq in Hj.
      unfold star in Hj.
      destruct Hj as [h5 [h6 [Hdisj2 [Hunion2 [Hj Hj1]]]]].
      exists h6, (h_union (h_union h3 h5) h2).
      split.
      {
        apply disjoint_union_still. apply disjoint_union_still.
        rewrite <- Hunion2 in Hdisj1. apply disjoint_symmetry in Hdisj1.
        apply disjoint_union_sep in Hdisj1. destruct Hdisj1; auto.
        apply disjoint_symmetry. auto.
        rewrite <- Hunion2 in Hunion1. rewrite <- Hunion1 in Hdisj.
        apply disjoint_union_sep in Hdisj. destruct Hdisj.
        apply disjoint_union_sep in H0. destruct H0; auto.
      }
      split. rewrite <- union_association.
      assert (h_union h3 h5 = h_union h5 h3).
      {
        apply disj_union_symmetry. rewrite <- Hunion2 in Hdisj1.
        apply disjoint_symmetry in Hdisj1.
        apply disjoint_union_sep in Hdisj1. destruct Hdisj1.
        apply disjoint_symmetry; auto.
      }
      rewrite H.
      assert (h_union h6 (h_union h5 h3) = h_union (h_union h6 h5) h3)
        by (symmetry; apply union_association).
      rewrite H0.
      assert (h_union h6 h5 = h_union h5 h6) by
          (apply disj_union_symmetry; apply disjoint_symmetry; auto).
      rewrite H1. rewrite Hunion2.
      assert (h_union h4 h3 = h_union h3 h4) by
          (apply disj_union_symmetry; apply disjoint_symmetry; auto).
      rewrite H2. rewrite Hunion1. auto.
      split. exists (s k). auto. intros. 
      exists h2, (h_union (h_union h3 h5) h'). split.
      apply disjoint_union_still. apply disjoint_union_still.
      rewrite <- Hunion1 in Hdisj. apply disjoint_union_sep in Hdisj.
      destruct Hdisj; apply disjoint_symmetry; auto.
      rewrite <- Hunion1 in Hdisj. rewrite <- Hunion2 in Hdisj.
      apply disjoint_union_sep in Hdisj; destruct Hdisj.
      apply disjoint_union_sep in H2; destruct H2.
      apply disjoint_symmetry; auto. apply disjoint_symmetry in H.
      apply disjoint_union_sep in H. destruct H. auto. split.
      rewrite <- union_association.
      assert (h_union h2 (h_union h3 h5) = h_union (h_union h3 h5) h2).
      {
        apply disj_union_symmetry. rewrite <- Hunion1 in Hdisj.
        rewrite <- Hunion2 in Hdisj. apply disjoint_union_sep in Hdisj.
        destruct Hdisj. apply disjoint_union_sep in H2. destruct H2.
        apply disjoint_union_still; apply disjoint_symmetry; auto.
      }
      rewrite H1. reflexivity. split. apply loc2_loc_seq in Hk.
      apply loc_any in Hk. auto.
      assert (((lseg l (AId i) (AId j))
                 ** ((AId j) |--> (ANum a), (AId t)))
                (s, h_union (h_union h3 h5) h')).
      {
        unfold star. exists h3, (h_union h5 h').
        split. rewrite <- Hunion2 in Hdisj1.
        apply disjoint_symmetry in Hdisj1. apply disjoint_union_sep
          in Hdisj1.
        apply disjoint_union_still. destruct Hdisj1;
                                      apply disjoint_symmetry; auto.
        apply disjoint_symmetry in H.
        apply disjoint_union_sep in H. destruct H.
        apply disjoint_union_sep in H; destruct H; auto.
        split. rewrite union_association. reflexivity.
        split. auto. simpl. simpl in Hj. rewrite Hj. rewrite H0.
        apply union_heap_cell. apply beq_nat_false_iff. omega.
      }
      apply lseg_add_tail in H1; auto.
    }
    unfold assert_implies. intros. destruct st as [s h].
    unfold star in H.
    destruct H as [h1 [h2 [Hdisj [Hunion [Hk Hlseg]]]]].
    unfold pto2_any in Hk. destruct Hk as [e1 [e2]].
    apply loc2_loc_seq in H. unfold star in H.
    destruct H as [h3 [h4 [Hdisj1 [Hunion1 [Hk Hk1]]]]].
    unfold star. exists h3, (h_union h4 h2). split.
    apply disjoint_union_still; auto. rewrite <- Hunion1 in Hdisj.
    apply disjoint_union_sep in Hdisj. destruct Hdisj; auto.
    split. rewrite <- union_association. rewrite Hunion1. auto.
    split. simpl. exists (aeval s e1). simpl in Hk; auto.
    exists h4, h2. repeat (split; auto).
    rewrite <- Hunion1 in Hdisj. apply disjoint_union_sep in Hdisj.
    destruct Hdisj; auto. simpl in Hk1. simpl. exists (aeval s e2).
    auto.
  Qed.
  
End SimpleExample.

Definition null : nat := 0.

(* Sometimes, we just care the construction of the list. We don't need to knew the content of the list. So we use Bornat List *)
Inductive listN : list nat -> aexp -> sass :=
| emp_listN : forall s h i,
    emp (s, h) /\ aeval s i = null -> listN nil i (s, h)
| cons_listN : forall s h a l i j,
    a = aeval s i -> aeval s i <> null ->
    (((APlus i (ANum 1)) |-> j) ** (listN l j)) (s, h) ->
    listN (a :: l) i (s, h).

Lemma ListN_eq : forall l i j s1 s2 h,
    aeval s1 i = aeval s2 j -> listN l i (s1, h) ->
    listN l j (s2, h).
Proof.
  intro l. induction l; intros.
  - constructor. inversion H0; subst. destruct H4. split.
    unfold emp in *. simpl in *. assumption. rewrite H in H2. auto.
  - inversion H0; subst. unfold star in H8.
    destruct H8 as [h1 [h2 [Hdisj [Hunion [Hj0 HlistN]]]]].
    apply cons_listN with (ANum (aeval s1 j1)); auto.
    rewrite <- H; auto. unfold star. exists h1, h2.
    repeat (split; auto). simpl. simpl in Hj0. rewrite <- H. assumption.
    apply IHl with (i := j1) (s1 := s1). reflexivity. auto.
Qed.

Lemma listN_null_nil : forall l i s h,
    listN l i (s, h) -> aeval s i = null ->
    l = nil /\ h = emp_heap.
Proof.
  intros. inversion H; subst; auto. destruct H4. unfold emp in H1.
  simpl in H1. subst h. auto. rewrite H0 in H6. omega.
Qed.

Section ListReverse.

  (* Here, we define the operation of reversion *)
  Fixpoint reverseList (l : list nat) : list nat :=
    match l with
    | nil => nil
    | a :: l' => reverseList l' ++ (a :: nil)
    end.

  Example listReverse :=
    j ::= (ANum null) ;;
      WHILE (BNot (BEq (AId i) (ANum null))) DO
         SCLookup k (APlus (AId i) (ANum 1)) ;;
         [APlus (AId i) (ANum 1)] ::= (AId j) ;;
         j ::= (AId i) ;;
         i ::= (AId k)
      END.
  
  Example proofListReverseCorrect : forall l0,
      {{ listN l0 (AId i) }}
        listReverse
      {{ listN (reverseList l0) (AId j) }}.
  Proof.
    intros. unfold listReverse.
    eapply hoare_seq with
    ((listN l0 (AId i)) ** (fun st => emp st /\
                                      (aeval (fst st) (AId j)) = null )).
    apply hoare_consquence_pre with
    (fun st => exists l1 l2,
         (listN l1 (AId i) ** listN l2 (AId j)) st
         /\ reverseList l0 = (reverseList l1) ++ l2).
    eapply hoare_consquence_post. apply hoare_while.
    {
      eapply hoare_seq. eapply hoare_seq. eapply hoare_seq.
      apply hoare_asgn. apply hoare_asgn.
      apply hoare_mubr. eapply hoare_consquence_pre.
      apply hoare_lookup_bkr. unfold assert_implies. intros.
      destruct st as [s h]. unfold s_conj in H.
      destruct H as [Hlist Hi]. destruct Hlist as [l1 [l2 [Hlist Hrev]]].
      unfold star in Hlist.
      destruct Hlist as [h1 [h2 [Hdisj [Hunion [Hlist1 Hlist2]]]]].
      unfold bassn in Hi. simpl in Hi. destruct (s i =? null) eqn:Heqe.
      simpl in Hi. inversion Hi. clear Hi. inversion Hlist1; subst.
      destruct H2. simpl in H0. apply beq_nat_false_iff in Heqe. omega.
      unfold star in H5.
      destruct H5 as [h3 [h4 [Hdisj1 [Hunion1 [Hi1 Hj0]]]]].
      exists (aeval s j0). unfold star.
      exists h3, (h_union h4 h2). split.
      apply disjoint_union_still; auto. rewrite <- Hunion1 in Hdisj.
      apply disjoint_union_sep in Hdisj; destruct Hdisj; auto.
      split. rewrite <- union_association. rewrite Hunion1. auto.
      split. simpl. simpl in Hi1. auto. simpl. intros.
      exists h', (h_union h4 h2). split; auto. split.
      apply disj_union_symmetry; auto. split. exists (aeval s j0).
      assert (st_update s k (aeval s j0) i = s i).
      {
        unfold st_update, eq_id_dec. simpl. reflexivity.  
      }
      rewrite H1. auto. intros.
      assert (st_update s k (aeval s j0) i + 1 = s i + 1).
      {
        unfold st_update, eq_id_dec. simpl. reflexivity.
      }
      rewrite H3 in H2. clear H3.
      assert (st_update s k (aeval s j0) j = s j).
      {
        unfold st_update, eq_id_dec. simpl. reflexivity.
      }
      rewrite H3 in H2; clear H3. exists l. exists ((s i) :: l2).
      split. exists h4, (h_union h'0 h2). split.
      apply disjoint_symmetry in H1. apply disjoint_union_sep in H1.
      destruct H1. apply disjoint_union_still; auto.
      rewrite <- Hunion1 in Hdisj.
      apply disjoint_union_sep in Hdisj. destruct Hdisj; auto. split.
      rewrite union_association.
      assert (h_union h'0 h2 = h_union h2 h'0).
      {
        apply disj_union_symmetry. apply disjoint_symmetry in H1.
        apply disjoint_union_sep in H1. destruct H1.
        apply disjoint_symmetry. auto.
      }
      rewrite H3. auto. split.
      assert (listN l j0 (s, h4) ->
             listN l (AId i)
    (st_update
       (st_update (st_update s k (aeval s j0)) j
          (st_update s k (aeval s j0) i)) i
       (st_update (st_update s k (aeval s j0)) j
                  (st_update s k (aeval s j0) i) k), h4)).
      {
        apply ListN_eq. unfold st_update, eq_id_dec. reflexivity.
      }
      auto. 
      apply cons_listN with (ANum (s j)). unfold st_update, eq_id_dec.
      reflexivity. unfold st_update, eq_id_dec. simpl. simpl in H4.
      auto. unfold star. exists h'0, h2. split.
      apply disjoint_symmetry in H1. apply disjoint_union_sep in H1.
      destruct H1. apply disjoint_symmetry; auto. split. auto.
      split. simpl. unfold st_update, eq_id_dec. simpl. auto.
      assert (listN l2 (AId j) (s, h2) ->
              listN l2 (ANum (s j))
    (st_update
       (st_update (st_update s k (aeval s j0)) j
          (st_update s k (aeval s j0) i)) i
       (st_update (st_update s k (aeval s j0)) j
                  (st_update s k (aeval s j0) i) k), h2)).
      {
        apply ListN_eq. unfold st_update, eq_id_dec. reflexivity.
      }
      auto. simpl in Hrev. SearchAbout list.
      rewrite <- app_assoc in Hrev. simpl in Hrev. auto.
    }
    {
      unfold assert_implies. intros. destruct st as [s h].
      destruct H as [H Hbassn].
      destruct H as [l1 [l2 [Hlist Hrev]]].
      unfold not, bassn in Hbassn. simpl in Hbassn.
      destruct (s i =? null) eqn:Heqe.
      apply beq_nat_true_iff in Heqe. unfold star in Hlist.
      destruct Hlist as [h1 [h2 [Hdisj [Hunion [Hlist1 Hlist2]]]]].
      apply listN_null_nil in Hlist1; auto. destruct Hlist1.
      subst l1. simpl in Hrev. rewrite Hrev. rewrite H0 in Hunion.
      rewrite union_emp_heap in Hunion. subst h2. auto.
      simpl in Hbassn. exfalso. auto.
    }
    {
      unfold assert_implies. intros. destruct st as [s h].
      unfold star in H.
      destruct H as [h1 [h2 [Hdisj [Hunion [Hlist [Hemp Hj]]]]]].
      unfold emp in Hemp. simpl in *. exists l0, nil.
      split. exists h, emp_heap. subst h2.
      assert (h1 = h).
      {
        assert (h_union h1 emp_heap = h_union emp_heap h1)
          by (apply disj_union_symmetry; auto).
        rewrite H in Hunion. rewrite union_emp_heap in Hunion. auto.
      }
      subst h1. repeat (split; auto). constructor. unfold emp.
      simpl. auto. rewrite app_nil_r. auto.
    }
    eapply hoare_consquence_pre. apply hoare_asgn.
    {
      unfold assert_implies. intros. destruct st as [s h].
      unfold star. simpl. exists h, emp_heap.
      split. unfold disjoint. intros. right. unfold not_in_dom.
      reflexivity. split.
      assert (h_union h emp_heap = h_union emp_heap h).
      {
        apply disj_union_symmetry. unfold disjoint. intros.
        right. unfold not_in_dom. reflexivity.
      }
      rewrite H0. rewrite union_emp_heap. reflexivity.
      split. apply ListN_eq with (i := AId i) (s1 := s); auto.
      unfold emp. simpl. split. reflexivity.
      unfold st_update, eq_id_dec. reflexivity.
    }
  Qed.
  
End ListReverse.
