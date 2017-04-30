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

(** In this file, we want to show some basic hoare triple. Those commands don't change the heap **)

Theorem hoare_skip : forall P,
    {{ P }} SKIP {{ P }}.
Proof.
  unfold hoare_triple. intros. split.
  unfold safeAt_bs, not. intro. inversion H0. intros.
  inversion H0; subst. assumption.
Qed.

Theorem hoare_asgn : forall P x a,
    {{ P [x --> a] }} (x ::= a) {{ P }}.
Proof.
  unfold hoare_triple. intros. split.
  unfold safeAt_bs, not. intros. inversion H0. intros.
  inversion H0; subst. unfold assertion_var_sub in H. assumption.
Qed.

Theorem hoare_seq : forall P R Q c1 c2,
    {{ P }} c1 {{ R }} ->
    {{ R }} c2 {{ Q }} ->
    {{ P }} c1 ;; c2 {{ Q }}.
Proof.
  unfold hoare_triple. intros. apply H in H1. destruct H1.
  split. unfold safeAt_bs, not. intro. inversion H3; subst.
  unfold safeAt_bs, not in H1. apply H1 in H5. inversion H5.
  apply H2 in H8. apply H0 in H8. destruct H8.
  unfold safeAt_bs, not in H4. apply H4 in H9. inversion H9.
  intros. inversion H3; subst. apply H2 in H8. apply H0 in H8.
  destruct H8. apply H5 in H9. assumption.
Qed.

Definition bassn b : sass :=
  fun st => (beval (fst st) b = true).

Lemma bexp_eval_true : forall b st,
    beval (fst st) b = true -> (bassn b) st.
Proof.
  intros. unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : forall b st,
    beval (fst st) b = false -> ~ ((bassn b) st).
Proof.
  intros. unfold not, bassn. intros. destruct st as [s h].
  simpl in *. rewrite H in H0. inversion H0.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
    {{ fun st => P st /\ bassn b st }} c1 {{ Q }} ->
    {{ fun st => P st /\ ~ bassn b st }} c2 {{ Q }} ->
    {{ P }} (IFB b THEN c1 ELSE c2 FI) {{ Q }}.
Proof.
  unfold hoare_triple. intros. unfold bassn in *.
  destruct (beval (fst st) b) eqn:Heqe.
  - split.
    assert (H2 : P st /\ beval (fst st) b = true) by auto.
    apply H in H2. destruct H2.
    unfold safeAt_bs, not. intro. inversion H4; subst.
    unfold safeAt_bs, not in H2. apply H2 in H11. inversion H11.
    simpl in Heqe. rewrite Heqe in H10. inversion H10.
    intros. inversion H2; subst.
    assert (P (s, h) /\ (beval (fst (s, h)) b = true)) by auto.
    apply H in H3. destruct H3. apply H4 in H9. assumption.
    simpl in Heqe. rewrite Heqe in H8. inversion H8.
  - split. destruct st as [s h].
    assert (P (s, h) /\ beval (fst (s, h)) b <> true).
    {
      simpl. split. assumption. apply (bexp_eval_false b (s, h)) in Heqe.
      unfold not, bassn in Heqe. simpl in *.
      destruct (beval s b) eqn:Heqe1. exfalso. auto. auto.
    }
    apply H0 in H2. destruct H2. unfold safeAt_bs, not.
    intro. inversion H4; subst. simpl in Heqe. rewrite Heqe in H11.
    inversion H11. unfold safeAt_bs, not in H2. apply H2 in H12.
    inversion H12. intros. inversion H2; subst.
    simpl in *. rewrite Heqe in H8. inversion H8. 
    assert (P (s, h) /\ beval (fst (s, h)) b <> true).
    {
      simpl. split. assumption. apply (bexp_eval_false b (s, h)) in Heqe.
      unfold not, bassn in Heqe. simpl in *.
      destruct (beval s b) eqn:Heqe1. exfalso. auto. auto.
    }
    apply H0 in H3. destruct H3. apply H4 in H9. assumption.
Qed.

Theorem hoare_while : forall P b c,
    {{ P //\\ (bassn b) }} c {{ P }} ->
    {{ P }} (WHILE b DO c END) {{ fun st => (P st /\ ~ (bassn b st)) }}.
Proof.
  unfold hoare_triple. intros. split.
  - unfold safeAt_bs, not. intros.
    remember (WHILE b DO c END, st) as comst.
    remember Abt as est. generalize dependent c.
    generalize dependent st.
    induction H1; intros; try inversion Heqest; try inversion Heqcomst;
      clear Heqest; clear Heqcomst; subst.
    + unfold bassn, s_conj in H2.
      assert (P (s, h) /\ beval s b = true) by auto.
      apply H2 in H3. destruct H3. unfold safeAt_bs, not in H3.
      apply H3 in H1. inversion H1.
    + assert ((WHILE b DO c0 END, (s', h'))
              = (WHILE b DO c0 END, (s', h')) -> False).
      {
        apply IHbig_step2; auto. unfold bassn, s_conj in H1.
        assert (P (s, h) /\ beval s b = true) by auto.
        apply H1 in H2. destruct H2. apply H3 in H1_. assumption.
      }
      apply H2. reflexivity.
  - intros. remember (WHILE b DO c END, st) as comst.
    remember (St est) as esst. generalize dependent c.
    generalize dependent st.
    induction H1; intros; try inversion Heqesst; try inversion Heqcomst;
      try clear Heqesst; try clear Heqcomst; subst.
    + unfold bassn. simpl. split. assumption. rewrite H. auto.
    + assert ((WHILE b DO c0 END, (s', h'))
              = (WHILE b DO c0 END, (s', h')) -> P est /\ ~ bassn b est).
      {
        apply IHbig_step2; auto. unfold s_conj, bassn in H1.
        assert (P (s, h) /\ beval s b = true) by auto.
        apply H1 in H2. destruct H2. apply H3 in H1_. assumption.
      }
      apply H2. reflexivity.
Qed.  
