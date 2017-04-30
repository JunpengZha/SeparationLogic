Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.
Require Import Hoare.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import SepLogic.

Example test : forall x y s h,
    x = Id 1 -> y = Id 2 ->
    s = st_update (st_update (fun _ => 0) x 1) y 2 ->
    h = h_update emp_heap 1 10 ->
    (((AId x) |-> (ANum 10) \\// (AId y) |-> (ANum 20)) --* (((AId x) |-> (ANum 10)) ** ((AId y) |-> (ANum 20)))) (s, h).
Proof.
  intros. unfold simp. intros. simpl in *.
  unfold s_disj in H4. destruct H4.
  - unfold pto in H4. simpl in H4. rewrite H1 in H4.
    subst. unfold st_update in H3. simpl in H3. unfold disjoint in H3.
    destruct (H3 1).
    + unfold not_in_dom in H. unfold h_update in H.
      simpl in H. inversion H.
    + unfold not_in_dom in H. unfold h_update in H.
      simpl in H. inversion H.
  - unfold pto in H4. simpl in *. subst.
    unfold st_update in H3. simpl in H3.
    unfold st_update; simpl.
    exists (h_update emp_heap 1 10).
    exists ( h_update emp_heap 2 20).
    split. unfold disjoint in *. intros. destruct (H3 l).
    right. assumption. left. assumption.
    auto.
Qed.

Axiom excluded_middle : forall P,
    P \/ (~P).

(* Extend Hoare Logic by separation logic *)
Notation "'SKIP'" :=
  SCSkip.
Notation "x '::=' a" :=
  (SCAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (SCSeq c1 c2) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (SCIf b c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (SCWhile b c) (at level 80, right associativity).
Notation "'Cons' X e1 e2" :=
  (SCCons X e1 e2) (at level 60, right associativity).
Notation "'Lookup' X e" :=
  (SCLookup X e) (at level 60, e at next level, right associativity).
Notation "'[' e1 ']' '::=' e2" :=
  (SCMutation e1 e2) (at level 60, e1 at next level, e2 at next level,
                      right associativity).
Notation "'Dispose' e" :=
  (SCDispose e) (at level 60, e at next level, right associativity).

(* The list of the variables that have been changed *)
Fixpoint modified_scom_var (c : scom) : list id :=
  match c with
  | SCSkip => nil
  | SCAss x a => x :: nil
  | SCSeq c1 c2 => (modified_scom_var c1) ++ (modified_scom_var c2)
  | SCIf b c1 c2 =>
    (modified_scom_var c1) ++ (modified_scom_var c2)
  | SCWhile b c => modified_scom_var c
  | SCCons x e1 e2 => x :: nil
  | SCLookup x e => x :: nil
  | SCMutation e1 e2 => nil
  | SCDispose e => nil
  end.

(* The list of the location that have been changed *)
Fixpoint modified_scom_loc (c : scom) : list aexp :=
  match c with
  | SCSkip => nil
  | SCAss x a => nil
  | SCSeq c1 c2 => (modified_scom_loc c1) ++ (modified_scom_loc c2)
  | SCIf b c1 c2 =>
    (modified_scom_loc c1) ++ (modified_scom_loc c2)
  | SCWhile b c => modified_scom_loc c
  | SCCons x e1 e2 => nil
  | SCLookup x e => nil
  | SCMutation e1 e2 => e1 :: nil
  | SCDispose e => e :: nil
  end.

(* Here we define the variables that free in assertion P *)
Definition inde (l : list id) (P : sass) :=
  forall s h,
    (forall x v, In x l ->
                 (P (s, h) <-> P (st_update s x v, h))).

(* There are some lemmas to help us in the next step *)
Lemma inde_seq : forall c1 c2 R,
    inde (modified_scom_var (c1 ;; c2)) R ->
    inde (modified_scom_var c1) R /\ inde (modified_scom_var c2) R.
Proof.
  intros. unfold inde in H. split.
  - unfold inde. intros. simpl in *.
    assert (In x (modified_scom_var c1 ++ modified_scom_var c2)).
    {
      apply in_or_app. left. assumption.
    }
    apply (H s h x v) in H1. assumption.
  - unfold inde. intros. simpl in *.
    assert (In x (modified_scom_var c1 ++ modified_scom_var c2)).
    {
      apply in_or_app. right. assumption.
    }
    apply (H s h x v) in H1. assumption.
Qed.

Lemma inde_if : forall b c1 c2 R,
    inde (modified_scom_var (IFB b THEN c1 ELSE c2 FI)) R ->
    inde (modified_scom_var c1) R /\ inde (modified_scom_var c2) R.
Proof.
  intros. simpl in *. unfold inde in *. split.
  - intros.
    assert (In x (modified_scom_var c1 ++ modified_scom_var c2)).
    {
      apply in_or_app. auto.
    }
    apply (H s h x v) in H1. assumption.
  - intros.
    assert (In x (modified_scom_var c1 ++ modified_scom_var c2)).
    {
      apply in_or_app. auto.
    }
    apply (H s h x v) in H1. assumption.
Qed.

(* Here we have to explain that if an assertion R doesn't mention any variable modified by c, then the R still support *)
Theorem mention_modified_free : forall st st' c R,
    inde (modified_scom_var c) R ->
    big_step (c, st) (St st') ->
    (forall h1, R (fst st, h1) -> R (fst st', h1)).
Proof.
  intros st st' c R Hinde Hstep.
  remember (c, st) as comst. remember (St st') as est.
  generalize dependent st. generalize dependent st'.
  generalize dependent c. induction Hstep; intros.
  - (* SKIP *) inversion Heqcomst; subst. inversion Heqest; subst.
    clear Heqcomst. clear Heqest. assumption.
  - (* Asg *) inversion Heqcomst; subst. inversion Heqest; subst.
    clear Heqcomst. clear Heqest. simpl in *.
    unfold inde in Hinde.
    assert (In X (X :: nil)).
    {
      unfold In. left. reflexivity.
    }
    apply (Hinde s h1 X (aeval s e)) in H. apply H. assumption.
  - (* SeqAb *) inversion Heqest.
  - (* Seq *) inversion Heqcomst; subst. clear Heqcomst.
    apply inde_seq in Hinde. destruct Hinde.
    apply IHHstep1
    with (c := c1) (st'0 := st') (st := st0) (h1 := h1) in H0; auto.
    apply IHHstep2
    with (c := c2) (st'1 := st'0) (st := st') (h1 := h1) in H1; auto.
  - (* If_true *) inversion Heqcomst; subst. clear Heqcomst.
    apply inde_if in Hinde. destruct Hinde.
    apply IHHstep with (st'0 := st') (st := (s, h)) (h1 := h1) in H1;
      auto.
  - (* If_false *) inversion Heqcomst; subst. clear Heqcomst.
    apply inde_if in Hinde. destruct Hinde.
    apply IHHstep with (st'0 := st') (st := (s, h)) (h1 := h1) in H2;
      auto.
  - (* WHILE_end *) inversion Heqest; subst. inversion Heqcomst; subst.
    assumption.
  - (* WHILE_Ab *) inversion Heqest.
  - (* WHILE_Loop *) inversion Heqcomst; subst. clear Heqcomst.
    simpl in H0.
    assert (inde (modified_scom_var (WHILE b DO c END)) R) by assumption.
    simpl in H1.
    apply IHHstep1 with
    (st' := (s', h')) (st := (s, h)) (h1 := h1) in H1; auto.
    simpl in H1.
    apply IHHstep2 with
    (st'0 := st') (st := (s', h')) (h1 := h1) in Hinde; auto.
  - (* Cons *) inversion Heqcomst; subst. inversion Heqest; subst.
    clear Heqest. clear Heqcomst. simpl in *. unfold inde in Hinde.
    assert (In X (X :: nil)).
    {
      unfold In. auto.
    }
    apply (Hinde s h1 X l) in H1. apply H1. assumption.
  - (* Lookup *) inversion Heqest; subst. inversion Heqcomst; subst.
    clear Heqest. clear Heqcomst. simpl in *. unfold inde in Hinde.
    assert (In X (X :: nil)).
    {
      unfold In. auto.
    }
    apply (Hinde s h1 X n) in H. apply H. assumption.
  - (* LookupAb *) inversion Heqest.
  - (* Mutation *) inversion Heqcomst; subst. inversion Heqest; subst.
    clear Heqcomst. clear Heqest. simpl in *. assumption.
  - (* MutationAb *) inversion Heqest.
  - (* Dispose *) inversion Heqcomst; subst. inversion Heqest; subst.
    clear Heqcomst. clear Heqest. simpl in *. assumption.
  - (* DisposeAb *) inversion Heqest.
Qed.

Definition safeAt_bs (c : scom) (s : sstate) :=
  ~ (big_step (c, s) (Abt)).
(*
  forall est, big_step (c, s) est -> exists st, est = St st.
*)

Definition safty_Mono_bs (c : scom) :=
  forall s h1 h2, safeAt_bs c (s, h1) -> disjoint h1 h2 ->
                  safeAt_bs c (s, h_union h1 h2).

Definition frame_bs (c : scom) :=
  forall s s' h1 h2 h',
    safeAt_bs c (s, h1) -> disjoint h1 h2 ->
    big_step (c, (s, h_union h1 h2)) (St (s', h')) ->
    (exists h1', big_step (c, (s, h1))(St (s', h1')) /\ disjoint h1' h2 /\
                 h_union h1' h2 = h').

Lemma safeAt_bs_seq : forall s h c1 c2,
    safeAt_bs (c1 ;; c2) (s, h) -> safeAt_bs c1 (s, h).
Proof.
  intros. unfold safeAt_bs, not in *. intro.
  assert (big_step (c1;; c2, (s, h)) Abt).
  {
    apply BS_SeqAb. assumption.
  }
  apply H in H1. inversion H1.
Qed.

Lemma safeAt_bs_seq2 : forall s h c1 c2 st,
    safeAt_bs (c1 ;; c2) (s, h) -> big_step (c1, (s, h)) (St st) ->
    safeAt_bs c2 st.
Proof.
  intros. unfold safeAt_bs, not in *. intro.
  assert (big_step (c1;; c2, (s, h)) Abt).
  {
    apply BS_Seq with st; assumption.
  }
  apply H in H2. inversion H2.
Qed.

Lemma safeAt_bs_if : forall s h b c1 c2,
    safeAt_bs (IFB b THEN c1 ELSE c2 FI) (s, h) /\ beval s b = true ->
    safeAt_bs c1 (s, h).
Proof.
  intros. unfold safeAt_bs, not in *. intro. destruct H.
  apply (BS_IfTrue b c1 c2 s h Abt) in H1; auto.
Qed.

Lemma safeAt_bs_if2 : forall s h b c1 c2,
    safeAt_bs (IFB b THEN c1 ELSE c2 FI) (s, h) /\ beval s b = false ->
    safeAt_bs c2 (s, h).
Proof.
  intros. unfold safeAt_bs, not in *. intro. destruct H.
  apply (BS_IfFalse b c1 c2 s h Abt) in H0; auto.
Qed.

Lemma safeAt_bs_while : forall s h b c,
    safeAt_bs (WHILE b DO c END) (s, h) /\ beval s b = true ->
    safeAt_bs c (s, h).
Proof.
  intros. destruct H. unfold safeAt_bs, not in *. intro.
  apply (BS_WhileLoopAb b c s h) in H0; auto.
Qed.

Lemma safeAt_bs_while2 : forall s h b c st,
    safeAt_bs (WHILE b DO c END) (s, h) -> beval s b = true ->
    big_step (c, (s, h)) (St st) -> 
    safeAt_bs (WHILE b DO c END) st.
Proof.
  intros. unfold safeAt_bs, not in *. intro.
  assert (big_step (WHILE b DO c END, (s, h)) Abt).
  destruct st as [s' h'].
  apply BS_WhileLoop with s' h'; auto. apply H in H3. inversion H3.
Qed.

Lemma safeAt_bs_lookup : forall s h i a,
    safeAt_bs (SCLookup i a) (s, h) ->
    in_dom (aeval s a) h.
Proof.
  intros. unfold safeAt_bs, not in H.
  destruct (in_not_in_dec (aeval s a) h). assumption.
  assert (big_step (SCLookup i a, (s, h)) Abt).
  {
    apply BS_LookupAb with (aeval s a); auto.
  }
  apply H in H0. inversion H0.
Qed.

Lemma safeAt_bs_mutation : forall s h e1 e2,
    safeAt_bs ([e1]::= e2) (s, h) ->
    in_dom (aeval s e1) h.
Proof.
  intros. unfold safeAt_bs, not in H.
  destruct (in_not_in_dec (aeval s e1) h). assumption.
  assert (big_step ([e1]::=e2, (s, h)) Abt).
  {
    apply BS_MutationAb with (aeval s e1); auto.
  }
  apply H in H0. inversion H0.
Qed.

Lemma safeAt_bs_dispose : forall s h e,
    safeAt_bs (Dispose e) (s, h) ->
    in_dom (aeval s e) h.
Proof.
  intros. unfold safeAt_bs, not in H.
  destruct (in_not_in_dec (aeval s e) h). assumption.
  assert (big_step (Dispose e, (s, h)) Abt).
  {
    apply BS_DisposeAb with (aeval s e); auto.
  }
  apply H in H0. inversion H0.
Qed.

Lemma union_num_unchange : forall l n h1 h2,
    in_dom l h1 -> (h_union h1 h2) l = Some n ->
    h1 l = Some n.
Proof.
  intros. unfold h_union in H0. destruct (in_not_in_dec l h1); auto.
  unfold in_dom in H. destruct H. unfold not_in_dom in n0.
  rewrite H in n0. inversion n0.
Qed.

Theorem frame_bs_correct : forall c, frame_bs c.
Proof with eauto.
  unfold frame_bs. intros.
  remember (c, (s, h_union h1 h2)) as comst.
  remember (St (s', h')) as est.
  generalize dependent c. generalize dependent s.
  generalize dependent h1. generalize dependent h2.
  generalize dependent h'. generalize dependent s'.
  induction H1; intros; inversion Heqest; subst;
    inversion Heqcomst; subst; try clear Heqcomst; try clear Heqest.
  - (* SKIP *) exists h1. auto.
  - (* Asg *) exists h1. auto.
  - (* Seq *) destruct st'.
    assert (
        exists h1', big_step (c1, (s, h1)) (St (s0, h1')) /\
                    disjoint h1' h2 /\ h_union h1' h2 = h
      ).
    {
      apply IHbig_step1; auto. apply safeAt_bs_seq in H.
      assumption.
    }
    destruct H2 as [h1' [Hstep1 [Hdisj1 Hunion1]]].
    assert (
        exists h1'', big_step (c2, (s0, h1')) (St (s', h1'')) /\
                     disjoint h1'' h2 /\ h_union h1'' h2 = h'
      ).
    {
      apply IHbig_step2; auto.
      apply safeAt_bs_seq2 with (st := (s0, h1')) in H; assumption.
      rewrite Hunion1. reflexivity.
    }
    destruct H2 as [h1'' [Hstep2 [Hdisj2 Hunion2]]].
    exists h1''. split. econstructor ... auto.
  - (* IFB_true *)
    assert (
        exists h1', big_step (c1, (s0, h1)) (St (s', h1')) /\
                    disjoint h1' h2 /\ h_union h1' h2 = h'
      ).
    {
      apply IHbig_step; auto. eapply safeAt_bs_if ...
    }
    destruct H4 as [h1' [Hstep [Hdisj Hunion]]]. exists h1'.
    split. eapply BS_IfTrue ... auto.
  - (* IFB_false *)
    assert (
        exists h1', big_step (c2, (s0, h1)) (St (s', h1')) /\
                    disjoint h1' h2 /\ h_union h1' h2 = h'
      ).
    {
      apply IHbig_step; auto. eapply safeAt_bs_if2 ...
    }
    destruct H4 as [h1' [Hstep [Hdisj Hunion]]]. exists h1'.
    split. eapply BS_IfFalse ... auto.
  - (* While_end *) exists h1. split. eapply BS_WhileEnd ...
    auto.
  - (* While_Loop *)
    assert (
        exists h1', big_step (c, (s0, h1)) (St (s', h1')) /\
                    disjoint h1' h2 /\ h_union h1' h2 = h'
      ).
    {
      apply IHbig_step1; auto. eapply safeAt_bs_while ...
    }
    destruct H3 as [h1' [Hstep1 [Hdisj1 Hunion1]]].
    assert (
        exists h1'', big_step (WHILE b DO c END, (s', h1'))
                              (St (s'0, h1'')) /\ disjoint h1'' h2 /\
                     h_union h1'' h2 = h'0
      ).
    {
      apply IHbig_step2; auto. eapply safeAt_bs_while2 ...
      rewrite Hunion1; reflexivity.
    }
    destruct H3 as [h1'' [Hstep2 [Hdisj2 Hunion2]]].
    exists h1''. split. eapply BS_WhileLoop ... auto.
  - (* Cons *)
    exists (h_update (h_update h1 l (aeval s0 e1))
                     (l+1) (aeval s0 e2)).
    split. econstructor ... apply union_not_in in H.
    destruct H; assumption. apply union_not_in in H0.
    destruct H0; assumption.
    apply disjoint_extend
    with (l := l) (n := aeval s0 e1) in H3 ...
    apply disjoint_extend
    with (l := l+1) (n := aeval s0 e2) in H3 ...
    split. assumption.
    rewrite h_union_extend. rewrite h_union_extend. reflexivity.
    apply union_not_in in H0. destruct H0 ...
    apply union_not_in in H. destruct H ...
  - (* Lookup *) exists h1. split. apply safeAt_bs_lookup in H3.
    apply union_num_unchange with (n := n) (h2 := h2) in H3; auto.
    econstructor ... rewrite <- plus_n_O. unfold in_dom.
    exists n. assumption. rewrite <- plus_n_O. assumption.
    auto.
  - (* Mutation *) 
    exists (h_update h1 (aeval s0 e1) (aeval s0 e2)). split.
    econstructor ... apply safeAt_bs_mutation in H3. assumption.
    split. apply disjoint_l_in with
           (l := aeval s0 e1) (n := aeval s0 e2) in H2; auto.
    apply safeAt_bs_mutation in H3; assumption.
    rewrite h_union_extend. reflexivity.
  - (* Dispose *)
    exists (fun l' => if eq_nat_dec (aeval s0 e) l' then None
                      else h1 l').
    split. econstructor ... apply safeAt_bs_dispose in H2. assumption.
    split. apply disjoint_l_seq ... apply safeAt_bs_dispose ...
    apply union_dispose ... apply safeAt_bs_dispose ...
Qed.

Lemma while_safty : forall b c st,
    (forall st', beval (fst st') b = true -> safeAt_bs c st') ->
    safeAt_bs (WHILE b DO c END) st.
Proof.
  intros. unfold safeAt_bs, not. intro.
  remember (WHILE b DO c END, st) as comst.
  remember Abt as est. generalize dependent st.
  generalize dependent c.
  induction H0; intros; try inversion Heqcomst; try inversion Heqest;
    try clear Heqcomst; try clear Heqest; subst.
  - apply (H1 (s, h)) in H. unfold safeAt_bs, not in H.
    apply H in H0. inversion H0.
  - assert ((WHILE b DO c0 END, (s', h')) =
            (WHILE b DO c0 END, (s', h')) -> False).
    {
      apply IHbig_step2; auto.
    }
    apply H1. reflexivity.
Qed.
    
Theorem safty_mono_correct : forall c,
    safty_Mono_bs c.
Proof with eauto.
  intro c. unfold safty_Mono_bs. induction c; intros.
  - (* SKIP *) unfold safeAt_bs, not in *. intro.
    inversion H1.
  - (* Asgn *) unfold safeAt_bs, not in *. intro.
    inversion H1.
  - (* Seq *) unfold safeAt_bs, not. intro.
    assert (safeAt_bs (c1;; c2) (s, h1)) by assumption.
    apply safeAt_bs_seq in H. apply (IHc1 s h1 h2) in H; auto.
    inversion H1; subst. unfold safeAt_bs, not in H.
    apply H in H4. inversion H4.
    assert (safeAt_bs (c1;; c2) (s, h1)) by assumption.
    apply safeAt_bs_seq in H2. destruct st' as [s' h'].
    assert (exists h1', big_step (c1, (s, h1)) (St (s', h1')) /\
                        disjoint h1' h2 /\ h_union h1' h2 = h').
    {
      apply frame_bs_correct; auto.
    }
    destruct H4 as [h1' [Hbs [Hdisj Hunion]]].
    apply safeAt_bs_seq2 with (st := (s', h1')) in H3; auto.
    apply IHc2 with (h2 := h2) in H3; eauto. subst h'.
    unfold safeAt_bs, not in H3. apply H3 in H8. inversion H8.
  - (* IFB *) unfold safeAt_bs, not. intro.
    inversion H1; subst.
    assert (safeAt_bs c1 (s, h1)).
    {
      apply safeAt_bs_if with (b := b) (c2 := c2). auto.
    }
    apply (IHc1 s h1 h2) in H2; auto.
    assert (safeAt_bs c2 (s, h1)).
    {
      apply safeAt_bs_if2 with (b := b) (c1 := c1). auto.
    }
    apply IHc2 with (h2 := h2) in H2; auto.
  - (* WHILE *) unfold safeAt_bs, not. intro.
    inversion H1; subst.
    assert (safeAt_bs c (s, h1)).
    {
      apply safeAt_bs_while with b. auto.
    }
    apply (IHc s h1 h2) in H2; auto.
    assert (safeAt_bs c (s, h1)).
    {
      apply safeAt_bs_while with b. auto.
    }
    admit.
  - (* Cons *) unfold safeAt_bs, not in *. intro.
    inversion H1; subst.
  - (* Lookup *) unfold safeAt_bs, not. intro.
    inversion H1; subst. apply union_not_in in H7.
    destruct H7. apply safeAt_bs_lookup in H.
    unfold in_dom in H. destruct H as [n]. unfold not_in_dom in H2.
    rewrite H in H2. inversion H2.
  - (* Mutation *) unfold safeAt_bs, not. intro.
    inversion H1; subst. apply union_not_in in H7.
    destruct H7. apply safeAt_bs_mutation in H.
    unfold not_in_dom in H2. unfold in_dom in H. destruct H as [n].
    rewrite H in H2. inversion H2.
  - (* Dispose *) unfold safeAt_bs, not. intro.
    inversion H1; subst. apply union_not_in in H6.
    destruct H6. apply safeAt_bs_dispose in H.
    unfold not_in_dom in H2. unfold in_dom in H. destruct H as [n].
    rewrite H in H2. inversion H2.
Admitted.

Definition hoare_triple (P : sass) (c : scom) (Q : sass) : Prop :=
  forall st,
    P st -> (safeAt_bs c st /\ (forall est, big_step (c, st) (St est) -> Q est)).

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Definition assert_implies (P Q : sass) : Prop :=
  forall st, P st -> Q st.
Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.
Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* frame rule *)
Theorem Frame_Rule : forall P Q c,
    {{ P }} c {{ Q }} ->
    ( forall R, inde (modified_scom_var c) R ->
    {{ P ** R }} c {{ Q ** R }}).
Proof.
  unfold hoare_triple in *. intros. unfold star in H1.
  destruct st as [s h].
  destruct H1 as [h1 [h2 [Hdisj [Hunion [HP HR]]]]].
  apply H in HP. destruct HP. split. rewrite <- Hunion.
  apply (safty_mono_correct); auto. intros. unfold star.
  destruct est as [s' h']. rewrite <- Hunion in H3.
  apply (frame_bs_correct c s s' h1 h2 h') in H1; auto.
  destruct H1 as [h1' [Hstep [Hdisj1 Hunion1]]].
  exists h1', h2. split. assumption. split. assumption.
  split. apply H2 in Hstep. assumption.
  eapply (mention_modified_free (s, h1) (s', h1') c R) in H0; eauto.
Qed.

Definition pto_any (e : aexp) : sass :=
  fun st => match st with
            | (s, h) => exists v, h = h_update emp_heap (aeval s e) v
            end.
Notation "e '|->' '-'" := (pto_any e) (at level 60).

Theorem hoare_consquence_post : forall c p q q',
    {{ p }} c {{ q' }} -> (q' ->> q) ->
    {{ p }} c {{ q }}.
Proof.
  unfold hoare_triple. intros. apply H in H1. destruct H1.
  split. assumption. intros. apply H2 in H3.
  unfold assert_implies in H0. apply H0 in H3. assumption.
Qed.

Theorem hoare_consquence_pre : forall c p p' q,
    {{ p' }} c {{ q }} -> (p ->> p') ->
    {{ p }} c {{ q }}.
Proof.
  unfold hoare_triple. intros. unfold assert_implies in H0.
  apply H0 in H1. apply H in H1. auto.
Qed.

(** Inference Rules for Mutation and Disposal **)
(* The local form mutation *)
Theorem hoare_mul : forall e e',
    {{ e |-> - }} ([e] ::= e') {{ e |-> e' }}.
Proof.
  unfold hoare_triple. intros. split.
  unfold safeAt_bs, not. intro. inversion H0; subst.
  simpl in H. destruct H as [v]. rewrite H in H5.
  unfold not_in_dom in H5. unfold h_update in H5.
  unfold eq_nat_dec in H5.
  assert (aeval s e =? aeval s e = true).
  {
    apply beq_nat_true_iff. reflexivity.
  }
  rewrite H1 in H5. inversion H5.
  intros. inversion H0; subst. simpl. simpl in H. destruct H as [v].
  rewrite H. apply functional_extensionality. intros.
  unfold h_update. destruct (eq_nat_dec (aeval s e) x); auto.
Qed.

(* The Global form mutation *)
Theorem hoare_mug : forall e e' r,
    {{ (e |-> -) ** r }} [e] ::= e' {{ (e |-> e') ** r }}.
Proof.
  intros. apply Frame_Rule. apply hoare_mul.
  simpl. unfold inde. intros. unfold In in H. inversion H.
Qed.

Lemma disjoint_in_still : forall h1 h2 l n,
    in_dom l h1 -> disjoint h1 h2 ->
    disjoint (h_update h1 l n) h2.
Proof.
  unfold disjoint in *. intros.
  destruct (H0 l0). left. unfold not_in_dom in *.
  unfold h_update. unfold eq_nat_dec. destruct (l =? l0) eqn:Heqe.
  apply beq_nat_true_iff in Heqe. rewrite <- Heqe in H1.
  unfold in_dom in H. destruct H as [n']. rewrite H in H1.
  inversion H1. assumption. right. assumption.
Qed.

(* The backward-reasoning form mutation *)
Theorem hoare_mubr : forall e e' p,
    {{ (e |-> -) ** ((e |-> e') --* p) }} [e] ::= e' {{ p }}.
Proof.
  unfold hoare_triple. intros. split.
  - unfold safeAt_bs, not. intro. inversion H0; subst.
    unfold star in H.
    destruct H as [h1 [h2 [Hdisj [Hunion [HP HQ]]]]].
    simpl in HP. destruct HP as [v]. rewrite <- Hunion in H5.
    rewrite H in H5. unfold not_in_dom in H5.
    unfold h_union in H5.
    destruct
      (in_not_in_dec (aeval s e) (h_update emp_heap (aeval s e) v)).
    unfold h_update in H5. unfold eq_nat_dec in H5.
    assert (aeval s e =? aeval s e = true)
      by (apply beq_nat_true_iff; reflexivity).
    rewrite H1 in H5. inversion H5. unfold not_in_dom in n.
    unfold h_update in n.
    assert (aeval s e =? aeval s e = true)
      by (apply beq_nat_true_iff; reflexivity).
    unfold eq_nat_dec in n. rewrite H1 in n. inversion n.
  - intros. unfold star in H. destruct st as [s h].
    destruct H as [h1 [h2 [Hdisj [Hunion [HP HQ]]]]].
    inversion H0; subst. unfold simp in HQ. simpl in HP.
    destruct HP as [v].
    assert (in_dom (aeval s e) h1).
    {
      rewrite H. unfold in_dom. exists v. unfold h_update.
      unfold eq_nat_dec.
      assert (aeval s e =? aeval s e = true) by
          (apply beq_nat_true_iff; auto).
      rewrite H1. reflexivity.
    }
    apply disjoint_in_still
    with (h2 := h2) (n := aeval s e') in H1; auto.
    apply HQ in H1.
    assert (h_union h2 (h_update h1 (aeval s e) (aeval s e'))
            = h_union (h_update h1 (aeval s e) (aeval s e')) h2).
    {
      apply disj_union_symmetry. apply disjoint_symmetry.
      apply disjoint_in_still; auto. rewrite H. unfold in_dom.
      exists v. unfold eq_nat_dec.
      assert (aeval s e =? aeval s e = true) by
          (apply beq_nat_true_iff; auto).
      unfold h_update, eq_nat_dec. rewrite H2. reflexivity.
    }
    rewrite H2 in H1. rewrite h_union_extend in H1. assumption.
    simpl. rewrite H. apply functional_extensionality. intros.
    unfold h_update, eq_nat_dec. destruct (aeval s e =? x); auto.
Qed.

(* The local form dispose *)
Theorem hoare_dispose_lc : forall e,
    {{ e |-> - }} (Dispose e) {{ emp }}.
Proof.
  unfold hoare_triple. intros. split. unfold safeAt_bs, not.
  intro. inversion H0; subst. simpl in H. destruct H as [v].
  rewrite H in H4.
  unfold not_in_dom in H4. unfold h_update, eq_nat_dec in H4.
  assert (aeval s e =? aeval s e = true)
    by (apply beq_nat_true_iff; auto).
  rewrite H1 in H4. inversion H4. intros.
  inversion H0; subst. simpl in H. destruct H as [v]. subst h.
  unfold emp. simpl. apply functional_extensionality. intros.
  unfold eq_nat_dec. destruct (aeval s e =? x) eqn:Heqe.
  unfold emp_heap. reflexivity. unfold h_update, eq_nat_dec.
  rewrite Heqe. reflexivity.
Qed.

Lemma union_emp : forall h1 h2,
    h_union emp_heap h1 = h2 -> h1 = h2.
Proof.
  intros. apply functional_extensionality. intros.
  apply equal_f with x in H. unfold h_union in H.
  destruct (in_not_in_dec x emp_heap); auto. unfold in_dom in i.
  destruct i. unfold emp_heap in H0. inversion H0.
Qed.

(* The global form dispose *)
Theorem hoare_dispose_gb : forall e r,
    {{ (e |-> -) ** r }} (Dispose e) {{ r }}.
Proof.
  intros. apply hoare_consquence_post with (emp ** r).
  apply Frame_Rule. apply hoare_dispose_lc.
  simpl. unfold inde. intros. unfold In in H. inversion H.
  unfold assert_implies. intros. unfold star in H.
  destruct st as [s h].
  destruct H as [h1 [h2 [Hdisj [Hunion [H1 H2]]]]].
  unfold emp in H1. simpl in H1. rewrite H1 in Hunion.
  apply union_emp in Hunion. subst h2. assumption.
Qed.

(* The specification for cons and lookup will be more complicated, since they will modify the stack even the heap *)
Fixpoint free_var_aexp (e : aexp) : list id :=
  match e with
  | AId v => v :: nil
  | ANum _ => nil
  | APlus e1 e2 => (free_var_aexp e1) ++ (free_var_aexp e2) 
  | AMinus e1 e2 => (free_var_aexp e1) ++ (free_var_aexp e2)
  | AMult e1 e2 => (free_var_aexp e1) ++ (free_var_aexp e2)
  end.

Definition distinct_var_aexp (x : id) (e : aexp) : Prop :=
  forall v s,
    aeval s e = aeval (st_update s x v) e.

Fixpoint aexp_subst_var (e : aexp) (x : id) (v : aexp) : aexp :=
  match e with
  | AId i => if beq_id i x then v else (AId i)
  | ANum n => ANum n
  | APlus e1 e2 =>
    APlus (aexp_subst_var e1 x v) (aexp_subst_var e2 x v)
  | AMinus e1 e2 =>
    AMinus (aexp_subst_var e1 x v) (aexp_subst_var e2 x v)
  | AMult e1 e2 =>
    AMult (aexp_subst_var e1 x v) (aexp_subst_var e2 x v)
  end.

Lemma disjoint_cell : forall l1 l2 n1 n2,
    l1 =? l2 = false ->
    disjoint (h_update emp_heap l1 n1) (h_update emp_heap l2 n2).
Proof.
  intros. unfold disjoint, not_in_dom. intros.
  unfold h_update, eq_nat_dec. destruct (l1 =? l) eqn:Heqe.
  right. destruct (l2 =? l) eqn:Heqe1.
  apply beq_nat_true_iff in Heqe. apply beq_nat_true_iff in Heqe1.
  subst l1. subst l2. rewrite <- beq_nat_refl in H. inversion H.
  reflexivity. left. reflexivity.
Qed.

Lemma beq_id_symmetry : forall x y,
    beq_id x y = beq_id y x.
Proof.
  intros. destruct x, y. simpl.
  apply Nat.eqb_sym.
Qed.
  
Lemma distinct_stability : forall v v' s l e,
    distinct_var_aexp v v' -> s v = aeval s v' ->
    aeval s e = aeval (st_update s v l) (aexp_subst_var e v v').
Proof.
  intros v v' s l e. generalize dependent v. generalize dependent s.
  generalize dependent l. induction e; intros.
  - reflexivity.
  - simpl. unfold distinct_var_aexp in H.
    destruct (beq_id i v) eqn:Heqe. rewrite <- H.
    apply beq_id_true_iff in Heqe. subst. assumption.
    simpl. unfold st_update, eq_id_dec. rewrite beq_id_symmetry.
    rewrite Heqe. reflexivity.
  - simpl. assert (H' : distinct_var_aexp v v') by assumption.
    assert (H1 : s v = aeval s v') by assumption.
    apply IHe1 with (l := l) (s := s) in H; auto.
  - simpl. assert (H' : distinct_var_aexp v v') by assumption.
    assert (H1 : s v = aeval s v') by assumption.
    apply IHe1 with (l := l) (s := s) in H; auto.
  - simpl. assert (H' : distinct_var_aexp v v') by assumption.
    assert (H1 : s v = aeval s v') by assumption.
    apply IHe1 with (l := l) (s := s) in H; auto.
Qed.

Definition assertion_var_sub X a P : sass :=
  fun (st : sstate) =>
    match st with
      (s, h) => P (st_update s X (aeval s a), h)
    end.
Notation "P [ X --> a ]" := (assertion_var_sub X a P) (at level 10).

Theorem hoare_cons_lc : forall v v' e1 e2,
    distinct_var_aexp v v' ->
    {{ (fun st => (fst st) v = aeval (fst st) v') //\\ emp }}
      (SCCons v e1 e2)
    {{ ((AId v) |-> (aexp_subst_var e1 v v')) **
         ((APlus (AId v) (ANum 1)) |-> (aexp_subst_var e2 v v')) }}.
Proof.
  unfold hoare_triple. intros. split.
  - unfold safeAt_bs, not. intro. inversion H1.
  - intros. destruct st as [s h]. unfold s_conj in H0. simpl in *.
    inversion H1; subst. unfold star. destruct H0.
    unfold emp in H2. simpl in H2. subst h.
    exists (h_update emp_heap l (aeval s e1)).
    exists (h_update emp_heap (l+1) (aeval s e2)).
    split. apply disjoint_cell. apply beq_nat_false_iff. omega.
    split.
    unfold h_union. apply functional_extensionality. intro.
    destruct (in_not_in_dec x (h_update emp_heap l (aeval s e1))).
    unfold h_update, eq_nat_dec. destruct (l =? x) eqn:Heqe.
    assert (l + 1 =? x = false). apply beq_nat_true_iff in Heqe.
    apply beq_nat_false_iff. subst x. omega. rewrite H2. reflexivity.
    unfold in_dom in i. destruct i as [n].
    unfold h_update, eq_nat_dec in H2. destruct (l =? x) eqn:Heqe1.
    inversion Heqe. unfold emp_heap in H2. inversion H2.
    unfold h_update, eq_nat_dec. destruct (l + 1 =? x) eqn:Heqe.
    reflexivity. destruct (l =? x) eqn:Heqe1. unfold not_in_dom in n.
    apply beq_nat_true_iff in Heqe1. rewrite Heqe1 in n.
    unfold h_update, eq_nat_dec in n. rewrite <- beq_nat_refl in n.
    inversion n. reflexivity. split.
    unfold pto. unfold st_update. simpl. unfold eq_id_dec.
    rewrite <- beq_id_refl.
    apply (distinct_stability v v' s l e1) in H; auto.
    unfold pto. simpl.
    assert (st_update s v l v = l).
    {
      unfold st_update, eq_id_dec. rewrite <- beq_id_refl.
      reflexivity.
    }
    rewrite H2.
    apply (distinct_stability v v' s l e2) in H; auto.
Qed.

Theorem hoare_cons_gb : forall v e1 e2 r,
    {{ r }} (SCCons v e1 e2)
    {{ fun st => exists v', distinct_var_aexp v v' /\
            ((((AId v) |-> (aexp_subst_var e1 v v'))
             ** ((APlus (AId v) (ANum 1)) |-> (aexp_subst_var e2 v v')))
                 ** (r [ v --> v' ])) st }}.
Proof.
  unfold hoare_triple. intros. split.
  unfold safeAt_bs, not. intro. inversion H0. intros.
  unfold star in *. inversion H0; subst. exists (ANum (s v)).
  split. unfold distinct_var_aexp. intros. simpl. reflexivity.
  exists
    (h_update (h_update emp_heap l (aeval s e1)) (l+1) (aeval s e2)).
  exists h.
  split. unfold disjoint, not_in_dom. intros.
  unfold h_update, eq_nat_dec. destruct (l + 1 =? l0) eqn:Heqe.
  apply beq_nat_true_iff in Heqe. unfold not_in_dom in H7.
  rewrite Heqe in H7. right. assumption.
  destruct (l =? l0) eqn:Heqe1. apply beq_nat_true_iff in Heqe1.
  unfold not_in_dom in H6. rewrite Heqe1 in H6. right. assumption.
  left. unfold emp_heap. reflexivity. split. unfold h_union.
  apply functional_extensionality. intros.
  destruct (in_not_in_dec x
    (h_update (h_update emp_heap l (aeval s e1)) (l + 1) (aeval s e2))).
  unfold h_update, eq_nat_dec. destruct (l + 1 =? x) eqn:Heqe; auto.
  destruct (l =? x) eqn:Heqe1; auto. unfold in_dom in i. destruct i.
  unfold h_update, eq_nat_dec in H1. rewrite Heqe in H1.
  rewrite Heqe1 in H1. unfold emp_heap in H1. inversion H1.
  unfold h_update, eq_nat_dec. destruct (l + 1 =? x) eqn:Heqe.
  unfold not_in_dom in n. unfold h_update, eq_nat_dec in n.
  rewrite Heqe in n. inversion n. destruct (l =? x) eqn:Heqe1.
  unfold not_in_dom in n. unfold h_update, eq_nat_dec in n.
  rewrite Heqe in n. rewrite Heqe1 in n. inversion n. reflexivity. split.
  exists (h_update emp_heap l (aeval s e1)).
  exists (h_update emp_heap (l+1) (aeval s e2)).
  split. apply disjoint_cell. apply beq_nat_false_iff. omega.
  split. unfold h_union. apply functional_extensionality. intro.
  destruct (in_not_in_dec x (h_update emp_heap l (aeval s e1))).
  unfold h_update, eq_nat_dec. destruct (l =? x) eqn:Heqe.
  destruct (l + 1 =? x) eqn:Heqe1. apply beq_nat_true_iff in Heqe.
  apply beq_nat_true_iff in Heqe1. rewrite <- Heqe in Heqe1. omega.
  reflexivity. destruct (l + 1 =? x) eqn:Heqe1.
  unfold in_dom in i. destruct i as [n].
  unfold h_update, eq_nat_dec in H1. rewrite Heqe in H1.
  unfold emp_heap in H1. inversion H1. reflexivity.
  unfold h_update, eq_nat_dec. destruct (l + 1 =? x) eqn:Heqe; auto.
  assert (st_update s v l v = l).
  {
     unfold st_update, eq_id_dec. rewrite <- beq_id_refl.
     reflexivity.
  }
  unfold pto. simpl. rewrite H1. split.
  assert ((aeval s e1)
     = (aeval (st_update s v l) (aexp_subst_var e1 v (ANum (s v))))).
  {
    apply distinct_stability; auto. unfold distinct_var_aexp.
    intros. simpl. reflexivity.
  }
  rewrite <- H2. reflexivity.
  assert ((aeval s e2) =
          (aeval (st_update s v l) (aexp_subst_var e2 v (ANum (s v))))).
  {
    apply distinct_stability; auto. unfold distinct_var_aexp.
    intros. reflexivity.
  }
  rewrite <- H2. reflexivity. unfold assertion_var_sub. simpl.
  assert (s = st_update (st_update s v l) v (s v)).
  {
    apply functional_extensionality. intros.
    unfold st_update, eq_id_dec. destruct (beq_id v x) eqn:Heqe; auto.
    apply beq_id_true_iff in Heqe. subst. reflexivity.
  }
  rewrite <- H1. assumption.
Qed.

Lemma aeval_subst_var_eq : forall s e v v',
    aeval s (aexp_subst_var e v v') =
    aeval (st_update s v (aeval s v')) e.
Proof.
  intros s e. generalize dependent s.
  induction e; intros; auto; try solve
                                 [simpl; rewrite IHe1; rewrite IHe2;
                                 reflexivity].
  - simpl. destruct (beq_id i v) eqn:Heqe. unfold st_update, eq_id_dec.
    rewrite beq_id_symmetry in Heqe. rewrite Heqe. reflexivity.
    simpl. unfold st_update, eq_id_dec. rewrite beq_id_symmetry in Heqe.
    rewrite Heqe. reflexivity.
Qed.

Theorem hoare_cons_br : forall e1 e2 p v,
    {{ fun st => (forall v'', (distinct_var_aexp v v'') /\
       (((v'' |-> e1) ** ((APlus v'' (ANum 1)) |-> e2))
          --* (p [v --> v''])) st) }}
      (SCCons v e1 e2)
    {{ p }}.
Proof.
  intros. eapply hoare_consquence_post. apply hoare_cons_gb.
  unfold assert_implies. intros. destruct H as [v'].
  destruct H as [Hdist]. unfold star in H. destruct st as [s h].
  destruct H as [h1 [h2]]. destruct H as [Hdisj [Hunion [H1 H2]]].
  destruct H1 as [h3 [h4]]. simpl in *.
  destruct (H2 (ANum (s v))). clear H2.
  destruct H as [Hdisj1 [Hunion2 [Hupdate1 Hupdate2]]].
  assert (disjoint h1 h2) by assumption.
  apply H1 in Hdisj. clear H1.
  assert (h_union h1 h2 = h_union h2 h1).
  {
    apply disj_union_symmetry; auto.
  }
  rewrite <- H1 in Hdisj. rewrite Hunion in Hdisj.
  simpl in Hdisj.
  assert (st_update (st_update s v (aeval s v')) v (s v) = s).
  {
    unfold st_update. apply functional_extensionality.
    intro. unfold eq_id_dec. destruct (beq_id v x) eqn:Heqe; auto.
    apply beq_id_true_iff in Heqe. rewrite Heqe. reflexivity.
  }
  rewrite H2 in Hdisj. assumption.
  simpl. exists h3, h4. split. assumption. split. assumption.
  split. rewrite Hupdate1. clear H1. rewrite aeval_subst_var_eq.
  reflexivity. rewrite Hupdate2. rewrite aeval_subst_var_eq.
  reflexivity.
Qed.

(* The specification for lookup *)
Theorem hoare_lookup_lc : forall v v' v'' e,
    (distinct_var_aexp v v' /\ distinct_var_aexp v v'') ->
    {{ fun st => ((fst st) v = aeval (fst st) v' /\
    (e |-> v'') st) }}
      (SCLookup v e)
      {{ fun st => ((fst st) v = aeval (fst st) v'')
                   /\ ((aexp_subst_var e v v' |-> (AId v)) st) }}.
Proof.
  unfold hoare_triple. intros. split.
  destruct st as [s h]. unfold safeAt_bs, not. intro.
  inversion H1; subst. destruct H0. simpl in *. rewrite H2 in H7.
  unfold not_in_dom in H7. unfold h_update, eq_nat_dec in H7.
  rewrite <- beq_nat_refl in H7. inversion H7. intros.
  inversion H1; subst. simpl in *. split.
  destruct H. unfold distinct_var_aexp in H2. rewrite <- H2.
  unfold st_update, eq_id_dec. rewrite <- beq_id_refl. destruct H0.
  rewrite H3 in H8. unfold h_update, eq_nat_dec in H8.
  rewrite <- beq_nat_refl in H8. inversion H8. reflexivity.
  destruct H0. rewrite H2. destruct H.
  apply (distinct_stability v v' s n e) in H; auto.
  rewrite <- H. rewrite H2 in H8. unfold h_update, eq_nat_dec in H8.
  rewrite <- beq_nat_refl in H8. inversion H8. rewrite H5.
  assert (st_update s v n v = n).
  {
    unfold st_update, eq_id_dec. rewrite <- beq_id_refl.
    reflexivity.
  }
  rewrite H4. reflexivity.
Qed.

Theorem hoare_lookup_gb : forall v r e,
    {{ fun st => (exists v'', distinct_var_aexp v v'' /\
                     ((e |-> v'') ** (r [v --> v''])) st) }}
      (SCLookup v e)
      {{ fun st => (exists v', distinct_var_aexp v v' /\
                   ((aexp_subst_var e v v' |-> (AId v)) ** r) st)  }}.
Proof.
  unfold hoare_triple. intros. destruct H as [v'' [Hdistinc Hass]].
  destruct st as [s h]. unfold star in Hass.
  destruct Hass as [h1 [h2 [Hdisj [Hunion [H1 H2]]]]].
  split. unfold safeAt_bs, not. intro. inversion H; subst.
  unfold pto in H1. unfold not_in_dom in H7. rewrite H1 in H7.
  unfold h_union in H7.
  destruct (in_not_in_dec (aeval s e)
                          (h_update emp_heap (aeval s e) (aeval s v''))).
  unfold h_update, eq_nat_dec in H7. rewrite <- beq_nat_refl in H7.
  inversion H7. unfold not_in_dom in n.
  unfold h_update, eq_nat_dec in n. rewrite <- beq_nat_refl in n.
  inversion n. intros. inversion H; subst.
  exists (ANum (s v)). split. unfold distinct_var_aexp. intros.
  simpl. reflexivity. unfold pto. simpl. exists h1, h2.
  split. assumption. split. reflexivity. split.
  unfold pto in H1. rewrite H1.
  assert (aeval s e =
          aeval (st_update s v n) (aexp_subst_var e v (ANum (s v)))).
  {
    apply distinct_stability. unfold distinct_var_aexp. intros.
    reflexivity. reflexivity.
  }
  rewrite <- H0. unfold assertion_var_sub in H2.
  rewrite H1 in H9. unfold h_union in H9.
  destruct (in_not_in_dec (aeval s e)
                          (h_update emp_heap (aeval s e) (aeval s v''))).
  unfold h_update, eq_nat_dec in H9. rewrite <- beq_nat_refl in H9.
  inversion H9; subst. unfold st_update, eq_id_dec.
  rewrite <- beq_id_refl. reflexivity. unfold not_in_dom in n0.
  unfold h_update, eq_nat_dec in n0. rewrite <- beq_nat_refl in n0.
  inversion n0. unfold assertion_var_sub in H2.
  unfold pto in H1. rewrite H1 in H9. unfold h_union in H9.
  destruct (in_not_in_dec (aeval s e)
                          (h_update emp_heap (aeval s e) (aeval s v''))).
  unfold h_update, eq_nat_dec in H9. rewrite <- beq_nat_refl in H9.
  inversion H9. assumption. unfold not_in_dom in n0.
  unfold h_update, eq_nat_dec in n0. rewrite <- beq_nat_refl in n0.
  inversion n0.
Qed.

Lemma in_union_in : forall h1 h2 l,
    in_dom l h1 -> in_dom l (h_union h1 h2).
Proof.
  intros. unfold in_dom in *. destruct H as [n].
  exists n. unfold h_union. destruct (in_not_in_dec l h1); auto.
  unfold not_in_dom in n0. rewrite H in n0. inversion n0.
Qed.

Theorem hoare_lookup_bw : forall e p v,
    {{ fun st => (exists v', ((e |-> v')
                   ** ((e |-> v') --* (p [v --> v']))) st) }}
      (SCLookup v e)
    {{ p }}.
Proof.
  unfold hoare_triple. intros. destruct H. unfold star in H.
  destruct st as [s h].
  destruct H as [h1 [h2 [Hdisj [Hunion [H1 H2]]]]].
  split. unfold safeAt_bs, not. intros. inversion H; subst.
  unfold pto in H1.
  assert (in_dom (aeval s e) h1).
  {
    unfold in_dom. exists (aeval s x). rewrite H1.
    unfold h_update, eq_nat_dec. rewrite <- beq_nat_refl.
    reflexivity.
  }
  apply in_union_in with (h2 := h2) in H0. unfold not_in_dom in H7.
  unfold in_dom in H0. destruct H0. rewrite H7 in H0. inversion H0.
  intros. inversion H; subst. unfold pto in H1.
  unfold pto, simp in H2. assert (Hdisj1 : disjoint h1 h2) by auto.
  apply (H2 h1) in Hdisj; auto.
  unfold assertion_var_sub in Hdisj.
  rewrite H1 in H9. unfold h_union in H9.
  destruct (in_not_in_dec (aeval s e)
                          (h_update emp_heap (aeval s e) (aeval s x))).
  unfold h_update, eq_nat_dec in H9. rewrite <- beq_nat_refl in H9.
  inversion H9; subst. apply disj_union_symmetry in Hdisj1.
  rewrite <- Hdisj1 in Hdisj. assumption.
  unfold not_in_dom in n0. unfold h_update, eq_nat_dec in n0.
  rewrite <- beq_nat_refl in n0. inversion n0.
Qed.
