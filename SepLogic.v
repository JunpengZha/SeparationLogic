Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.
Require Import Hoare.
Require Import Coq.Logic.FunctionalExtensionality.

(* First we define syntax of the language *)

(* We could reuse aexp and bexp defined for Imp. *)

(* Redefine commands here. To distinguish them 
   from Imp commands, we call them scom *)
(* You need to change it into an inductive definition *)
Inductive scom : Type :=
| SCSkip : scom
| SCAss : id -> aexp -> scom
| SCSeq : scom -> scom -> scom
| SCIf : bexp -> scom -> scom -> scom
| SCWhile : bexp -> scom -> scom
| SCCons : id -> aexp -> aexp -> scom
| SCLookup : id -> aexp -> scom
| SCMutation : aexp -> aexp -> scom
| SCDispose : aexp -> scom.

(* Program states, which is called sstate *)
Definition store := id -> nat.

(* if heap maps a natural number (address) to
   None, we say the address is not a valid address,
   or it is not in the domain of the heap *)
Definition heap := nat -> option nat.

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

(* Define an empty heap, which contains no memory cells *)
Definition emp_heap : heap := 
  fun (l: nat) => None.

Definition in_dom (l: nat) (h: heap) : Prop :=
  exists n, h l = Some n.

Definition not_in_dom (l: nat) (h: heap) : Prop :=
  h l = None.

Theorem in_not_in_dec : 
  forall l h, {in_dom l h} + {not_in_dom l h}.
Proof.
  intros l h. unfold in_dom. unfold not_in_dom.
  destruct (h l).
  left. exists n. auto.
  right. auto.
Defined.

Axiom finite_heap : forall h : heap, exists l',
    forall l n, h l = Some n -> l < l'.

Corollary heap_allocate_success : forall (h : heap),
    exists l,  forall l', l < l' ->  h l' = None.
Proof.
  intros. destruct (finite_heap h) as [l' Hh].
  exists l'. intros. destruct (h l'0) eqn:Heqe; auto.
  apply Hh in Heqe. omega.
Qed.

(* h1 and h2 have disjoint domain *)
Definition disjoint (h1 h2: heap) : Prop := 
  forall l, not_in_dom l h1 \/ not_in_dom l h2.

(* union of two heaps *)
Definition h_union (h1 h2: heap) : heap :=
  fun l => 
    if (in_not_in_dec l h1) then h1 l else h2 l.

(* h1 is a subset of h2 *)
Definition h_subset (h1 h2: heap) : Prop := 
  forall l n, h1 l = Some n -> h2 l = Some n.

Definition eq_id_dec := beq_id.
(* store update *)
Definition st_update (s: store) (x: id) (n: nat) : store :=
  fun x' => if eq_id_dec x x' then n else s x'.

Definition eq_nat_dec := beq_nat.
(* heap update *)
Definition h_update (h: heap) (l: nat) (n: nat) : heap :=
  fun l' => if eq_nat_dec l l' then Some n else h l'.

Definition sstate := (store * heap) %type.

(* since program may abort, we extend our state
   definition to add a special state Abt *)
Inductive ext_state : Type :=
  St:  sstate -> ext_state    (* normal state *)
| Abt: ext_state.             (* abort *)


(* Next we define the operational semantics *)

(* big-step semantics. You should change it into 
   an inductive definition *)
Inductive big_step: 
  scom * sstate -> ext_state -> Prop :=
| BS_Skip : forall st, big_step (SCSkip, st) (St st)
| BS_Ass : forall s h X e n,
    aeval s e = n ->
    big_step (SCAss X e, (s, h)) (St (st_update s X n, h))
| BS_SeqAb : forall c1 c2 st,
    big_step (c1, st) Abt ->
    big_step (SCSeq c1 c2, st) Abt
| BS_Seq : forall c1 c2 st st' esst,
    big_step (c1, st) (St st') -> big_step (c2, st') esst ->
    big_step (SCSeq c1 c2, st) esst
| BS_IfTrue : forall b c1 c2 s h esst,
    beval s b = true ->
    big_step (c1, (s, h)) esst ->
    big_step (SCIf b c1 c2, (s, h)) esst
| BS_IfFalse : forall b c1 c2 s h esst,
    beval s b = false ->
    big_step (c2, (s, h)) esst ->
    big_step (SCIf b c1 c2, (s, h)) esst
| BS_WhileEnd : forall b c s h,
    beval s b = false ->
    big_step (SCWhile b c, (s, h)) (St (s, h))
| BS_WhileLoopAb : forall b c s h,
    beval s b = true ->
    big_step (c, (s, h)) Abt ->
    big_step (SCWhile b c, (s, h)) Abt
| BS_WhileLoop : forall b c s h s' h' esst,
    beval s b = true ->
    big_step (c, (s, h)) (St (s', h')) ->
    big_step (SCWhile b c, (s', h')) esst ->
    big_step (SCWhile b c, (s, h)) esst
| BS_Cons : forall s h e1 e2 X n1 n2 l,
    not_in_dom l h -> not_in_dom (l+1) h ->
    aeval s e1 = n1 -> aeval s e2 = n2 ->
    big_step (SCCons X e1 e2, (s, h))
             (St (st_update s X l, h_update (h_update h l n1) (l+1) n2))
| BS_Lookup : forall s h e X l n,
    aeval s e = l -> in_dom l h -> h l = Some n ->
    big_step (SCLookup X e, (s, h)) (St (st_update s X n, h))
| BS_LookupAb : forall s h e X l,
    aeval s e = l -> not_in_dom l h ->
    big_step (SCLookup X e, (s, h)) Abt
| BS_Mutation : forall s h e1 e2 l n,
    aeval s e1 = l -> in_dom l h -> aeval s e2 = n ->
    big_step (SCMutation e1 e2, (s, h))
             (St (s, h_update h l n))
| BS_MutationAb : forall s h e1 e2 l,
    aeval s e1 = l -> not_in_dom l h ->
    big_step (SCMutation e1 e2, (s, h)) Abt
| BS_Dispose : forall s h e l,
    aeval s e = l -> in_dom l h ->
    big_step (SCDispose e, (s, h))
             (St (s, (fun l' => if eq_nat_dec l l' then
                                  None else h l')))
| BS_DisposeAb : forall s h e l,
    aeval s e = l -> not_in_dom l h ->
    big_step (SCDispose e, (s, h)) Abt.
             
(* small-step semantics. Should be inductive too *)
Inductive small_step: 
   scom * ext_state -> scom * ext_state -> Prop := 
| SS_Ass : forall s h e n X,
    aeval s e = n ->
    small_step (SCAss X e, St (s, h))
               (SCSkip, St (st_update s X n, h))
| SS_Seq : forall c1 c2 c1' st esst,
    small_step (c1, st) (c1', esst) ->
    small_step (SCSeq c1 c2, st) (SCSeq c1' c2, esst)
| SS_SeqSkip : forall c2 st,
    small_step (SCSeq SCSkip c2, st) (c2, st)
| SS_IfTrue : forall b c1 c2 s h,
    beval s b = true ->
    small_step (SCIf b c1 c2, St (s, h)) (c1, St (s, h))
| SS_IfFalse : forall b c1 c2 s h,
    beval s b = false ->
    small_step (SCIf b c1 c2, St (s, h)) (c2, St (s, h))
| SS_WhileEnd : forall b c s h,
    beval s b = false ->
    small_step (SCWhile b c, St (s, h)) (SCSkip, St (s, h))
| SS_WhileLoop : forall b c s h,
    beval s b = true ->
    small_step (SCWhile b c, St (s, h))
               (SCSeq c (SCWhile b c), (St (s, h)))
| SS_Cons : forall s h e1 e2 X n1 n2 l,
    not_in_dom l h -> not_in_dom (l+1) h ->
    aeval s e1 = n1 -> aeval s e2 = n2 ->
    small_step (SCCons X e1 e2, St (s, h))
               (SCSkip, St (st_update s X l,
                            h_update (h_update h l n1) (l+1) n2))
| SS_Lookup : forall s h e X n l,
    aeval s e = l -> in_dom l h -> h l = Some n ->
    small_step (SCLookup X e, St (s, h))
               (SCSkip, St (st_update s X n, h))
| SS_LookupAb : forall s h e X l,
    aeval s e = l -> not_in_dom l h ->
    small_step (SCLookup X e, St (s, h)) (SCSkip, Abt)
| SS_Mutation : forall s h e1 e2 l n,
    aeval s e1 = l -> in_dom l h -> aeval s e2 = n ->
    small_step (SCMutation e1 e2, St (s, h))
               (SCSkip, St (s, h_update h l n))
| SS_MutationAb : forall s h e1 e2 l,
    aeval s e1 = l -> not_in_dom l h ->
    small_step (SCMutation e1 e2, St (s, h)) (SCSkip, Abt)
| SS_Dispose : forall s h e l,
    aeval s e = l -> in_dom l h ->
    small_step (SCDispose e, St (s, h))
               (SCSkip, St (s, (fun l' => if eq_nat_dec l l' then
                                            None else h l')))
| SS_DisposeAb : forall s h e l,
    aeval s e = l -> not_in_dom l h ->
    small_step (SCDispose e, St (s, h)) (SCSkip, Abt).

Hint Constructors big_step.
Hint Constructors small_step.
               
(** Assertions **)
Definition sass := sstate -> Prop.

(* define semantics of assertion emp *)
Definition emp : sass := 
    fun st: sstate => 
      snd st = emp_heap.

(* assertion e1 |-> e2 *)
Definition pto (e1 e2: aexp) : sass := 
    fun st: sstate =>
      match st with
      | (s, h) => h = h_update emp_heap (aeval s e1) (aeval s e2)
      end.
Notation "e1 '|->' e2" := (pto e1 e2) (at level 60).

(* p * q *)
Definition star (p q : sass) : sass := 
    fun st: sstate =>
      match st with
      | (s, h) => 
        exists h1, exists h2, 
          disjoint h1 h2 /\ h_union h1 h2 = h /\ p (s, h1) /\ q (s, h2)
      end.
Notation "p '**' q" := (star p q) (at level 70).

(* p --* q *)
Definition simp (p q: sass) : sass := 
  fun (st : sstate) =>
    match st with
    | (s, h) => 
      forall h', disjoint h' h -> p (s, h') -> q (s, h_union h h')
    end.
Notation "p '--*' q" := (simp p q) (at level 80).

Definition pure (p: sass) : Prop := 
  forall s h1 h2, p (s, h1) -> p (s, h2).

Definition precise (p: sass) : Prop := 
  forall h h1 h2 s, 
     h_subset h1 h 
     -> h_subset h2 h 
     -> p (s, h1) 
     -> p (s, h2)
     -> h1 = h2.

Definition intuitionistic (p: sass) : Prop := 
  forall s h h', p (s, h) -> disjoint h h' -> p (s, h_union h h').


(* continue here *)

Definition s_conj (p q: sass) : sass :=
  fun (s: sstate) => p s /\ q s.
Notation "p '//\\' q" := (s_conj p q) (at level 75).

Definition s_disj (p q: sass) : sass :=
  fun (s: sstate) => p s \/ q s.
Notation "p '\\//' q" := (s_disj p q) (at level 78).

Definition s_imp (p q: sass) : sass :=
  fun (s: sstate) => p s -> q s.
Notation "p '~~>' q" := (s_imp p q) (at level 85).

Definition strongerThan (p q: sass) : Prop :=
  forall s: sstate, s_imp p q s.
Notation "p '==>' q" := (strongerThan p q) (at level 90).

Definition spEquiv (p q: sass) : Prop :=
  (p ==> q) /\ (q ==> p).
Notation "p '<==>' q" := (spEquiv p q) (at level 90).

(* Prove the following lemmas *)
Lemma disj_star_distr: forall (p q r: sass),
  (p \\// q) ** r <==> (p ** r) \\// (q ** r).
Proof.
  unfold spEquiv, strongerThan, s_imp. split.
  - intros. unfold s_disj, star in *. destruct s as [s h].
    destruct H as [h1 [h2]]. destruct H as [Hdisj [Hunion [Hpq Hr]]].
    destruct Hpq as [Hp | Hq].
    + left. exists h1, h2. eauto.
    + right. exists h1, h2. eauto.
  - intros. unfold s_disj, star in *. destruct s as [s h].
    destruct H as [H1 | H2].
    + destruct H1 as [h1 [h2 [Hdisj [Hunion [Hp Hr]]]]].
      exists h1, h2. eauto.
    + destruct H2 as [h1 [h2 [Hdisj [Hunion [Hp Hr]]]]].
      exists h1, h2. eauto.
Qed.

Lemma conj_star_distr: forall (p q r: sass),
  (p //\\ q) ** r ==> (p ** r) //\\ (q ** r).
Proof.
  unfold strongerThan, s_imp, star, s_conj. intros.
  destruct s as (s, h). destruct H as [h1 [h2]]. split.
  - destruct H as [Hdisj [Hunion [[Hp Hq] Hr]]].
    exists h1, h2. auto.
  - destruct H as [Hdisj [Hunion [[Hp Hq] Hr]]].
    exists h1, h2. auto.
Qed.

Lemma sub_union_h : forall h1 h2 h,
    disjoint h1 h2 ->
    h_union h1 h2 = h -> (h_subset h1 h /\ h_subset h2 h).
Proof.
  intros. split.
  - rewrite <- H0. unfold h_subset, h_union. intros.
    destruct (in_not_in_dec l h1). auto. unfold not_in_dom in n0.
    rewrite n0 in H1. inversion H1.
  - rewrite <- H0. unfold h_subset, h_union. intros.
    destruct (in_not_in_dec l h1); auto. unfold in_dom in i.
    destruct i. unfold disjoint in H. unfold not_in_dom in H.
    destruct (H l) as [Hl1 | Hl2]. rewrite Hl1 in H2. inversion H2.
    rewrite Hl2 in H1. inversion H1.
Qed.

Lemma union_part : forall h1 h2 h3 h4 h,
    disjoint h1 h2 -> disjoint h3 h4 ->
    h_union h1 h2 = h -> h_union h3 h4 = h -> h1 = h3 ->
    h2 = h4.
Proof.
  intros. apply functional_extensionality. intros.
  unfold disjoint, h_union in *. apply equal_f with x in H1.
  apply equal_f with x in H2.
  destruct (in_not_in_dec x h1) in H1.
  destruct (in_not_in_dec x h3) in H2.
  - unfold in_dom in *. destruct i; destruct i0.
    rewrite H4 in H1. rewrite <- H1 in H2. rewrite H5 in H2.
    inversion H2. subst. destruct (H x) as [Hh3 | Hh2].
    + unfold not_in_dom in Hh3. rewrite Hh3 in H5. inversion H5.
    + destruct (H0 x) as [Hh3' | Hh4]. unfold not_in_dom in Hh3'.
      rewrite Hh3' in H5. inversion H5.
      unfold not_in_dom in Hh2, Hh4. rewrite Hh2, Hh4. reflexivity.
  - subst. unfold in_dom in i. unfold not_in_dom in n. destruct i.
    rewrite n in H3. inversion H3.
  - subst. destruct (in_not_in_dec x h3).
    + unfold in_dom in i. destruct i. unfold not_in_dom in n.
      rewrite n in H3. inversion H3.
    + rewrite H1, H2. reflexivity.
Qed.

Lemma disjoint_symmetry : forall h1 h2,
    disjoint h1 h2 -> disjoint h2 h1.
Proof.
  intros. unfold disjoint in *. intros.
  destruct (H l) as [H1 | H2]; auto.
Qed.

Lemma disj_union_symmetry : forall h1 h2,
    disjoint h1 h2 -> h_union h1 h2 = h_union h2 h1.
Proof.
  intros. unfold h_union. apply functional_extensionality.
  intros. destruct (in_not_in_dec x h1); destruct (in_not_in_dec x h2);
            try reflexivity.
  - unfold disjoint in H. destruct (H x) as [H1 | H2].
    unfold not_in_dom, in_dom in *. destruct i.
    rewrite H1 in H0. inversion H0.
    unfold not_in_dom, in_dom in *. destruct i0.
    rewrite H0 in H2. inversion H2.
  - unfold not_in_dom in *. rewrite n, n0. reflexivity.
Qed.
   
Lemma precise_conj_distr: forall (p q r: sass),
  precise r -> (p ** r) //\\ (q ** r) ==> (p //\\ q) ** r.
Proof.
  unfold strongerThan, s_imp, s_conj, star. intros.
  destruct s as [s h]. destruct H0 as [H1 H2].
  destruct H1 as [h1 [h2]]. destruct H2 as [h3 [h4]].
  unfold precise in H.
  destruct H0 as [Hdisj1 [Hunion1 [Hp1 Hr1]]].
  destruct H1 as [Hdisj2 [Hunion2 [Hp2 Hr2]]].
  assert (H1 : h2 = h4).
  { apply (H h h2 h4 s); auto.
    apply (sub_union_h h1 h2 h) in Hdisj1; auto.
    destruct Hdisj1 as [H1 H2]. auto.
    apply (sub_union_h h3 h4 h) in Hdisj2; auto.
    destruct Hdisj2 as [H1 H2]. auto.
  }
  assert (H2 : h1 = h3).
  { apply (union_part h2 h1 h4 h3 h). apply disjoint_symmetry. auto.
    apply disjoint_symmetry. auto.
    apply disj_union_symmetry in Hdisj1. rewrite <- Hdisj1. auto.
    apply disj_union_symmetry in Hdisj2. rewrite <- Hdisj2. auto.
    auto.
  }
  subst. exists h3, h4. auto.
Qed.
 
Inductive multiStep : 
    scom * ext_state -> scom * ext_state -> Prop :=
| step0: forall c s, multiStep (c, s) (c, s)
| stepn: forall c s c' s' c'' s'', 
           small_step (c, s) (c', s')
           -> multiStep (c', s') (c'', s'')
           -> multiStep (c, s) (c'', s'').

(* c is safe at state s *)
Definition safeAt (c: scom) (s: sstate) : Prop :=
  forall c' s',
    multiStep (c, St s) (c', St s') ->
    c' = SCSkip \/ exists c'' s'', small_step (c', St s') (c'', St s'').
(* ~ multiStep (c, St s) Abt *) 
(*
forall c' s',
  multiStep (c, St s) (c', St s')
  -> c' = SKIP \/ exists c'', exists s'', small_step (c', St s') (c'', St s'').
*)

Definition safeMono (c: scom) : Prop :=
  forall s h h',
    safeAt c (s, h) -> disjoint h h' -> safeAt c (s, h_union h h').
(*
  forall s h h', 
    safeAt c (s, h) -> disjoint h h' -> safeAt c (s, h_union h h').
*)

Definition frame (c: scom) : Prop :=
  forall s h1 h2 c' s' h',
    safeAt c (s, h1) 
    -> disjoint h1 h2 
    -> small_step (c, St (s, h_union h1 h2)) (c', St (s', h'))
    -> exists h1', 
         small_step (c, St (s, h1)) (c', St (s', h1'))
         /\ disjoint h1' h2 
         /\ h_union h1' h2 = h'.

Lemma multiStep_excu : forall c1 c2 c3 s1 s2 s3,
    multiStep (c1, s1) (c2, s2) -> multiStep (c2, s2) (c3, s3) ->
    multiStep (c1, s1) (c3, s3).
Proof.
  intros. generalize dependent c3.
  generalize dependent s3. induction H; intros.
  - assumption.
  - apply IHmultiStep in H1. eapply stepn. apply H.
    assumption.
Qed.

Lemma small_step_Abt : forall c c' st st',
    small_step (c, st) (c', st') -> st = Abt -> st' = Abt.
Proof.
  intros c c' st. generalize dependent c'.
  induction c; intros; subst; try solve [inversion H].
  inversion H; subst. apply IHc1 in H1; auto. reflexivity.
Qed.

Lemma multiStep_seq : forall cs cs' c2,
    multiStep cs cs' ->
    multiStep (SCSeq (fst cs) c2, (snd cs))
              (SCSeq (fst cs') c2, (snd cs')).
Proof.
  intros. induction H.
  - simpl. constructor.
  - simpl in *. econstructor. constructor. apply H. assumption.
Qed.

Lemma multiStep_Abt : forall cs cs',
    multiStep cs cs' -> snd cs = Abt -> snd cs' = Abt.
Proof.
  intros. induction H; auto. simpl in H0. subst s.
  apply IHmultiStep. apply small_step_Abt in H; auto.
Qed.

Lemma safeAt_seq : forall c1 c2 (s : state) h,
    safeAt (SCSeq c1 c2) (s, h) -> safeAt c1 (s, h).
Proof.
  unfold safeAt. intros.
  assert (H1 : multiStep (SCSeq c1 c2, St (s, h)) (SCSeq c' c2, St s')).
  { remember (c1, St (s, h)) as cs. remember (c', St s') as cs'.
    apply multiStep_seq with (c2 := c2) in H0. subst cs. subst cs'.
    simpl in H0. assumption.
  }
  apply H in H1. destruct H1. inversion H1. destruct H1 as [c'' [s'']].
  inversion H1; subst. right. exists c1', s''. assumption.
  left. reflexivity.
Qed.

Lemma disjoint_extend : forall h1 h2 l n,
    disjoint h1 h2 -> not_in_dom l h2 ->
    disjoint (h_update h1 l n) h2.
Proof.
  intros. unfold disjoint in *. intros.
  destruct (H l0) as [Hh1 | Hh2].
  - destruct (l =? l0) eqn:Heqe. apply beq_nat_true_iff in Heqe.
    subst. right. assumption. left. unfold not_in_dom.
    unfold not_in_dom in Hh1. unfold h_update.
    destruct (eq_nat_dec l l0) eqn:Heqe1. unfold eq_nat_dec in Heqe1.
    rewrite Heqe in Heqe1. inversion Heqe1. assumption.
  - right. assumption.
Qed.

Lemma union_in : forall h1 h2 l,
    disjoint h1 h2 -> in_dom l h1 \/ in_dom l h2 ->
    in_dom l (h_union h1 h2).
Proof.
  intros. destruct H0 as [H1 | H2].
  - unfold in_dom in *. destruct H1. exists x.
    unfold h_union. destruct (in_not_in_dec l h1).
    assumption. unfold not_in_dom in n. rewrite n in H0. inversion H0.
  - unfold in_dom in *. destruct H2. exists x.
    unfold h_union. destruct (in_not_in_dec l h1); auto.
    unfold disjoint in H. destruct (H l) as [H1 | H2].
    unfold in_dom in i. destruct i. unfold not_in_dom in H1.
    rewrite H1 in H2. inversion H2. unfold not_in_dom in H2.
    rewrite H2 in H0. inversion H0.
Qed.

Lemma union_not_in : forall h1 h2 l,
    not_in_dom l (h_union h1 h2) ->
    not_in_dom l h1 /\ not_in_dom l h2.
Proof.
  intros. split.
  - unfold not_in_dom in *. unfold h_union in *.
    destruct (in_not_in_dec l h1). assumption. unfold not_in_dom in n.
    assumption.
  - unfold not_in_dom in *. unfold h_union in *.
    destruct (in_not_in_dec l h1). unfold in_dom in i. destruct i.
    rewrite H0 in H. inversion H. assumption.
Qed.

Lemma h_union_extend : forall h h' l n,
    h_union (h_update h l n) h' = h_update (h_union h h') l n.
Proof.
  intros. apply functional_extensionality. intro.
  unfold h_union. destruct (in_not_in_dec x (h_update h l n)).
  unfold h_update. destruct (eq_nat_dec l x) eqn:Heqe; auto.
  unfold in_dom in i. destruct i. unfold h_update in H.
  destruct (eq_nat_dec l x) eqn:Heqe1; auto. inversion Heqe.
  destruct (in_not_in_dec x h); auto. unfold not_in_dom in n0.
  rewrite n0 in H. inversion H.
  unfold h_update. unfold not_in_dom in n0.
  destruct (eq_nat_dec l x) eqn:Heqe. unfold h_update in n0.
  destruct (eq_nat_dec l x) eqn:Heqe1. inversion n0.
  inversion Heqe. destruct (in_not_in_dec x h); auto.
  unfold h_update in n0. destruct (eq_nat_dec l x) eqn:Heqe1.
  inversion Heqe. unfold in_dom in i. destruct i.
  rewrite n0 in H. inversion H.
Qed.

Lemma union_get_value : forall h1 h2 l n,
    h1 l = Some n -> (h_union h1 h2) l = Some n.
Proof.
  intros. unfold h_union. destruct (in_not_in_dec l h1).
  assumption. unfold not_in_dom in n0. rewrite n0 in H. inversion H.
Qed.

Lemma union_dispose : forall h1 h2 l,
    disjoint h1 h2 -> in_dom l h1 ->
    h_union (fun l' : nat =>
               if eq_nat_dec l l' then None else h1 l') h2 =
    (fun l' : nat =>
       if eq_nat_dec l l' then None else (h_union h1 h2) l').
Proof.
  intros. apply functional_extensionality. intro.
  unfold h_union. destruct (eq_nat_dec l x) eqn:Heqe.
  - destruct (in_not_in_dec x
          (fun l' : nat => if eq_nat_dec l l' then None else h1 l')).
    reflexivity. unfold eq_nat_dec in Heqe.
    apply beq_nat_true_iff in Heqe. subst. unfold disjoint in H.
    destruct (H x) as [H1 | H2]. unfold in_dom, not_in_dom in *.
    destruct H0. rewrite H0 in H1. inversion H1.
    unfold not_in_dom in H2. assumption.
  - destruct (in_not_in_dec x
           (fun l' : nat => if eq_nat_dec l l' then None else h1 l')).
    unfold in_dom in i. destruct i. rewrite Heqe in H1.
    destruct (in_not_in_dec x h1). reflexivity.
    unfold not_in_dom in n. rewrite n in H1. inversion H1.
    destruct (in_not_in_dec x h1). unfold not_in_dom in n.
    rewrite Heqe in n. unfold in_dom in i. destruct i.
    rewrite n in H1. inversion H1. reflexivity.
Qed.

Lemma disjoint_l_in : forall h1 h2 l n,
    disjoint h1 h2 -> in_dom l h1 ->
    disjoint (h_update h1 l n) h2.
Proof.
  intros. unfold disjoint in *. intros.
  destruct (H l0) as [H1 | H2].
  - destruct (l =? l0) eqn:Heqe. apply beq_nat_true_iff in Heqe.
    subst. unfold not_in_dom, in_dom in *. destruct H0.
    rewrite H1 in H0. inversion H0. left.
    unfold not_in_dom in *. unfold h_update.
    destruct (eq_nat_dec l l0) eqn:Heqe1. unfold eq_nat_dec in *.
    rewrite Heqe in Heqe1. inversion Heqe1. assumption.
  - right. assumption.
Qed.

Lemma disjoint_l_seq : forall h1 h2 l,
    disjoint h1 h2 -> in_dom l h1 ->
    disjoint (fun l' : nat => if eq_nat_dec l l' then None
                              else h1 l') h2.
Proof.
  intros. unfold disjoint in *. intro l0. destruct (H l0) as [H1 | H2].
  - left. unfold not_in_dom in *. destruct (eq_nat_dec l l0) eqn:Heqe.
    reflexivity. unfold eq_nat_dec in Heqe. assumption.
  - right. assumption.
Qed.

Theorem frame_correct : forall c, frame c.
Proof.
  intros c. induction c; unfold frame in *; intros;
              try solve [exists h1; inversion H1; subst; auto].
  - (* Seq *) apply safeAt_seq in H. inversion H1; subst.
    + eapply IHc1 in H; eauto.
      destruct H as [h'' [Hstp [Hdisj]]]. exists h''.
      auto.
    + exists h1. auto.
  - (* Cons *) inversion H1; subst.
    assert (Hnot_in1 : not_in_dom l h1).
    { apply union_not_in in H6. destruct H6 as [Hh1 Hh2].
      assumption.
    }
    assert (Hnot_in2 : not_in_dom (l+1) h1).
    { apply union_not_in in H11. destruct H11 as [Hh1 Hh2].
      assumption.
    }
    exists (h_update (h_update h1 l (aeval s a)) (l+1) (aeval s a0)).
    split. constructor; auto. split. apply disjoint_extend.
    apply disjoint_extend. assumption. apply union_not_in in H6.
    apply H6. apply union_not_in in H11. apply H11.
    rewrite h_union_extend. rewrite h_union_extend. reflexivity.
  - (* Lookup *) unfold safeAt in H.
    assert (H2 : multiStep (SCLookup i a, St (s, h1))
                           (SCLookup i a, St (s, h1))). constructor.
    apply H in H2. destruct H2. inversion H2.
    destruct H2 as [c'' [s'']]. inversion H2; subst.
    inversion H1; subst. exists h1. split.
    apply union_get_value with (h2 := h2) in H11. rewrite H11 in H14.
    inversion H14; subst. assumption. auto.
  - (* Mutation *) unfold safeAt in H.
    assert (H2 : multiStep (SCMutation a a0, St (s, h1))
                           (SCMutation a a0, St (s, h1))).
    constructor. apply H in H2. destruct H2. inversion H2.
    destruct H2 as [c'' [s'']]. inversion H2; subst.
    inversion H1; subst.
    exists (h_update h1 (aeval s' a) (aeval s' a0)).
    split. assumption. split. apply disjoint_l_in; auto.
    rewrite h_union_extend. reflexivity.
  - (* Dispose *) unfold safeAt in H.
    assert (H2 : multiStep (SCDispose a, St (s, h1))
                           (SCDispose a, St (s, h1))). constructor.
    apply H in H2. destruct H2 as [Hskip | Hstep]. inversion Hskip.
    destruct Hstep as [c'' [s'']]. inversion H2; subst.
    inversion H1; subst.
    exists (fun l' : nat =>
              if eq_nat_dec (aeval s' a) l' then None else h1 l').
    split. assumption. split. apply disjoint_l_seq; auto.
    apply union_dispose; auto.
Qed.
  
Theorem small_step_extend : forall c c' s s' h h' h'',
    small_step (c, St (s, h)) (c', St (s', h')) -> disjoint h h'' ->
    exists sh,
      small_step (c, St (s, h_union h h''))
                 (c', St sh).
Proof.
  intros c. induction c; intros.
  - (* Skip *) inversion H.
  - (* Ass *) inversion H; subst. exists (st_update s i (aeval s a),
                                            h_union h' h''). 
    constructor. reflexivity.
  - (* Seq *) inversion H; subst.
    apply IHc1 with (h'' := h'') in H2; auto. destruct H2.
    exists x. constructor. assumption.
    exists (s', h_union h' h''). constructor.
  - (* If *) inversion H; subst. exists (s', h_union h' h'').
    constructor; auto. exists (s', h_union h' h''). constructor; auto.
  - (* While *) inversion H; subst. exists (s', h_union h' h'').
    constructor; auto. exists (s', h_union h' h''). constructor; auto.
  - (* Cons *) inversion H; subst.
    destruct (heap_allocate_success (h_union h h'')) as [l'].
    assert (Hl : l' < l' + 1) by omega.
    assert (Hl' : l' < l' + 2) by omega.
    apply H1 in Hl. apply H1 in Hl'.
    exists (st_update s i (l'+1),
        h_update
          (h_update (h_union h h'') (l' + 1) (aeval s a))
           ((l' + 1) + 1) (aeval s a0)
      ).
    constructor; auto.
    assert (l' + 1 + 1 = l' + 2) by omega. rewrite H2. auto.
  - (* Lookup *) inversion H; subst. 
    exists (st_update s i n, h_union h' h'').
    apply SS_Lookup with (aeval s a); auto. apply union_in; auto.
    unfold h_union. destruct (in_not_in_dec (aeval s a) h').
    auto. unfold not_in_dom in n0. rewrite n0 in H10. inversion H10.
  - (* Mutation *) inversion H; subst.
    exists (s', h_update (h_union h h'')
                         (aeval s' a) (aeval s' a0)).
    constructor; auto. apply union_in; auto.
  - (* Dispose *) inversion H; subst.
    exists (s',
          fun l' : nat =>
            if eq_nat_dec (aeval s' a) l' then None
            else (h_union h h'') l').
    constructor; auto. apply union_in; auto.
Qed.

Lemma safeAt_continues :
  forall c c' st st',
    safeAt c st -> small_step (c, St st) (c', St st') ->
    safeAt c' st'.
Proof.
  intros. unfold safeAt. intros. unfold safeAt in H.
  assert (H' : multiStep (c, St st) (c'0, St s')).
  { eapply stepn. apply H0. apply H1. }
  apply H in H'. destruct H' as [Hskip | Hstep].
  left. assumption. right. assumption.
Qed.

Lemma safeMono_correct : forall c, safeMono c.
Proof.
  unfold safeMono. unfold safeAt. intros.
  remember (c, St (s, h_union h h')) as cs.
  remember (c', St s') as cs'.
  generalize dependent c. generalize dependent s.
  generalize dependent h. induction H1; intros.
  - inversion Heqcs; subst. inversion  Heqcs'; subst.
    clear Heqcs. clear Heqcs'.
    assert (H' : multiStep (c', St (s0, h)) (c', St (s0, h)))
      by constructor.
    apply H in H'. destruct H' as [Hskip | Hstep].
    left. assumption.
    right. destruct Hstep as [c'' [s'']]. destruct s'' as [s'' h''].
    apply small_step_extend with (h'' := h') in H1; auto.
    destruct H1 as [sh]. exists c''. exists sh. assumption.
  - inversion Heqcs; subst. inversion Heqcs'; subst.
    assert (frame c0). apply frame_correct. unfold frame in H3.
    destruct s'0. destruct s.
    assert (safeAt c0 (s0, h)). unfold safeAt. apply H2.
    eapply H3 in H4; eauto. destruct H4 as [h1' [Hstep [Hdisj Hunion]]].
    eapply IHmultiStep in Hdisj; eauto.
    eapply safeAt_continues in H2; eauto. rewrite <- Hunion.
    reflexivity. apply multiStep_Abt in H1; auto. simpl in H1.
    inversion H1.
Qed.

Theorem locality: forall c : scom, safeMono c /\ frame c.
  intros. split. apply safeMono_correct. apply frame_correct.
Qed.
