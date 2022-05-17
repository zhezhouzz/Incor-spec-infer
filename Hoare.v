(** * Hoare: Hoare Logic, Part I *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
From PLF Require Import Imp.
From PLF Require Import Maps.

Hint Constructors ceval.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Definition assert_frame_within_vars_implies (P Q : Assertion) (vars: list string) : Prop :=
  forall st, P st -> exists st', Q st' /\ frame_within_vars st st' vars.

Definition assert_frame_within_vars (P Q : Assertion) (vars: list string) : Prop :=
  assert_frame_within_vars_implies P Q vars /\ assert_frame_within_vars_implies Q P vars.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : under_spec_scope.
Notation "'D<' vars 'D>' P ->> Q" := (assert_frame_within_vars P Q vars)
                      (at level 10, P at next level, vars at next level, Q at next level) : under_spec_scope.
Open Scope under_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : under_spec_scope.

Definition under_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st', Q st' -> exists st,
      P st /\ c / st \\ st'.

Notation "[[ P ]]  c [[ Q ]]" :=
  (under_triple P c Q) (at level 90, c at next level)
  : under_spec_scope.

Theorem under_post_false : forall (P Q : Assertion) c,
  (forall st, ~ (Q st)) ->
  [[P]] c [[Q]].
Proof.
  intros P Q c H. unfold under_triple.
  intros st' HQ.
  assert (~ (Q st')). auto.
  exfalso. auto.
Qed.

Definition assn_v_n X v P :=
  fun (st : state) =>
    (snd st) X = v /\ P (remove_n st X).

Definition assn_v_l X v P : Assertion :=
  fun (st : state) =>
    (fst st) X = v /\ P (remove_l st X).

Definition assn_sub_n X a P :=
  fun (st : state) =>
    (snd st) X = neval (remove_n st X) a /\ P (remove_n st X).

Definition assn_sub_l X a P : Assertion :=
  fun (st : state) =>
    (fst st) X = leval (remove_l st X) a /\ P (remove_l st X).

Notation "P { X N-> a }" := (assn_v_n X a P) (at level 10).
Notation "P { X L-> a }" := (assn_v_l X a P) (at level 10).
Notation "P { X |N-> a }" := (assn_sub_n X a P) (at level 10).
Notation "P { X |L-> a }" := (assn_sub_l X a P) (at level 10).

Theorem under_asgn_n : forall (P: Assertion) (X: string) (a:nexp) ,
    (forall st, P st -> ((snd st) X = None)) ->
    [[P]] (X N= a) [[P { X |N-> a}]].
Proof.
  unfold under_triple.
  intros P X a HFresh st' HP.
  unfold assn_sub_n in HP.
  destruct HP as [HP1 HP2].
  exists (remove_n st' X).
  split.
  - auto.
  - assert (st' = update_n (remove_n st' X) X (snd st' X)).
    rewrite -> update_after_remove_n. auto.
    rewrite HP1 in H.
    rewrite H at 2.
    apply E_AssN.
    auto.
Qed.

Theorem under_asgn_l : forall (P: Assertion) (X: string) (a:lexp),
    (forall st, P st -> ((fst st) X = None)) ->
    [[P]] (X L= a) [[P { X |L-> a}]].
Proof.
  unfold under_triple.
  intros P X a HFresh st' HP.
  unfold assn_sub_l in HP.
  destruct HP as [HP1 HP2].
  exists (remove_l st' X).
  split.
  - auto.
  - assert (st' = update_l (remove_l st' X) X (fst st' X)).
    rewrite -> update_after_remove_l. auto.
    rewrite HP1 in H.
    rewrite H at 2.
    apply E_AssL.
    auto.
Qed.

Definition assertion_same_besides (P Q: Assertion) (x: string) :=
  (forall st, Q st -> exists nu, (fst st x) = Some nu /\ P (remove_l st x)) /\
    (forall st, P st -> exists nu, P (update_l st x (Some nu))).

Definition frame_pre (P P': Assertion) (arg1 arg2: string) :=
  forall st, P st ->
        exists st' s1 s2,
          P' st'
          /\ (fst st' arg1 = Some s1)
          /\ (fst st' arg2 = Some s2)
          /\ (fst st S1 = Some s1)
          /\ (fst st S2 = Some s2).

Definition frame_post (Q Q': Assertion) (arg1 arg2 ret: string) :=
  forall st', Q' st' ->
         exists st s1 s2 nu,
           Q st
           /\ (fst st' arg1 = Some s1)
           /\ (fst st' arg2 = Some s2)
           /\ (fst st' ret = Some nu)
           /\ (fst st S1 = Some s1)
           /\ (fst st S2 = Some s2)
           /\ (fst st NU = Some nu).

Definition assertion_elim_vars (P P': Assertion) :=
  fun st =>
    P st <-> (exists s1 s2 st',
               st = ({S1 --> s1; S2 --> s2}, empty) /\
                 fst st' S1 = Some s1 /\
                 fst st' S2 = Some s2 /\
                 P' st'
           ).

Definition assertion_clean_pre (P: Assertion) :=
  forall st,
    P st ->
    (forall s,
      ((~(s = S1)) /\ (~(s = S2))) -> fst st s = None) /\ (forall s, snd st s = None).

Definition frame_implies2 (P SpecP: Assertion) (arg1 arg1' arg2 arg2': string) :=
  (forall st, SpecP st ->
         (exists st' s1 s2,
             P st' /\
               fst st arg1 = Some s1 /\
               fst st arg2 = Some s2 /\
               fst st' arg1' = Some s1 /\
               fst st' arg2' = Some s2
  )).

Definition frame_implies3 (P SpecP: Assertion) (arg1 arg1' arg2 arg2' ret ret': string) :=
  (forall st, SpecP st ->
         (exists st' s1 s2 nu,
             P st' /\
               fst st arg1 = Some s1 /\
               fst st arg2 = Some s2 /\
               fst st ret = Some nu /\
               fst st' arg1' = Some s1 /\
               fst st' arg2' = Some s2 /\
               fst st' ret' = Some nu
  )).

Definition pre_apply_frame (P SpecP: Assertion) (arg1 arg1' arg2 arg2': string) :=
  frame_implies2 P SpecP arg1 arg1' arg2 arg2' /\ frame_implies2 SpecP P arg1' arg1 arg2' arg2.

Definition post_apply_frame (P SpecP: Assertion) (arg1 arg1' arg2 arg2' ret ret': string) :=
  frame_implies3 P SpecP arg1 arg1' arg2 arg2' ret ret' /\ frame_implies3 SpecP P arg1' arg1 arg2' arg2 ret' ret.

Definition assertion_forget (Q: Assertion) (x: string) :=
  fun st => fst st x = None /\ (exists nu, Q (update_l st x (Some nu))).

Lemma functional_execution (st st': state) (c: com):
  c / st \\ st' ->
  (forall x v, (fst st x = Some v) -> (fst st' x = Some v)) /\
     (forall x v, (snd st x = Some v) -> (snd st' x = Some v)).
Proof.
Admitted.

Theorem under_asgn_assn : forall (P Q Q': Assertion) (ret arg1 arg2: string) (c: com),
    pre_apply_frame P (assertion_forget Q ret) arg1 S1 arg2 S2 ->
    post_apply_frame Q Q' arg1 S1 arg2 S2 ret NU ->
    [[P]] c [[Q]] ->
    [[assertion_forget Q' ret]] (CAssApply ret c arg1 arg2) [[Q']].
Proof.
  fold under_triple.
  intros P Q Q' ret arg1 arg2 c (_ & HPre) (HPost & _) HC st' HQ.
  unfold frame_implies3 in HPost.
  assert (Q' st') as HQ_dup. auto.
  apply HPost in HQ.
  destruct HQ as (cst' & s1 & s2 & nu & Hspec & Hs1 & Hs2 & Hnu & Hs1' & Hs2' & Hnu').
  exists (remove_l st' ret).
  split.
  - split.
    + admit.
    + exists nu. rewrite <- Hnu. rewrite update_after_remove_l. auto.
  - rewrite <- update_after_remove_l with (x := ret). rewrite Hnu.
    apply HC in Hspec.
    destruct Hspec as (cst & HcP & Hc).
    assert (c / cst \\ cst') as Hc_dup. auto.
    apply functional_execution in Hc.
    destruct Hc as (Hc & _).
    apply HPre in HcP.
    destruct HcP as (_ & s1' & s2' & _ & Hcs1 & Hcs2 & _ & _).
    apply E_AssApply with (s1 := s1) (s2 := s2) (cst := cst) (cst':= cst'); auto.
    + rewrite Hcs1. apply Hc in Hcs1. rewrite <- Hs1'. rewrite Hcs1. auto.
    + rewrite Hcs2. apply Hc in Hcs2. rewrite <- Hs2'. rewrite Hcs2. auto.
    + admit.
    + admit.
    + admit.
Admitted.

(* Theorem under_asgn_assn : forall (P Q P' Q': Assertion) (ret arg1 arg2: string) (c: com), *)
(*     frame_pre P P' arg1 arg2 -> *)
(*     assertion_clean_pre P -> *)
(*     assertion_same_besides P Q ret -> *)
(*     [[P]] c [[Q]] -> *)
(*     frame_post Q Q' arg1 arg2 ret -> *)
(*     assertion_same_besides P' Q' ret -> *)
(*     [[P']] (CAssApply ret c arg1 arg2) [[Q']]. *)
(* Proof. *)
(*   unfold under_triple. *)
(*   intros P Q P' Q' ret arg1 arg2 c HFramePre HCleanPre (HcSame1 & HcSame2) HC HFramePost (HSame1 & HSame2) st' HQ. *)
(*   assert (exists nu, (fst st' ret) = Some nu /\ P' (remove_l st' ret)) as HP'; auto. *)
(*   destruct HP' as (nu & Hst' & HP'). *)
(*   exists (remove_l st' ret). *)
(*   split; auto. *)
(*   rewrite <- update_after_remove_l with (x := ret). *)
(*   rewrite Hst'. *)
(*   apply HFramePost in HQ. *)
(*   destruct HQ as (cst' & s1 & s2 & nu' & HcQ & Harg1 & Harg2 & Hret & Hs1 & Hs2 & Hnu). *)
(*   rewrite Hst' in Hret. subst. *)
(*   inversion Hret. subst. clear Hret. *)
(*   apply HC in HcQ. *)
(*   destruct HcQ as (cst & HP & Hcst). *)
(*   apply HFramePre in HP. *)
(*   destruct HP as (st_dup & s1' & s2' & Hstdup & Harg1' & Harg2' & Hs1' & Hs2'). *)
(*   assert (s1 = s1'). admit. *)
(*   assert (s2 = s2'). admit. *)
(*   subst. *)
(*   assert (cst = ({S1 --> s1'; S2 --> s2'}, empty)). admit. *)
(*   apply E_AssApply with (s1 := s1') (s2 := s2') (cst := cst) (cst':= cst'); auto. *)
(*   admit. *)
(*   admit. *)
(*   admit. *)
(* Admitted. *)

Theorem under_consequence : forall (P P' Q Q' : Assertion) c,
  [[P]] c [[Q]] ->
  P ->> P' ->
  Q' ->> Q ->
  [[P']] c [[Q']].
Proof.
  unfold under_triple.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st' Qst'.
  apply HQ'Q in Qst'.
  assert (exists st : state, P st /\ c / st \\ st'); auto.
  destruct H as [st H].
  destruct H as [H1 H2].
  exists st.
  split; auto. Qed.

(** ** Skip *)

Theorem under_skip : forall P,
     [[P]] SKIP [[P]].
Proof.
  intros P st' HQ.
  exists st'.
  split; auto.
Qed.
(** ** Sequencing *)

Theorem under_seq : forall P Q R c1 c2,
     [[Q]] c2 [[R]] ->
     [[P]] c1 [[Q]] ->
     [[P]] c1;;c2 [[R]].
Proof.
  unfold under_triple.
  intros P Q R c1 c2 H1 H2 st HR.
  apply H1 in HR.
  destruct HR as [st' HQ].
  destruct HQ as [HQ1 HQ2].
  apply H2 in HQ1.
  destruct HQ1 as [st'' HP].
  destruct HP as [HP1 HP2].
  exists st''.
  split; auto.
  eapply E_Seq; eauto.
  Qed.

Definition bassn_true b : Assertion :=
  fun st => (beval st b = Some true).

Definition bassn_false b : Assertion :=
  fun st => (beval st b = Some false).

Lemma bexp_eval_true : forall b st,
  beval st b = Some true -> (bassn_true b) st.
Proof.
  intros b st Hbe.
  unfold bassn_true. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = Some false -> ~ ((bassn_true b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn_true in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Theorem under_if_true : forall P Q b c1 c2,
  [[fun st => P st /\ bassn_true b st]] c1[[Q]] ->
  [[P]] (IFB b THEN c1 ELSE c2 FI) [[Q]].
Proof.
  intros P Q b c1 c2 HTrue st HQ.
  apply HTrue in HQ.
  destruct HQ as [st' HQ].
  exists st'.
  destruct HQ as [HQ1 HQ2].
  destruct HQ1 as [HQ11 HQ12].
  split; auto.
Qed.

Theorem under_if_false : forall P Q b c1 c2,
    [[fun st => P st /\ bassn_false b st]] c2 [[Q]] ->
    [[P]] (IFB b THEN c1 ELSE c2 FI) [[Q]].
Proof.
  intros P Q b c1 c2 HTrue st HQ.
  apply HTrue in HQ.
  destruct HQ as [st' HQ].
  exists st'.
  destruct HQ as [HQ1 HQ2].
  destruct HQ1 as [HQ11 HQ12].
  split; auto.
Qed.

Definition spec_to_P (spec: list nat -> list nat -> list nat -> Prop) (arg1 arg2: string) : Assertion :=
  fun st =>
    exists s1 s2 nu, spec s1 s2 nu /\ st = ({arg1 --> s1; arg2 --> s2}, empty).

Definition spec_to_Q (spec: list nat -> list nat -> list nat -> Prop) (arg1 arg2 ret: string) : Assertion :=
  fun st =>
    exists s1 s2 nu, spec s1 s2 nu /\ st = ({arg1 --> s1; arg2 --> s2; ret --> nu}, empty).

Theorem under_spec : forall (spec: list nat -> list nat -> list nat -> Prop),
    [[spec_to_P spec S1 S2]] (CSpec spec) [[ spec_to_Q spec S1 S2 NU ]].
Proof.
  unfold spec_to_P, spec_to_Q.
  intros spec st HQ.
  destruct HQ as (s1 & s2 & nu & Hspec & Hst). subst.
  exists ({S1 --> s1; S2 --> s2}, empty).
  split; auto.
  - exists s1, s2, nu. split; auto.
Qed.

(** ** Loops *)

Theorem under_fix : forall P Q (spec: list nat -> list nat -> list nat -> Prop) c,
    pre_apply_frame P (spec_to_P spec S1 S2) S1 S1 S2 S2 ->
    post_apply_frame Q (spec_to_Q spec S1 S2 NU) S1 S1 S2 S2 NU NU ->
    [[P]] subst_self (CSpec spec) c [[Q]] ->
    [[P]] CFix c [[Q]].
Proof.
  intros P Q spec c HPre (_ & Hpost) HC st' HQ.
  apply Hpost in HQ.
  destruct HQ as (cst' & s1 & s2 & nu & Hspec & Hs1 & Hs2 & Hnu & Hs1' & Hs2' & Hnu').
  exists st'.
  split.
  + admit.
  + apply E_Fix.
Admitted.

Fixpoint mem (l : list nat) (x: nat) :=
  match l with
  | nil => false
  | cons h t => (if Nat.eqb h x then true else mem t x)
  end.

Fixpoint dup (l : list nat) :=
  match l with
  | nil => false
  | cons h t =>
      if mem t h then true else dup t
  end.

Fixpoint twice (l : list nat) (x: nat) :=
  match l with
  | nil => false
  | cons h t => (if Nat.eqb h x then mem t x else twice t x)
  end.

Fixpoint dup3 (l : list nat) :=
  match l with
  | nil => false
  | cons h t =>
      if twice t h then true else dup3 t
  end.

Definition concat_spec1 := fun (s1 s2 nu: list nat) => s1 = nil /\ nu = s2.
Definition concat_spec2 := fun (s1 s2 nu: list nat) =>
                             (~ (s1 = nil)) /\ (dup s1 = false) /\ (dup s2 = false) /\
                               (forall x, ~ (mem s1 x = true /\ mem s2 x = true)) /\
dup nu .

Definition concat_spec :=
  fun (s1 s2 nu: list nat) =>
    (dup s1 = false) /\ (dup s2 = false) /\ (forall x, ~ (mem s1 x = true /\ mem s2 x = true)) /\.

Definition concat_P1: Assertion :=
  fun st =>
    exists s1 s2,
      concat_pre1 s1 s2 /\ st = ({S1 --> s1; S2 --> s2}, empty).

Definition concat_Q1: Assertion :=
  fun st =>
    (exists s1 s2,
      concat_post1 s1 s2 s2
      /\ st = ({S1 --> s1 ; S2 --> s2 ; NU --> s2}, empty))
      \/
    (exists s1 s2 nu h t s3,
      concat_post1 s1 s2 nu
      /\ st = ({S1 --> s1; S2 --> s2; T --> t; S3 --> s3; NU --> nu}, {H --> h})
      /\ s1 = (cons h t) /\ nu = (cons h s3)).

Theorem concat_verification: [[concat_P1]] concat_program  [[concat_Q1]].
Proof.
  unfold concat_P1.
  unfold concat_Q1.
  unfold concat_program.
  remember concat_pre1 as Pre.
  remember concat_post1 as Post.
  (* unfold concat_pre1 in HeqPre. *)
  (* unfold concat_post1 in HeqPost. *)
  apply under_fix with (Pre:= Pre) (Post:= Post).
  - assert (assertion_clean_pre (fun st : state => exists s1 s2 : list nat, Pre s1 s2 /\ st = ({S1 --> s1; S2 --> s2}, empty))).
    { unfold assertion_clean_pre.
      intros st (s1 & s2 & HPre & H). subst. split; auto. admit. }
    unfold pre_is_assertion. split. auto. split.
    intros st H0.
    destruct H0 as (s1 & s2 & HPre & H0); subst. exists s1, s2. split; auto.
    intros s1 s2 H0.
    exists ({S1 --> s1; S2 --> s2}, empty). split; auto. split; auto.
    exists s1, s2. split; auto.
 - unfold post_is_assertion. split.
   + intros. destruct H.
     destruct H as (s1 & s2 & H1 & H2); subst. exists s1, s2, s2. split; auto.
     destruct H as (s1 & s2 & nu & h & t & s3 & H1 & H2 & H3 & H4). subst. exists (cons h t), s2, (cons h s3). split; auto.
   + intros s1 s2 nu HPost.
     assert ()

    destruct H0 as (s1 & s2 & H1 & H2 & HPre). exists s1, s2. split; auto.
    unfold assertion_clean_pre in H.
    
