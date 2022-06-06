(** * Hoare: Hoare Logic, Part I *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
From PLF Require Import Imp.
From PLF Require Import Maps.
Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Notation "a -[ b ]=>  c" := (b / a \\ c) (at level 80) : hoare_spec_scope.

(* The definition of the under triple *)

Definition under_hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st', Q st' -> exists st, P st /\ st -[c]=> st'.

Notation "|= [[ P ]]  c  [[ Q ]]" :=
  (under_hoare_triple P c Q) (at level 90, c at next level)
    : hoare_spec_scope.

Reserved Notation " |- [[ P ]]  c  [[ Q ]]"
         (at level 40, c at next level).

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (st & { X  --> aeval st a }).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Definition assn_sub_rev X a P: Assertion :=
  fun (st : state) => exists v, st X = aeval (st & {X --> v}) a /\ P (st & {X --> v}).

Notation "P [ X /== a ]" := (assn_sub_rev X a P) (at level 10).

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
    beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
    beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Lemma bexp_eval_false_rev : forall b st,
     ~ bassn b st -> beval st b = false.
Proof.
  intros b st.
  destruct (beval st b) eqn:H; intros; auto.
  - exfalso. auto.
Qed.

Lemma bexp_eval_true_rev : forall b st,
     bassn b st -> beval st b = true.
Proof.
  intros b st H.
  inversion H. auto.
Qed.

Hint Resolve bexp_eval_true : core.
Hint Resolve bexp_eval_false : core.
Hint Resolve bexp_eval_false_rev : core.
Hint Resolve bexp_eval_true_rev : core.

Inductive under_hoare_proof : Assertion -> com -> Assertion -> Prop :=
| UH_Skip : forall P,
    |- [[ P ]] SKIP [[P]]
| UH_Asgn : forall P V a,
    |- [[ P ]] (V ::= a) [[ P [V /== a] ]]
| UH_Seq  : forall P c Q d R,
    |- [[P]] c [[Q]] ->
    |- [[Q]] d [[R]] ->
    |- [[P]] (c;; d) [[R]]
| UH_If_t : forall P Q b c1 c2,
    |- [[fun st => P st /\ bassn b st]] c1 [[Q]] ->
    |- [[P]] (IFB b THEN c1 ELSE c2 FI) [[Q]]
| UH_If_f : forall P Q b c1 c2,
    |- [[fun st => P st /\ ~(bassn b st)]] c2 [[Q]] ->
    |- [[P]] (IFB b THEN c1 ELSE c2 FI) [[Q]]
| UH_Consequence  : forall (P Q P' Q' : Assertion) c,
    |- [[P']] c [[Q']] ->
      P' ->> P ->
      Q ->> Q' ->
    |- [[P]] c [[Q]]
| UH_While : forall {A : Type} (R : A -> A -> Prop) M P inv b c,
    (* well founded order relation R a b: a < b *)
    well_founded R ->
    (* Assume M is a ranking function (relation) M st a := ranking function maps st to a.
       Every state in the invaraint has a rank *)
    inv ->> (fun st' => exists a', M st' a') ->
    (* The invaraint should cover the state that is in the precondition and makes the guard to be false *)
    (fun st => P st /\ ~ (bassn b st)) ->> inv ->
    (* Any state in the invaraint and not directly reached from the precondition, there exists a pre state
       1) is in the invaraint
       2) make the guard to be true
       3) is well founded. *)
    (forall a',
        |- [[fun st => exists a, R a a' /\ M st a /\ inv st /\ bassn b st]] c [[ fun st' => inv st' /\ M st' a' /\ ~ P st']]) ->
    (* The conjunction of the negation of guard and the invariant is the postcondition *)
    |- [[P]] WHILE b DO c END [[fun st => inv st /\ ~ (bassn b st)]]

where " |- [[ P ]]  c  [[ Q ]]" := (under_hoare_proof P c Q) : hoare_spec_scope.

Definition uh_while_st := forall {A : Type} (R : A -> A -> Prop) M P b c (Q: Assertion),
    well_founded R ->
    (forall st, Q st -> exists a, M a st) ->
    (forall st' a', Q st' /\ M a' st' ->
               (exists st a,
                   (M a st /\ R a a') /\
                     st -[c]=> st' /\ Q st /\ bassn b st) \/ (~ bassn b st' /\ P st')).

Hint Constructors under_hoare_proof : core.
Hint Constructors ceval : core.
Hint Unfold under_hoare_triple : core.
Hint Unfold assn_sub : core.

Inductive while_prefix (c: com) b : state -> state -> Prop:=
| While_prefix_nil : forall st, while_prefix c b st st
| While_prefix_cons : forall st st' st'',
    bassn b st ->
    st -[c]=> st' ->
    while_prefix c b st' st'' -> while_prefix c b st st''.

Hint Constructors while_prefix : core.

Lemma while_prefix_end (c: com) b: forall st st'',
    while_prefix c b st st'' -> ~ (bassn b st'') -> st -[WHILE b DO c END]=> st''.
Proof.
  intros.
  induction H; eauto.
Qed.

Lemma while_prefix_rev : forall (c: com) b (st st' st'': state),
  while_prefix c b st st' ->
  bassn b st' ->
  st' -[c]=> st'' ->
  while_prefix c b st st''.
Proof.
  intros.
  induction H; eauto.
Qed.

Lemma assertion_destruct: forall (P: Assertion) st, (P st \/ ~ P st).
Proof. Admitted.

Lemma under_hoare_while: forall {A : Type} (R : A -> A -> Prop) M P Q b c,
    well_founded R ->
    Q ->> (fun st' => exists a', M st' a') ->
    (fun st => P st /\ ~ (bassn b st)) ->> Q ->
    (forall a',
        |= [[fun st => exists a, R a a' /\ M st a /\ Q st /\ bassn b st]] c [[ fun st' => Q st' /\ M st' a' /\ ~ P st']]) ->
    (forall st', Q st' -> exists st, while_prefix c b st st' /\ P st).
Proof.
  intros A R M P Q b c Hwellfound HQE H1 Hbody st' HQ'.
  destruct (HQE st' HQ') as (a' & Hm').
  generalize dependent st'.
  induction Hwellfound with a'.
  intros st' HQ' HM'.
  destruct (assertion_destruct P st') as [Hbase | Hind].
  exists st'; split; eauto.
  destruct (Hbody x st') as (stmid & (a & HR & HM & HQ & HT) & Heval). split; auto.
  destruct (H0 a HR stmid) as (st & HW & HP); auto.
  exists st; split; auto.
  apply while_prefix_rev with stmid; auto.
Qed.

(* Soundness *)
Theorem under_hoare_proof_sound  : forall P c Q,
    |- [[P]] c [[Q]] -> |= [[P]] c [[Q]].
Proof.
  intros.
  induction H; intros st' HQ.
  - (* skip *)
    exists st'; split; eauto.
  - (* assign *)
    inversion HQ; subst. destruct H as [Hassn HP].
    exists (st' & {V --> x}); split; eauto.
    assert (st' = st' & {V --> x; V --> aeval (st' & {V --> x}) a}).
    rewrite t_update_shadow. rewrite <- Hassn. rewrite t_update_same. auto.
    rewrite H at 2. auto.
  - (* seq *)
    apply IHunder_hoare_proof2 in HQ.
    destruct HQ as (st_mid & Hmid & Hevalmid).
    apply IHunder_hoare_proof1 in Hmid.
    destruct Hmid as (st & HP & HevalP).
    exists st; split; eauto.
  - (* if true *)
    apply IHunder_hoare_proof in HQ.
    destruct HQ as (st & (HP & HT) & Heval).
    exists st; split; eauto.
  - (* if false *)
    apply IHunder_hoare_proof in HQ.
    destruct HQ as (st & (HP & HF) & Heval).
    exists st; split; eauto.
  - apply H1 in HQ. apply IHunder_hoare_proof in HQ.
    destruct HQ as (st & HP & Heval).
    exists st; split; eauto.
  - (* while *)
    destruct HQ as [HQ' HF'].
    assert (exists st, while_prefix c b st st' /\ P st). eapply under_hoare_while; eauto.
    destruct H4 as (st & HW & HP).
    exists st. split; auto.
    apply while_prefix_end; auto.
Qed.
