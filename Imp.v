Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

From PLF Require Import Maps.


Inductive nexp : Type :=
| Num: nat -> nexp
| Hd: lexp -> nexp
| Nid: string -> nexp
with lexp : Type :=
| NumList : list nat -> lexp
| Nil: lexp
| Cons: nexp -> lexp -> lexp
| Tail: lexp -> lexp
| Lid: string -> lexp.
Inductive bexp : Type :=
| BTrue
| BFalse
| Bemp (a: lexp)
| BEq (a1 a2 : nexp)
| BLt (a1 a2 : nexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).

Definition state : Type := partial_map (list nat) * (partial_map nat).

Definition update_n (st: state) X v := (fst st, t_update (snd st) X v).
Definition update_l (st: state) X v := (t_update (fst st) X v, snd st).
Definition remove_n (st: state) X := (fst st, remove (snd st) X).
Definition remove_l (st: state) X := (remove (fst st) X, snd st).

Lemma update_after_remove_n (st: state) x :
  update_n (remove_n st x) x ((snd st) x) = st.
Admitted.

Lemma update_after_remove_l (st: state) x :
  update_l (remove_l st x) x ((fst st) x) = st.
Admitted.

Fixpoint neval (st : state) (n : nexp) : option nat :=
  match n with
  | Num n => Some n
  | Hd l =>
      match leval st l with
      | Some (h :: _) => Some h
      | _ => None
      end
  | Nid x => (snd st) x
  end
with leval (st : state) (l : lexp) : option (list nat) :=
       match l with
       | NumList l => Some l
       | Nil => Some []
       | Cons h t =>
           match neval st h, leval st t with
           | Some h, Some t => Some (h :: t)
           | _, _ => None
           end
       | Tail l =>
           match leval st l with
           | Some (_ :: t) => Some t
           | _ => None
           end
       | Lid x => (fst st) x
       end.

Fixpoint beval (st : state) (b : bexp) : option bool :=
  match b with
  | BTrue       => Some true
  | BFalse      => Some false
  | Bemp a =>
      match leval st a with
      | Some ([]) => Some true
      | Some (_) => Some false
      | _ => None
      end
  | BEq a1 a2   =>
      match (neval st a1), (neval st a2) with
      | Some a1, Some a2 => Some (beq_nat a1 a2)
      | _, _ => None
      end
  | BLt a1 a2   =>
      match (neval st a1), (neval st a2) with
      | Some a1, Some a2 => Some (Nat.ltb a1 a2)
      | _, _ => None
      end
  | BNot b1     =>
      match beval st b1 with
      | Some b1 => Some (negb b1)
      | None => None
      end
  | BAnd b1 b2  =>
      match beval st b1 , beval st b2 with
      | Some b1, Some b2 => Some (andb b1 b2)
      | _, _ => None
      end
  end.

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition S1 : string := "S1".
Definition S2 : string := "S2".
Definition S3 : string := "S3".
Definition H : string := "H".
Definition T : string := "T".
Definition NU : string := "NU".

(** ** Notations *)

Coercion Nid : string >-> nexp.
Coercion Lid : string >-> lexp.
Coercion Num : nat >-> nexp.
Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope lexp_scope with lexp.
Infix ":::" := Cons (at level 50, left associativity) : lexp_scope.
Bind Scope bexp_scope with bexp.
Infix "<" := BLt : bexp_scope.
Infix "=" := BEq : bexp_scope.
Infix "&&" := BAnd : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.

Notation "{ a --> x }" :=
  (update empty a x) (at level 0).
Notation "{ a --> x ; b --> y }" :=
  (update ({ a --> x }) b y) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z }" :=
  (update ({ a --> x ; b --> y }) c z) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t }" :=
  (update ({ a --> x ; b --> y ; c --> z }) d t) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
  (update ({ a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
  (update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 0).

Inductive under_spec (pre: list nat -> list nat -> list nat -> Prop) (post: list nat -> Prop) : Prop :=
  | U_spec : (forall nu, post nu -> exists s1 s2, pre s1 s2 nu) -> under_spec pre post.

Inductive com : Type :=
| CSkip : com
| CAssN : string -> nexp -> com
| CAssL : string -> lexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CAssApply: string -> com -> string -> string -> com
| CSpec : ((list nat) -> (list nat) -> (list nat) -> Type) -> ((list nat) -> Type) -> com
| CSelf : com
| CFix : com -> com.

Bind Scope com_scope with com.
Notation "'SKIP'" :=
  CSkip : com_scope.
Notation "'SELF'" :=
  CSelf : com_scope.
Notation "x 'N=' a" :=
  (CAssN x a) (at level 60) : com_scope.
Notation "x 'L=' a" :=
  (CAssL x a) (at level 60) : com_scope.
Notation "c1 '<>=' f '<' c2  c3 '>' " :=
  (CAssApply c1 f c2 c3) (at level 80, right associativity) : com_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "'Fix' b '=>=' c " :=
  (CFix b c) (at level 80, right associativity) : com_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.

Reserved Notation "c1 '/' st '\\' st'"
         (at level 40, st at level 39).

Definition frame_within_vars (st st': state) vars : Prop := same_within (fst st) (fst st') vars.
Definition frame_beside_vars (st st': state) vars : Prop := same_besides (fst st) (fst st') vars.

Definition has_value_n (st: state) x v := snd st x = v.

Definition has_value_l (st: state)  x v := fst st x = v.

Fixpoint subst_self (self body: com) :=
  match body with
  | CSkip | CAssN _ _ | CAssL _ _ | CSpec _ _ => body
  | CSeq e1 e2 => CSeq (subst_self self e1) (subst_self self e2)
  | CIf b e1 e2 => CIf b (subst_self self e1) (subst_self self e2)
  | CAssApply ret e arg1 arg2 => CAssApply ret (subst_self self e) arg1 arg2
  | CSelf => self
  | CFix body => CFix (subst_self self body)
  end.

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st, SKIP / st \\ st
| E_Spec : forall pre post s1 s2 nu,
    under_spec pre post ->
    post nu ->
    pre s1 s2 nu ->
    (CSpec pre post) / ({S1 --> s1 ; S2 --> s2}, empty) \\ ({S1 --> s1 ; S2 --> s2 ; NU --> nu}, empty)
| E_AssN  : forall st a1 n x,
    neval st a1 = n ->
    (x N= a1) / st \\ (update_n st x n)
| E_AssL  : forall st a1 n x,
    leval st a1 = n ->
    (x L= a1) / st \\ (update_l st x n)
| E_AssApply :
  forall ret arg1 arg2 s1 s2 nu c cst cst' st,
    c / cst \\ cst' ->
    fst cst S1 = Some s1 ->
    fst cst S2 = Some s2 ->
    fst cst' NU = Some nu ->
    fst st arg1 = Some s1 ->
    fst st arg2 = Some s2 ->
    fst st ret = None ->
    (CAssApply ret c arg1 arg2) / st \\ (update_l st ret (Some nu))
| E_Seq : forall c1 c2 st st' st'',
    c1 / st  \\ st' ->
    c2 / st' \\ st'' ->
    (c1 ;; c2) / st \\ st''
| E_IfTrue : forall st st' b c1 c2,
    beval st b = Some true ->
    c1 / st \\ st' ->
    (IFB b THEN c1 ELSE c2 FI) / st \\ st'
| E_IfFalse : forall st st' b c1 c2,
    beval st b = Some false ->
    c2 / st \\ st' ->
    (IFB b THEN c1 ELSE c2 FI) / st \\ st'
| E_Fix : forall c st st',
    subst_self (CFix c) c / st \\ st' ->
    (CFix c) / st \\ st'

where " c1 '/' st '\\' st'" := (ceval c1 st st').

Definition has_under_spec (pre: list nat -> list nat -> list nat -> Prop) (post: list nat -> Prop) (c: com) :=
  forall nu, post nu ->
        (exists s1 s2 st',
            pre s1 s2 nu /\
              c / ({S1 --> s1 ; S2 --> s2}, empty) \\
                (update_l (update_l (update_l st' S1 (Some s1)) S2 (Some s2)) NU (Some nu))
        ).

Lemma update_l_dup (st: state) (x: string) v:
  fst st x = v -> update_l st x v = st.
Proof. Admitted.

Lemma spec_has_spec (pre: list nat -> list nat -> list nat -> Prop) (post: list nat -> Prop) :
  under_spec pre post ->
  has_under_spec pre post (CSpec pre post).
Proof.
  unfold has_under_spec.
  intros HSpec nu HPost.
  inversion HSpec.
  assert (post nu) as HSpec'; auto.
  apply H0 in HPost.
  destruct HPost as (s1 & s2 & HPre).
  exists s1, s2, ({S1 --> s1 ; S2 --> s2}, empty).
  split; auto.
  assert (update_l (update_l ({S1 --> s1; S2 --> s2}, empty) S1 (Some s1)) S2 (Some s2) =
         ({S1 --> s1 ; S2 --> s2}, empty)).
  repeat (rewrite update_l_dup; auto).
  rewrite H1.
  assert (update_l ({S1 --> s1; S2 --> s2}, empty) NU (Some nu) = ({S1 --> s1; S2 --> s2; NU --> nu}, empty)).
  unfold update_l. simpl. auto.
  apply E_Spec; auto.
Qed.

Definition concat_program :=
  (CFix (IFB Bemp S1
             THEN (NU L= Lid S2)
             ELSE (H N= (Hd (Lid S1));; T L= (Tail (Lid S1));; (CAssApply S3 SELF T S2);; (NU L= Cons (Nid H) (Lid S3)))
         FI)).

Lemma concat_example0 :
  concat_program / ({S1 --> [] ; S2 --> [1;3]}, empty) \\
                 ({S1 --> [] ; S2 --> [1;3]; NU --> [1;3]}, empty).
Proof.
  unfold concat_program.
  intros.
  apply E_Fix. simpl.
  apply E_IfTrue; auto.
  apply E_AssL. simpl. auto.
Qed.

Lemma concat_example1 :
  concat_program / ({S1 --> [2] ; S2 --> [1;3]}, empty) \\
                 ({S1 --> [2] ; S2 --> [1;3]; T --> []; S3 --> [1;3] ; NU --> [2;1;3]}, {H --> 2}).
Proof.
  unfold concat_program.
  intros.
  apply E_Fix. simpl.
  apply E_IfFalse; auto.
  eapply E_Seq. apply E_AssN. simpl. auto.
  eapply E_Seq. apply E_AssL. simpl. auto.
  fold concat_program.
  eapply E_Seq; auto.
  - eapply E_AssApply with (s1 := []) (s2 := [1;3]) (nu := [1;3]); eauto. apply concat_example0.
    auto.
    auto.
    auto.
  - apply E_AssL. simpl. auto.
Qed.

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

Fixpoint splitable_aux (l r : list nat) :=
  match r with
  | nil => false
  | cons h t =>
      if mem l h then false
      else
        if dup t then splitable_aux (h::l) t
        else true
  end.

Definition splitable (l: list nat) := splitable_aux nil l.

Lemma splitable_can_be_split (l: list nat) :
  splitable l = true <-> exists l1 l2, l1 ++ l2 = l /\ dup l1 = false /\ dup l2 = false.
Proof. Admitted.

Fixpoint dup3 (l : list nat) :=
  match l with
  | nil => false
  | cons h t =>
      if twice t h then true else dup3 t
  end.

Definition concat_post1 := fun (nu: list nat) => dup nu = false.
Definition concat_pre1 := fun (s1 s2 nu: list nat) =>
                             (dup s1 = false) /\ (dup s2 = false) /\
                               (forall x, ~ (mem s1 x = true /\ mem s2 x = true)).

Definition concat_spec1 : under_spec concat_pre1 concat_post1.
Proof.
  unfold concat_pre1, concat_post1.
  apply U_spec.
  intros nu HPost.
  exists nil, nu. repeat (split; auto).
  intros x. intro H. destruct H as [H _]. inversion H.
Qed.

Lemma concat_program_s1_empty: forall s2,
    concat_program / ({S1 --> nil; S2 --> s2}, empty) \\ ({S1 --> nil; S2 --> s2; NU --> s2}, empty).
Proof.
  intros nu.
  unfold concat_program.
  intros.
  apply E_Fix. simpl.
  apply E_IfTrue; auto.
  apply E_AssL. simpl. auto.
Qed.


Lemma concat_program_has_concat_spec1 :
  has_under_spec concat_pre1 concat_post1 concat_program.
Proof.
  unfold has_under_spec, concat_pre1, concat_post1.
  intros nu HPost.
  exists nil, nu, ({S1 --> nil ; S2 --> nu; NU --> nu}, empty). repeat (split; auto).
  intros x. intro H. destruct H as [H _]. inversion H.
  repeat (rewrite update_l_dup; auto).
  apply concat_program_s1_empty.
Qed.

Definition concat_post2 := fun (nu: list nat) => (dup nu = true) /\ (splitable nu = true).
Definition concat_pre2 := fun (s1 s2 nu: list nat) =>
                             (dup s1 = false) /\ (dup s2 = false) /\
                               (exists x, mem s1 x = true /\ mem s2 x = true).

Lemma list_destruct (l : list nat) : l = nil \/ exists h t, l = h :: t.
Proof. Admitted.

Lemma concat_program_has_concat_spec2 :
  has_under_spec concat_pre2 concat_post2 concat_program.
Proof.
  unfold has_under_spec, concat_pre2, concat_post2.
  intros nu HPost.
  destruct (list_destruct nu); subst.
  + destruct HPost as (Hdup & _). inversion Hdup.
  + destruct H0 as (h & s3 & H); subst.
    destruct HPost as (Hdup & Hsplit).
    rewrite splitable_can_be_split in Hsplit.
    destruct Hsplit as (s1 & s2 & HK & Hs1 & Hs2).
    assert (exists t, s1 = h :: t /\ t ++ s2 = s3). admit.
    destruct H0 as (t & H0 & H1). subst.
    exists (h :: t), s2, ({S1 --> (h :: t) ; S2 --> s2; T --> t; S3 --> (t ++ s2); NU --> (h :: (t ++ s2))}, { H --> h }).
    repeat (split; auto).
    - admit.
    - repeat (rewrite update_l_dup; auto).
      generalize dependent h.
      generalize dependent t.
      induction t.
      {
        intros h.
        unfold concat_program.
        intros.
        apply E_Fix. simpl.
        apply E_IfFalse; auto.
        eapply E_Seq. apply E_AssN. simpl. auto.
        eapply E_Seq. apply E_AssL. simpl. auto.
        eapply E_Seq; auto.
        apply E_AssApply with (s1 := nil) (s2 := s2) (nu := s2)
                              (cst := ({S1 --> nil; S2 --> s2}, empty)) (cst' := ({S1 --> nil; S2 --> s2; NU --> s2}, empty)); auto.
        apply concat_program_s1_empty.
        apply E_AssL. simpl. auto.
        }
      {
        intros h.
        unfold concat_program.
        intros.
        apply E_Fix. simpl.
        apply E_IfFalse; auto.
        eapply E_Seq. apply E_AssN. simpl. auto.
        eapply E_Seq. apply E_AssL. simpl. auto.
        eapply E_Seq; auto.
        apply E_AssApply with (s1 := (a :: t)) (s2 := s2) (nu := (a :: t) ++ s2)
                              (cst := ({S1 --> (a :: t); S2 --> s2}, empty))
                              (cst' := ({S1 --> (a :: t); S2 --> s2; T --> t; S3 --> (t ++ s2); NU --> (a :: t) ++ s2}, {H --> a})); auto.
        apply (IHt a); auto.
        - admit.
        - admit.
        - apply E_AssL. simpl. auto.
      }
Admitted.
