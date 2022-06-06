Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Psatz.
Import ListNotations.

From PLF Require Import Maps.

Inductive val : Type :=
| val_bool: bool -> val
| val_nat: nat -> val
| val_listnat : list nat -> val
| val_fun: string -> trm -> val
| val_fix: string -> string -> trm -> val
| val_tuple: list val -> val
with trm : Type :=
| trm_val : val -> trm
| trm_var : string -> trm
| trm_tuple: list trm -> trm
| trm_app : trm -> trm -> trm
| trm_let : string -> trm -> trm -> trm
| trm_if : trm -> trm -> trm -> trm
| trm_cons: trm -> trm -> trm
| trm_match_list: trm -> trm -> (string * string * trm) -> trm.

Coercion val_bool : bool >-> val.
Coercion val_nat : nat >-> val.

Fixpoint subst (y:string) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if String.eqb x y then t1 else t2 in
  match t with
  | trm_val v => trm_val (subst_val y w v)
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_cons t0 t1 => trm_cons (aux t0) (aux t1)
  | trm_match_list t0 t1 (p, q, t2) => trm_match_list (aux t0) (aux t1) (p, q, if_y_eq p t2 (if_y_eq q t2 (aux t2)))
  | trm_tuple ts => trm_tuple (map aux ts)
  end
with subst_val (y:string) (w:val) (t:val) : val :=
  let aux t := subst_val y w t in
  let if_y_eq x t1 t2 := if String.eqb x y then t1 else t2 in
  match t with
  | val_bool _ | val_nat _ | val_listnat _ => t
  | val_fun x t1 => val_fun x (if_y_eq x t1 (subst y w t1))
  | val_fix f x t1 => val_fix f x (if_y_eq f t1 (if_y_eq x t1 (subst y w t1)))
  | val_tuple ts => val_tuple (map aux ts)
  end.

Implicit Types b : bool.
Implicit Types v r : val.
Implicit Types t : trm.
Coercion trm_val : val >-> trm.
Coercion trm_var : string >-> trm.
Coercion trm_app : trm >-> Funclass.

Inductive eval : trm -> val -> Prop :=
| eval_val : forall v, eval (trm_val v) v
| eval_fun : forall x body, eval (trm_val (val_fun x body)) (val_fun x body)
| eval_fix : forall f x body, eval (trm_val (val_fix f x body)) (val_fix f x body)
| eval_tuple_nil : eval (trm_tuple nil) (val_tuple nil)
| eval_tuple_cons : forall t1 (t2: list trm) v1 (v2: list val),
  eval t1 v1 ->
  eval (trm_tuple t2) (val_tuple v2) ->
  eval (trm_tuple (t1::t2)) (val_tuple (v1::v2))
| eval_app_fun : forall f v2 x t1 t2 v,
      eval f (val_fun x t1) ->
      eval t2 v2 ->
      eval (subst x v2 t1) v ->
      eval (trm_app f t2) v
| eval_app_fix : forall fixf v2 f x t1 t2 v,
    eval fixf (val_fix f x t1) ->
    eval t2 v2 ->
    eval (subst x v2 (subst f (val_fix f x t1) t1)) v ->
    eval (trm_app fixf t2) v
| eval_let : forall x t1 t2 v1 r,
    eval t1 v1 ->
    eval (subst x v1 t2) r ->
    eval (trm_let x t1 t2) r
| eval_if : forall b v t1 t2,
    eval (if b then t1 else t2) v ->
    eval (trm_if (val_bool b) t1 t2) v
| eval_cons : forall t1 t2 (v1: nat) (v2: list nat),
    eval t1 (val_nat v1) ->
    eval t2 (val_listnat v2) ->
    eval (trm_cons t1 t2) (val_listnat (v1 :: v2))
| eval_match_list : forall (x1 x2: string) (l: list nat) t1 t2 v,
    eval
      (match l with
       | nil => t1
       | v1 :: v2 =>
           trm_let x1 (val_nat v1) (trm_let x2 (val_listnat v2) t2)
       end) v ->
    eval (trm_match_list (val_listnat l) t1 (x1, x2, t2)) v.

Hint Constructors eval.

Inductive tp: Type :=
| tp_nat: (nat -> Prop) -> tp
| tp_listnat: (list nat -> Prop) -> tp
| tp_arrow: tp -> tp -> tp.

Definition context := partial_map tp.

Inductive has_type_val: context -> val -> tp -> Prop :=
| t_nat: forall m n, has_type_val m (val_nat n) (tp_nat (fun x => x = n))
| t_listnat: forall m l, has_type_val m (val_listnat l) (tp_listnat (fun x => x = l))
| t_fun: forall m x body (in_tp out_tp: tp),
    has_type_trm (m & {x --> Some in_tp}) body out_tp ->
    has_type_val m (val_fun x body) (tp_arrow in_tp out_tp)
| t_fix: forall m f x body (in_tp out_tp: tp),
    has_type_trm (m & {x --> Some in_tp} & {f --> Some (tp_arrow in_tp out_tp)}) body out_tp ->
    has_type_val m (val_fix f x body) (tp_arrow in_tp out_tp)
with has_type_trm: context -> trm -> tp -> Prop :=
| t_val: forall m v tp, has_type_val m v tp -> has_type_trm m (trm_val v) tp
| t_app : forall m f arg in_tp out_tp,
    has_type_trm m arg in_tp ->
    has_type_trm m f (tp_arrow in_tp out_tp) ->
    has_type_trm m (trm_app f arg) out_tp
| t_let : forall m x t1 t2 tp1 tp,
    has_type_trm m t1 tp1 ->
    has_type_trm (m & {x --> Some tp1}) t2 tp ->
    has_type_trm m (trm_let x t1 t2) tp
| t_cons : forall m t1 t2 p1 p2,
    has_type_trm m t1 (tp_nat p1) ->
    has_type_trm m t2 (tp_listnat p2) ->
    has_type_trm m (trm_cons t1 t2)
                 (tp_listnat
                    (fun l => exists x y ,
                         l = x::y /\ p1 x /\ p2 y
                 ))
| t_match_list_nil : forall m (x1 x2: string) t0 t1 t2 tp,
    has_type_trm m t0 (tp_listnat (fun x => x = nil)) ->
    has_type_trm m t1 tp ->
    has_type_trm m (trm_match_list t0 t1 (x1, x2, t2)) tp
| t_match_list_cons : forall m (x1 x2: string) t0 t1 t2 tp p,
    has_type_trm m t0 (tp_listnat p) ->
    has_type_trm
      (m & {x1 --> Some (tp_nat (fun h => exists tt, p (h :: tt))); x2 --> Some (tp_listnat (fun tt => exists h, p (h :: tt )))}) t2 tp ->
    has_type_trm m (trm_match_list t0 t1 (x1, x2, t2)) tp.

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
Definition CONCAT : string := "CONCAT".

Definition concat_program :=
  val_fix CONCAT S1 (
            trm_match_list S1 (val_fun S2 S2)
                           (H, T,
                             trm_val (val_fun S2 (trm_cons H (CONCAT T S2)))
                           )
          ).

Lemma concat_example0 :
  eval (concat_program (val_listnat []) (val_listnat [1;3])) (val_listnat [1;3]).
Proof.
  unfold concat_program.
  eapply eval_app_fun with (x := S2); simpl; eauto.
  - eapply eval_app_fix with (x := S1); simpl; eauto.
    eapply eval_match_list; simpl; eauto.
  - simpl; eauto.
Qed.

Lemma concat_example1 :
  eval (concat_program (val_listnat [2]) (val_listnat [1;3])) (val_listnat [2;1;3]).
Proof.
  unfold concat_program.
  eapply eval_app_fun with (x := S2); simpl; eauto.
  - eapply eval_app_fix with (x := S1); simpl; eauto.
    eapply eval_match_list; simpl; eauto.
    eapply eval_let; simpl; auto.
    eapply eval_let; simpl; auto.
  - simpl.
    eapply eval_cons; simpl; eauto.
    fold concat_program.
    apply concat_example0.
Qed.

Lemma concat_empty : forall s,
    eval (concat_program (val_listnat []) (val_listnat s)) (val_listnat s).
Proof.
  unfold concat_program.
  intros s.
  eapply eval_app_fun with (x := S2); simpl; eauto.
  - eapply eval_app_fix with (x := S1); simpl; eauto.
    eapply eval_match_list; simpl; eauto.
  - simpl; eauto.
Qed.

Definition hd (l : list nat) (x: nat) :=
  match l with
  | nil => false
  | cons h t => Nat.eqb h x
  end.

Fixpoint mem (l : list nat) (x: nat) :=
  match l with
  | nil => false
  | cons h t => (if Nat.eqb h x then true else mem t x)
  end.

Fixpoint order (l : list nat) (u v: nat) :=
  match l with
  | nil => false
  | cons h t =>
      if Nat.eqb u h then mem t v else order t u v
  end.

Lemma mem_then_exists_first (l: list nat) (u: nat) :
  mem l u = true -> exists s1 s2, s1 ++ (u :: s2) = l /\ ~ (mem s1 u = true).
Admitted.

Lemma mem_concat (l1 l2: list nat) (u: nat) :
  (mem l1 u = true \/ mem l2 u = true) -> mem (l1 ++ l2) u = true.
Proof.
  intros H.
  destruct H.
  + induction l1.
    - intros. inversion H0.
    - intros. simpl. simpl in H0. destruct (Nat.eqb a u).
      auto. auto.
  + induction l1.
    - auto.
    - simpl. destruct (Nat.eqb a u); auto.
Qed.

Lemma l1 (nu: list nat) :
  (exists (u v: nat), hd nu u = true /\ mem nu v = true /\ v > u /\ (forall w, mem nu w = true -> (u >= w \/ v = w))) ->
  exists s1 s2,
    (forall (u v: nat), (hd s1 u = true /\ mem s1 v = true) -> u >= v) /\
      (forall (u v: nat), (hd s2 u = true /\ mem s2 v = true) -> u >= v) /\ s1 ++ s2 = nu.
Proof.
  intro H.
  destruct H as (u & v & H0 & H1 & H2 & H).
  apply mem_then_exists_first in H1. destruct H1 as (s1 & s2 & Hconcat & HNmem).
  exists s1, (v :: s2).
  repeat split; auto.
  + intros u' v' (H1' & H2').
    assert (u' = u). { destruct s1. inversion H1'. inversion H1'. subst. inversion H0. apply Nat.eqb_eq in H3. apply Nat.eqb_eq in H4. subst. auto. } subst.
    assert (mem (s1 ++ v :: s2) v' = true). apply mem_concat; auto.
    apply H in H1. destruct H1; subst; auto. exfalso. auto.
  + intros u' v' (H1' & H2').
    assert (u' = v). { subst. inversion H1'.  apply Nat.eqb_eq in H3. auto. } subst.
    assert (mem (s1 ++ v :: s2) v' = true). apply mem_concat; auto.
    apply H in H1. destruct H1; subst; auto. lia.
Qed.


Definition under_pre0 (s1 s2: list nat): Prop :=
  forall u, order s1 u u = false /\ order s2 u u = false /\ ~ (exists (v: nat), mem s1 v = true /\ mem s2 v = true).

Definition under_post0 (nu: list nat): Prop := forall u, order nu u u = false.

Lemma concat_under0 : forall nu,
    under_post0 nu ->
    exists s1 s2,
      under_pre0 s1 s2 /\
        eval (concat_program (val_listnat s1) (val_listnat s2)) (val_listnat nu).
Proof.
  unfold concat_program.
  intros nu HQ.
  exists nil, nu.
  split.
  + intros u. repeat (split; auto). intros H. inversion H. destruct H0. inversion H0.
  + eapply eval_app_fun with (x := S2); simpl; eauto.
    - eapply eval_app_fix with (x := S1); simpl; eauto.
      eapply eval_match_list; simpl; eauto.
    - simpl; auto.
Qed.

Definition under_pre1 (s1 s2: list nat): Prop :=
  forall u, order s1 u u = false /\ order s2 u u = false /\ (exists (v: nat), mem s1 v = true /\ mem s2 v = true).

Definition splitable (nu: list nat): Prop :=
  exists s1 s2, nu = s1 ++ s2 /\ (forall u, order s1 u u = false) /\ (forall u, order s2 u u = false).

Definition under_post1_precise (nu: list nat) : Prop := (exists u, order nu u u = true) /\ splitable nu.

Definition under_post1_appr (nu: list nat): Prop :=
  (exists u, order nu u u = true) /\
    (exists w, forall (u v: nat),
        (order nu u w = true /\ order nu v w = true /\ order nu u v = true -> ~ u = v) /\
          (order nu w u = true /\ order nu w v = true /\ order nu u v = true -> ~ u = v) /\
          (order nu w w = false)
    ).

Lemma unde_post1_appr_valid: forall nu, under_post1_appr nu -> under_post1_precise nu.
Proof.
Admitted.

Lemma duplist_after_split_shared_same_elem: forall nu s1 s2,
    (exists u, order nu u u = true) ->
    (forall u, order s1 u u = false) ->
    (forall u, order s2 u u = false) ->
    nu = s1 ++ s2 ->
    (exists u, mem s1 u = true /\ mem s2 u = true).
Proof. Admitted.

Lemma concat_under1 : forall nu,
    under_post1_precise nu ->
    exists s1 s2,
      under_pre1 s1 s2 /\
        eval (concat_program (val_listnat s1) (val_listnat s2)) (val_listnat nu).
Proof.
  unfold concat_program.
  intros nu HQ.
  destruct HQ as (HQ & (s1 & s2 & Hconcat & Hs1 & Hs2)).
  { exists s1, s2.
    assert (under_pre1 s1 s2).
    { intros u. repeat (split; auto). eapply duplist_after_split_shared_same_elem; auto. destruct HQ as (v & HQ). exists v. rewrite Hconcat in HQ. auto. }
    split; subst; auto.
    induction s1.
    + unfold under_pre1 in H0. destruct (H0 0) as (_ & _ & (v & H & _ )). inversion H.
    + eapply eval_app_fun with (x := S2)
                               (t1 := (trm_cons a
                                                (val_fix CONCAT S1 (trm_match_list S1 (val_fun S2 S2)
                                                                                   (H, T, trm_val (val_fun S2 (trm_cons H (CONCAT T S2)))))
                                                       (val_listnat s1) S2))); simpl; eauto.
  - eapply eval_app_fix with (x := S1); simpl; eauto.
    eapply eval_match_list; simpl; eauto.
      eapply eval_let; simpl; auto.
      eapply eval_let; simpl; auto.
  - eapply eval_cons. simpl; eauto.
    assert ((exists dup, order (s1 ++ s2) dup dup = true) \/ (forall dup, order (s1 ++ s2) dup dup = false)). admit.
    assert ((mem (s1 ++ s2) a) = true \/ (mem (s1 ++ s2) a) = false). admit.
    destruct H1, H2.
    { apply IHs1; auto. admit. admit. }
    { admit. }
    { apply concat_under0 in H2.

    { assert ((exists dup, order (s1 ++ s2) dup dup = true) \/ (forall dup, order (s1 ++ s2) dup dup = false)). admit.
      destruct H1.
      + apply IHs1; auto. admit. admit.
      + apply concat_under0 in H1.
    assert ((exists dup, order (s1 ++ s2) dup dup = true) \/ (forall dup, order (s1 ++ s2) dup dup = false)). admit.
    destruct H1.
    { apply IHs1; auto. admit. admit. }
    { assert (under_post0 (s1++s2)). auto.
      apply concat_under0 in H2.

          destruct (mem (s1 ++ s2) a).
    apply IHs1; auto. admit. admit.
    destruct (mem (s1 ++ s2) a).


    fold concat_program.
    apply concat_example0.
      { inversion Hs1.
      induction s1.
    - simpl; auto.



  induction s1.
  { simpl in Hconcat. subst. destruct HQ as (x & HQ). rewrite (Hs2 x) in HQ. inversion HQ. }
  { destruct nu. inversion Hconcat.
    inversion Hconcat; subst.
    exists s1, s2.
    assert (under_pre1 s1 s2).
    { intros u. repeat (split; auto). admit. eapply duplist_after_split_shared_same_elem; auto. destruct HQ as (v & HQ). exists v. rewrite Hconcat in HQ. auto. admit. admit. }
    split; subst; auto.
    destruct s1.
    + unfold under_pre1 in H0. destruct (H0 0) as (_ & _ & (v & H & _ )). inversion H.
    + eapply eval_app_fun with (x := S2)
                               (t1 := (trm_cons a
                                                (val_fix CONCAT S1 (trm_match_list S1 (val_fun S2 S2)
                                                                                   (H, T, trm_val (val_fun S2 (trm_cons H (CONCAT T S2)))))
                                                         (val_listnat s1) S2))); simpl; eauto.
    - eapply eval_app_fix with (x := S1); simpl; eauto.
      eapply eval_match_list; simpl; eauto.
      eapply eval_let; simpl; auto.
      eapply eval_let; simpl; auto.
    - simpl. inversion Hconcat; subst.
      eapply eval_cons. simpl; eauto.


  }


  induction nu.
  destruct nu. inversion HQ. inversion H0.
  assert ((exists dup, order nu dup dup = true) \/ (forall dup, order nu dup dup = false)). admit.
  { exists s1, s2.
    assert (under_pre1 s1 s2).
    { intros u. repeat (split; auto). eapply duplist_after_split_shared_same_elem; auto. destruct HQ as (v & HQ). exists v. rewrite Hconcat in HQ. auto. }
    split; subst; auto.
    induction s1.
  + unfold under_pre1 in H1. destruct (H1 0) as (_ & _ & (v & H & _ )). inversion H.
  + eapply eval_app_fun with (x := S2)
                             (t1 := (trm_cons a
                                              (val_fix CONCAT S1 (trm_match_list S1 (val_fun S2 S2)
                                                                                 (H, T, trm_val (val_fun S2 (trm_cons H (CONCAT T S2)))))
                                                       (val_listnat s1) S2))); simpl; eauto.
  - eapply eval_app_fix with (x := S1); simpl; eauto.
    eapply eval_match_list; simpl; eauto.
      eapply eval_let; simpl; auto.
      eapply eval_let; simpl; auto.
  - simpl. inversion Hconcat; subst.
    eapply eval_cons. simpl; eauto.
    apply IHs1; auto.
    assert ((exists dup, order (s1 ++ s2) dup dup = true) \/ (forall dup, order (s1 ++ s2) dup dup = false)). admit.
    destruct H1.
    { apply IHs1; auto. admit. admit. }
    { assert (under_post0 (s1++s2)). auto.
      apply concat_under0 in H2.


    fold concat_program.
    apply concat_example0.
      { inversion Hs1.
      induction s1.
    - simpl; auto.
Qed.


Definition type_safe (c: trm) (tp: val -> Prop) := forall v, tp v -> eval c v.

Inductive under_type: Type :=
| ut_spec: forall (P: Prop) (Q: Prop) 

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
