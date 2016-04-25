(** * Formula Choice Calculus (FCC) *)

Require Import Bool.
Require Import Relations.Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Setoids.Setoid.

(* TODO: import Formula correctly *)
Load Formula.
Import Formula.

Module FCC.

(** ** Syntax *)
(** Syntax of choice calculus expressions with global dimensions and formula
    choices. The object language is binary trees. *)

(** Object language syntax. *)
Inductive obj : Type :=
  | empty : obj
  | tree  : unit -> obj -> obj -> obj.

(** Expression syntax. *)
Inductive cc : Type :=
  | empty' : cc
  | tree'  : unit -> cc -> cc -> cc
  | chc    : formula -> cc -> cc -> cc.

(* TODO: write notation for choice. *)

(** ** Semantics *)
(** The semantics of a choice calculus expression is a function from
    configuration to binary trees. *)

(** Expression semantics. *)
Fixpoint seme (e : cc) (c : config) : obj :=
  match e with
  | empty'      => empty
  | tree' x l r => tree x (seme l c) (seme r c)
  | chc f l r   => if semf f c then seme l c else seme r c
  end.

(** ** Semantic Equivalence Rules *)
(** Statement and proof of semantic equivalence rules for expressions from my
    thesis. Multiple proofs are given when it is instructive. *)

(** Semantic equivalence for expressions. *)
Definition equive : relation cc :=
  fun e e' => forall c, (seme e c) = (seme e' c).

Infix "=e=" := equive (at level 70) : type_scope.

(** Expression equivalence is reflexive. *)
Remark equive_refl : Reflexive equive.
Proof.
  intros x c.
  reflexivity.
Qed.

(** Expression equivalence is symmetric. *)
Remark equive_sym : Symmetric equive.
Proof.
  intros x y H c.
  symmetry.
  apply H.
Qed.

(** Expression equivalence is transitive. *)
Remark equive_trans : Transitive equive.
Proof.
  intros x y z H1 H2 c.
  transitivity (seme y c).
    apply H1.
    apply H2.
Qed.

(** Expression equivalence is an equivalence relation. *)
Instance eqe : Equivalence equive.
Proof.
  split.
    apply equive_refl.
    apply equive_sym.
    apply equive_trans.
Qed.

(* TODO: make choice congruence rules instances of [Proper] typeclass. *)

(** Choice transposition rule. *)
Theorem chc_trans : forall (f : formula) (l r : cc),
                    chc f l r =e= chc (~ f) r l.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f l r c.
  simpl.
  destruct (semf f c);
    reflexivity.
Qed.

(** Choice congruence rule for labels. *)
Theorem chc_cong_f : forall (f f' : formula) (l r : cc),
                     f =f= f' ->
                     chc f l r =e= chc f' l r.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f f' l r H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Choice congruence rule for left alternatives. *)
Theorem chc_cong_l : forall (f : formula) (l l' r : cc),
                     l =e= l' ->
                     chc f l r =e= chc f l' r.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f l l' r H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Choice congruence rule for right alternatives. *)
Theorem chc_cong_r : forall (f : formula) (l r r' : cc),
                     r =e= r' ->
                     chc f l r =e= chc f l r'.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f l r r' H c.
  simpl.
  rewrite -> H.
  reflexivity.
Restart.
  (* Proof by deriving from [chc_cong_l]. *)
  intros f l r r' H.
  rewrite -> chc_trans.
  rewrite -> chc_cong_l by apply H.
  rewrite <- chc_trans.
  reflexivity.
Qed.

(** Choice simplification rule for left label. *)
Theorem chc_f_l : forall (l r : cc),
                  chc (litT L) l r =e= l.
Proof.
  (* Proof by unfolding [equive]. *)
  intros l r c.
  reflexivity.
Qed.

(** Choice simplification rule for right label. *)
Theorem chc_f_r : forall (l r : cc),
                  chc (litT R) l r =e= r.
Proof.
  (* Proof by unfolding [equive]. *)
  intros l r c.
  reflexivity.
Restart.
  (* Proof by deriving from [chc_f_l]. *)
  intros l r.
  rewrite -> chc_trans.
  rewrite -> chc_cong_f by apply comp_r_l.
  apply chc_f_l.
Qed.

(** Choice label join rule. *)
Theorem chc_f_join : forall (f1 f2 : formula) (l r : cc),
                     chc f1 l (chc f2 l r) =e= chc (f1 \/ f2) l r.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f1 f2 l r c.
  simpl.
  destruct (semf f1 c);
    reflexivity.
Qed.

(** Choice label meet rule. *)
Theorem chc_f_meet : forall (f1 f2 : formula) (l r : cc),
                     chc f1 (chc f2 l r) r =e= chc (f1 /\ f2) l r.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f1 f2 l r c.
  simpl.
  destruct (semf f1 c);
    reflexivity.
Restart.
  (* Proof by deriving from [chc_f_join]. *)
  intros f1 f2 l r.
  rewrite -> chc_cong_l with (l' := chc (~ f2) r l) by apply chc_trans.
  rewrite -> chc_trans.
  rewrite -> chc_f_join.
  rewrite -> chc_cong_f with (f' := ~ (f1 /\ f2)).
  rewrite <- chc_trans.
  reflexivity.
  symmetry.
  apply comp_meet.
Qed.

(** Choice label join complement rule. *)
Theorem chc_f_join_comp : forall (f1 f2 : formula) (l r : cc),
                          chc f1 l (chc f2 r l) =e= chc (f1 \/ ~ f2) l r.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f1 f2 l r c.
  simpl.
  destruct (semf f1 c);
    simpl;
    try rewrite -> negb_if;
    reflexivity.
Restart.
  (* Proof by deriving from [chc_f_join]. *)
  intros f1 f2 l r.
  rewrite -> chc_cong_r with (r' := chc (~ f2) l r) by apply chc_trans.
  rewrite -> chc_f_join.
  reflexivity.
Qed.

(** Choice label meet complement rule. *)
Theorem chc_f_meet_comp : forall (f1 f2 : formula) (l r : cc),
                          chc f1 (chc f2 r l) r =e= chc (f1 /\ ~ f2) l r.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f1 f2 l r c.
  simpl.
  destruct (semf f1 c);
    simpl;
    try rewrite -> negb_if;
    reflexivity.
Restart.
  (* Proof by deriving from [chc_f_meet]. *)
  intros f1 f2 l r.
  rewrite -> chc_cong_l with (l' := chc (~ f2) l r) by apply chc_trans.
  rewrite -> chc_f_meet.
  reflexivity.
Qed.

(** Choice idempotence rule. *)
Theorem chc_idemp : forall (f : formula) (e : cc),
                    chc f e e =e= e.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f e c.
  simpl.
  destruct (semf f c);
    reflexivity.
Qed.

(* TODO: choice domination rule? *)

(** C-C-Merge rule. *)
Theorem cc_merge : forall (f : formula) (l r e e' : cc),
                   chc f (chc f l e) (chc f e' r) =e= chc f l r.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f l r e e' c.
  simpl.
  destruct (semf f c);
    reflexivity.
Qed.

(** C-C-Merge rule for the case where the nested choice appears in the left
    alternative. *)
Theorem cc_merge_l : forall (f : formula) (l r e : cc),
                     chc f (chc f l e) r =e= chc f l r.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f l r e c.
  simpl.
  destruct (semf f c);
    reflexivity.
Restart.
  (* Proof by deriving from [cc_merge]. *)
  intros f l r e.
  rewrite <- chc_cong_r with (r := chc f r r) by apply chc_idemp.
  rewrite -> cc_merge.
  reflexivity.
Qed.

(** C-C-Merge rule for the case where the nested choice appears in the right
    alternative. *)
Theorem cc_merge_r : forall (f : formula) (l r e : cc), 
                     chc f l (chc f e r) =e= chc f l r.
Proof.
  (* Proof by deriving from [cc_merge_l]. *)
  intros f l r e.
  rewrite -> chc_cong_r with (r' := chc (~ f) r e) by apply chc_trans.
  rewrite -> chc_trans.
  rewrite -> cc_merge_l.
  rewrite <- chc_trans.
  reflexivity.
Qed.

(** C-C-Swap rule. *)
Theorem cc_swap : forall (f1 f2 : formula) (e1 e2 e3 e4 : cc),
                  chc f1 (chc f2 e1 e2) (chc f2 e3 e4) =e=
                  chc f2 (chc f1 e1 e3) (chc f1 e2 e4).
Proof.
  (* Proof by unfolding [equive]. *)
  intros f1 f2 e1 e2 e3 e4 c.
  simpl.
  destruct (semf f1 c);
    reflexivity.
Qed.

(** C-C-Swap rule for the case where the nested choice appears in the left
    alternative of the simpler form. *)
Theorem cc_swap_l : forall (f f' : formula) (l r r' : cc),
                    chc f' (chc f l r') (chc f r r') =e=
                    chc f (chc f' l r) r'.
Proof.
  (* Proof by unfolding [equive]. *)
  intros f f' l r r' c.
  simpl.
  destruct (semf f' c);
    reflexivity.
Restart.
  (* Proof by deriving from [cc_swap]. *)
  intros f f' l r r'.
  rewrite -> cc_swap.
  rewrite -> chc_cong_r by apply chc_idemp.
  reflexivity.
Qed.

(** C-C-Swap rule for the case where the nested choice appears in the right
    alternative of the simpler form. *)
Theorem cc_swap_r : forall (f f' : formula) (l l' r : cc),
                    chc f' (chc f l l') (chc f l r) =e=
                    chc f l (chc f' l' r).
Proof.
  (* Proof by deriving from [cc_swap_l]. *)
  intros f f' l l' r.
  rewrite -> chc_cong_l with (l' := chc (~ f) l' l) by apply chc_trans.
  rewrite -> chc_cong_r with (r' := chc (~ f) r l) by apply chc_trans.
  rewrite -> cc_swap_l.
  rewrite <- chc_trans.
  reflexivity.
Qed.

(** AST-Factoring rule. *)
Theorem ast_factor : forall (f : formula) (l l' r r' : cc),
                     chc f (tree' tt l r) (tree' tt l' r') =e=
                     tree' tt (chc f l l') (chc f r r').
Proof.
  intros f l l' r r' c.
  simpl.
  destruct (semf f c);
    reflexivity.
Qed.

(** AST-L-Congruence rule. *)
Theorem ast_l_cong : forall l l' r : cc,
                     l =e= l' ->
                     tree' tt l r =e= tree' tt l' r.
Proof.
  intros l l' r H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** AST-R-Congruence rule. *)
Theorem ast_r_cong : forall l r r' : cc,
                     r =e= r' ->
                     tree' tt l r =e= tree' tt l r'.
Proof.
  intros l r r' H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** ** Examples *)
(** Examples of some additional properties of formula choice calculus. *)
Module Examples.

(** Flip operation. *)
Fixpoint flip (e : cc) : cc :=
  match e with
  | chc f l r => chc (~ f) (flip r) (flip l)
  | _         => e
  end.

(** The flip operation is an involution. *)
Example flip_invo : forall e : cc,
                    flip (flip e) =e= e.
Proof.
  induction e as [n | n l IHl r IHr | f l IHl r IHr].
  (* Case: [e = leaf' n]. *)
    reflexivity.
  (* Case: [e = node' n l r]. *)
    reflexivity.
  (* Case: [e = chc f l r]. *)
    simpl.
    rewrite -> chc_cong_f by apply comp_invo.
    rewrite -> chc_cong_l by apply IHl.
    rewrite -> chc_cong_r by apply IHr.
    reflexivity.
Qed.

End Examples.

End FCC.
