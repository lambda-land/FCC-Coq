(** * Formula *)

Require Import Bool.
Require Import Relations.Relation_Definitions.
Require Import Classes.Morphisms.
Require Import Setoids.Setoid.

Module Formula.

(** ** Syntax *)
(** Syntax of formulas is Boolean expressions in dimensions and tags. *)

(** Dimensions and tags. *)
Definition dim := nat.
Definition tag := bool.
Definition L : tag := true.
Definition R : tag := false.

(** Formula syntax. *)
Inductive formula : Type :=
  | litT : tag -> formula
  | litD : dim -> formula
  | comp : formula -> formula
  | join : formula -> formula -> formula
  | meet : formula -> formula -> formula.

(* TODO: add scope to notation. *)
Notation "~ f" := (comp f) (at level 75, right associativity).
Infix "\/" := join (at level 85, right associativity).
Infix "/\" := meet (at level 80, right associativity).

(** ** Semantics *)
(** The semantics of a formula is a function from configurations to tags. *)

(** Configurations. *)
Definition config := dim -> tag.

(** Formula semantics. *)
Fixpoint semF (f : formula) (c : config) : tag :=
  match f with
  | litT t   => t
  | litD d   => c d
  | ~ f      => negb (semF f c)
  | f1 \/ f2 => (semF f1 c) || (semF f2 c)
  | f1 /\ f2 => (semF f1 c) && (semF f2 c)
  end.

(** ** Semantic Equivalence Rules *)
(** Statement and proof of semantic equivalence rules for formulas from my
    thesis. Multiple proofs are given when it is instructive. *)

(** Semantic equivalence for formulas. *)
Definition equivF : relation formula :=
  fun f f' => forall c, (semF f c) = (semF f' c).

Infix "=f=" := equivF (at level 70) : type_scope.

(** Formula equivalence is reflexive. *)
Remark equivF_refl : Reflexive equivF.
Proof.
  intros x c.
  reflexivity.
Qed.

(** Formula equivalence is symmetric. *)
Remark equivF_sym : Symmetric equivF.
Proof.
  intros x y H c.
  symmetry.
  apply H.
Qed.

(** Formula equivalence is transitive. *)
Remark equivF_trans : Transitive equivF.
Proof.
  intros x y z H1 H2 c.
  transitivity (semF y c).
    apply H1.
    apply H2.
Qed.

(** Formula equivalence is an equivalence relation. *)
Instance eqF : Equivalence equivF.
Proof.
  split.
    apply equivF_refl.
    apply equivF_sym.
    apply equivF_trans.
Qed.

(* TODO: make formula congruence rules instance of [Proper] typeclass. *)

(** Congruence rule for complement. *)
Remark comp_cong : forall f f' : formula,
                   f =f= f' ->
                   (~ f) =f= (~ f').
Proof.
  intros f f' H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Left congruence rule for join. *)
Remark join_cong_l : forall l l' r : formula,
                     l =f= l' ->
                     (l \/ r) =f= (l' \/ r).
Proof.
  intros l l' r H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Right congruence rule for join. *)
Remark join_cong_r : forall l r r' : formula,
                     r =f= r' ->
                     (l \/ r) =f= (l \/ r').
Proof.
  intros l r r' H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Congruence rule for join. *)
Remark join_cong : forall l l' r r' : formula,
                   l =f= l' -> r =f= r' ->
                   (l \/ r) =f= (l' \/ r').
Proof.
  intros l l' r r' Hl Hr.
  rewrite -> join_cong_l by apply Hl.
  rewrite -> join_cong_r by apply Hr.
  reflexivity.
Qed.

(** Left congruence rule for meet. *)
Remark meet_cong_l : forall l l' r : formula,
                     l =f= l' ->
                     (l /\ r) =f= (l' /\ r).
Proof.
  intros l l' r H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Right congruence rule for meet. *)
Remark meet_cong_r : forall l r r' : formula,
                     r =f= r' ->
                     (l /\ r) =f= (l /\ r').
Proof.
  intros l r r' H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Congruence rule for meet. *)
Remark meet_cong : forall l l' r r' : formula,
                   l =f= l' -> r =f= r' ->
                   (l /\ r) =f= (l' /\ r').
Proof.
  intros l l' r r' Hl Hr.
  rewrite -> meet_cong_l by apply Hl.
  rewrite -> meet_cong_r by apply Hr.
  reflexivity.
Qed.

(** Join is associative. *)
Theorem join_assoc : forall x y z : formula,
                     (x \/ y \/ z) =f= ((x \/ y) \/ z).
Proof.
  intros x y z c.
  apply orb_assoc.
Qed.

(** Meet is associative. *)
Theorem meet_assoc : forall x y z : formula,
                     (x /\ y /\ z) =f= ((x /\ y) /\ z).
Proof.
  intros x y z c.
  apply andb_assoc.
Qed.

(** Join is commutative. *)
Theorem join_comm : forall x y : formula,
                     (x \/ y) =f= (y \/ x).
Proof.
  intros x y c.
  apply orb_comm.
Qed.

(** Meet is commutative. *)
Theorem meet_comm : forall x y : formula,
                    (x /\ y) =f= (y /\ x).
Proof.
  intros x y c.
  apply andb_comm.
Qed.

(** Join distributes over meet. *)
Theorem join_meet_dist_r : forall x y z : formula,
                              (x \/ y /\ z) =f= ((x \/ y) /\ (x \/ z)).
Proof.
  intros x y z c.
  apply orb_andb_distrib_r.
Qed.

(** Meet distributes over join. *)
Theorem meet_join_dist_r : forall x y z : formula,
                              (x /\ (y \/ z)) =f= (x /\ y \/ x /\ z).
Proof.
  intros x y z c.
  apply andb_orb_distrib_r.
Qed.

(** Join is idempotent. *)
Theorem join_diag : forall f : formula,
                    (f \/ f) =f= f.
Proof.
  intros f c.
  apply orb_diag.
Qed.

(** Meet is idempotent. *)
Theorem meet_diag : forall f : formula,
                    (f /\ f) =f= f.
Proof.
  intros f c.
  apply andb_diag.
Qed.

(** De Morgan's law for join. *)
Theorem comp_join : forall x y : formula,
                    (~ (x \/ y)) =f= (~ x /\ ~ y).
Proof.
  intros x y c.
  apply negb_orb.
Qed.

(** De Morgan's law for meet. *)
Theorem comp_meet : forall x y : formula,
                    (~ (x /\ y)) =f= (~ x \/ ~ y).
Proof.
  intros x y c.
  apply negb_andb.
Qed.

(** Complementation for join. *)
Theorem join_comp_r : forall f : formula,
                     (f \/ ~ f) =f= litT L.
Proof.
  intros f c.
  apply orb_negb_r.
Qed.

(** Complementation for meet. *)
Theorem meet_comp_r : forall f : formula,
                     (f /\ ~ f) =f= litT R.
Proof.
  intros f c.
  apply andb_negb_r.
Qed.

(** Right is a left identity for join. *)
Theorem join_id_l : forall f : formula,
                    (litT R \/ f) =f= f.
Proof.
  intros f c.
  apply orb_false_l.
Qed.

(** Right is a right identity for join. *)
Theorem join_id_r : forall f : formula,
                    (f \/ litT R) =f= f.
Proof.
  intros f c.
  apply orb_false_r.
Qed.

(** Left is a left identity for meet. *)
Theorem meet_id_l : forall f : formula,
                    (litT L /\ f) =f= f.
Proof.
  intros f c.
  apply andb_true_l.
Qed.

(** Left is a right identity for meet. *)
Theorem meet_id_r : forall f : formula,
                    (f /\ litT L) =f= f.
Proof.
  intros f c.
  apply andb_true_r.
Qed.

(** Left is a left annihilator for join. *)
Theorem join_ann_l : forall f : formula,
                     (litT L \/ f) =f= litT L.
Proof.
  intros f c.
  apply orb_true_l.
Qed.

(** Left is a right annihilator for join. *)
Theorem join_ann_r : forall f : formula,
                     (f \/ litT L) =f= litT L.
Proof.
  intros f c.
  apply orb_true_r.
Qed.

(** Right is a left annihilator for meet. *)
Theorem meet_ann_l : forall f : formula,
                     (litT R /\ f) =f= litT R.
Proof.
  intros f c.
  apply andb_false_l.
Qed.

(** Right is a right annihilator for meet. *)
Theorem meet_ann_r : forall f : formula,
                     (f /\ litT R) =f= litT R.
Proof.
  intros f c.
  apply andb_false_r.
Qed.

(** Complement of left is right. *)
Theorem comp_l_r : (~ litT L) =f= litT R.
Proof.
  intro c.
  reflexivity.
Qed.

(** Complement of right is left. *)
Theorem comp_r_l : (~ litT R) =f= litT L.
Proof.
  intro c.
  reflexivity.
Qed.

(** Complement is an involution. *)
Theorem comp_invo : forall f : formula,
                    (~ ~ f) =f= f.
Proof.
  intros f c.
  apply negb_involutive.
Qed.

End Formula.
