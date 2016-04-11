(** * Formula Choice Calculus (FCC) *)

(* TODO: edit imports *)
Require Import Bool.
Require Import Relations.Relation_Definitions.
(* Require Import Classes.RelationClasses. *)
Require Import Classes.Morphisms.
(* Require Import Classes.Equivalence. *)
Require Import Setoids.Setoid.

Module FCC.

Definition admit {T: Type} : T.
Admitted.

(** ** Syntax *)

(** Syntax of binary formula choice calculus expressions with global dimensions.
    The object language is binary trees. *)

(** Dimensions and configurations. *)
Definition dim := nat.
Definition tag := bool.
Definition L : tag := true.
Definition R : tag := false.
Definition config := dim -> tag.

(** Formula syntax. *)
Inductive formula : Type :=
  | top  : formula
  | bot  : formula
  | ref  : dim -> formula
  | neg  : formula -> formula
  | join : formula -> formula -> formula
  | meet : formula -> formula -> formula.

Infix "|||" := join.
Infix "&&&" := meet.

(* Object language syntax. *)
Inductive tree : Type :=
  | t_leaf : nat -> tree
  | t_node : nat -> tree -> tree -> tree.

(** Formula choice calculus syntax. *)
Inductive fcc : Type :=
  (* TODO: replace one with node and leaf *)
  | one : nat -> fcc
  | chc : formula -> fcc -> fcc -> fcc.

(** ** Semantics *)

(** The semantics of a formula choice calculus expression is a function from
    selections/configuration to plain binary trees. A selection is a (total)
    function from a dimension name to the tag to select. *)

(** Formula semantics. *)
Fixpoint eval (f : formula) (c : config) : tag :=
  match f with
  | top       => L
  | bot       => R
  | ref d     => c d
  | neg f     => negb (eval f c)
  | f1 ||| f2 => (eval f1 c) || (eval f2 c)
  | f1 &&& f2 => (eval f1 c) && (eval f2 c)
  end.

(** Formula choice calculus semantics. *)
Fixpoint sem (e : fcc) (c : config) : nat :=
  match e with
  | one n     => n
  | chc f l r => if eval f c then sem l c else sem r c
  end.

(** ** Equivalence *)

(** Statement and proof of semantic equivalence rules from the TOSEM paper (for
    formula choice calculus), the GPCE paper, and some additional rules. *)

(** Formula equivalence. *)
Definition f_equiv : relation formula :=
  fun f f' => forall c, (eval f c) = (eval f' c).

Infix "=f=" := f_equiv (at level 70) : type_scope.

(** Formula equivalence is reflexive. *)
Remark f_equiv_refl : Reflexive f_equiv.
Proof.
  intros x c.
  reflexivity.
Qed.

(** Formula equivalence is symmetric. *)
Remark f_equiv_sym : Symmetric f_equiv.
Proof.
  intros x y H c.
  symmetry.
  apply H.
Qed.

(** Formula equivalence is transitive. *)
Remark f_equiv_trans : Transitive f_equiv.
Proof.
  intros x y z H1 H2 c.
  transitivity (eval y c).
    apply H1.
    apply H2.
Qed.

(** Formula equivalence is an equivalence relation. *)
Instance f_eq : Equivalence f_equiv.
Proof.
  split;
    [apply f_equiv_refl | apply f_equiv_sym | apply f_equiv_trans].
Qed.

(** Formula choice calculus equivalence. *)
Definition fcc_equiv : relation fcc :=
  fun e e' => forall c, (sem e c) = (sem e' c).

Infix "=fcc=" := fcc_equiv (at level 70) : type_scope.

(** Formula choice calculus equivalence is reflexive. *)
Remark fcc_equiv_refl : Reflexive fcc_equiv.
Proof.
  intros x c.
  reflexivity.
Qed.

(** Formula choice calculus equivalence is symmetric. *)
Remark fcc_equiv_sym : Symmetric fcc_equiv.
Proof.
  intros x y H c.
  symmetry.
  apply H.
Qed.

(** Formula choice calculus equivalence is transitive. *)
Remark fcc_equiv_trans : Transitive fcc_equiv.
Proof.
  intros x y z H1 H2 c.
  transitivity (sem y c).
    apply H1.
    apply H2.
Qed.

(** Formula choice calculus equivalence is an equivalence relation. *)
Instance fcc_eq : Equivalence fcc_equiv.
Proof.
  split;
    [apply fcc_equiv_refl | apply fcc_equiv_sym | apply fcc_equiv_trans].
Qed.

(* TODO: make choice congruence rules instances of Proper typeclass. *)

(** Choice-Transposition rule. *)
Theorem chc_trans : forall (f : formula) (l r : fcc),
                    chc f l r =fcc= chc (neg f) r l.
Proof.
  intros f l r c.
  destruct (eval f c) eqn:H;
    simpl;
    rewrite -> H;
    reflexivity.
Qed.

(** Choice-F-Congruence rule for formulas. *)
Theorem chc_f_cong : forall (f f' : formula) (l r : fcc),
                 f =f= f' ->
                 chc f l r =fcc= chc f' l r.
Proof.
  intros f f' l r H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Choice-L-Congruence rule for left alternatives. *)
Theorem chc_l_cong : forall (f : formula) (l l' r : fcc),
                     l =fcc= l' ->
                     chc f l r =fcc= chc f l' r.
Proof.
  intros f l l' r H c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Choice-R-Congruence rule for right alternatives. *)
Theorem chc_r_cong : forall (f : formula) (l r r' : fcc),
                     r =fcc= r' ->
                     chc f l r =fcc= chc f l r'.
Proof.
  (*
  intros f l r r' H c.
  simpl.
  rewrite -> H.
  reflexivity.
  *)
  intros f l r r' H.
  rewrite -> chc_trans.
  rewrite -> chc_l_cong by apply H.
  rewrite <- chc_trans.
  reflexivity.
Qed.

(* Formula-Top rule. *)
Theorem f_top : forall (l r : fcc),
                chc top l r =fcc= l.
Proof.
  intros l r c.
  reflexivity.
Qed.

(* Formula-Bottom rule. *)
Theorem f_bot : forall (l r : fcc),
                chc bot l r =fcc= r.
Proof.
  (*
  intros l r c.
  reflexivity.
  *)
  intros l r.
  rewrite -> chc_trans.
  rewrite -> chc_f_cong with (f' := top);
    [apply f_top | intro c; reflexivity].
Qed.

(** Formula-Join rule. *)
Theorem f_join : forall (f1 f2 : formula) (l r : fcc),
                 chc f1 l (chc f2 l r) =fcc= chc (f1 ||| f2) l r.
Proof.
  intros f1 f2 l r c.
  simpl.
  destruct (eval f1 c);
    reflexivity.
Qed.

(** Formula-Meet rule. *)
Theorem f_meet : forall (f1 f2 : formula) (l r : fcc),
                 chc f1 (chc f2 l r) r =fcc= chc (f1 &&& f2) l r.
Proof.
  intros f1 f2 l r c.
  simpl.
  destruct (eval f1 c);
    reflexivity.
  (* TODO: rewrite proof *)
Qed.

(** Formula-Join-Not rule. *)
Theorem f_join_not : forall (f1 f2 : formula) (l r : fcc),
                     chc f1 l (chc f2 r l) =fcc= chc (f1 ||| (neg f2)) l r.
Proof.
  intros f1 f2 l r.
Admitted. (* TODO: write proof *)

(** Formula-Meet-Not rewrite rule. *)
Theorem f_meet_not : forall (f1 f2 : formula) (l r : fcc),
                     chc f1 (chc f2 r l) l =fcc= chc (f1 &&& (neg f2)) r l.
Proof.
Admitted. (* TODO: write proof *)

(** Choice Idempotence rule. *)
Theorem chc_idemp : forall (f : formula) (e : fcc),
                    chc f e e =fcc= e.
Proof.
  intros f e c.
  simpl.
  destruct (eval f c);
    reflexivity.
Qed.

(* TODO: C-C-Merge rule *)

(** C-C-Merge rule for the case where the nested choice appears in the left
    alternative. *)
Theorem cc_merge_l : forall (f : formula) (l r e : fcc),
                     chc f (chc f l e) r =fcc= chc f l r.
Proof.
  intros f l r e c.
  simpl.
  destruct (eval f c);
    reflexivity.
Qed.

(** C-C-Merge rule for the case where the nested choice appears in the right
    alternative. *)
Theorem cc_merge_r : forall (f : formula) (l r e : fcc), 
                     chc f l (chc f e r) =fcc= chc f l r.
Proof.
  intros f l r e c.
  simpl.
  destruct (eval f c);
    reflexivity.
  (* TODO: rewrite using cc_merge_l *)
Qed.

(** C-C-Swap rule. *)
Theorem cc_swap : forall (f1 f2 : formula) (e1 e2 e3 e4 : fcc),
                  chc f1 (chc f2 e1 e2) (chc f2 e3 e4) =fcc=
                  chc f2 (chc f1 e1 e3) (chc f1 e2 e4).
Proof.
  intros f1 f2 e1 e2 e3 e4 c.
  simpl.
  destruct (eval f1 c);
    reflexivity.
Qed.

(** C-C-Swap rule for the case where the nested choice appears in the left
    alternative of the simpler form. *)
Theorem cc_swap_l : forall (f1 f2 : formula) (e1 e2 e3 : fcc),
                    chc f1 (chc f2 e1 e3) (chc f2 e2 e3) =fcc=
                    chc f2 (chc f1 e1 e2) e3.
Proof.
  intros f1 f2 e1 e2 e3.
  rewrite -> cc_swap.
  rewrite -> chc_r_cong by apply chc_idemp.
  reflexivity.
Qed.

(** C-C-Swap rule for the case where the nested choice appears in the right
    alternative of the simpler form. *)
Theorem cc_swap_r : forall (f1 f2 : formula) (e1 e2 e3 : fcc),
                    chc f1 (chc f2 e1 e2) (chc f2 e1 e3) =fcc=
                    chc f2 e1 (chc f1 e2 e3).
Proof.
  intros f1 f2 e1 e2 e3.
  rewrite -> cc_swap.
  rewrite -> chc_l_cong by apply chc_idemp.
  reflexivity.
  (* TODO: rewrite using cc_swap_l *)
Qed.

(** ** Examples *)

(** Examples of some additional properties of formula choice calculus. *)
Module Examples.

(** Flip operation for formula choice calculus expressions. *)
Fixpoint flip (e : fcc) : fcc :=
  match e with
  | one n => one n
  | chc f l r => chc (neg f) (flip r) (flip l)
  end.

(** Negation is an involution. *)
Example neg_invo : forall f : formula,
                   neg (neg f) =f= f.
Proof.
  intros f c.
  simpl.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

(** The flip operation for formula choice calculus expressions is an
    involution. *)
Example flip_invo : forall e : fcc,
                    flip (flip e) =fcc= e.
Proof.
  intros e.
  induction e as [n | f l IHl r IHr].
  (* case: e = one n *)
    reflexivity.
  (* case: e = chc f l r *)
    simpl.
    rewrite -> chc_f_cong by apply neg_invo.
    rewrite -> chc_l_cong by apply IHl.
    rewrite -> chc_r_cong by apply IHr.
    reflexivity.
Qed.

End Examples.

End FCC.
