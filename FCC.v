(** * Formula Choice Calculus (FCC) *)

(* TODO: edit imports *)
(* Require Omega. *)
Require Export Bool.
(* Require Export List. *)
(* Export ListNotations. *)
Require Export Arith.
Require Export Arith.EqNat.
Require Export Logic.

Module FCC.

Definition admit {T: Type} : T.
Admitted.

(** ** Syntax *)
(** Syntax of binary formula choice calculus expressions with global dimensions.
    The object language is binary trees. *)
Section Syntax.

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
  | meet : formula -> formula -> formula
  | join : formula -> formula -> formula.

(* Object language syntax. *)
Inductive tree : Type :=
  | t_leaf : nat -> tree
  | t_node : nat -> tree -> tree -> tree.

(** Choice calculus syntax. *)
Inductive cc : Type :=
  (* TODO: replace one with node and leaf *)
  | one : nat -> cc
  | chc : formula -> cc -> cc -> cc.

End Syntax.

(** ** Semantics *)
(** The semantics of a choice calculus expression is a function from
    selections/configuration to plain binary trees. A selection is a (total)
    function from a dimension name to the tag to select. *)
Section Semantics.

(** Formula semantics. *)
Fixpoint eval (c : config) (f : formula) : tag :=
  match f with
  | top        => L
  | bot        => R
  | ref d      => c d
  | neg f      => negb (eval c f)
  | meet f1 f2 => (eval c f1) && (eval c f2)
  | join f1 f2 => (eval c f1) || (eval c f2)
  end.

(** Choice calculus semantics. *)
Fixpoint sem (c : config) (e : cc) : nat :=
  match e with
  | one n     => n
  | chc f l r => if eval c f then sem c l else sem c r
  end.

End Semantics.

(** ** Equivalence *)
(** TODO: write comment *)
Section Equivalence.

(** Definition of equivalence for formula. *)
Definition fequiv (f1 f2 : formula) : Prop :=
  forall (c : config), (eval c f1) = (eval c f2).

(** Equivalence for formulas is reflexive. *)
Remark fequiv_refl : forall f : formula,
                     fequiv f f.
Proof.
  intro f.
  unfold fequiv.
  intro c.
  reflexivity.
Qed.

(** Equivalence for formulas is symmetric. *)
Remark fequiv_symm : forall f1 f2 : formula,
                     fequiv f1 f2 -> fequiv f2 f1.
Proof. Admitted. (* TODO: prove if needed *)

(** Equivalence for formulas is transitive. *)
Remark fequiv_trans : forall f1 f2 f3 : formula,
                      fequiv f1 f2 -> fequiv f2 f3 -> fequiv f1 f3.
Proof. Admitted. (* TODO: prove if needed *)

(** Definition of equivalence for choice calculus. *)
Definition equiv (e1 e2 : cc) : Prop :=
  forall (c : config), (sem c e1) = (sem c e2).

(** Equivalence for choice calculus expressions is reflexive. *)
Remark equiv_refl : forall e : cc,
                    equiv e e.
Proof.
  intro e.
  unfold equiv.
  intro c.
  reflexivity.
Qed.

(** Equivalence for choice calculus expressions is symmetric. *)
Remark equiv_symm : forall e1 e2 : cc,
                    equiv e1 e2 -> equiv e2 e1.
Proof. Admitted. (* TODO: prove if needed *)

(** Equivalence for choice calculus expressions is transitive. *)
Remark equiv_trans : forall e1 e2 e3 : cc,
                     equiv e1 e2 -> equiv e2 e3 -> equiv e1 e3.
Proof. Admitted. (* TODO: prove if needed *)

Theorem chc_neg : forall (f : formula) (l r : cc),
                  equiv (chc f l r) (chc (neg f) r l).
Proof.
  unfold equiv.
  intros f l r c.
  destruct (eval c f) eqn:H;
  simpl;
  rewrite -> H;
  reflexivity.
Qed.

(** Choice congruence rule for equivalent formulas. *)
Theorem chc_cong_f : forall (f f' : formula) (l r : cc),
                     fequiv f f' ->
                     equiv (chc f l r) (chc f' l r).
Proof.
  intros f f' l r H.
  unfold equiv.
  intro c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Choice Congruence for the case when equivalent choices appear in the left
    alternative. *)
Theorem chc_cong_l : forall (f : formula) (l l' r : cc),
                     equiv l l' ->
                     equiv (chc f l r) (chc f l' r).
Proof.
  intros f l l' r H.
  unfold equiv.
  intro c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Choice Congruence for the case when equivalent choices appear in the right
    alternative. *)
Corollary chc_cong_r : forall (f : formula) (l r r' : cc),
                       equiv r r' ->
                       equiv (chc f l r) (chc f l r').
Proof.
  (* TODO: rewrite using chc_neg, chc_cong_l, and equivalence rules. *)
  intros f l r r' H.
  unfold equiv.
  intro c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

Corollary chc_cong : forall (f1 f2 : formula) (l1 l2 r1 r2 : cc),
                     fequiv f1 f2 -> equiv l1 l2 -> equiv r1 r2 ->
                     equiv (chc f1 l1 r1) (chc f2 l2 r2).
Proof.
  (* TODO: rewrite using chc_cong_f, chc_cong_l, and chc_cong_r *)
  intros f1 f2 l1 l2 r1 r2 Hf Hl Hr.
  unfold equiv.
  intro c.
  simpl.
  rewrite -> Hf.
  rewrite -> Hl.
  rewrite -> Hr.
  reflexivity.
Qed.

(** Choice Idempotence. *)
Theorem cc_idemp : forall (f : formula) (e : cc),
                   equiv e (chc f e e).
Proof.
  intros f e.
  unfold equiv.
  intro c.
  simpl.
  destruct (eval c f);
    reflexivity.
Qed.

(** C-C-Merge for the case when the nested choice appears in the left
    alternative. *)
Theorem cc_merge_l : forall (f : formula) (e1 e2 e3 : cc),
                     equiv (chc f (chc f e1 e2) e3) (chc f e1 e3).
Proof.
  intros f e1 e2 e3.
  unfold equiv.
  intro c.
  simpl.
  destruct (eval c f);
    reflexivity.
Qed.

(** C-C-Merge for the case when the nested choice appears in the right
    alternative. *)
Corollary cc_merge_r : forall (f : formula) (e1 e2 e3 : cc), 
                       equiv (chc f e1 (chc f e2 e3)) (chc f e1 e3).
Proof.
  (* TODO: rewrite using chc_neg, cc_merge_l, and equivalence rules. *)
  intros f e1 e2 e3.
  unfold equiv.
  intro c.
  simpl.
  destruct (eval c f);
    reflexivity.
Qed.

(** C-C-Swap for the case when the nested choice appears in the left
    alternative of the simpler form. *)
Theorem cc_swap_l : forall (f1 f2 : formula) (e1 e2 e3 : cc),
                    equiv (chc f1 (chc f2 e1 e3) (chc f2 e2 e3))
                          (chc f2 (chc f1 e1 e2) e3).
Proof. Admitted. (* TODO: write proof *)

(** C-C-Swap for the case when the nested choice appears in the right
    alternative of the simpler form. *)
Corollary cc_swap_r : forall (f1 f2 : formula) (e1 e2 e3 : cc),
                      equiv (chc f1 (chc f2 e1 e2) (chc f2 e1 e3))
                            (chc f2 e1 (chc f1 e2 e3)).
Proof. Admitted. (* TODO: write proof *)

(** Join-Or rule. *)
Theorem join_or : forall (f1 f2 : formula) (e1 e2 : cc),
                  equiv (chc f1 e1 (chc f2 e1 e2)) (chc (join f1 f2) e1 e2).
Proof. Admitted. (* TODO: write proof *)

(** Join-And rule. *)
Theorem join_and : forall (f1 f2 : formula) (e1 e2 : cc),
                   equiv (chc f1 (chc f2 e1 e2) e2) (chc (meet f1 f2) e1 e2).
Proof. Admitted. (* TODO: write proof *)

(** Join-Or-Not rule. *)
Theorem join_or_not : forall (f1 f2 : formula) (e1 e2 : cc),
                      equiv (chc f1 e1 (chc f2 e2 e1))
                            (chc (join f1 (neg f2)) e1 e2).
Proof.
  intros f1 f2 e1 e2.
  assert (H : equiv (chc f2 e2 e1) (chc (neg f2) e1 e2)).
Admitted. (* TODO: write proof *)

(** Join-And-Not rule. *)
Theorem join_and_not : forall (f1 f2 : formula) (e1 e2 : cc),
                       equiv (chc f1 (chc f2 e2 e1) e2)
                             (chc (meet f1 (neg f2)) e1 e2).
Proof. Admitted. (* TODO: write proof *)

End Equivalence.

(** ** Examples *)
(** Some addition properties of formula choice calculus. *)
Section Examples.

(** Flip operation for choice calculus expressions. *)
Fixpoint flip (e : cc) : cc :=
  match e with
  | one n => one n
  | chc f l r => chc (neg f) (flip r) (flip l)
  end.

(** Negation is an involution. *)
Example neg_involutive : forall f : formula,
                         fequiv f (neg (neg f)).
Proof.
  intro f.
  unfold fequiv.
  intro c.
  simpl.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

(** The flip operation for choice calculus expressions is an involution. *)
Example flip_involutive : forall e : cc,
                          equiv e (flip (flip e)).
Proof.
  intros e.
  induction e as [n | f l IHl r IHr].
  (* case: e = one n *)
    simpl.
    apply equiv_refl.
  (* case: e = chc f l r *)
    simpl.
    apply chc_cong;
      [apply neg_involutive | apply IHl | apply IHr].
Qed.

End Examples.

End FCC.
