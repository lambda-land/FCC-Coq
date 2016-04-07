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

(** Definition of equivalent choice calculus expressions. *)
Definition equiv (e1 e2 : cc) : Prop :=
  forall (c : config), (sem c e1) = (sem c e2).

(** Equivalence for choice calculus expressions is reflexive. *)
Fact equiv_reflexive : forall (e : cc),
                       equiv e e.
Proof.
  intro e.
  unfold equiv.
  intro c.
  reflexivity.
Qed.

(** Equivalence for choice calculus expressions is symmetric. *)
Fact equiv_symmetric : forall (e1 e2 : cc),
                       equiv e1 e2 -> equiv e2 e1.
Proof. Admitted. (* TODO: prove if needed *)

(** Equivalence for choice calculus expressions is transitive. *)
Fact equiv_transitive : forall (e1 e2 e3 : cc),
                        equiv e1 e2 -> equiv e2 e3 -> equiv e1 e3.
Proof. Admitted. (* TODO: prove if needed *)

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
Theorem cc_merge_r : forall (f : formula) (e1 e2 e3 : cc), 
                     equiv (chc f e1 (chc f e2 e3)) (chc f e1 e3).
Proof.
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
Theorem cc_swap_r : forall (f1 f2 : formula) (e1 e2 e3 : cc),
                    equiv (chc f1 (chc f2 e1 e2) (chc f2 e1 e3))
                          (chc f2 e1 (chc f1 e2 e3)).
Proof. Admitted. (* TODO: write proof *)

(** Definition of equivalent formulas. *)
Definition fequiv (f1 f2 : formula) : Prop :=
  forall (c : config), (eval c f1) = (eval c f2).

(** Equivalence for formulas is reflexive. *)
Fact fequiv_reflexive : forall (f : formula),
                        fequiv f f.
Proof.
  intro f.
  unfold fequiv.
  intro c.
  reflexivity.
Qed.

(** Equivalence for formulas is symmetric. *)
Fact fequiv_symmetric : forall (f1 f2 : formula),
                        fequiv f1 f2 -> fequiv f2 f1.
Proof. Admitted. (* TODO: prove if needed *)

(** Equivalence for formulas is transitive. *)
Fact fequiv_transitive : forall (f1 f2 f3 : formula),
                         fequiv f1 f2 -> fequiv f2 f3 -> fequiv f1 f3.
Proof. Admitted. (* TODO: prove if needed *)

(** Choices with equivalent formulas and alternatives are equivalent. *)
Lemma chc_equiv : forall (f1 f2 : formula) (l1 l2 r1 r2 : cc),
                  fequiv f1 f2 -> equiv l1 l2 -> equiv r1 r2 ->
                  equiv (chc f1 l1 r1) (chc f2 l2 r2).
Proof.
  intros f1 f2 l1 l2 r1 r2 Hf Hl Hr.
  unfold equiv.
  intro c.
  simpl.
  rewrite -> Hf.
  rewrite -> Hl.
  rewrite -> Hr.
  reflexivity.
Qed.

(** Flip the alternative selected for a dimension in a configuration. *)
Definition fflip (d : dim) (c : config) : config :=
  fun d' => if beq_nat d d' then negb (c d) else c d'.

(** Flip operation for choice calculus expressions. *)
Fixpoint flip (e : cc) : cc :=
  match e with
  | one n => one n
  | chc f l r => chc (neg f) r l
  end.

(** Flip all operation for choice calculus expressions. *)
Fixpoint flipall (e : cc) : cc :=
  match e with
  | one n => one n
  | chc f l r => chc (neg f) (flipall r) (flipall l)
  end.

(** Negation is an involution. *)
Lemma neg_involutive : forall (f : formula),
                       fequiv f (neg (neg f)).
Proof.
  intro f.
  unfold fequiv.
  intro c.
  simpl.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

(** The flip all operation for choice calculus expressions is an involution. *)
Lemma flipall_involutive : forall (e : cc),
                           equiv e (flipall (flipall e)).
Proof.
  intros e.
  induction e as [n | f l IHl r IHr].
  (* case: e = one n *)
    simpl.
    apply equiv_reflexive.
  (* case: e = chc f l r *)
    simpl.
    apply chc_equiv;
      [apply neg_involutive | apply IHl | apply IHr].
Qed.

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
Proof. Admitted. (* TODO: write proof *)

(** Join-And-Not rule. *)
Theorem join_and_not : forall (f1 f2 : formula) (e1 e2 : cc),
                       equiv (chc f1 (chc f2 e2 e1) e2)
                             (chc (meet f1 (neg f2)) e1 e2).
Proof. Admitted. (* TODO: write proof *)

(* TODO: add more theorems *)

End Equivalence.

End FCC.
