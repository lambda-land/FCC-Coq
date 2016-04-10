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

(** Formula choice calculus syntax. *)
Inductive fcc : Type :=
  (* TODO: replace one with node and leaf *)
  | one : nat -> fcc
  | chc : formula -> fcc -> fcc -> fcc.

End Syntax.

(** ** Semantics *)
(** The semantics of a formula choice calculus expression is a function from
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

(** Formula choice calculus semantics. *)
Fixpoint sem (c : config) (e : fcc) : nat :=
  match e with
  | one n     => n
  | chc f l r => if eval c f then sem c l else sem c r
  end.

End Semantics.

(** ** Equivalence *)
(** Statement and proof of semantic equivalence rules from the TOSEM paper (for
    formula choice calculus), the GPCE paper, and some additional rules. *)
Section Equivalence.

(** Definition of equivalence for formula. *)
Definition f_equiv (f1 f2 : formula) : Prop :=
  forall (c : config), (eval c f1) = (eval c f2).

(** Equivalence for formulas is reflexive. *)
Remark f_equiv_refl : forall f : formula,
                      f_equiv f f.
Proof.
  unfold f_equiv.
  intros f c.
  reflexivity.
Qed.

(** Equivalence for formulas is symmetric. *)
Remark f_equiv_symm : forall f1 f2 : formula,
                      f_equiv f1 f2 -> f_equiv f2 f1.
Proof.
  intros f1 f2 H.
  unfold f_equiv in H.
  unfold f_equiv.
  intro c.
  symmetry.
  apply H.
Qed.

(** Equivalence for formulas is transitive. *)
Remark f_equiv_trans : forall f1 f2 f3 : formula,
                       f_equiv f1 f2 -> f_equiv f2 f3 -> f_equiv f1 f3.
Proof.
  intros f1 f2 f3 H1 H2.
  unfold f_equiv in H1.
  unfold f_equiv in H2.
  unfold f_equiv.
  intro c.
  transitivity (eval c f2).
    apply H1.
    apply H2.
Qed.

(** Definition of equivalence for formula choice calculus. *)
Definition fcc_equiv (e1 e2 : fcc) : Prop :=
  forall (c : config), (sem c e1) = (sem c e2).

(** Equivalence for formula choice calculus expressions is reflexive. *)
Remark fcc_equiv_refl : forall e : fcc,
                        fcc_equiv e e.
Proof.
  unfold fcc_equiv.
  intros e c.
  reflexivity.
Qed.

(** Equivalence for formula choice calculus expressions is symmetric. *)
Remark fcc_equiv_symm : forall e1 e2 : fcc,
                        fcc_equiv e1 e2 -> fcc_equiv e2 e1.
Proof.
  intros e1 e2 H.
  unfold fcc_equiv in H.
  unfold fcc_equiv.
  intro c.
  symmetry.
  apply H.
Qed.

(** Equivalence for formula choice calculus expressions is transitive. *)
Remark fcc_equiv_trans : forall e1 e2 e3 : fcc,
                         fcc_equiv e1 e2 -> fcc_equiv e2 e3 -> fcc_equiv e1 e3.
Proof.
  intros e1 e2 e3 H1 H2.
  unfold fcc_equiv in H1.
  unfold fcc_equiv in H2.
  unfold fcc_equiv.
  intro c.
  transitivity (sem c e2).
    apply H1.
    apply H2.
Qed.

(** Choice-Transposition rule. *)
Theorem chc_trans : forall (f : formula) (l r : fcc),
                    fcc_equiv (chc f l r) (chc (neg f) r l).
Proof.
  unfold fcc_equiv.
  intros f l r c.
  destruct (eval c f) eqn:H;
    simpl;
    rewrite -> H;
    reflexivity.
Qed.

(** Choice-Congruence rule for formulas. *)
Theorem f_cong : forall (f f' : formula) (l r : fcc),
                 f_equiv f f' ->
                 fcc_equiv (chc f l r) (chc f' l r).
Proof.
  intros f f' l r H.
  unfold fcc_equiv.
  intro c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Choice-Congruence rule for left alternatives. *)
Theorem chc_l_cong : forall (f : formula) (l l' r : fcc),
                     fcc_equiv l l' ->
                     fcc_equiv (chc f l r) (chc f l' r).
Proof.
  intros f l l' r H.
  unfold fcc_equiv.
  intro c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Choice-Congruence rule for right alternatives. *)
Corollary chc_r_cong : forall (f : formula) (l r r' : fcc),
                       fcc_equiv r r' ->
                       fcc_equiv (chc f l r) (chc f l r').
Proof.
  (* The commented proof below uses symmetric reasoning as in the proof for
     chc_l_cong. The uncommented proof avoids this repetition and should be
     simpler than the commented proof.
     
     TODO: use setoid to make the uncommented proof shorter *)
  (*
  intros f l r r' H.
  unfold fcc_equiv.
  intro c.
  simpl.
  rewrite -> H.
  reflexivity.
  *)
  intros f l r r' H.
  assert (C1 : fcc_equiv (chc f l r) (chc (neg f) r l)).
    apply chc_trans.
  assert (C2 : fcc_equiv (chc (neg f) r l) (chc (neg f) r' l)).
    apply chc_l_cong.
    apply H.
  assert (C3 : fcc_equiv (chc f l r) (chc (neg f) r' l)).
    apply fcc_equiv_trans with (e2 := chc (neg f) r l).
    apply C1.
    apply C2.
  assert (C4 : fcc_equiv (chc f l r') (chc (neg f) r' l)).
    apply chc_trans.
  assert (C5 : fcc_equiv (chc (neg f) r' l) (chc f l r')).
    apply fcc_equiv_symm.
    apply C4.
  apply fcc_equiv_trans with (e2 := chc (neg f) r' l).
    apply C3.
    apply C5.
Qed.

(** TODO: comment *)
Corollary chc_cong : forall (f1 f2 : formula) (l1 l2 r1 r2 : fcc),
                     f_equiv f1 f2 -> fcc_equiv l1 l2 -> fcc_equiv r1 r2 ->
                     fcc_equiv (chc f1 l1 r1) (chc f2 l2 r2).
Proof.
  (* TODO: rewrite using f_cong, chc_l_cong, and chc_r_cong *)
  intros f1 f2 l1 l2 r1 r2 Hf Hl Hr.
  unfold fcc_equiv.
  intro c.
  simpl.
  rewrite -> Hf.
  rewrite -> Hl.
  rewrite -> Hr.
  reflexivity.
Qed.

(** TODO: comment and rewrite without hypothesis *)
Theorem f_top : forall (f : formula) (l r : fcc),
                f_equiv f top ->
                fcc_equiv (chc f l r) l.
Proof.
  intros f l r H.
  unfold f_equiv in H.
  unfold fcc_equiv.
  intro c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** TODO: comment and rewrite without hypothesis *)
Theorem f_bot : forall (f : formula) (l r : fcc),
                f_equiv f bot ->
                fcc_equiv (chc f l r) r.
Proof.
  intros f l r H.
  unfold f_equiv in H.
  unfold fcc_equiv.
  intro c.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(** Formula-Join rule. *)
Theorem join_or : forall (f1 f2 : formula) (e1 e2 : fcc),
                  fcc_equiv (chc f1 e1 (chc f2 e1 e2))
                            (chc (join f1 f2) e1 e2).
Proof.
Admitted. (* TODO: write proof *)

(** Formula-Meet rule. *)
Theorem join_and : forall (f1 f2 : formula) (e1 e2 : fcc),
                   fcc_equiv (chc f1 (chc f2 e1 e2) e2)
                             (chc (meet f1 f2) e1 e2).
Proof.
Admitted. (* TODO: write proof *)

(** Formula-Join-Not rule. *)
Corollary join_or_not : forall (f1 f2 : formula) (e1 e2 : fcc),
                        fcc_equiv (chc f1 e1 (chc f2 e2 e1))
                                  (chc (join f1 (neg f2)) e1 e2).
Proof.
Admitted. (* TODO: write proof *)

(** Formula-Meet-Not rule. *)
Corollary join_and_not : forall (f1 f2 : formula) (e1 e2 : fcc),
                         fcc_equiv (chc f1 (chc f2 e2 e1) e2)
                                   (chc (meet f1 (neg f2)) e1 e2).
Proof.
Admitted. (* TODO: write proof *)

(** Choice Idempotence. *)
Theorem chc_idemp : forall (f : formula) (e : fcc),
                    fcc_equiv e (chc f e e).
Proof.
  intros f e.
  unfold fcc_equiv.
  intro c.
  simpl.
  destruct (eval c f);
    reflexivity.
Qed.

(** C-C-Merge for the case where the nested choice appears in the left
    alternative. *)
Theorem cc_merge_l : forall (f : formula) (e1 e2 e3 : fcc),
                     fcc_equiv (chc f (chc f e1 e2) e3) (chc f e1 e3).
Proof.
  intros f e1 e2 e3.
  unfold fcc_equiv.
  intro c.
  simpl.
  destruct (eval c f);
    reflexivity.
Qed.

(** C-C-Merge for the case where the nested choice appears in the right
    alternative. *)
Corollary cc_merge_r : forall (f : formula) (e1 e2 e3 : fcc), 
                       fcc_equiv (chc f e1 (chc f e2 e3)) (chc f e1 e3).
Proof.
  (* TODO: rewrite using chc_trans, cc_merge_l, and equivalence rules. *)
  intros f e1 e2 e3.
  unfold fcc_equiv.
  intro c.
  simpl.
  destruct (eval c f);
    reflexivity.
Qed.

(** C-C-Swap. *)
Theorem cc_swap : forall (f1 f2 : formula) (e1 e2 e3 e4 : fcc),
                  fcc_equiv (chc f1 (chc f2 e1 e2) (chc f2 e3 e4))
                            (chc f2 (chc f1 e1 e3) (chc f2 e2 e4)).
Proof.
Admitted. (* TODO: write proof *)

(** C-C-Swap for the case where the nested choice appears in the left
    alternative of the simpler form. *)
Theorem cc_swap_l : forall (f1 f2 : formula) (e1 e2 e3 : fcc),
                    fcc_equiv (chc f1 (chc f2 e1 e3) (chc f2 e2 e3))
                              (chc f2 (chc f1 e1 e2) e3).
Proof.
Admitted. (* TODO: write proof *)

(** C-C-Swap for the case where the nested choice appears in the right
    alternative of the simpler form. *)
Corollary cc_swap_r : forall (f1 f2 : formula) (e1 e2 e3 : fcc),
                      fcc_equiv (chc f1 (chc f2 e1 e2) (chc f2 e1 e3))
                                (chc f2 e1 (chc f1 e2 e3)).
Proof.
Admitted. (* TODO: write proof *)

End Equivalence.

(** ** Examples *)
(** Examples of some additional properties of formula choice calculus. *)
Section Examples.

(** Flip operation for formula choice calculus expressions. *)
Fixpoint flip (e : fcc) : fcc :=
  match e with
  | one n => one n
  | chc f l r => chc (neg f) (flip r) (flip l)
  end.

(** Negation is an involution. *)
Example neg_invo : forall f : formula,
                   f_equiv f (neg (neg f)).
Proof.
  intro f.
  unfold f_equiv.
  intro c.
  simpl.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

(** The flip operation for formula choice calculus expressions is an
    involution. *)
Example flip_invo : forall e : fcc,
                    fcc_equiv e (flip (flip e)).
Proof.
  intros e.
  induction e as [n | f l IHl r IHr].
  (* case: e = one n *)
    simpl.
    apply fcc_equiv_refl.
  (* case: e = chc f l r *)
    simpl.
    apply chc_cong;
      [apply neg_invo | apply IHl | apply IHr].
Qed.

End Examples.

End FCC.
