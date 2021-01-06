(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Reals ssreflect Psatz.

Require Import Rcomplements.

(** This file contains the definition and properties of the set
 [R] # &#8746; {+ &infin;} &#8746; {- &infin;} # denoted by [Rbar]. We have defined:
  - coercions from [R] to [Rbar] and vice versa ([Finite] gives [R0] at infinity points)
  - an order [Rbar_lt] and [Rbar_le]
  - total operations: [Rbar_opp], [Rbar_plus], [Rbar_minus], [Rbar_inv], [Rbar_min] and [Rbar_abs]
  - lemmas about the decidability of the order and properties of the operations (such as [Rbar_plus_comm] or [Rbar_plus_lt_compat])
 *)


Open Scope R_scope.

(** * Definitions *)

Inductive Rbar :=
  | Finite : R -> Rbar
  | p_infty : Rbar
  | m_infty : Rbar.
Definition real (x : Rbar) :=
  match x with
    | Finite x => x
    | _ => 0
  end.
Coercion Finite : R >-> Rbar.
Coercion real : Rbar >-> R.

Definition is_finite (x : Rbar) := Finite (real x) = x.
Lemma is_finite_correct (x : Rbar) :
  is_finite x <-> exists y : R, x = Finite y.
Proof.
  rewrite /is_finite ;
  case: x => /= ; split => // H.
  by exists r.
  by case: H.
  by case: H.
Qed.

(** ** Order *)

Definition Rbar_lt (x y : Rbar) : Prop :=
  match x,y with
    | p_infty, _ | _, m_infty => False
    | m_infty, _ | _, p_infty => True
    | Finite x, Finite y => Rlt x y
  end.

Definition Rbar_le (x y : Rbar) : Prop :=
  match x,y with
    | m_infty, _ | _, p_infty => True
    | p_infty, _ | _, m_infty => False
    | Finite x, Finite y => Rle x y
  end.

(** ** Operations *)
(** *** Additive operators *)

Definition Rbar_opp (x : Rbar) :=
  match x with
    | Finite x => Finite (-x)
    | p_infty => m_infty
    | m_infty => p_infty
  end.

Definition Rbar_plus' (x y : Rbar) :=
  match x,y with
    | p_infty, m_infty | m_infty, p_infty => None
    | p_infty, _ | _, p_infty => Some p_infty
    | m_infty, _ | _, m_infty => Some m_infty
    | Finite x', Finite y' => Some (Finite (x' + y'))
  end.
Definition Rbar_plus (x y : Rbar) :=
  match Rbar_plus' x y with Some z => z | None => Finite 0 end.
Arguments Rbar_plus !x !y /.
Definition is_Rbar_plus (x y z : Rbar) : Prop :=
  Rbar_plus' x y = Some z.
Definition ex_Rbar_plus (x y : Rbar) : Prop :=
  match Rbar_plus' x y with Some _ => True | None => False end.
Arguments ex_Rbar_plus !x !y /.

Lemma is_Rbar_plus_unique (x y z : Rbar) :
  is_Rbar_plus x y z -> Rbar_plus x y = z.
Proof.
  unfold is_Rbar_plus, ex_Rbar_plus, Rbar_plus.
  case: Rbar_plus' => // a Ha.
  by inversion Ha.
Qed.
Lemma Rbar_plus_correct (x y : Rbar) :
  ex_Rbar_plus x y -> is_Rbar_plus x y (Rbar_plus x y).
Proof.
  unfold is_Rbar_plus, ex_Rbar_plus, Rbar_plus.
  by case: Rbar_plus'.
Qed.

Definition Rbar_minus (x y : Rbar) := Rbar_plus x (Rbar_opp y).
Arguments Rbar_minus !x !y /.
Definition is_Rbar_minus (x y z : Rbar) : Prop :=
  is_Rbar_plus x (Rbar_opp y) z.
Definition ex_Rbar_minus (x y : Rbar) : Prop :=
  ex_Rbar_plus x (Rbar_opp y).
Arguments ex_Rbar_minus !x !y /.

(** *** Multiplicative operators *)

Definition Rbar_inv (x : Rbar) : Rbar :=
  match x with
    | Finite x => Finite (/x)
    | _ => Finite 0
  end.

Definition Rbar_mult' (x y : Rbar) :=
  match x with
    | Finite x => match y with
      | Finite y => Some (Finite (x * y))
      | p_infty => match (Rle_dec 0 x) with
        | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some p_infty | right _ => None end
        | right _ => Some m_infty
      end
      | m_infty => match (Rle_dec 0 x) with
        | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some m_infty | right _ => None end
        | right _ => Some p_infty
      end
    end
    | p_infty => match y with
      | Finite y => match (Rle_dec 0 y) with
        | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some p_infty | right _ => None end
        | right _ => Some m_infty
      end
      | p_infty => Some p_infty
      | m_infty => Some m_infty
    end
    | m_infty => match y with
      | Finite y => match (Rle_dec 0 y) with
        | left H => match Rle_lt_or_eq_dec _ _ H with left _ => Some m_infty | right _ => None end
        | right _ => Some p_infty
      end
      | p_infty => Some m_infty
      | m_infty => Some p_infty
    end
  end.
Definition Rbar_mult (x y : Rbar) :=
  match Rbar_mult' x y with Some z => z | None => Finite 0 end.
Arguments Rbar_mult !x !y /.

Definition is_Rbar_mult (x y z : Rbar) : Prop :=
  Rbar_mult' x y = Some z.
Definition ex_Rbar_mult (x y : Rbar) : Prop :=
  match x with
    | Finite x => match y with
      | Finite y => True
      | p_infty => x <> 0
      | m_infty => x <> 0
    end
    | p_infty => match y with
      | Finite y => y <> 0
      | p_infty => True
      | m_infty => True
    end
    | m_infty => match y with
      | Finite y => y <> 0
      | p_infty => True
      | m_infty => True
    end
  end.
Arguments ex_Rbar_mult !x !y /.

Definition Rbar_mult_pos (x : Rbar) (y : posreal) :=
  match x with
    | Finite x => Finite (x*y)
    | _ => x
  end.

Lemma is_Rbar_mult_unique (x y z : Rbar) :
  is_Rbar_mult x y z -> Rbar_mult x y = z.
Proof.
  unfold is_Rbar_mult ;
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //= H ;
  inversion H => // ;
  case: Rle_dec H => // H0 ;
  case: Rle_lt_or_eq_dec => //.
Qed.
Lemma Rbar_mult_correct (x y : Rbar) :
  ex_Rbar_mult x y -> is_Rbar_mult x y (Rbar_mult x y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= H ;
  apply sym_not_eq in H ;
  unfold is_Rbar_mult ; simpl ;
  case: Rle_dec => // H0 ;
  case: Rle_lt_or_eq_dec => //.
Qed.
Lemma Rbar_mult_correct' (x y z : Rbar) :
  is_Rbar_mult x y z -> ex_Rbar_mult x y.
Proof.
  unfold is_Rbar_mult ;
  case: x => [x | | ] ;
  case: y => [y | | ] //= ;
  case: Rle_dec => //= H ; try (case: Rle_lt_or_eq_dec => //=) ; intros.
  by apply Rgt_not_eq.
  by apply Rlt_not_eq, Rnot_le_lt.
  by apply Rgt_not_eq.
  by apply Rlt_not_eq, Rnot_le_lt.
  by apply Rgt_not_eq.
  by apply Rlt_not_eq, Rnot_le_lt.
  by apply Rgt_not_eq.
  by apply Rlt_not_eq, Rnot_le_lt.
Qed.


Definition Rbar_div (x y : Rbar) : Rbar :=
  Rbar_mult x (Rbar_inv y).
Arguments Rbar_div !x !y /.
Definition is_Rbar_div (x y z : Rbar) : Prop :=
  is_Rbar_mult x (Rbar_inv y) z.
Definition ex_Rbar_div (x y : Rbar) : Prop :=
  ex_Rbar_mult x (Rbar_inv y).
Arguments ex_Rbar_div !x !y /.
Definition Rbar_div_pos (x : Rbar) (y : posreal) :=
  match x with
    | Finite x => Finite (x/y)
    | _ => x
  end.

(** * Compatibility with real numbers *)
(** For equality and order.
The compatibility of addition and multiplication is proved in Rbar_seq *)

Lemma Rbar_finite_eq (x y : R) :
  Finite x = Finite y <-> x = y.
Proof.
  split ; intros.
  apply Rle_antisym ; apply Rnot_lt_le ; intro.
  assert (Rbar_lt (Finite y) (Finite x)).
  simpl ; apply H0.
  rewrite H in H1 ; simpl in H1 ; by apply Rlt_irrefl in H1.
  assert (Rbar_lt (Finite x) (Finite y)).
  simpl ; apply H0.
  rewrite H in H1 ; simpl in H1 ; by apply Rlt_irrefl in H1.
  rewrite H ; reflexivity.
Qed.
Lemma Rbar_finite_neq (x y : R) :
  Finite x <> Finite y <-> x <> y.
Proof.
  split => H ; contradict H ; by apply Rbar_finite_eq.
Qed.

(** * Properties of order *)

(** ** Relations between inequalities *)

Lemma Rbar_lt_not_eq (x y : Rbar) :
  Rbar_lt x y -> x<>y.
Proof.
  destruct x ; destruct y ; simpl ; try easy.
  intros H H0.
  apply Rbar_finite_eq in H0 ; revert H0 ; apply Rlt_not_eq, H.
Qed.

Lemma Rbar_not_le_lt (x y : Rbar) :
  ~ Rbar_le x y -> Rbar_lt y x.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
Qed.

Lemma Rbar_lt_not_le (x y : Rbar) :
  Rbar_lt y x -> ~ Rbar_le x y.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  apply (Rlt_irrefl r0).
  now apply Rlt_le_trans with (1 := H).
Qed.

Lemma Rbar_not_lt_le (x y : Rbar) :
  ~ Rbar_lt x y -> Rbar_le y x.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  now apply Rnot_lt_le.
Qed.

Lemma Rbar_le_not_lt (x y : Rbar) :
  Rbar_le y x -> ~ Rbar_lt x y.
Proof.
  destruct x ; destruct y ; simpl ; intuition ; contradict H0.
  now apply Rle_not_lt.
Qed.

Lemma Rbar_le_refl :
  forall x : Rbar, Rbar_le x x.
Proof.
intros [x| |] ; try easy.
apply Rle_refl.
Qed.

Lemma Rbar_lt_le :
  forall x y : Rbar,
  Rbar_lt x y -> Rbar_le x y.
Proof.
  intros [x| |] [y| |] ; try easy.
  apply Rlt_le.
Qed.

(** ** Decidability *)

Lemma Rbar_total_order (x y : Rbar) :
  {Rbar_lt x y} + {x = y} + {Rbar_lt y x}.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
  destruct (total_order_T r r0) ; intuition.
Qed.

Lemma Rbar_eq_dec (x y : Rbar) :
  {x = y} + {x <> y}.
Proof.
  intros ; destruct (Rbar_total_order x y) as [[H|H]|H].
  right ; revert H ; destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intros H ;
  try easy.
  contradict H.
  apply Rbar_finite_eq in H ; try apply Rle_not_lt, Req_le ; auto.
  left ; apply H.
  right ; revert H ; destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intros H ;
  try easy.
  contradict H.
  apply Rbar_finite_eq in H ; apply Rle_not_lt, Req_le ; auto.
Qed.

Lemma Rbar_lt_dec (x y : Rbar) :
  {Rbar_lt x y} + {~Rbar_lt x y}.
Proof.
  destruct (Rbar_total_order x y) as [H|H] ; [ destruct H as [H|H]|].
  now left.
  right ; rewrite H ; clear H ; destruct y ; auto ; apply Rlt_irrefl ; auto.
  right ; revert H ; destruct x as [x | | ] ; destruct y as [y | | ] ; intros H ; auto ;
  apply Rle_not_lt, Rlt_le ; auto.
Qed.

Lemma Rbar_lt_le_dec (x y : Rbar) :
  {Rbar_lt x y} + {Rbar_le y x}.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  now left.
  right.
  rewrite H.
  apply Rbar_le_refl.
  right.
  now apply Rbar_lt_le.
Qed.

Lemma Rbar_le_dec (x y : Rbar) :
  {Rbar_le x y} + {~Rbar_le x y}.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  left.
  now apply Rbar_lt_le.
  left.
  rewrite H.
  apply Rbar_le_refl.
  right.
  now apply Rbar_lt_not_le.
Qed.

Lemma Rbar_le_lt_dec (x y : Rbar) :
  {Rbar_le x y} + {Rbar_lt y x}.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  left.
  now apply Rbar_lt_le.
  left.
  rewrite H.
  apply Rbar_le_refl.
  now right.
Qed.

Lemma Rbar_le_lt_or_eq_dec (x y : Rbar) :
  Rbar_le x y -> { Rbar_lt x y } + { x = y }.
Proof.
  destruct (Rbar_total_order x y) as [[H|H]|H].
  now left.
  now right.
  intros K.
  now elim (Rbar_le_not_lt _ _ K).
Qed.

(** ** Transitivity *)

Lemma Rbar_lt_trans (x y z : Rbar) :
  Rbar_lt x y -> Rbar_lt y z -> Rbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rlt_trans with r0.
Qed.

Lemma Rbar_lt_le_trans (x y z : Rbar) :
  Rbar_lt x y -> Rbar_le y z -> Rbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rlt_le_trans with r0.
Qed.

Lemma Rbar_le_lt_trans (x y z : Rbar) :
  Rbar_le x y -> Rbar_lt y z -> Rbar_lt x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rle_lt_trans with r0.
Qed.

Lemma Rbar_le_trans (x y z : Rbar) :
  Rbar_le x y -> Rbar_le y z -> Rbar_le x z.
Proof.
  destruct x ; destruct y ; destruct z ; simpl ; intuition.
  now apply Rle_trans with r0.
Qed.

Lemma Rbar_le_antisym (x y : Rbar) :
  Rbar_le x y -> Rbar_le y x -> x = y.
Proof.
  destruct x ; destruct y ; simpl ; intuition.
Qed.

(** * Properties of operations *)
(** ** Additive operators *)
(** *** Rbar_opp *)

Lemma Rbar_opp_involutive (x : Rbar) : (Rbar_opp (Rbar_opp x)) = x.
Proof.
  destruct x as [x| | ] ; auto ; simpl ; rewrite Ropp_involutive ; auto.
Qed.

Lemma Rbar_opp_lt (x y : Rbar) : Rbar_lt (Rbar_opp x) (Rbar_opp y) <-> Rbar_lt y x.
Proof.
  destruct x as [x | | ] ; destruct y as [y | | ] ;
  split ; auto ; intro H ; simpl ; try left.
  apply Ropp_lt_cancel ; auto.
  apply Ropp_lt_contravar ; auto.
Qed.

Lemma Rbar_opp_le (x y : Rbar) : Rbar_le (Rbar_opp x) (Rbar_opp y) <-> Rbar_le y x.
Proof.
  destruct x as [x| |] ; destruct y as [y| |] ; simpl ; intuition.
Qed.

Lemma Rbar_opp_eq (x y : Rbar) : (Rbar_opp x) = (Rbar_opp y) <-> x = y.
Proof.
  split ; intros H.
  rewrite <- (Rbar_opp_involutive x), H, Rbar_opp_involutive ; reflexivity.
  rewrite H ; reflexivity.
Qed.

Lemma Rbar_opp_real (x : Rbar) : real (Rbar_opp x) = - real x.
Proof.
  destruct x as [x | | ] ; simpl ; intuition.
Qed.

Lemma Rbar_opp_finite (x : Rbar): is_finite x -> is_finite (Rbar_opp x).
Proof.
  destruct x as [x | | ]; rewrite /is_finite; simpl; intuition; congruence.
Qed.

(** *** Rbar_plus *)

Lemma Rbar_plus'_comm :
  forall x y, Rbar_plus' x y = Rbar_plus' y x.
Proof.
intros [x| |] [y| |] ; try reflexivity.
apply (f_equal (fun x => Some (Finite x))), Rplus_comm.
Qed.

Lemma ex_Rbar_plus_comm :
  forall x y,
  ex_Rbar_plus x y -> ex_Rbar_plus y x.
Proof.
now intros [x| |] [y| |].
Qed.

Lemma ex_Rbar_plus_opp (x y : Rbar) :
  ex_Rbar_plus x y -> ex_Rbar_plus (Rbar_opp x) (Rbar_opp y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] => //.
Qed.

Lemma Rbar_plus_0_r (x : Rbar) : Rbar_plus x (Finite 0) = x.
Proof.
  case: x => //= ; intuition.
Qed.
Lemma Rbar_plus_0_l (x : Rbar) : Rbar_plus (Finite 0) x = x.
Proof.
  case: x => //= ; intuition.
Qed.

Lemma Rbar_plus_comm (x y : Rbar) : Rbar_plus x y = Rbar_plus y x.
Proof.
  case x ; case y ; intuition.
  simpl.
  apply f_equal, Rplus_comm.
Qed.

Lemma Rbar_plus_lt_compat (a b c d : Rbar) :
  Rbar_lt a b -> Rbar_lt c d -> Rbar_lt (Rbar_plus a c) (Rbar_plus b d).
Proof.
  case: a => [a | | ] // ; case: b => [b | | ] // ;
  case: c => [c | | ] // ; case: d => [d | | ] // ;
  apply Rplus_lt_compat.
Qed.

Lemma Rbar_plus_le_compat (a b c d : Rbar) :
  Rbar_le a b -> Rbar_le c d -> Rbar_le (Rbar_plus a c) (Rbar_plus b d).
Proof.
  case: a => [a | | ] // ; case: b => [b | | ] // ;
  case: c => [c | | ] // ; case: d => [d | | ] //.
  apply Rplus_le_compat.
  intros _ _.
  apply Rle_refl.
  intros _ _.
  apply Rle_refl.
Qed.

Lemma Rbar_plus_opp (x y : Rbar) :
  Rbar_plus (Rbar_opp x) (Rbar_opp y) = Rbar_opp (Rbar_plus x y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= ; apply f_equal ; ring.
Qed.

Lemma Rbar_plus_opp_finite (x : Rbar) :
  is_finite x ->
  Rbar_plus x (Rbar_opp x) = Finite 0.
Proof.
  intros Hfin.
  destruct x as [x | |]; eauto. simpl. f_equal. field.
Qed.

Lemma Rbar_plus_assoc_opp_finite (x y : Rbar) :
  is_finite y ->
  Rbar_plus (Rbar_plus x y) (Rbar_opp y) = x.
Proof.
  intros Hfin1.
  destruct x, y => //=; simpl in *; try intuition; try (f_equal; nra).
Qed.

Lemma Rbar_plus_assoc_opp_finite' (x y : Rbar) :
  Rbar_le 0 x ->
  Rbar_le 0 y ->
  Rbar_le 0 (Rbar_plus (Rbar_plus x y) (Rbar_opp y)).
Proof.
  intros Hle1 Hle2. destruct y; last by (simpl in *; intuition).
  - rewrite Rbar_plus_assoc_opp_finite //=.
  - destruct x => //=; try nra.
Qed.

Lemma Rbar_plus_assoc_finite (x y z : Rbar) :
  is_finite y ->
  is_finite z ->
  Rbar_plus (Rbar_plus x y) z =
  Rbar_plus x (Rbar_plus y z).
Proof.
  intros Hfin1 Hfin2.
  rewrite /Rbar_plus/Rbar_plus'. destruct x, y, z => //=.
  f_equal.
  field.
Qed.

Lemma Rbar_plus_assoc_nonneg (x y z : Rbar) :
  Rbar_le 0 x ->
  Rbar_le 0 y ->
  Rbar_le 0 z ->
  Rbar_plus (Rbar_plus x y) z =
  Rbar_plus x (Rbar_plus y z).
Proof.
  intros Hle1 Hle2 Hle3.
  rewrite /Rbar_plus/Rbar_plus'. destruct x, y, z => //=.
  f_equal.
  field.
Qed.

(** *** Rbar_minus *)

Lemma Rbar_minus_eq_0 (x : Rbar) : Rbar_minus x x = 0.
Proof.
  case: x => //= x ; by apply f_equal, Rcomplements.Rminus_eq_0.
Qed.
Lemma Rbar_opp_minus (x y : Rbar) :
  Rbar_opp (Rbar_minus x y) = Rbar_minus y x.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //=.
  by rewrite Ropp_minus_distr'.
  by rewrite Ropp_0.
  by rewrite Ropp_0.
Qed.

(** ** Multiplicative *)

(** *** Rbar_inv *)

Lemma Rbar_inv_opp (x : Rbar) :
  x <> 0 -> Rbar_inv (Rbar_opp x) = Rbar_opp (Rbar_inv x).
Proof.
  case: x => [x | | ] /= Hx.
  rewrite Ropp_inv_permute => //.
  contradict Hx.
  by rewrite Hx.
  by rewrite Ropp_0.
  by rewrite Ropp_0.
Qed.

(** *** Rbar_mult *)

Lemma Rbar_mult'_comm (x y : Rbar) :
  Rbar_mult' x y = Rbar_mult' y x.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //=.
  by rewrite Rmult_comm.
Qed.

Lemma Rbar_mult'_opp_r (x y : Rbar) :
  Rbar_mult' x (Rbar_opp y) = match Rbar_mult' x y with Some z => Some (Rbar_opp z) | None => None end.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= ;
  (try case: Rle_dec => Hx //=) ;
  (try case: Rle_lt_or_eq_dec => //= Hx0).
  by rewrite Ropp_mult_distr_r_reverse.
  rewrite -Ropp_0 in Hx0.
  apply Ropp_lt_cancel in Hx0.
  case Rle_dec => Hy //=.
  now elim Rle_not_lt with (1 := Hy).
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Rlt_not_le with (1 := Hy0).
  apply Ropp_le_cancel.
  by rewrite Ropp_0.
  elim Hy.
  apply Ropp_le_cancel.
  rewrite -Hx0 Ropp_0.
  apply Rle_refl.
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Hx.
  rewrite -Hy0 Ropp_0.
  apply Rle_refl.
  elim Hx.
  rewrite -Ropp_0.
  apply Ropp_le_contravar.
  apply Rlt_le.
  now apply Rnot_le_lt.
  case Rle_dec => Hy //=.
  elim Rlt_not_le with (1 := Hx0).
  rewrite -Ropp_0.
  now apply Ropp_le_contravar.
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Rlt_not_le with (1 := Hy0).
  apply Ropp_le_cancel.
  rewrite -Hx0 Ropp_0.
  apply Rle_refl.
  elim Hy.
  apply Ropp_le_cancel.
  rewrite -Hx0 Ropp_0.
  apply Rle_refl.
  case Rle_dec => Hy //=.
  case Rle_lt_or_eq_dec => Hy0 //=.
  elim Hx.
  rewrite -Hy0 Ropp_0.
  apply Rle_refl.
  elim Hx.
  rewrite -Ropp_0.
  apply Ropp_le_contravar.
  apply Rlt_le.
  now apply Rnot_le_lt.
Qed.

Lemma Rbar_mult_comm (x y : Rbar) :
  Rbar_mult x y = Rbar_mult y x.
Proof.
  unfold Rbar_mult.
  by rewrite Rbar_mult'_comm.
Qed.
Lemma Rbar_mult_opp_r (x y : Rbar) :
  Rbar_mult x (Rbar_opp y) = (Rbar_opp (Rbar_mult x y)).
Proof.
  unfold Rbar_mult.
  rewrite Rbar_mult'_opp_r.
  case Rbar_mult' => //=.
  apply f_equal, eq_sym, Ropp_0.
Qed.
Lemma Rbar_mult_opp_l (x y : Rbar) :
  Rbar_mult (Rbar_opp x) y = Rbar_opp (Rbar_mult x y).
Proof.
  rewrite ?(Rbar_mult_comm _ y).
  by apply Rbar_mult_opp_r.
Qed.
Lemma Rbar_mult_opp (x y : Rbar) :
  Rbar_mult (Rbar_opp x) (Rbar_opp y) = Rbar_mult x y.
Proof.
  by rewrite Rbar_mult_opp_l -Rbar_mult_opp_r Rbar_opp_involutive.
Qed.
Lemma Rbar_mult_0_l (x : Rbar) : Rbar_mult 0 x = 0.
Proof.
  case: x => [x | | ] //=.
  by rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
Qed.
Lemma Rbar_mult_0_r (x : Rbar) : Rbar_mult x 0 = 0.
Proof.
  rewrite Rbar_mult_comm ; by apply Rbar_mult_0_l.
Qed.

Lemma Rbar_mult_eq_0 (y x : Rbar) :
  Rbar_mult x y = 0 -> x = 0 \/ y = 0.
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //= ;
  (try case: Rle_dec => //= H) ;
  (try case: Rle_lt_or_eq_dec => //=) ;
  (try (left ; by apply f_equal)) ;
  (try (right ; by apply f_equal)).
  intros H.
  apply (f_equal real) in H.
  simpl in H.
  apply Rmult_integral in H ; case: H => ->.
  by left.
  by right.
Qed.

Lemma ex_Rbar_mult_sym (x y : Rbar) :
  ex_Rbar_mult x y -> ex_Rbar_mult y x.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //.
Qed.
Lemma ex_Rbar_mult_opp_l (x y : Rbar) :
  ex_Rbar_mult x y -> ex_Rbar_mult (Rbar_opp x) y.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= Hx ;
  by apply Ropp_neq_0_compat.
Qed.
Lemma ex_Rbar_mult_opp_r (x y : Rbar) :
  ex_Rbar_mult x y -> ex_Rbar_mult x (Rbar_opp y).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] //= Hx ;
  by apply Ropp_neq_0_compat.
Qed.

Lemma is_Rbar_mult_sym (x y z : Rbar) :
  is_Rbar_mult x y z -> is_Rbar_mult y x z.
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //= ;
  unfold is_Rbar_mult, Rbar_mult' ;
  try (case: Rle_dec => // H) ;
  try (case: Rle_lt_or_eq_dec => // H0) ;
  try (case => <-) ; try (move => _).
  by rewrite Rmult_comm.
Qed.
Lemma is_Rbar_mult_opp_l (x y z : Rbar) :
  is_Rbar_mult x y z -> is_Rbar_mult (Rbar_opp x) y (Rbar_opp z).
Proof.
  case: x => [x | | ] ;
  case: y => [y | | ] ;
  case: z => [z | | ] //= ;
  unfold is_Rbar_mult, Rbar_mult' ;
  try (case: Rle_dec => // H) ;
  try (case: Rle_lt_or_eq_dec => // H0) ;
  try (case => <-) ; try (move => _).
  apply (f_equal (@Some _)), f_equal ; ring.
  apply Ropp_lt_contravar in H0 ; rewrite Ropp_0 in H0 ;
  now move/Rlt_not_le: H0 ; case: Rle_dec.
  apply Rnot_le_lt, Ropp_lt_contravar in H ; rewrite Ropp_0 in H ;
  move/Rlt_le: (H) ; case: Rle_dec => // H0 _ ;
  now move/Rlt_not_eq: H ; case: Rle_lt_or_eq_dec.
  apply Rnot_le_lt, Ropp_lt_contravar in H ; rewrite Ropp_0 in H ;
  move/Rlt_le: (H) ; case: Rle_dec => // H0 _ ;
  now move/Rlt_not_eq: H ; case: Rle_lt_or_eq_dec.
  apply Ropp_lt_contravar in H0 ; rewrite Ropp_0 in H0 ;
  now move/Rlt_not_le: H0 ; case: Rle_dec.
Qed.
Lemma is_Rbar_mult_opp_r (x y z : Rbar) :
  is_Rbar_mult x y z -> is_Rbar_mult x (Rbar_opp y) (Rbar_opp z).
Proof.
  move/is_Rbar_mult_sym => H.
  now apply is_Rbar_mult_sym, is_Rbar_mult_opp_l.
Qed.

Lemma is_Rbar_mult_p_infty_pos (x : Rbar) :
  Rbar_lt 0 x -> is_Rbar_mult p_infty x p_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec (Rlt_le _ _ Hx) => // Hx' _.
  now case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hx).
Qed.
Lemma is_Rbar_mult_p_infty_neg (x : Rbar) :
  Rbar_lt x 0 -> is_Rbar_mult p_infty x m_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec (Rlt_not_le _ _ Hx) => // Hx' _.
Qed.
Lemma is_Rbar_mult_m_infty_pos (x : Rbar) :
  Rbar_lt 0 x -> is_Rbar_mult m_infty x m_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec (Rlt_le _ _ Hx) => // Hx' _.
  now case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Hx).
Qed.
Lemma is_Rbar_mult_m_infty_neg (x : Rbar) :
  Rbar_lt x 0 -> is_Rbar_mult m_infty x p_infty.
Proof.
  case: x => [x | | ] // Hx.
  unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec (Rlt_not_le _ _ Hx) => // Hx' _.
Qed.

(** Rbar_div *)

Lemma is_Rbar_div_p_infty (x : R) :
  is_Rbar_div x p_infty 0.
Proof.
  apply (f_equal (@Some _)).
  by rewrite Rmult_0_r.
Qed.
Lemma is_Rbar_div_m_infty (x : R) :
  is_Rbar_div x m_infty 0.
Proof.
  apply (f_equal (@Some _)).
  by rewrite Rmult_0_r.
Qed.

(** Rbar_mult_pos *)

Lemma Rbar_mult_pos_eq (x y : Rbar) (z : posreal) :
  x = y <-> (Rbar_mult_pos x z) = (Rbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H ; apply Rbar_finite_eq in H.
  by rewrite H.
  apply Rbar_finite_eq, (Rmult_eq_reg_r (z)) => // ;
  by apply Rgt_not_eq.
Qed.

Lemma Rbar_mult_pos_lt (x y : Rbar) (z : posreal) :
  Rbar_lt x y <-> Rbar_lt (Rbar_mult_pos x z) (Rbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H.
  apply (Rmult_lt_compat_r (z)) => //.
  apply (Rmult_lt_reg_r (z)) => //.
Qed.

Lemma Rbar_mult_pos_le (x y : Rbar) (z : posreal) :
  Rbar_le x y <-> Rbar_le (Rbar_mult_pos x z) (Rbar_mult_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H.
  apply Rmult_le_compat_r with (2 := H).
  now apply Rlt_le.
  now apply Rmult_le_reg_r with (2 := H).
Qed.

(** Rbar_div_pos *)

Lemma Rbar_div_pos_eq (x y : Rbar) (z : posreal) :
  x = y <-> (Rbar_div_pos x z) = (Rbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H ; apply Rbar_finite_eq in H.
  by rewrite H.
  apply Rbar_finite_eq, (Rmult_eq_reg_r (/z)) => // ;
  by apply Rgt_not_eq, Rinv_0_lt_compat.
Qed.

Lemma Rbar_div_pos_lt (x y : Rbar) (z : posreal) :
  Rbar_lt x y <-> Rbar_lt (Rbar_div_pos x z) (Rbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H.
  apply (Rmult_lt_compat_r (/z)) => // ; by apply Rinv_0_lt_compat.
  apply (Rmult_lt_reg_r (/z)) => // ; by apply Rinv_0_lt_compat.
Qed.

Lemma Rbar_div_pos_le (x y : Rbar) (z : posreal) :
  Rbar_le x y <-> Rbar_le (Rbar_div_pos x z) (Rbar_div_pos y z).
Proof.
  case: z => z Hz ; case: x => [x | | ] ; case: y => [y | | ] ;
  split => //= H.
  apply Rmult_le_compat_r with (2 := H).
  now apply Rlt_le, Rinv_0_lt_compat.
  apply Rmult_le_reg_r with (2 := H).
  now apply Rinv_0_lt_compat.
Qed.

(** * Rbar_min *)

Definition Rbar_min (x y : Rbar) : Rbar :=
  match x, y with
  | z, p_infty | p_infty, z => z
  | _ , m_infty | m_infty, _ => m_infty
  | Finite x, Finite y => Rmin x y
  end.

Lemma Rbar_lt_locally (a b : Rbar) (x : R) :
  Rbar_lt a x -> Rbar_lt x b ->
  exists delta : posreal,
    forall y, Rabs (y - x) < delta -> Rbar_lt a y /\ Rbar_lt y b.
Proof.
  case: a => [ a /= Ha | | _ ] //= ; (try apply Rminus_lt_0 in Ha) ;
  case: b => [ b Hb | _ | ] //= ; (try apply Rminus_lt_0 in Hb).
  assert (0 < Rmin (x - a) (b - x)).
    by apply Rmin_case.
  exists (mkposreal _ H) => y /= Hy ; split.
  apply Rplus_lt_reg_r with (-x).
  replace (a+-x) with (-(x-a)) by ring.
  apply (Rabs_lt_between (y - x)).
  apply Rlt_le_trans with (1 := Hy).
  by apply Rmin_l.
  apply Rplus_lt_reg_r with (-x).
  apply (Rabs_lt_between (y - x)).
  apply Rlt_le_trans with (1 := Hy).
  by apply Rmin_r.
  exists (mkposreal _ Ha) => y /= Hy ; split => //.
  apply Rplus_lt_reg_r with (-x).
  replace (a+-x) with (-(x-a)) by ring.
  by apply (Rabs_lt_between (y - x)).
  exists (mkposreal _ Hb) => y /= Hy ; split => //.
  apply Rplus_lt_reg_r with (-x).
  by apply (Rabs_lt_between (y - x)).
  exists (mkposreal _ Rlt_0_1) ; by split.
Qed.

Lemma Rbar_min_comm (x y : Rbar) : Rbar_min x y = Rbar_min y x.
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //=.
  by rewrite Rmin_comm.
Qed.

Lemma Rbar_min_r (x y : Rbar) : Rbar_le (Rbar_min x y) y.
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //=.
  by apply Rmin_r.
  by apply Rle_refl.
Qed.

Lemma Rbar_min_l (x y : Rbar) : Rbar_le (Rbar_min x y) x.
Proof.
  rewrite Rbar_min_comm.
  by apply Rbar_min_r.
Qed.

Lemma Rbar_min_case (x y : Rbar) (P : Rbar -> Type) :
  P x -> P y -> P (Rbar_min x y).
Proof.
  case: x => [x | | ] //= ;
  case: y => [y | | ] //=.
  by apply Rmin_case.
Qed.
Lemma Rbar_min_case_strong (r1 r2 : Rbar) (P : Rbar -> Type) :
  (Rbar_le r1 r2 -> P r1) -> (Rbar_le r2 r1 -> P r2)
    -> P (Rbar_min r1 r2).
Proof.
  case: r1 => [x | | ] //= ;
  case: r2 => [y | | ] //= Hx Hy ;
  (try by apply Hx) ; (try by apply Hy).
  by apply Rmin_case_strong.
Qed.

(** * Rbar_abs *)

Definition Rbar_abs (x : Rbar) :=
  match x with
    | Finite x => Finite (Rabs x)
    | _ => p_infty
  end.

Lemma Rbar_abs_lt_between (x y : Rbar) :
  Rbar_lt (Rbar_abs x) y <-> (Rbar_lt (Rbar_opp y) x /\ Rbar_lt x y).
Proof.
  case: x => [x | | ] ; case: y => [y | | ] /= ; try by intuition.
  by apply Rabs_lt_between.
Qed.

Lemma Rbar_abs_opp (x : Rbar) :
  Rbar_abs (Rbar_opp x) = Rbar_abs x.
Proof.
  case: x => [x | | ] //=.
  by rewrite Rabs_Ropp.
Qed.

Lemma Rbar_abs_pos (x : Rbar) :
  Rbar_le 0 x -> Rbar_abs x = x.
Proof.
  case: x => [x | | ] //= Hx.
  by apply f_equal, Rabs_pos_eq.
Qed.
Lemma Rbar_abs_neg (x : Rbar) :
  Rbar_le x 0 -> Rbar_abs x = Rbar_opp x.
Proof.
  case: x => [x | | ] //= Hx.
  rewrite -Rabs_Ropp.
  apply f_equal, Rabs_pos_eq.
  now rewrite -Ropp_0 ; apply Ropp_le_contravar.
Qed.

Lemma is_Rbar_plus_ex_Rbar_plus v1 v2 r:
  is_Rbar_plus v1 v2 r -> ex_Rbar_plus v1 v2.
Proof. by rewrite /is_Rbar_plus/ex_Rbar_plus => ->. Qed.
Lemma ex_Rbar_plus_is_Rbar_plus v1 v2:
  ex_Rbar_plus v1 v2 -> is_Rbar_plus v1 v2 (Rbar_plus v1 v2).
Proof. rewrite /is_Rbar_plus/ex_Rbar_plus/Rbar_plus. destruct (Rbar_plus' _ _) => //=. Qed.

Lemma ex_Rbar_plus_nonneg v1 v2:
  Rbar_le 0 v1 ->
  Rbar_le 0 v2 ->
  ex_Rbar_plus v1 v2.
Proof.
  intros Hle1 Hl2.
  destruct v1, v2 => //=.
Qed.

Require Import Iter.

Definition Rbar_sum_n_m' (a : nat -> Rbar) n m :=
  iter_nat (fun mx my => match mx, my with | Some x, Some y => Rbar_plus' x y | _, _ => None end)
           (Some (Finite R0)) (fun x => Some (a x)) n m.
Definition Rbar_sum_n' (a : nat -> Rbar) n :=
  Rbar_sum_n_m' a O n.

Definition Rbar_sum_n_m (a : nat -> Rbar) n m :=
  iter_nat Rbar_plus R0 a n m.
Definition Rbar_sum_n (a : nat -> Rbar) n :=
  Rbar_sum_n_m a O n.

Definition is_Rbar_sum_n_m (a : nat -> Rbar) n m v :=
  Rbar_sum_n_m' a n m = Some v.
Definition is_Rbar_sum_n (a : nat -> Rbar) n v :=
  Rbar_sum_n' a n = Some v.

Definition ex_Rbar_sum_n_m a n m := exists v, is_Rbar_sum_n_m a n m v.
Definition ex_Rbar_sum_n a n := exists v, is_Rbar_sum_n a n v.

Lemma Rbar_sum_n_m'_Some a n m v :
  Rbar_sum_n_m' a n m = Some v -> Rbar_sum_n_m a n m = v.
Proof.
  rewrite /Rbar_sum_n_m/Rbar_sum_n_m'/iter_nat.
  revert v. induction (seq.iota n (S m - n)) => v //=.
  - congruence.
  - intros Heq.
    destruct (iter _ _ _ _) as [v'|] eqn:Heq'; last by congruence.
    erewrite IHl; last done.
    rewrite /Rbar_plus Heq //=.
Qed.

Lemma is_Rbar_sum_n_m_unique a n m v :
  is_Rbar_sum_n_m a n m v -> Rbar_sum_n_m a n m = v.
Proof. rewrite /is_Rbar_sum_n_m. apply Rbar_sum_n_m'_Some. Qed.
Lemma is_Rbar_sum_n_unique a n v :
  is_Rbar_sum_n a n v -> Rbar_sum_n a n = v.
Proof. apply is_Rbar_sum_n_m_unique. Qed.

Lemma Rbar_sum_n_m_correct a n m :
  ex_Rbar_sum_n_m a n m -> is_Rbar_sum_n_m a n m (Rbar_sum_n_m a n m).
Proof. destruct 1 as (?&His). by rewrite (is_Rbar_sum_n_m_unique _ _ _ _ His). Qed.
Lemma Rbar_sum_n_correct a n :
  ex_Rbar_sum_n a n -> is_Rbar_sum_n a n (Rbar_sum_n a n).
Proof. destruct 1 as (?&His). by rewrite (is_Rbar_sum_n_unique _ _ _ His). Qed.

Lemma Rbar_sum_n_m'_Chasles (a : nat -> Rbar) (n m k : nat) :
  (n <= S m)%nat -> (m <= k)%nat
  -> Rbar_sum_n_m' a n k =
     match (Rbar_sum_n_m' a n m), (Rbar_sum_n_m' a (S m) k) with
     | Some x, Some y => Rbar_plus' x y
     | _, _ => None
     end.
Proof.
  intros Hnm Hmk.
  rewrite /Rbar_sum_n_m'.
  rewrite (iter_nat_Chasles _ _ _ _ _ n m k); swap 1 5; eauto.
  { intros []; last done. rewrite -{2}(Rbar_plus_0_l r) /Rbar_plus//=. destruct r; eauto. }
  { intros [r0|] [r1|] [r2|]; try done.
    * rewrite /Rbar_plus'. destruct r0, r1, r2 => //=. do 2 f_equal. ring.
    * destruct (Rbar_plus' _ _); eauto.
  }
Qed.

Lemma is_Rbar_sum_n_m_Chasles (a : nat -> Rbar) (n m k : nat) v :
  (n <= S m)%nat -> (m <= k)%nat
  -> (is_Rbar_sum_n_m a n k v <->
      (ex_Rbar_sum_n_m a n m /\
       ex_Rbar_sum_n_m a (S m) k /\
       is_Rbar_plus (Rbar_sum_n_m a n m) (Rbar_sum_n_m a (S m) k) v)).
Proof.
  intros Hnm Hmk.
  rewrite /ex_Rbar_sum_n_m/is_Rbar_sum_n_m/Rbar_sum_n_m/Rbar_sum_n_m'.
    rewrite (iter_nat_Chasles _ _ _ _ _ n m k); swap 1 5; eauto.
    { intros []; last done. rewrite -{2}(Rbar_plus_0_l r) /Rbar_plus//=. destruct r; eauto. }
    { intros [r0|] [r1|] [r2|]; try done.
      * rewrite /Rbar_plus'. destruct r0, r1, r2 => //=. do 2 f_equal. ring.
      * destruct (Rbar_plus' _ _); eauto.
    }
  split.
    intros Heq.
    destruct (iter_nat _ _ _ n m) eqn:Heq0;
    destruct (iter_nat _ _ _ (S m) k) eqn:Heq1; try congruence.
    split; [| split]; eauto.
    rewrite /is_Rbar_plus -Heq. f_equal.
    * by eapply Rbar_sum_n_m'_Some.
    * by eapply Rbar_sum_n_m'_Some.
  - intros ((v1&Hex1)&(v2&Hex2)&Hplus).
    rewrite Hex1 Hex2. rewrite /is_Rbar_plus in Hplus. rewrite -Hplus. f_equal; symmetry.
    * by eapply Rbar_sum_n_m'_Some.
    * by eapply Rbar_sum_n_m'_Some.
Qed.

Lemma Rbar_sum_n_n' (a : nat -> Rbar) (n: nat) :
  Rbar_sum_n_m' a n n = Some (a n).
Proof.
  rewrite /Rbar_sum_n_m'. rewrite iter_nat_point //=.
  { intros []; last done. rewrite -{2}(Rbar_plus_0_r r) /Rbar_plus//=. destruct r; eauto. }
Qed.

Lemma is_Rbar_sum_n_n (a : nat -> Rbar) (n : nat) :
  is_Rbar_sum_n_m a n n (a n).
Proof. by apply Rbar_sum_n_n'. Qed.
Lemma ex_Rbar_sum_n_n (a : nat -> Rbar) (n : nat) :
  ex_Rbar_sum_n_m a n n.
Proof. eexists; eapply is_Rbar_sum_n_n. Qed.
Lemma Rbar_sum_n_n a n :
  Rbar_sum_n_m a n n = a n.
Proof. eapply Rbar_sum_n_m'_Some, Rbar_sum_n_n'. Qed.

Lemma is_Rbar_sum_O (a : nat -> Rbar) : is_Rbar_sum_n a 0 (a O).
Proof.
  by apply is_Rbar_sum_n_n.
Qed.
Lemma Rbar_sum_O (a : nat -> Rbar) : Rbar_sum_n a 0 = a O.
Proof. rewrite /Rbar_sum_n Rbar_sum_n_n //=. Qed.

Lemma Rbar_sum_n_Sm' (a : nat -> Rbar) (n m : nat) :
  (n <= S m)%nat -> Rbar_sum_n_m' a n (S m) =
                    match (Rbar_sum_n_m' a n m) with
                    | Some x => Rbar_plus' x (a (S m))
                    | _ => None
                    end.
Proof.
  intros Hnmk.
  rewrite (Rbar_sum_n_m'_Chasles _ _ m).
  by rewrite Rbar_sum_n_n'.
  by [].
  by apply le_n_Sn.
Qed.
Lemma is_Rbar_sum_n_Sm (a : nat -> Rbar) (n m : nat) v :
  (n <= S m)%nat -> (is_Rbar_sum_n_m a n (S m) v <->
                     ex_Rbar_sum_n_m a n m /\ is_Rbar_plus (Rbar_sum_n_m a n m) (a (S m)) v).
Proof.
  intros Hnmk.
  rewrite (is_Rbar_sum_n_m_Chasles _ _ m); auto.
  split.
  - intros (Hex1&Hex2&His); split; auto.
    rewrite Rbar_sum_n_n in His; eauto.
  - intros (Hex1&His); split; [| split]; auto.
    { apply ex_Rbar_sum_n_n. }
    { rewrite Rbar_sum_n_n; eauto. }
Qed.
Lemma ex_Rbar_sum_n_Sm (a : nat -> Rbar) (n m : nat) :
  (n <= S m)%nat -> (ex_Rbar_sum_n_m a n (S m) <->
                     ex_Rbar_sum_n_m a n m /\ ex_Rbar_plus (Rbar_sum_n_m a n m) (a (S m))).
Proof.
  intros; split.
  - intros (v&(?&?)%is_Rbar_sum_n_Sm); eauto.
    split; eauto. eapply is_Rbar_plus_ex_Rbar_plus; eauto.
  - intros ((v&Hex1)&Hex2). apply ex_Rbar_plus_is_Rbar_plus in Hex2.
    eexists. eapply is_Rbar_sum_n_Sm; eauto. split; eauto.
    eexists; eauto.
Qed.

Lemma Rbar_sum_n_Sm (a : nat -> Rbar) (n m : nat) :
  (n <= S m)%nat ->
  ex_Rbar_sum_n_m a n (S m) ->
  Rbar_sum_n_m a n (S m) = Rbar_plus (Rbar_sum_n_m a n m) (a (S m)).
Proof.
  intros Hle Hex.
  eapply is_Rbar_sum_n_m_unique.
  eapply is_Rbar_sum_n_Sm; eauto.
  split.
  * eapply ex_Rbar_sum_n_Sm; eauto.
  * eapply Rbar_plus_correct.
    eapply ex_Rbar_sum_n_Sm; eauto.
Qed.

Lemma Rbar_sum_Sn_m' (a : nat -> Rbar) (n m : nat) :
  (n <= m)%nat -> Rbar_sum_n_m' a n m =
                  match (Rbar_sum_n_m' a (S n) m) with
                  | Some x => Rbar_plus' (a n) x
                  | None => None
                  end.
Proof.
  intros Hnmk.
  rewrite (Rbar_sum_n_m'_Chasles _ _ n).
  by rewrite Rbar_sum_n_n'.
  by apply le_n_Sn.
  by [].
Qed.

Lemma is_Rbar_sum_Sn_m (a : nat -> Rbar) (n m : nat) v :
  (n <= m)%nat -> (is_Rbar_sum_n_m a n m v <->
                   ex_Rbar_sum_n_m a (S n) m /\
                   is_Rbar_plus (a n) (Rbar_sum_n_m a (S n) m) v).
Proof.
  intros Hnmk.
  rewrite (is_Rbar_sum_n_m_Chasles _ _ n); auto.
  split.
  - intros (Hex1&Hex2&His); split; auto.
    rewrite Rbar_sum_n_n in His; eauto.
  - intros (Hex1&His); split; [| split]; auto.
    { apply ex_Rbar_sum_n_n. }
    { rewrite Rbar_sum_n_n; eauto. }
Qed.

Lemma Rbar_sum_n_m'_S (a : nat -> Rbar) (n m : nat) :
  Rbar_sum_n_m' (fun n => a (S n)) n m = Rbar_sum_n_m' a (S n) (S m).
Proof. rewrite /Rbar_sum_n_m'. rewrite -iter_nat_S. eauto. Qed.

Lemma is_Rbar_sum_n_m_S (a : nat -> Rbar) (n m : nat) v :
  is_Rbar_sum_n_m (fun n => a (S n)) n m v <-> is_Rbar_sum_n_m a (S n) (S m) v.
Proof. rewrite /is_Rbar_sum_n_m Rbar_sum_n_m'_S //=. Qed.

Lemma Rbar_sum_n_m_S (a : nat -> Rbar) (n m : nat) :
  Rbar_sum_n_m (fun n => a (S n)) n m = Rbar_sum_n_m a (S n) (S m).
Proof. rewrite /Rbar_sum_n_m. apply iter_nat_S. Qed.

Lemma is_Rbar_sum_Sn (a : nat -> Rbar) (n: nat) v :
  is_Rbar_sum_n a (S n) v <->
  ex_Rbar_sum_n a n /\ is_Rbar_plus (Rbar_sum_n a n) (a (S n)) v.
Proof. apply is_Rbar_sum_n_Sm. by apply le_O_n. Qed.

Lemma ex_Rbar_sum_Sn (a : nat -> Rbar) (n: nat) :
  ex_Rbar_sum_n a (S n) <->
  ex_Rbar_sum_n a n /\ ex_Rbar_plus (Rbar_sum_n a n) (a (S n)).
Proof. apply ex_Rbar_sum_n_Sm. by apply le_O_n. Qed.

Lemma Rbar_sum_Sn (a : nat -> Rbar) (n : nat) :
  ex_Rbar_sum_n_m a 0 (S n) ->
  Rbar_sum_n a (S n) = Rbar_plus (Rbar_sum_n a n) (a (S n)).
Proof. apply Rbar_sum_n_Sm. by apply le_O_n. Qed.

Lemma Rbar_sum_n_m'_zero a n m:
  (m < n)%nat -> Rbar_sum_n_m' a n m = Some (Finite R0).
Proof.
  intros Hnm.
  rewrite /Rbar_sum_n_m'.
  elim: n m a Hnm => [ | n IH] m a Hnm.
  by apply lt_n_O in Hnm.
  case: m Hnm => [|m] Hnm //.
  rewrite -iter_nat_S.
  apply IH.
  by apply lt_S_n.
Qed.

Lemma is_Rbar_sum_n_m_zero (a : nat -> Rbar) (n m : nat) :
  (m < n)%nat -> is_Rbar_sum_n_m a n m R0.
Proof. eapply Rbar_sum_n_m'_zero. Qed.

Lemma is_Rbar_sum_n_m_zero_inv (a : nat -> Rbar) (n m : nat) v :
  (m < n)%nat -> is_Rbar_sum_n_m a n m v -> v = R0.
Proof.
  intros.
  assert (Heqv: Rbar_sum_n_m a n m = v) by (eapply is_Rbar_sum_n_m_unique; eauto).
  rewrite -Heqv.
  eapply is_Rbar_sum_n_m_unique. apply is_Rbar_sum_n_m_zero; eauto.
Qed.

Lemma Rbar_sum_n_m_zero (a : nat -> Rbar) (n m : nat) :
  (m < n)%nat -> Rbar_sum_n_m a n m = R0.
Proof. intros Hnm. by apply Rbar_sum_n_m'_Some, Rbar_sum_n_m'_zero. Qed.

Lemma Rbar_sum_n_m'_const_zero (n m : nat) :
  Rbar_sum_n_m' (fun _ => R0) n m = Some (Finite R0).
Proof.
  rewrite /Rbar_sum_n_m' /iter_nat.
  elim: (seq.iota n (S m - n)) => //= h t ->.
  do 2 f_equal. nra.
Qed.

Lemma is_Rbar_sum_n_m_const_zero (n m : nat) :
  is_Rbar_sum_n_m (fun _ => R0) n m R0.
Proof. eapply Rbar_sum_n_m'_const_zero. Qed.

Lemma Rbar_sum_n_m_const_zero (n m : nat) :
  Rbar_sum_n_m (fun _ => R0) n m = R0.
Proof. by apply Rbar_sum_n_m'_Some, Rbar_sum_n_m'_const_zero. Qed.

Lemma Rbar_sum_n_m'_ext_loc (a b : nat -> Rbar) (n m : nat) :
  (forall k, (n <= k <= m)%nat -> a k = b k) ->
  Rbar_sum_n_m' a n m = Rbar_sum_n_m' b n m.
Proof.
  intros Heq. rewrite /Rbar_sum_n_m'. apply iter_nat_ext_loc.
  intros; eauto. rewrite Heq //=.
Qed.

Lemma Rbar_plus_correct' x y : ex_Rbar_plus x y -> Rbar_plus' x y = Some (Rbar_plus x y).
Proof.
  rewrite /ex_Rbar_plus/Rbar_plus; destruct (Rbar_plus'); eauto. intuition.
Qed.

Lemma Rbar_sum_n_m'_nonneg_Some (a : nat -> Rbar) n m:
  (forall n, Rbar_le 0 (a n)) ->
  exists v, Rbar_le 0 v /\ Rbar_sum_n_m' a n m = Some v.
Proof.
  intros Hnonneg.
  destruct (Nat.le_decidable n m) as [Hle|Hnle].
  - induction Hle.
    * rewrite /Rbar_sum_n_m' iter_nat_point //. eauto.
      { intros []; auto. destruct r => //=; do 2 f_equal. nra. }
    * rewrite Rbar_sum_n_Sm'; eauto.
      destruct IHHle as (v&Hnonneg'&->).
      { specialize (Hnonneg (S m)).
        exists (Rbar_plus v (a (S m))).
        split.
        * replace (Finite 0) with (Rbar_plus 0 0); last first.
          { rewrite //=. f_equal; nra. }
          apply Rbar_plus_le_compat; auto.
        * apply Rbar_plus_correct'. apply ex_Rbar_plus_nonneg; auto.
      }
      exists 0. split; first apply Rbar_le_refl.
      apply Rbar_sum_n_m'_zero. lia.
Qed.

Lemma ex_Rbar_sum_n_m_nonneg (a : nat -> Rbar) n m:
  (forall n, Rbar_le 0 (a n)) ->
  ex_Rbar_sum_n_m a n m.
Proof.
  intros Hnonneg. rewrite /ex_Rbar_sum_n_m.
  rewrite /is_Rbar_sum_n_m.
  edestruct Rbar_sum_n_m'_nonneg_Some as (v&?&->); eauto.
Qed.

Lemma is_Rbar_sum_n_m_ext_loc (a b : nat -> Rbar) (n m : nat) v :
  (forall k, (n <= k <= m)%nat -> a k = b k) ->
  is_Rbar_sum_n_m a n m v ->
  is_Rbar_sum_n_m b n m v.
Proof.
  intros. rewrite /is_Rbar_sum_n_m. erewrite Rbar_sum_n_m'_ext_loc; try eassumption.
  intros; symmetry; eauto.
Qed.

Lemma Rbar_sum_n_m_ext_loc (a b : nat -> Rbar) (n m : nat) :
  (forall k, (n <= k <= m)%nat -> a k = b k) ->
  Rbar_sum_n_m a n m = Rbar_sum_n_m b n m.
Proof.
  intros.
  by apply iter_nat_ext_loc.
Qed.

Lemma Rbar_sum_n_m_ext (a b : nat -> Rbar) n m :
  (forall n, a n = b n) ->
  Rbar_sum_n_m a n m = Rbar_sum_n_m b n m.
Proof.
  intros H.
  by apply Rbar_sum_n_m_ext_loc.
Qed.

Lemma is_Rbar_sum_n_ext_loc :
  forall (a b : nat -> Rbar) N v,
  (forall n, (n <= N)%nat -> a n = b n) ->
  is_Rbar_sum_n a N v ->
  is_Rbar_sum_n b N v.
Proof.
  intros a b N v H.
  apply is_Rbar_sum_n_m_ext_loc => k [ _ Hk].
  by apply H.
Qed.

Lemma Rbar_sum_n_ext_loc :
  forall (a b : nat -> Rbar) N,
  (forall n, (n <= N)%nat -> a n = b n) ->
  Rbar_sum_n a N = Rbar_sum_n b N.
Proof.
  intros a b N H.
  apply Rbar_sum_n_m_ext_loc => k [ _ Hk].
  by apply H.
Qed.
Lemma Rbar_sum_n_ext :
  forall (a b : nat -> Rbar) N,
  (forall n, a n = b n) ->
  Rbar_sum_n a N = Rbar_sum_n b N.
Proof.
  intros a b N H.
  by apply Rbar_sum_n_ext_loc.
Qed.

Lemma Rbar_plus4_sum_inv a b c d v1 v2:
  is_Rbar_plus a b v1 ->
  is_Rbar_plus c d v2 ->
  ex_Rbar_plus v1 v2 ->
  ex_Rbar_plus a c /\ is_Rbar_plus (Rbar_plus a c) (Rbar_plus b d) (Rbar_plus v1 v2).
Proof.
  rewrite /is_Rbar_plus/ex_Rbar_plus/Rbar_plus/Rbar_plus'.
  destruct a,b,c,d => //=;
  inversion 1; subst;
  inversion 1; subst; split; eauto; try do 2 f_equal; nra.
Qed.
Lemma is_Rbar_plus_ext a b c a' b':
  a = a' ->
  b = b' ->
  is_Rbar_plus a b c <-> is_Rbar_plus a' b' c.
Proof. intros; subst; eauto. intuition. Qed.

Lemma is_Rbar_sum_n_m_plus :
  forall (u v : nat -> Rbar) (n m : nat) x1 x2,
    is_Rbar_sum_n_m u n m x1 ->
    is_Rbar_sum_n_m v n m x2 ->
    ex_Rbar_plus x1 x2 ->
    is_Rbar_sum_n_m (fun k => Rbar_plus (u k) (v k)) n m (Rbar_plus x1 x2).
Proof.
  intros u v n m x1 x2.
  case: (le_dec n m) => Hnm.
  elim: m n u v x1 x2 Hnm => [ | m IH] ;
  case => [ | n] u v x1 x2 Hnm.
  { rewrite /is_Rbar_sum_n_m. rewrite ?is_Rbar_sum_n_n.
    inversion 1; subst.
    inversion 1; subst.
    intros. eauto.
  }
  {
    by apply le_Sn_O in Hnm.
  }
  {
    rewrite is_Rbar_sum_n_Sm; auto.
    rewrite is_Rbar_sum_n_Sm; auto.
    rewrite is_Rbar_sum_n_Sm; auto.
    intros (Hex1&Hplus1) (Hex2&Hplus2); split; last first.
    {
      apply Rbar_sum_n_m_correct in Hex1.
      apply Rbar_sum_n_m_correct in Hex2.
      edestruct Rbar_plus4_sum_inv as (Hex&Hplus); [ apply Hplus1 | apply Hplus2 | apply H | ].
      eapply is_Rbar_plus_ext; try eassumption; eauto.
      eapply is_Rbar_sum_n_m_unique.
      eapply IH; eauto. apply le_O_n.
    }
    eexists.
    apply Rbar_sum_n_m_correct in Hex1.
    apply Rbar_sum_n_m_correct in Hex2.
    eapply IH; eauto.
    { apply le_O_n. }
      edestruct Rbar_plus4_sum_inv as (Hex&Hplus); [ apply Hplus1 | apply Hplus2 | apply H | ]. eauto.
  }
  { rewrite -?is_Rbar_sum_n_m_S. eapply IH. by apply le_S_n. }
  {
    intros ?%is_Rbar_sum_n_m_zero_inv; last lia.
    intros ?%is_Rbar_sum_n_m_zero_inv; last lia.
    subst. intros _.
    rewrite /= Rplus_0_r. apply is_Rbar_sum_n_m_zero.
    lia.
  }
Qed.

Lemma Rbar_sum_n_m_plus :
  forall (u v : nat -> Rbar) (n m : nat),
  ex_Rbar_sum_n_m u n m ->
  ex_Rbar_sum_n_m v n m ->
  ex_Rbar_plus (Rbar_sum_n_m u n m) (Rbar_sum_n_m v n m)->
  Rbar_sum_n_m (fun k => Rbar_plus (u k) (v k)) n m = Rbar_plus (Rbar_sum_n_m u n m) (Rbar_sum_n_m v n m).
Proof.
  intros.
  apply is_Rbar_sum_n_m_unique.
  eapply is_Rbar_sum_n_m_plus; eauto using Rbar_sum_n_m_correct.
Qed.

Lemma Rbar_sum_n_plus :
  forall (u v : nat -> Rbar) (n : nat),
  ex_Rbar_sum_n u n ->
  ex_Rbar_sum_n v n ->
  ex_Rbar_plus (Rbar_sum_n u n) (Rbar_sum_n v n)->
  Rbar_sum_n (fun k => Rbar_plus (u k) (v k)) n = Rbar_plus (Rbar_sum_n u n) (Rbar_sum_n v n).
Proof.
  intros u v n.
  apply Rbar_sum_n_m_plus.
Qed.

(* TODO: this is annoying to prove right now. Maybe the right way is to
   observe that the option Rbar with Rbar_plus' can be made into an Absorbing abelian monoid
   (where 0 is the absorbing element) and then use sum_n_switch from Hierarchy.v *)
(*
Lemma Rbar_sum_n'_switch :
  forall (u : nat -> nat -> Rbar) (m n : nat),
  Rbar_sum_n' (fun i => Rbar_sum_n' (u i) n) m = Rbar_sum_n' (fun j => Rbar_sum_n' (fun i => u i j) m) n.
Proof.
  intros u.
  rewrite /sum_n.
  induction m ; simpl ; intros n.
  rewrite sum_n_n.
  apply iter_nat_ext_loc => k Hk.
  rewrite sum_n_n.
  by [].
  rewrite !sum_n_Sm.
  rewrite IHm ; clear IHm.
  rewrite -sum_n_m_plus.
  apply sum_n_m_ext_loc => k Hk.
  rewrite sum_n_Sm //.
  by apply le_O_n.
  by apply le_O_n.
Qed.
*)
