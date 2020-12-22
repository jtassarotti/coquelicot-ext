(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond
Copyright (C) 2020      Joseph Tassarotti

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

From Coq Require Import Reals Psatz ssreflect Utf8 ClassicalEpsilon.

Require Import Rcomplements Lim_seq Rbar Hierarchy Series.

Section Definitions.

(** * Definitions *)

Definition enn_is_series (a : nat -> Rbar) (l : Rbar) :=
  (∀ n, Rbar_le 0 (a n)) ∧
  match l with
  | Finite x => (∀ n, is_finite (a n)) ∧ is_series (λ n, real (a n)) x
  | m_infty => False
  | p_infty => (∃ n, a n = p_infty) ∨ (¬ ex_series (λ n, real (a n)))
  end.

Definition enn_ex_series (a : nat -> Rbar) :=
   exists l : Rbar, enn_is_series a l.

End Definitions.

Definition enn_Series (a : nat -> Rbar) : Rbar.
  destruct (ClassicalEpsilon.excluded_middle_informative (enn_ex_series a)) as [e|ne].
  - apply ClassicalEpsilon.constructive_indefinite_description in e.
    destruct e as (e&_). apply e.
  - exact (Series a).
Defined.

Lemma enn_is_series_unique (a : nat -> Rbar) (l : Rbar) :
  enn_is_series a l -> enn_Series a = l.
Proof.
  rewrite /enn_Series/enn_is_series.
  move => Ha.
  destruct (excluded_middle_informative _) as [?|n]; last first.
  { exfalso. apply n. exists l. eauto. }
  destruct Ha.
  destruct constructive_indefinite_description as (l''&HHle&Hl'').
  destruct l; try (exfalso; eauto; fail); destruct l''; eauto.
  - intuition.
    apply is_series_unique in H2.
    apply is_series_unique in H3. congruence.
  - destruct Hl''. intuition. exfalso. destruct H1 as (n&Heq). specialize (H2 n).
    rewrite Heq in H2. rewrite /is_finite in H2. inversion H2.
  - intuition. exfalso. eapply H1; eauto. eexists; eauto.
  - intuition.
  - destruct H0.
    * destruct Hl''. destruct H0 as (n&?). specialize (H1 n). rewrite H0 in H1. inversion H1.
    * exfalso. apply H0. eexists; eauto. eapply Hl''.
  - exfalso; eauto.
Qed.
Lemma enn_Series_correct (a : nat -> Rbar) :
  enn_ex_series a -> enn_is_series a (enn_Series a).
Proof.
  case => l Ha.
  by rewrite (enn_is_series_unique a l).
Qed.

Lemma enn_is_series_reals (a : nat -> R) (l : R) :
  (∀ n, 0 <= a n) ->
  is_series a l <-> enn_is_series a l.
Proof.
  intros Hnonneg.
  split.
  - intros His. split; [| split]; eauto. intros. rewrite /is_finite. reflexivity.
  - intros (?&?&His). eauto.
Qed.

Lemma enn_is_series_reals2 (a : nat -> Rbar) (l : R) :
  (∀ n, is_finite (a n)) ->
  enn_ex_series a ->
  is_series (fun n => real (a n)) l -> enn_is_series a l.
Proof.
  intros Hfin Hex His.
  rewrite /enn_is_series.
  split; [| split]; auto.
  destruct Hex as (?&?&?); eauto.
Qed.

Lemma enn_is_series_ext (a b : nat -> Rbar) (l : Rbar) :
  (forall n, a n = b n) -> (enn_is_series a l)
    -> enn_is_series b l.
Proof.
  move => Heq.
  rewrite /enn_is_series. intros (Hnonneg&Hlim).
  destruct l; eauto.
  - destruct Hlim as (Hfin&Hseries); split; [| split]; auto.
    * intros. rewrite -Heq; eauto.
    * intros. rewrite -Heq; eauto.
    * eapply is_series_ext; eauto. intros. simpl. f_equal. by rewrite Heq.
  - split.
    { intros. rewrite -Heq; eauto. }
    destruct Hlim as [Hpinfty|Hnotex].
    * left. destruct Hpinfty as (n&Heq'). exists n. congruence.
    * right. intros Hex. eapply Hnotex. eapply ex_series_ext; try eassumption.
      intros. simpl. symmetry. congruence.
  - exfalso; eauto.
Qed.

Lemma enn_ex_series_ext (a b : nat -> Rbar) :
  (forall n, a n = b n) -> enn_ex_series a
    -> enn_ex_series b.
Proof.
  move => Heq [l Ha].
  exists l ; by apply enn_is_series_ext with a.
Qed.

Lemma enn_Series_ext (a b : nat -> Rbar) :
  (forall n, a n = b n) -> enn_Series a = enn_Series b.
Proof.
  move => Heq.
  rewrite {1}/enn_Series.
  destruct (excluded_middle_informative _) as [He|Hne].
  - destruct constructive_indefinite_description.
    symmetry. eapply enn_is_series_unique. eapply enn_is_series_ext; eauto.
  - rewrite /enn_Series. destruct excluded_middle_informative; auto.
    * exfalso. eapply Hne. eapply enn_ex_series_ext; try eassumption.
      intros. congruence.
    * f_equal. apply Series_ext; eauto.
      intros. f_equal. eauto.
Qed.

Lemma enn_ex_series_nonneg (a : nat -> Rbar) :
  (∀ n, Rbar_le 0 (a n)) ->
  enn_ex_series a.
Proof.
  intros Hnonneg.
  rewrite /enn_ex_series.
  rewrite /enn_is_series.
  destruct (excluded_middle_informative (∃ n, a n = p_infty)) as [He|Hne].
  { destruct He as (n&Heq).
    exists p_infty. split; auto. left; eauto. }
  destruct (excluded_middle_informative (ex_series (λ n, real (a n)))) as [He|Hne2].
  { destruct He as (l&His). exists l. split; [| split]; eauto.
    intros n. destruct (a n) eqn:Heq; eauto; rewrite /is_finite//=.
    { exfalso. eapply Hne. eauto. }
    specialize (Hnonneg n). rewrite Heq in Hnonneg. exfalso; simpl in Hnonneg. eauto.
  }
  exists p_infty. split; eauto.
Qed.

Lemma enn_ex_series_inv (a : nat -> Rbar) :
  enn_ex_series a ->
  (ex_series (fun n => real (a n)) ∧ (forall n, is_finite (a n)) ∧ enn_Series a = Series a) ∨
  enn_Series a = p_infty.
Proof.
  intros Hex.
  destruct Hex as (l&His).
  destruct l.
  - left.
    split; [| split].
    * destruct His as (Hnonneg&?&?); eexists; eauto.
    * destruct His as (Hnonneg&?&?); eauto.
    * apply enn_is_series_unique.
      destruct His as (Hnonneg&?&?); eexists; eauto.
      split; eauto. apply Series_correct; eexists; eauto.
  - right. by apply enn_is_series_unique.
  - exfalso; eapply His.
Qed.

(** Index offset *)

Lemma enn_is_series_incr_1 (a : nat -> Rbar) (l : Rbar) :
  is_finite (a O) ->
  enn_is_series a (Rbar_plus l (a O))
    -> enn_is_series (fun k => a (S k)%nat) l.
Proof.
  rewrite /enn_is_series.
  intros Hfin (Hnonneg&Hlim).
  split.
  { intros. eapply Hnonneg. }
  destruct l.
  - destruct (a O) as [r'| |] eqn:Heq; try (exfalso; congruence).
    destruct Hlim as (Hfin'&His). split; eauto. Check is_series_incr_1.
    apply (is_series_incr_1 (fun k => real (a k))).
    rewrite Heq. eauto.
  - destruct (a O) as [r'| |] eqn:Heq; try (exfalso; congruence).
    simpl in Hlim. destruct Hlim as [(n&Heqn)|Hnex].
    * destruct n as [| n]; first by congruence.
      left. exists n; eauto.
    * right. intros Hex. apply Hnex.
      eapply ex_series_incr_1; eauto.
  - destruct (a O) as [r'| |] eqn:Heq; try (exfalso; congruence).
    simpl in Hlim; eauto.
Qed.

Lemma enn_ex_series_incr_1 (a : nat -> Rbar) :
  enn_ex_series a ->
  enn_ex_series (fun k => a (S k)).
Proof.
  intros (l&Heq). destruct Heq. apply enn_ex_series_nonneg; eauto.
Qed.

(*
Lemma enn_is_series_incr_n (a : nat -> V) (n : nat) (l : V) :
  (0 < n)%nat -> is_series a (plus l (sum_n a (pred n)))
    -> is_series (fun k => a (n + k)%nat) l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n l Ha => [ | n IH] l Ha.
  rewrite sum_O in Ha.
  by apply is_series_incr_1.
  apply is_series_ext with (fun k : nat => a (S (n + S k))).
  move => k ; apply f_equal ; ring.
  apply (is_series_incr_1 (fun k : nat => a (S (n + k))) l).
  rewrite plus_0_r.
  apply IH.
  replace (plus (plus l (a (S n))) (sum_n a n)) with (plus l (sum_n a (S n))).
  assumption.
  rewrite <- plus_assoc, sum_Sn; apply f_equal; simpl; apply plus_comm.
Qed.
*)

Lemma enn_is_series_decr_1 (a : nat -> Rbar) (l : Rbar) :
  is_finite (a O) ->
  Rbar_le 0 (a O) ->
  enn_is_series (fun k => a (S k)%nat) (Rbar_plus l (Rbar_opp (a O))) -> enn_is_series a l.
Proof.
  rewrite /enn_is_series.
  intros Hfin0 Hnonneg0 (Hnonneg&Hlim).
  split.
  { intros. destruct n; eauto; eapply Hnonneg. }
  destruct l.
  - destruct (a O) as [r'| |] eqn:Heq; try (exfalso; congruence).
    destruct Hlim as (Hfin'&His). split; eauto.
    { intros [|]; eauto. rewrite Heq; eauto. }
    apply (is_series_decr_1 (fun k => real (a k))).
    rewrite Heq. eauto.
  - destruct (a O) as [r'| |] eqn:Heq; try (exfalso; congruence).
    simpl in Hlim. destruct Hlim as [(n&Heqn)|Hnex].
    * left. eauto.
    * right. intros Hex. apply Hnex.
      eapply ex_series_incr_1 in Hex; eauto.
  - destruct (a O) as [r'| |] eqn:Heq; try (exfalso; congruence).
    simpl in Hlim; eauto.
Qed.

Lemma enn_ex_series_decr_1 (a : nat -> Rbar) :
  is_finite (a O) ->
  Rbar_le 0 (a O) ->
  enn_ex_series (fun k => a (S k)%nat) -> enn_ex_series a.
Proof.
  intros Hfin Hle (l&Hnonneg&?).
  apply enn_ex_series_nonneg. intros [| n']; eauto.
Qed.

(*
Lemma is_series_decr_n (a : nat -> V) (n : nat) (l : V) :
  (0 < n)%nat -> is_series (fun k => a (n + k)%nat) (plus l (opp (sum_n a (pred n))))
    -> is_series a l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n a l Ha => [ | n IH] a l Ha.
  rewrite sum_O in Ha.
  by apply is_series_decr_1.
  apply is_series_decr_1.
  apply IH.
  replace (plus (plus l (opp (a 0%nat))) (opp (sum_n (fun k : nat => a (S k)) n)))
    with (plus l (opp (sum_n a (S n)))).
  by apply Ha.
  rewrite /sum_n sum_n_m_S sum_Sn_m /=.
  rewrite <- plus_assoc.
  apply f_equal.
  now rewrite opp_plus.
  by apply le_O_n.
Qed.
*)

(*
Lemma ex_series_incr_1 (a : nat -> V) :
  ex_series a <-> ex_series (fun k => a (S k)%nat).
Proof.
  split ; move => [la Ha].
  exists (plus la  (opp (a O))).
  apply is_series_incr_1.
  now rewrite -plus_assoc plus_opp_l plus_zero_r.
  exists (plus la (a O)).
  apply is_series_decr_1.
  now rewrite -plus_assoc plus_opp_r plus_zero_r.
Qed.

Lemma ex_series_incr_n (a : nat -> V) (n : nat) :
  ex_series a <-> ex_series (fun k => a (n + k)%nat).
Proof.
  case: n => [ | n].
  split ; apply ex_series_ext ; by intuition.
  split ; move => [la Ha].
  exists (plus la (opp (sum_n a (pred (S n))))).
  apply is_series_incr_n.
  by apply lt_O_Sn.
  now rewrite -plus_assoc plus_opp_l plus_zero_r.
  exists (plus la (sum_n a (pred (S n)))).
  apply is_series_decr_n with (S n).
  by apply lt_O_Sn.
  now rewrite -plus_assoc plus_opp_r plus_zero_r.
Qed.
*)

Lemma enn_Series_incr_1 (a : nat -> Rbar) :
  is_finite (a O) ->
  Rbar_le 0 (a O) ->
  enn_ex_series a -> enn_Series a = Rbar_plus (a O) (enn_Series (fun k => a (S k))).
Proof.
  move => Hfin Hnonneg Ha.
  apply enn_is_series_unique.
  rewrite Rbar_plus_comm.
  apply enn_is_series_decr_1; auto.
  rewrite Rbar_plus_assoc_finite //=; last first.
  { by apply Rbar_opp_finite. }
  rewrite Rbar_plus_opp_finite; auto.
  rewrite Rbar_plus_0_r.
  eapply enn_Series_correct.
  eapply enn_ex_series_incr_1; eauto.
Qed.

(*
Lemma Series_incr_n (a : nat -> R) (n : nat) :
  (0 < n)%nat -> ex_series a
    -> Series a = sum_f_R0 a (pred n)  + Series (fun k => a (n + k)%nat).
Proof.
  move => Hn Ha.
  apply is_series_unique.
  rewrite Rplus_comm.
  apply is_series_decr_n with n.
  by [].
  rewrite /plus /opp /= sum_n_Reals.
  ring_simplify (Series (fun k : nat => a (n+ k)%nat) + sum_f_R0 a (pred n) + - sum_f_R0 a (pred n)).
  apply Series_correct.
  by apply ex_series_incr_n.
Qed.
*)

Lemma enn_Series_incr_1_aux (a : nat -> Rbar) :
  a O = 0 -> enn_Series a = enn_Series (fun k => a (S k)).
Proof.
  intros Heq. destruct (excluded_middle_informative (enn_ex_series a)) as [He|Hne] eqn:Heq'.
  - rewrite enn_Series_incr_1; rewrite ?Heq //=.
    * by rewrite Rbar_plus_0_l.
    * nra.
  - rewrite /enn_Series. rewrite Heq'.
    destruct (excluded_middle_informative (enn_ex_series (λ k, a (S k)))) as [He'|Hne'].
    { exfalso. apply Hne. apply enn_ex_series_decr_1; rewrite ?Heq => //=. nra. }
    rewrite Series_incr_1_aux ?Heq //=.
Qed.

(*
Lemma Series_incr_n_aux (a : nat -> R) (n : nat) :
   (forall k, (k < n)%nat -> a k = 0)
     -> Series a = Series (fun k => a (n + k)%nat).
Proof.
  elim: n => [ | n IH] Ha.
  by apply Series_ext => k.
  rewrite IH.
  rewrite Series_incr_1_aux.
  apply Series_ext => k.
  apply f_equal ; ring.
  intuition.
  move => k Hk ; intuition.
Qed.
*)

(** * Convergence theorems *)

(** Comparison *)

Lemma enn_Series_finite (a : nat -> Rbar) :
  (forall n, is_finite (a n)) ->
  ex_series (fun n => real (a n)) ->
  enn_Series a = Series (fun n => real (a n)).
Proof.
  intros Hfin Hex.
  destruct (excluded_middle_informative (enn_ex_series a)) eqn:Heq; last first.
  { rewrite /enn_Series. rewrite Heq. auto. }
  apply enn_is_series_unique.
  apply enn_is_series_reals2; auto.
  apply Series_correct; auto.
Qed.

Lemma enn_Series_le (a b : nat -> Rbar) :
  (forall n : nat, Rbar_le 0 (a n) /\ Rbar_le (a n) (b n)) ->
   Rbar_le (enn_Series a) (enn_Series b).
Proof.
  intros Hle.
  assert (enn_ex_series a).
  { apply enn_ex_series_nonneg. eapply Hle. }
  assert (enn_ex_series b).
  { apply enn_ex_series_nonneg. intros. apply (Rbar_le_trans _ (a n)); eapply Hle. }
  destruct (enn_ex_series_inv b) as [Hex|Hpinfty]; auto.
  - destruct Hex as (Hex&Hfin&->).
    assert (Hfina: ∀ n, is_finite (a n)).
    { intros n.
      rewrite /is_finite.
      specialize (Hle n).
      specialize (Hfin n).
      destruct (a n) => //=; rewrite -Hfin in Hle; simpl in Hle; intuition.
    }
    rewrite enn_Series_finite; auto; last first.
    { apply: ex_series_le; eauto.
      simpl. rewrite /norm //= /abs //=. intros n.
      destruct (Hle n) as (Hnonneg&Hleb).
      rewrite -Hfin in Hleb.
      rewrite -Hfina in Hleb Hnonneg.
      simpl in Hleb, Hnonneg.
      rewrite Rabs_right; auto. nra.
    }
    simpl. apply Series_le; eauto.
    { intros n.
      specialize (Hle n).
      specialize (Hfin n).
      rewrite -Hfin in Hle.
      rewrite -Hfina in Hle. simpl in Hle. auto.
    }
  - rewrite Hpinfty. destruct (enn_Series a) => //=.
Qed.

(*
(** * Operations *)

(** Additive operators *)

Section Properties2.

Context {K : AbsRing} {V : NormedModule K}.

Lemma is_series_opp (a : nat -> V) (la : V) :
  is_series a la
    -> is_series (fun n => opp (a n)) (opp la).
Proof.
  move => Ha.
   apply filterlim_ext with (fun n => opp (sum_n a n)).
  elim => [ | n IH].
  rewrite !sum_O ; easy.
  rewrite !sum_Sn -IH.
  apply: opp_plus.
  apply filterlim_comp with (1:=Ha).
  apply filterlim_opp.
Qed.

Lemma ex_series_opp (a : nat -> V) :
  ex_series a
    -> ex_series (fun n => opp (a n)).
Proof.
  move => [la Ha].
  exists (opp la).
  by apply is_series_opp.
Qed.
Lemma Series_opp (a : nat -> R) :
  Series (fun n => - a n) = - Series a.
Proof.
  rewrite /Series
    (Lim_seq_ext (sum_n (fun k : nat => - a k)) (fun n => - (sum_n (fun k => a k) n))).
  rewrite Lim_seq_opp.
  by rewrite Rbar_opp_real.
  elim => [ | n IH].
  rewrite !sum_O ; ring.
  rewrite !sum_Sn IH /plus /=.
  ring.
Qed.

Lemma is_series_plus (a b : nat -> V) (la lb : V) :
  is_series a la -> is_series b lb
    -> is_series (fun n => plus (a n)  (b n)) (plus la  lb).
Proof.
  move => Ha Hb.
  apply filterlim_ext with (fun n => plus (sum_n a n) (sum_n b n)).
  elim => [ | n IH]; simpl.
  by rewrite !sum_O.
  rewrite !sum_Sn -IH; rewrite <- 2!plus_assoc; apply f_equal.
  rewrite 2!plus_assoc; apply f_equal2; try easy.
  apply plus_comm.
  now apply filterlim_comp_2 with (3 := filterlim_plus _ _).
Qed.
Lemma ex_series_plus (a b : nat -> V) :
  ex_series a -> ex_series b
    -> ex_series (fun n => plus (a n) (b n)).
Proof.
  move => [la Ha] [lb Hb].
  exists (plus la lb).
  by apply is_series_plus.
Qed.

Lemma is_series_minus (a b : nat -> V) (la lb : V) :
  is_series a la -> is_series b lb
    -> is_series (fun n => plus (a n) (opp (b n))) (plus la (opp lb)).
Proof.
  move => Ha Hb.
  apply is_series_plus => //.
  apply is_series_opp => //.
Qed.
Lemma ex_series_minus (a b : nat -> V) :
  ex_series a -> ex_series b
    -> ex_series (fun n => plus (a n) (opp (b n))).
Proof.
  move => Ha Hb.
  apply ex_series_plus => //.
  apply ex_series_opp => //.
Qed.

End Properties2.

Lemma Series_plus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> Series (fun n => a n + b n) = Series a + Series b.
Proof.
  intros Ha Hb.
  replace (Series a + Series b) with (real (Series a + Series b)) by auto.
  apply (f_equal real), is_lim_seq_unique.
  apply: is_series_plus ;
  by apply Series_correct.
Qed.

Lemma Series_minus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> Series (fun n => a n - b n) = Series a - Series b.
Proof.
  intros Ha Hb.
  rewrite Series_plus => //.
  rewrite Series_opp => //.
  apply ex_series_opp in Hb.
  now simpl in Hb.
Qed.

(** Multiplication by a scalar *)

Section Properties3.

Context {K : AbsRing} {V : NormedModule K}.

Lemma is_series_scal (c : K) (a : nat -> V) (l : V) :
  is_series a l -> is_series (fun n => scal c (a n)) (scal c l).
Proof.
  move => Ha.
  apply filterlim_ext with (fun n => scal c (sum_n a n)).
  elim => [ | n IH]; simpl.
  by rewrite !sum_O.
  rewrite !sum_Sn -IH.
  apply: scal_distr_l.
  now apply filterlim_comp with (2 := filterlim_scal_r _ _).
Qed.
Lemma is_series_scal_l : forall (c : K) (a : nat -> V) (l : V),
  is_series a l -> is_series (fun n => scal c (a n)) (scal c l).
exact is_series_scal.
Qed.

Lemma ex_series_scal (c : K) (a : nat -> V) :
  ex_series a -> ex_series (fun n => scal c (a n)).
Proof.
  move => [l Ha].
  exists (scal c l).
  by apply: is_series_scal_l.
Qed.

Lemma ex_series_scal_l : forall (c : K) (a : nat -> V),
  ex_series a -> ex_series (fun n => scal c (a n)).
exact ex_series_scal.
Qed.

End Properties3.

Lemma Series_scal_l (c : R) (a : nat -> R) :
  Series (fun n => c * a n) = c * Series a.
Proof.
  rewrite /Series.
  have H0 : (forall x, c * Rbar.real x = Rbar.real (Rbar.Rbar_mult (Rbar.Finite c) x)).
  case: (Req_dec c 0) => [-> | Hk].
  case => [x | | ] //= ; rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => //= H0 _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case: Rle_dec (Rle_refl 0) => //= H0 _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case => [x | | ] //= ; rewrite Rmult_0_r.
  case: Rle_dec => //= H0.
  case: Rle_lt_or_eq_dec => //=.
  case: Rle_dec => //= H0.
  case: Rle_lt_or_eq_dec => //=.
  rewrite H0 -(Lim_seq_scal_l _ c).
  apply f_equal, Lim_seq_ext.
  elim => [ | n IH].
  rewrite !sum_O ; ring.
  rewrite !sum_Sn IH /plus /=.
  ring.
Qed.

Lemma is_series_scal_r (c : R) (a : nat -> R) (l : R) :
  is_series  a l -> is_series  (fun n => (a n) * c) (l * c).
Proof.
  move => Ha.
  rewrite Rmult_comm.
  apply is_series_ext with (fun n : nat => c * a n).
  move => n ; apply Rmult_comm.
  apply (is_series_scal_l _ _ _ Ha).
Qed.
Lemma ex_series_scal_r (c : R) (a : nat -> R) :
  ex_series  a -> ex_series  (fun n => a n * c).
Proof.
  intros [l Ha].
  exists (l * c).
  by apply is_series_scal_r.
Qed.

Lemma Series_scal_r (c : R) (a : nat -> R) :
  Series (fun n => a n * c) = Series a * c.
Proof.
  rewrite Rmult_comm -Series_scal_l.
  apply Series_ext.
  move => n ; apply Rmult_comm.
Qed.

Lemma is_series_mult_pos (a b : nat -> R) (la lb : R) :
  is_series  a la -> is_series  b lb ->
  (forall n, 0 <= a n) -> (forall n, 0 <= b n)
  -> is_series  (fun n => sum_f_R0 (fun k => a k * b (n - k)%nat) n) (la * lb).
Proof.
  move => Hla Hlb Ha Hb.

  have H0 : forall n,
    sum_f_R0 (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k) n
      <= sum_f_R0 a n * sum_f_R0 b n.
    case => [ | n].
    simpl ; apply Rle_refl.
    rewrite (cauchy_finite a b (S n) (lt_O_Sn n)).
    apply Rminus_le_0 ; ring_simplify.
    apply cond_pos_sum => m.
    apply cond_pos_sum => k.
    by apply Rmult_le_pos.
  have H1 : forall n, sum_f_R0 a n * sum_f_R0 b n
    <= sum_f_R0 (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k) ((2*n)%nat).
    case => [ /= | n].
    by apply Rle_refl.
    rewrite (cauchy_finite a b (S n) (lt_O_Sn n)).
    rewrite Rplus_comm ; apply Rle_minus_r.
    replace (pred (S n)) with n by auto.
    replace (2 * S n)%nat with (S n + S n)%nat by ring.
    rewrite -sum_f_rw.
    rewrite /sum_f.
    replace (S n + S n - S (S n))%nat with n.
    elim: {1 5 8}n (le_refl n) => [ | m IH] Hm ; rewrite /sum_f_R0 -/sum_f_R0.
    rewrite -minus_n_O plus_0_l ; simpl pred.
    rewrite -?sum_f_rw_0.
    replace (sum_f 0 (S (S n)) (fun p : nat => a p * b (S (S n) - p)%nat))
      with ((sum_f 0 (S (S n)) (fun p : nat => a p * b (S (S n) - p)%nat) -
        (fun p : nat => a p * b (S (S n) - p)%nat) 0%nat)
        + a O * b (S (S n))) by (rewrite -minus_n_O ; ring).
    rewrite -(sum_f_Sn_m _ O (S (S n))) ; [ | by apply lt_O_Sn].
    rewrite sum_f_u_Sk ; [ | by apply le_O_n].
    rewrite sum_f_n_Sm ; [ | by apply le_O_n].
    apply Rle_trans with (sum_f 0 n (fun l0 : nat => a (S (l0 + 0)) * b (S n - l0)%nat) +
      a (S (S n)) * b (S (S n) - S (S n))%nat + a 0%nat * b (S (S n))).
      apply Rminus_le_0 ; ring_simplify.
      apply Rplus_le_le_0_compat ; by apply Rmult_le_pos.
      repeat apply Rplus_le_compat_r.
      apply Req_le.
      rewrite ?sum_f_rw_0.
      elim: {1 4 6}n (le_refl n) => [ | k IH] Hk // ;
      rewrite /sum_f_R0 -/sum_f_R0.
      rewrite IH ; try by intuition.
      apply f_equal.
      by rewrite plus_0_r /=.
    apply Rplus_le_compat.
    apply IH ; intuition.
    rewrite -?sum_f_rw_0.
    rewrite MyNat.sub_succ_l ; try by intuition.
    replace (pred (S (n - S m))) with (n - S m)%nat by auto.
    rewrite plus_Sn_m -?plus_n_Sm.
    replace (sum_f 0 (S (S (S (m + n))))
      (fun p : nat => a p * b (S (S (S (m + n))) - p)%nat))
      with (sum_f 1 (S (S (S (m + n))))
      (fun p : nat => a p * b (S (S (S (m + n))) - p)%nat) + a O * b (S (S (S (m + n))))).
    rewrite -(Rplus_0_r (sum_f O _ _)).
    apply Rplus_le_compat.
    rewrite (sum_f_chasles _ O (S m) (S (S (S (m + n))))) ; try by intuition.
    rewrite -(Rplus_0_l (sum_f O _ _)).
    apply Rplus_le_compat.
    rewrite /sum_f.
    elim: (S m - 1)%nat => {IH} [ | k IH] ; rewrite /sum_f_R0 -/sum_f_R0 //.
    by apply Rmult_le_pos.
    apply Rplus_le_le_0_compat.
    by apply IH.
    by apply Rmult_le_pos.
    replace (S (S m)) with (1 + S m)%nat by ring.
    replace (S (S (S (m + n)))) with (S (S n) + S m )%nat by ring.
    rewrite sum_f_u_add.
    rewrite (sum_f_chasles _ O (S (n - S m)) (S (S n))) ; try by intuition.
    rewrite -(Rplus_0_r (sum_f O _ _)).
    apply Rplus_le_compat.
    rewrite sum_f_u_Sk.
    rewrite ?sum_f_rw_0.
    apply Req_le.
    elim: (n - S m)%nat => {IH} [ | k IH] ; rewrite /sum_f_R0 -/sum_f_R0 //.
    apply f_equal2 ; apply f_equal ; intuition.
    rewrite IH ; apply f_equal, f_equal2 ; apply f_equal.
    ring.
    rewrite ?(Coq.Arith.Plus.plus_comm _ (S m)) -minus_plus_simpl_l_reverse //=.
    apply le_O_n.
    rewrite /sum_f.
    elim: (S (S n) - S (S (n - S m)))%nat => {IH} [ | k IH] ;
    rewrite /sum_f_R0 -/sum_f_R0 //.
    by apply Rmult_le_pos.
    apply Rplus_le_le_0_compat => // ; by apply Rmult_le_pos.
    by apply le_n_S, le_O_n.
    by apply Rmult_le_pos.
    rewrite sum_f_Sn_m -?minus_n_O ; try by intuition.
    ring.
    replace (S (S n)) with (S n + 1)%nat.
    rewrite -minus_plus_simpl_l_reverse.
    simpl; apply minus_n_O.
    now rewrite Coq.Arith.Plus.plus_comm.
    elim: n => [ | n IH] //.
    rewrite -plus_n_Sm plus_Sn_m.
    apply lt_n_S ; intuition.
    have H2 : forall n, sum_f_R0 a (Div2.div2 n)%nat * sum_f_R0 b (Div2.div2 n)%nat <=
      sum_f_R0
      (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k)
      n.
      move => n.
      case: (even_odd_cor n) => k ; case => -> {n}.
      rewrite div2_double.
      by apply H1.
      rewrite div2_S_double.
      apply Rle_trans with (1 := H1 _).
      apply Rminus_le_0 ; rewrite -sum_f_rw ; try by intuition.
      rewrite /sum_f minus_diag /sum_f_R0 -/sum_f_R0.
      apply cond_pos_sum => l ; by apply Rmult_le_pos.

    change (is_lim_seq (sum_n (fun n : nat => sum_f_R0 (fun k : nat => a k * b (n - k)%nat) n)) (Finite (la * lb))).
    apply is_lim_seq_le_le with (u := fun n => sum_f_R0 a (Div2.div2 n) * sum_f_R0 b (Div2.div2 n))
    (w := fun n => sum_f_R0 a n * sum_f_R0 b n).
    intros n; rewrite sum_n_Reals.
    by split.
    replace (Finite (la * lb)) with (Rbar_mult la lb) by auto.
    suff H : is_lim_seq
      (fun n : nat => sum_f_R0 a n * sum_f_R0 b n)
      (Rbar_mult la lb).
    apply is_lim_seq_spec in H.
    apply is_lim_seq_spec.
    move => eps.
    case: (H eps) => {H} N H.
    exists (S (2 * N))%nat => n Hn.
    apply H.
    apply le_double.
    apply le_S_n.
    apply le_trans with (1 := Hn).
    apply (Div2.ind_0_1_SS (fun n => (n <= S (2 * Div2.div2 n))%nat)).
    by apply le_O_n.
    by apply le_refl.
    move => k Hk.
    replace (Div2.div2 (S (S k))) with (S (Div2.div2 k)) by auto.
    replace (2 * S (Div2.div2 k))%nat with (S (S (2 * Div2.div2 k))) by ring.
    by repeat apply le_n_S.

    apply is_lim_seq_mult'.
    apply filterlim_ext with (2:=Hla); apply sum_n_Reals.
    apply filterlim_ext with (2:=Hlb); apply sum_n_Reals.
    apply is_lim_seq_mult'.
    apply filterlim_ext with (2:=Hla); apply sum_n_Reals.
    apply filterlim_ext with (2:=Hlb); apply sum_n_Reals.
Qed.

Lemma is_series_mult (a b : nat -> R) (la lb : R) :
  is_series  a la -> is_series  b lb
  -> ex_series  (fun n => Rabs (a n)) -> ex_series  (fun n => Rabs (b n))
  -> is_series  (fun n => sum_f_R0 (fun k => a k * b (n - k)%nat) n) (la * lb).
Proof.
  move => Hla Hlb Ha Hb.

  set ap := fun n => (a n + Rabs (a n)) / 2.
  set am := fun n => - (a n - Rabs (a n)) / 2.
  set bp := fun n => (b n + Rabs (b n)) / 2.
  set bm := fun n => - (b n - Rabs (b n)) / 2.

  have Hap : forall n, 0 <= ap n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_0_l.
    apply Rabs_maj2.
    by apply Rlt_0_2.
  assert (Sap : ex_series  ap).
    apply ex_series_scal_r.
    apply (@ex_series_plus ) => //.
    by exists la.
  have Ham : forall n, 0 <= am n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Ropp_minus_distr'.
    apply (Rminus_le_0 (a _)).
    by apply Rle_abs.
    by apply Rlt_0_2.
  assert (Sam : ex_series  am).
    apply ex_series_scal_r.
    apply @ex_series_opp.
    apply @ex_series_minus => //.
    by exists la.
  have Hbp : forall n, 0 <= bp n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_0_l.
    apply Rabs_maj2.
    by apply Rlt_0_2.
  assert (Sbp : ex_series  bp).
    apply ex_series_scal_r.
    apply @ex_series_plus => //.
    by exists lb.
  have Hbm : forall n, 0 <= bm n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Ropp_minus_distr'.
    apply (Rminus_le_0 (b _)).
    by apply Rle_abs.
    by apply Rlt_0_2.
  assert (Sbm : ex_series  bm).
    apply ex_series_scal_r.
    apply @ex_series_opp.
    apply @ex_series_minus => //.
    by exists lb.

  apply is_series_ext with (fun n => sum_f_R0 (fun k : nat => ap k * bp (n - k)%nat) n
    - sum_f_R0 (fun k : nat => am k * bp (n - k)%nat) n
    - sum_f_R0 (fun k : nat => ap k * bm (n - k)%nat) n
    + sum_f_R0 (fun k : nat => am k * bm (n - k)%nat) n).
  move => n.
  rewrite -?minus_sum -plus_sum.
  apply sum_eq => k _.
  rewrite /ap /am /bp /bm ; field.
  replace (la*lb) with ((Series ap*Series bp-Series am*Series bp-Series ap*Series bm)+Series am*Series bm).
  apply @is_series_plus.
  apply @is_series_minus.
  apply @is_series_minus.
  apply is_series_mult_pos => // ; by apply Series_correct.
  apply is_series_mult_pos => // ; by apply Series_correct.
  apply is_series_mult_pos => // ; by apply Series_correct.
  apply is_series_mult_pos => // ; by apply Series_correct.
  replace (la) with (Series ap - Series am).
  replace (lb) with (Series bp - Series bm).
  ring.
  rewrite -Series_minus // -(is_series_unique _ _ Hlb) ; apply Series_ext => n.
  rewrite /ap /am /bp /bm ; field.
  rewrite -Series_minus // -(is_series_unique _ _ Hla) ; apply Series_ext => n.
  rewrite /ap /am /bp /bm ; field.
Qed.
*)

