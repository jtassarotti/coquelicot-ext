Require Import Reals ssreflect.
Require Import Coquelicot.

(** Exponential *)

Section INK.

Context {K : Ring}.

Fixpoint INK (n : nat) : K :=
  match n with
  | O => zero
  | S n => plus one (INK n)
  end.
Definition IZK (n : Z) : K :=
  match n with
  | 0%Z => zero
  | Z.pos n => INK (Pos.to_nat n)
  | Z.neg n => opp (INK (Pos.to_nat n))
  end.

End INK.

(* Search UniformSpace AbsRing.

Lemma ex_exp {K : AbsRing} {CK : @CompleteSpace.mixin_of (AbsRing_UniformSpace K)}
  (a : nat -> K) (x : K) :
  (forall k, mult (a k) (INK (fact k)) = one) ->
  ex_pseries a x.
Proof.
  intros Hfact.
  unfold ex_pseries, ex_series, is_series.
  assert (H := proj1 (filterlim_locally_cauchy (F := eventually) (sum_n (fun k : nat => scal (pow_n x k) (a k))))) ;
  destruct H as [l Hl].
  intros eps.
  rewrite /ball /=.
Qed.*)

Open Local Scope C_scope.

(** * New in Coquelicot *)

Definition C_RInt (f : R -> C) (a b : R) : C :=
  (RInt (fun t => fst (f t)) a b, RInt (fun t => snd (f t)) a b).

Lemma is_C_RInt_unique (f : R -> C) (a b : R) (l : C) :
  is_RInt f a b l -> C_RInt f a b = l.
Proof.
  intros Hf.
  apply RInt_fct_extend_pair with (3 := Hf).
  by apply is_RInt_unique.
  by apply is_RInt_unique.
Qed.
Lemma C_RInt_correct (f : R -> C) (a b : R) :
  ex_RInt f a b -> is_RInt f a b (C_RInt f a b).
Proof.
  case => l Hf.
  replace (C_RInt f a b) with l.
  by [].
  by apply sym_eq, is_C_RInt_unique.
Qed.

Lemma C_RInt_ext (f g : R -> C) (a b : R) :
  (forall x, Rmin a b <= x <= Rmax a b -> g x = f x)
    -> C_RInt g a b = C_RInt f a b.
Proof.
  intros Heq.
  apply injective_projections ; simpl ;
  apply RInt_ext => x Hx ; by rewrite Heq.
Qed.
Lemma C_RInt_swap (f : R -> C) (a b : R) :
  - C_RInt f a b = C_RInt f b a.
Proof.
  apply injective_projections ; simpl ;
  apply RInt_swap.
Qed.
Lemma C_RInt_scal_R (f : R -> C) (a b : R) (k : R) :
  C_RInt (fun t => scal k (f t)) a b = scal k (C_RInt f a b).
Proof.
  apply injective_projections ; simpl ;
  apply RInt_scal.
Qed.

Lemma is_C_RInt_scal f a b (k : C) l :
  is_RInt f a b l -> is_RInt (fun t => k * f t) a b (k * l).
Proof.
  intros H.
  move: (is_RInt_fct_extend_fst _ _ _ _ H) => /= H1.
  move: (is_RInt_fct_extend_snd _ _ _ _ H) => /= {H} H2.
  apply is_RInt_fct_extend_pair ; simpl.
  by apply: is_RInt_minus ; apply: is_RInt_scal.
  by apply: is_RInt_plus ; apply: is_RInt_scal.
Qed.

Lemma ex_C_RInt_scal f k a b :
  ex_RInt f a b -> ex_RInt (fun t => k * f t) a b.
Proof.
  intros [lf If].
  eexists.
  apply is_C_RInt_scal ; eassumption.
Qed.
Lemma C_RInt_scal (f : R -> C) (k : C) (a b : R) :
  ex_RInt f a b ->
  C_RInt (fun t => k * f t) a b = k * C_RInt f a b.
Proof.
  intros Hf.
  apply is_C_RInt_unique.
  apply is_C_RInt_scal.
  by apply C_RInt_correct.
Qed.
Lemma C_RInt_opp (f : R -> C) (a b : R) :
  C_RInt (fun t => - f t) a b = - C_RInt f a b.
Proof.
  apply injective_projections ; simpl ;
  apply RInt_opp.
Qed.
Lemma C_RInt_comp_lin (f : R -> C) (u v a b : R) :
  C_RInt (fun y : R => (u * f (u * y + v)%R)) a b =
     C_RInt f (u * a + v) (u * b + v).
Proof.
  apply injective_projections ; simpl ;
  rewrite -RInt_comp_lin ; apply RInt_ext => x _ ; ring.
Qed.
Lemma C_RInt_Chasles (f : R -> C) (a b c : R) :
  ex_RInt f a b -> ex_RInt f b c ->
  C_RInt f a b + C_RInt f b c =
     C_RInt f a c.
Proof.
  intros Hf1 Hf2.
  apply sym_eq, is_C_RInt_unique.
  apply C_RInt_correct in Hf1.
  apply C_RInt_correct in Hf2.

  move: (is_RInt_fct_extend_fst _ _ _ _ Hf1) => /= Hf1_1.
  move: (is_RInt_fct_extend_snd _ _ _ _ Hf1) => /= Hf1_2.
  move: (is_RInt_fct_extend_fst _ _ _ _ Hf2) => /= Hf2_1.
  move: (is_RInt_fct_extend_snd _ _ _ _ Hf2) => /= Hf2_2.
  now apply @is_RInt_Chasles with b ; apply is_RInt_fct_extend_pair.
Qed.

(** * Definition 2 *)

Definition complex_segment (a b : C) (z : C) :=
  exists (t : R), (0 <= t <= 1)%R /\ z = (1 - t) * a + t * b.

Definition is_C_RInt_segm f z1 z2 l :=
  is_RInt (fun t => (z2 - z1) * f ((1-t)*z1+t*z2)) 0 1 l.
Definition ex_C_RInt_segm (f : C -> C) (z1 z2 : C) :=
  exists l : C, is_C_RInt_segm f z1 z2 l.
Definition C_RInt_segm (f : C -> C) (z1 z2 : C) : C :=
  (z2 - z1) * C_RInt (fun t => f ((1 - t) * z1 + t * z2)) 0 1.

Lemma is_C_RInt_segm_unique (f : C -> C) (z1 z2 l : C) :
  is_C_RInt_segm f z1 z2 l -> C_RInt_segm f z1 z2 = l.
Proof.
  intros.
  unfold C_RInt_segm.
  rewrite -C_RInt_scal.
  by apply is_C_RInt_unique.
  case: (Ceq_dec z1 z2) => Hz.
  - rewrite Hz.
    apply ex_RInt_ext with (fun _ => f z2).
      move => x _.
      apply f_equal ; ring.
    apply ex_RInt_const.
  - eapply ex_RInt_ext.
    2: apply (fun f => ex_C_RInt_scal f (/(z2 - z1))).
    2: eexists ; apply H.
    simpl => x _.
    fold C.
    field.
    contradict Hz.
    replace z2 with (z1 + (z2 - z1)) by ring.
    rewrite Hz ; ring.
Qed.
Lemma C_RInt_segm_correct (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z1 z2 -> is_C_RInt_segm f z1 z2 (C_RInt_segm f z1 z2).
Proof.
  intros [l If].
  now rewrite (is_C_RInt_segm_unique _ _ _ _ If).
Qed.

(** * Proposition 3 *)

Lemma is_C_RInt_segm_swap (f : C -> C) (z1 z2 l : C) :
  is_C_RInt_segm f z2 z1 l -> is_C_RInt_segm f z1 z2 (-l).
Proof.
  rewrite /is_C_RInt_segm => H.
  evar (k : C).
  replace (- l) with k.
  apply is_RInt_swap.
  apply is_RInt_ext with (fun t : R => scal (-1)((z1 - z2) * f ((1 - (-1 * t + 1)%R) * z2 + (-1 * t + 1)%R * z1)%C)).
    move => x _.
    replace ((1 - (-1 * x + 1)%R) * z2 + (-1 * x + 1)%R * z1)
      with ((1 - x) * z1 + x * z2)
      by (apply injective_projections ; simpl ; ring).
    rewrite scal_opp_one.
    change opp with Copp.
    change eq with (@eq C).
    field.
  apply: (is_RInt_comp_lin (fun t : R => (z1 - z2) * f ((1 - t) * z2 + t * z1)) (-1) (1) 1 0).
  ring_simplify (-1 * 1 + 1)%R (-1 * 0 + 1)%R.
  apply H.
  by [].
Qed.
Lemma ex_C_RInt_segm_swap (f : C -> C) (z1 z2 : C) :
  ex_C_RInt_segm f z2 z1 -> ex_C_RInt_segm f z1 z2.
Proof.
  intros [l Hl].
  exists (-l) ; by apply is_C_RInt_segm_swap.
Qed.
Lemma C_RInt_segm_swap (f : C -> C) (z1 z2 : C) :
  - C_RInt_segm f z1 z2 = C_RInt_segm f z2 z1.
Proof.
  unfold C_RInt_segm.
  generalize (opp_mult_l (z2 - z1) (C_RInt (fun t : R => f ((1 - t) * z1 + t * z2)) 0 1)).
  rewrite /opp /mult /=.
  move => /= ->.
  apply f_equal2.
  apply injective_projections ; simpl ; ring.
  rewrite (C_RInt_ext (fun t : R => opp
    ((-1) * (f ((1 - (-1 * t + 1)%R) * z2 + (-1 * t + 1)%R * z1)%C)))).
  rewrite C_RInt_opp.
  rewrite C_RInt_swap.
  rewrite (C_RInt_comp_lin (fun t : R => f ((1 - t) * z2 + t * z1)) (-1) (1) 1 0) ;
  apply f_equal2 ; ring.
  intros x _ ; simpl.
  apply injective_projections ; simpl ; ring_simplify ;
  apply f_equal ; apply f_equal ;
  apply injective_projections ; simpl ; ring.
Qed.

Lemma scal_R_Cmult :
  forall (x : R) (y : C),
  scal (V := C_R_ModuleSpace) x y = Cmult x y.
Proof.
intros x y.
apply injective_projections ;
  rewrite /scal /= /scal /= /mult /= ; ring.
Qed.

Lemma is_C_RInt_segm_Chasles (f : C -> C) (z1 z2 z3 : C) l1 l2 :
  (exists p : R, z2 = ((1 - p) * z1 + p * z3))
  -> is_C_RInt_segm f z1 z2 l1 -> is_C_RInt_segm f z2 z3 l2
    -> is_C_RInt_segm f z1 z3 (plus l1 l2).
Proof.
  rewrite /is_C_RInt_segm ;
  case => p -> H1 H2.

  case: (Req_dec p 0) => Hp0.
  rewrite Hp0 in H1 H2 => {p Hp0}.
  apply (is_RInt_ext _ (fun t : R => (z3 - z1) * f ((1 - t) * z1 + t * z3))) in H2.
Focus 2.
  move => x _.
  replace ((1 - x) * ((1 - 0) * z1 + 0 * z3) + x * z3) with ((1 - x) * z1 + x * z3) by ring.
  change eq with (@eq C).
  ring.
  apply (is_RInt_ext _ (fun _ => zero)) in H1.
Focus 2.
  move => x _ ; simpl.
  change zero with (RtoC 0).
  change eq with (@eq C).
  ring.
  move: (is_RInt_plus _ _ _ _ _ _ H1 H2).
  apply is_RInt_ext.
  now move => x _ ; rewrite plus_zero_l.

  case: (Req_dec 1 p) => Hp1.
  rewrite -Hp1 in H1 H2 => {p Hp1 Hp0}.
  apply (is_RInt_ext _ (fun t : R => (z3 - z1) * f ((1 - t) * z1 + t * z3))) in H1.
Focus 2.
  move => x _.
  replace ((1 - x) * z1 + x * ((1 - 1) * z1 + 1 * z3)) with ((1 - x) * z1 + x * z3) by ring.
  change eq with (@eq C).
  ring.
  apply (is_RInt_ext _ (fun _ => zero)) in H2.
Focus 2.
  move => x _ ; simpl.
  change zero with (RtoC 0).
  change eq with (@eq C).
  ring.
  move: (is_RInt_plus _ _ _ _ _ _ H1 H2).
  apply is_RInt_ext.
  now move => x _ ; rewrite plus_zero_r.

  case: (Ceq_dec z1 z3) => Hz.
  rewrite -Hz in H1 H2 |- * => {z3 Hz}.
  move: (is_RInt_plus _ _ _ _ _ _ H1 H2).
    apply is_RInt_ext => x _.
    replace ((1 - x) * z1 + x * ((1 - p) * z1 + p * z1)) with z1 by ring.
    replace ((1 - x) * ((1 - p) * z1 + p * z1) + x * z1) with z1 by ring.
    replace ((1 - x) * z1 + x * z1) with z1 by ring.
    apply injective_projections ; rewrite /= /plus /= ; ring.

  apply (is_C_RInt_scal _ _ _ (/((1 - p) * z1 + p * z3 - z1))) in H1.
  apply (is_RInt_ext _ (fun t => ( (f ((1 - t) * z1 + t * ((1 - p) * z1 + p * z3)))))) in H1.
Focus 2.
  move => x _.
  change eq with (@eq C).
  field.
  replace (((1, 0) - p) * z1 + p * z3 - z1) with (p * (z3 - z1))
    by (apply injective_projections ; simpl ; ring).
  apply Cmult_neq_0.
  contradict Hp0.
  now apply (f_equal (@fst R R)) in Hp0 ; simpl in Hp0.
  now apply Cminus_eq_contra, sym_not_eq.
  apply (is_RInt_ext _ (fun t => opp (scal (-1)%R (f ((1 - t) * z1 + t * ((1 - p) * z1 + p * z3)))))) in H1.
Focus 2.
  intros x _.
  by rewrite scal_opp_one opp_opp.

  apply (is_C_RInt_scal _ _ _ (/(z3 - ((1 - p) * z1 + p * z3)))) in H2.
  apply (is_RInt_ext _ (fun t => f ((1 - t) * ((1 - p) * z1 + p * z3) + t * z3))) in H2.
Focus 2.
  move => x _.
  change eq with (@eq C).
  field.
  change (1, 0)%R with (RtoC 1).
  replace (z3 - ((1 - p) * z1 + p * z3)) with ((1-p) * (z3 - z1)) by ring.
  apply Cmult_neq_0.
  contradict Hp1.
  apply (f_equal (@fst R R)) in Hp1 ; simpl in Hp1.
  now apply Rminus_diag_uniq.
  now apply Cminus_eq_contra, sym_not_eq.
  apply (is_RInt_ext _ (fun t => opp (scal (-1)%R (f ((1 - t) * ((1 - p) * z1 + p * z3) + t * z3))))) in H2.
Focus 2.
  intros x _.
  by rewrite scal_opp_one opp_opp.

  evar (k : C).
  replace (plus l1 l2) with k.
  apply is_C_RInt_scal.

  apply is_RInt_Chasles with p.
  replace 0%R with (/p * 0 + 0)%R in H1 by ring.
  pattern 1%R at 4 in H1.
  replace 1%R with (/p * p + 0)%R in H1 by (by field).
  apply (is_RInt_comp_lin _ (/p) 0 0 p) in H1.
  apply (is_C_RInt_scal _ _ _ p) in H1.
  move: H1 ; apply is_RInt_ext => x Hx.
  replace ((1 - (/ p * x + 0)%R) * z1 + (/ p * x + 0)%R * ((1 - p) * z1 + p * z3))
    with ((1 - x) * z1 + x * z3).
  rewrite scal_opp_one opp_opp scal_R_Cmult.
  apply injective_projections ; simpl ; by field.
  apply injective_projections ; simpl ; by field.

  clear H1.
  replace 0%R with ((/(1-p)) * p + -/(1-p)*p)%R in H2 by ring.
  pattern 1%R at 6 in H2.
  replace 1%R with ((/(1-p)) * 1 + -/(1-p)*p)%R in H2 by
    (by field ; apply Rminus_eq_contra).
  apply (is_RInt_comp_lin _ (/(1-p)) (-/(1-p)*p) p 1) in H2.
  apply (is_C_RInt_scal _ _ _ (1-p)) in H2.
  move: H2 ; apply is_RInt_ext => x Hx.
  replace ((1 - (/ (1 - p) * x + - / (1 - p) * p)%R) * ((1 - p) * z1 + p * z3) +
      (/ (1 - p) * x + - / (1 - p) * p)%R * z3)
    with ((1 - x) * z1 + x * z3).
  rewrite scal_opp_one opp_opp scal_R_Cmult.
  now apply injective_projections ; simpl ; field ; apply Rminus_eq_contra.
  now apply injective_projections ; simpl ; field ; apply Rminus_eq_contra.

  unfold k ; change plus with Cplus.
  field.
  change (1, 0) with (RtoC 1).
  split.
  replace (z3 - ((1 - p) * z1 + p * z3)) with ((1 - p) * (z3 - z1)) by ring.
  apply Cmult_neq_0.
  apply Cminus_eq_contra.
  contradict Hp1 ; by apply RtoC_inj.
  by apply Cminus_eq_contra, sym_not_eq.
  replace ((1 - p) * z1 + p * z3 - z1) with (p * (z3 - z1)) by ring.
  apply Cmult_neq_0.
  contradict Hp0 ; by apply RtoC_inj.
  by apply Cminus_eq_contra, sym_not_eq.
Qed.
Lemma ex_C_RInt_segm_Chasles (f : C -> C) (z1 z2 z3 : C) :
  (exists p : R, z2 = ((1 - p) * z1 + p * z3))
  -> ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm f z2 z3
    -> ex_C_RInt_segm f z1 z3.
Proof.
  intros Hz2 [l1 H1] [l2 H2] ; exists (plus l1 l2) ;
  by apply is_C_RInt_segm_Chasles with z2.
Qed.
Lemma C_RInt_segm_Chasles (f : C -> C) (z1 z2 z3 : C) :
  (exists p : R, z2 = ((1 - p) * z1 + p * z3))
  -> ex_C_RInt_segm f z1 z2 -> ex_C_RInt_segm f z2 z3
  -> C_RInt_segm f z1 z2 + C_RInt_segm f z2 z3 = C_RInt_segm f z1 z3.
Proof.
  intros.
  apply sym_eq, is_C_RInt_segm_unique.
  now apply is_C_RInt_segm_Chasles with z2 ;
  try (by apply C_RInt_segm_correct).
Qed.

(** * Proposition 4 *)

Lemma prop4 (f : C -> C) (z1 z2 : C) lf (m : R) :
  is_C_RInt_segm f z1 z2 lf
  -> (forall z, complex_segment z1 z2 z ->  Cmod (f z) <= m)
  -> Cmod lf <= m * (Cmod (z1 - z2)).
Proof.
  intros Cf Hm.
  rewrite 2!Cmod_norm.
  apply: (RInt_norm (fun t => (z2 - z1) * f ((1 - t) * z1 + t * z2)) (fun _ => Rmult (Cmod (z2 - z1)) m) 0 1).
  by apply Rle_0_1.
  intros x Hx.
  rewrite <- Cmod_norm.
  rewrite Cmod_mult.
  apply Rmult_le_compat_l.
  by apply Cmod_ge_0.
  apply Hm.
  now exists x ; split.
  by apply Cf.
  replace (m * _)%R
    with (scal (1 - 0)%R (Cmod (z2 - z1)%C * m)%R).
  apply: is_RInt_const.
  rewrite -Cmod_norm -Cmod_opp Copp_minus_distr ; simpl.
  rewrite /scal /= /mult /=.
  ring.
Qed.

(** * Proposition 5 *)

(* Lemma completeness_any_2 : forall (P : R -> R -> Prop),
  (forall a, P a a) ->
  (forall a b, P a b -> P b a) ->
  (forall a b c, a <= b <= c -> P a b -> P b c -> P a c) ->
  (forall a b c, a <= b <= c -> P a c -> P a b) ->
  (forall a, locally a (P a))
  -> forall (a b : R), ~ ~ P a b.
Proof.
  intros P Hpoint Hswap Hchasles Hchasles' Hloc a b.
  wlog: a b / (a <= b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    specialize (Hw _ _ (Rlt_le _ _ Hab)).
    contradict Hw.
    contradict Hw.
    by apply Hswap.
  set (P' := fun c => c <= b /\ P a (Rmax a c)).
  assert (He : exists x : R, P' x).
    exists a ; split ; intuition.
    now rewrite /Rmax ; case: Rle_dec (Rle_refl a).
  assert (Hb : bound P').
    exists b => x Hx ; by apply Hx.
  assert (Hincr : forall x y : R, x <= y -> P' y -> P' x).
    intros x y Hxy Py ; split.
    by eapply Rle_trans, Py.
    eapply Hchasles', Py.
    split.
    by apply Rmax_l.
    by apply Rle_max_compat_l.
  move: (completeness_any P' Hincr He Hb).
  destruct completeness as [c Hc] => /= Hc'.
  assert (~ ~ P' c).
    destruct (Hloc (Rmax a c)) as [d Hd].
    set y := (c - d / 2)%R.
    assert (y < c).
      unfold y ; apply Rminus_lt_0 ; ring_simplify.
      by apply is_pos_div_2.
    specialize (Hc' _ H) ; clear H.
    contradict Hc' ; contradict Hc'.
    split.
    apply Hc => x Hx ; by apply Hx.
    assert (y < c).
      unfold y ; apply Rminus_lt_0 ; ring_simplify.
      by apply is_pos_div_2.
    assert (Rmax a y <= Rmax a c).
      apply Rle_max_compat_l.
      by apply Rlt_le.
    eapply Hchasles.
    2: apply Hc'.
    split.
    by apply Rmax_l.
    by [].
    apply Hswap, Hd.
    apply Rle_lt_trans with (c - y)%R ; simpl.
    rewrite /abs /minus /plus /opp /= -Rabs_Ropp Rabs_pos_eq ; ring_simplify.
    rewrite Rplus_comm.
    rewrite /Rmax ; case: Rle_dec => H1 ; case: Rle_dec => H2.
    by apply Rle_refl.
    by apply Rplus_le_compat_l, Ropp_le_contravar, Rlt_le, Rnot_le_lt.
    contradict H1.
    eapply Rle_trans, Rlt_le, H.
    by apply H2.
    now ring_simplify ; apply Rlt_le ; apply -> Rminus_lt_0.
    now rewrite Rplus_comm ; apply -> Rminus_le_0.
    rewrite (double_var d) /y ; apply Rminus_lt_0 ; ring_simplify.
    by apply is_pos_div_2.
    clear Hc' ; rename H into Hc'.
  replace b with c.
  contradict Hc' ; contradict Hc'.
  unfold P' in Hc'.
  replace c with (Rmax a c).
  by apply Hc'.
  apply Rmax_right.
  apply Hc ; split.
  by [].
  rewrite /Rmax ; by case: Rle_dec (Rle_refl a).
  apply Rle_antisym.
  apply Hc => x Hx ; by apply Hx.
  apply Rnot_lt_le => H.
  destruct (Hloc (Rmax a c)) as [d Hd].
  assert (Heps : 0 < Rmin (b - c) (d / 2)).
    apply Rmin_case.
    by apply Rminus_lt_0 in H.
    by apply is_pos_div_2.
  set eps := mkposreal _ Heps.
  set y := (c + eps)%R.
  absurd (y <= c).
  - apply Rlt_not_le, Rminus_lt_0.
    rewrite /y ; ring_simplify.
    by apply eps.
  - apply Hc ; split.
    rewrite /y /= Rplus_min_distr_l.
    eapply Rle_trans.
    apply Rmin_l.
    apply Req_le ; ring.
    assert (c < y).
      unfold y ; apply Rminus_lt_0 ; ring_simplify.
      by apply eps.
    assert (Rmax a c <= Rmax a y).
      apply Rle_max_compat_l.
      by apply Rlt_le.
    eapply Hchasles.
    (** use [Classical_Prop.classic] *)
    2: apply Classical_Prop.NNPP in Hc'.
    2: apply Hc'.
    split.
    apply Rmax_l.
    by apply H1.
    apply Hd ; simpl.
    rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
    rewrite Rabs_pos_eq.
    apply Rle_lt_trans with (y - c)%R.
    rewrite /Rmax ; case: Rle_dec => H2 ; case: Rle_dec => H3.
    by apply Rle_refl.
    by apply Rplus_le_compat_l, Ropp_le_contravar, Rlt_le, Rnot_le_lt.
    contradict H2.
    eapply Rle_trans, Rlt_le, H0.
    by apply H3.
    now ring_simplify ; apply Rlt_le ; apply -> Rminus_lt_0.
    apply Rle_lt_trans with eps.
    unfold y ; apply Req_le ; ring.
    rewrite (double_var d).
    eapply Rle_lt_trans.
    by apply Rmin_r.
    apply Rminus_lt_0 ; ring_simplify.
    by apply is_pos_div_2.
    by apply Rminus_le_0 in H1.
Qed. *)

Definition continuous {U V : UniformSpace} (f : U -> V) (x : U) :=
  filterlim f (locally x) (locally (f x)).

Section UnifCont.

Context {V : UniformSpace}.


Lemma unifcont_1d (f : R -> V) a b :
  (forall x, a <= x <= b -> continuous f x) ->
  forall eps : posreal, {delta : posreal | forall x y, 
    a <= x <= b -> a <= y <= b -> ball x delta y -> ~~ ball (f x) eps (f y)}.
Proof.
  intros Cf eps.
  wlog: f Cf / (forall z : R, continuous f z) => [ Hw | {Cf} Cf ].
    destruct (C0_extension_le f a b) as [g [Cg Hg]].
    by apply Cf.
    destruct (Hw g) as [d Hd].
    intros x Hx ; apply Cg.
    apply Cg.
    exists d => x y Hx Hy Hxy.
    rewrite -!Hg //.
    by apply Hd.

  assert (forall (x : R), {delta : posreal | forall y : R,
    ball x delta y -> ~~ ball (f x) (pos_div_2 eps) (f y)}).
    move: (pos_div_2 eps) => {eps} eps x.
    assert (exists d : R, forall y : R, ball x d y -> ball (f x) eps (f y)).
      case: (proj1 (filterlim_locally _ _) (Cf x) eps) => d Hd.
      exists d.
      by apply Hd.
    assert (Rbar_lt 0 (Lub_Rbar_ne _ H)).
      case: (Lub_Rbar_ne_correct _ H).
      move: (Lub_Rbar_ne _ _) => {H} l H1 H2.
      case: (proj1 (filterlim_locally _ _) (Cf x) eps) => d Hd.
      eapply Rbar_lt_le_trans, H1.
      by apply d.
      by apply Hd.
    assert (0 < Rbar_min 1 (Lub_Rbar_ne _ H)).
      move: H0 ; case: (Lub_Rbar_ne _ _) => [l | | ] //= H0.
      apply Rbar_min_case => //.
      by apply Rlt_0_1.
      unfold Rbar_min ; case: Rbar_le_dec => //= _.
      by apply Rlt_0_1.
    set d := mkposreal _ H1.
    exists d.
    unfold d ; clear d ; simpl.
    case: (Lub_Rbar_ne_correct _ H).
    move: (Lub_Rbar_ne _ _) H0 => {H H1} l H0 H1 H2 y Hy.
    contradict Hy.
    apply Rle_not_lt.
    apply (Rbar_le_trans (Finite _) l (Finite _)).
    case: (l) H0 => [r | | ] //= H0.
    rewrite Rbar_finite_min /=.
    apply Rmin_r.
    apply H2 => d /= Hd.
    apply Rnot_lt_le ; contradict Hy.
    by apply Hd.
  destruct (compactness_value_1d a b (fun x => pos_div_2 (projT1 (H x)))) as [d Hd].
  exists d => x y Hx Hy Hxy Hf.
  apply (Hd x Hx).
  case => {Hd} t [Ht].
  case: H => /= delta Hdelta [Htx Hdt].
  apply (Hdelta x).
    eapply ball_le, Htx.
    rewrite {2}(double_var delta).
    apply Rminus_le_0 ; ring_simplify.
    apply Rlt_le, is_pos_div_2.
  intro Hftx.
  apply (Hdelta y).
    rewrite (double_var delta).
    apply ball_triangle with x.
    apply Htx.
    by eapply ball_le, Hxy.
  contradict Hf.
  rewrite (double_var eps).
  eapply ball_triangle, Hf.
  by apply ball_sym.
Qed.

End UnifCont.

Require Import seq.

Lemma unif_part_S a b n :
  unif_part a b (S n) = a :: unif_part ((a * INR (S n) + b) / INR (S (S n))) b n.
Proof.
  apply eq_from_nth with 0.
  by rewrite /= !size_map !size_iota.
  case => [ | i] Hi.
  rewrite /= /Rdiv ; ring.
  replace (nth 0 (a :: unif_part ((a * INR (S n) + b) / INR (S (S n))) b n) (S i))
    with (nth 0 (unif_part ((a * INR (S n) + b) / INR (S (S n))) b n) i) by auto.
  rewrite /unif_part size_mkseq in Hi.
  rewrite /unif_part !nth_mkseq ; try by intuition.
  rewrite !S_INR ; field.
  rewrite -!S_INR ; split ; apply sym_not_eq, (not_INR 0), O_S.
Qed.

Lemma minus_trans {G : AbelianGroup} (r x y : G) :
  minus x y = plus (minus x r) (minus r y).
Proof.
  rewrite /minus -!plus_assoc.
  apply f_equal.
  by rewrite plus_assoc plus_opp_l plus_zero_l.
Qed.
Lemma ptd_f2 (f : R -> R -> R) s :
  sorted Rle s -> (forall x y, x <= y -> x <= f x y <= y)
  -> pointed_subdiv (SF_seq_f2 f s).
Proof.
  intros Hs Hf.
  elim: s Hs => [ _ | h s].
  intros i Hi.
  by apply lt_n_O in Hi.
  case: s => [ | h' s] IH Hs.
  intros i Hi.
  by apply lt_n_O in Hi.
  case => [ | i] Hi.
  apply Hf, Hs.
  apply IH.
  apply Hs.
  by apply lt_S_n.
Qed.

Section Prop5_RInt.

Context {V : CompleteNormedModule R_AbsRing}.

Lemma cont_ex_RInt (f : R -> V) (a b : R) :
  (forall z, Rmin a b <= z <= Rmax a b -> continuous f z)
  -> ex_RInt f a b.
Proof.
  wlog: f / (forall z : R, continuous f z) => [ Hw Cf | Cf _ ].
    destruct (C0_extension_le f (Rmin a b) (Rmax a b)) as [g [Cg Hg]].
    by apply Cf.
    apply ex_RInt_ext with g.
    intros x Hx ; apply Hg ; split ; apply Rlt_le ; apply Hx.
    apply Hw => // z _ ; by apply Cg.

  wlog: a b / (a < b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.
    rewrite Hab ; by apply ex_RInt_point.
    apply ex_RInt_swap.
    by apply Hw.

  assert (H := unifcont_1d f a b (fun x Hx => Cf x)).

  set n := fun eps => projT1 (seq_step_unif_part_ex a b (projT1 (H eps))).
  set s := fun eps => (SF_seq_f2 (fun x y => ((x+y)/2)%R) (unif_part a b (n eps))).
  set (f_eps := fun eps => fun x => match (Rle_dec a x) with
    | left _ => match (Rle_dec x b) with
       | left _ => SF_fun (SF_map f (s eps)) zero x
       | right _ => f x
       end
     | right _ => f x
     end).
  set F := fun (P : posreal -> Prop) => exists eps : posreal, forall x : posreal,
    x < eps -> P x.
  set If_eps := fun eps => Riemann_sum f (s eps).
  
  assert (FF : ProperFilter F).
  - assert (forall P, F P <-> at_right 0 (fun x => 0 < x /\ forall Hx, P (mkposreal x Hx))).
      split ; intros [e He].
      exists e => y Hy H0 ; split => //.
      move => {H0} H0.
      apply He.
      eapply Rle_lt_trans, Hy.
      rewrite minus_zero_r.
      by apply Req_le, sym_eq, Rabs_pos_eq, Rlt_le.
      exists e ; intros [ y H0] Hy.
      apply He.
      apply Rabs_lt_between.
      rewrite minus_zero_r ; split.
      eapply Rlt_trans, H0.
      rewrite -Ropp_0 ; apply Ropp_lt_contravar, e.
      by apply Hy.
      by apply H0.
    case: (at_right_proper_filter 0) => H1 H2.
    split.
    + intros P HP.
      apply H0 in HP.
      destruct (H1 _ HP) as [x [Hx Px]].
      by exists (mkposreal x Hx).
      destruct H2 ; split.
    + by exists (mkposreal _ Rlt_0_1).
    + intros.
      apply H0.
      eapply filter_imp.
      2: apply filter_and ; apply H0.
      2: apply H2.
      2: apply H3.
      intuition ; apply H4.
    + intros.
      apply H0.
      eapply filter_imp.
      2: apply H0 ; apply H3.
      intuition.
      by apply H4.
      by apply H2, H4.
  assert (Ha : forall eps, a = (SF_h (s eps))).
    intros eps ; simpl.
    rewrite /Rdiv ; ring.
  assert (Hb : forall eps, b = (last (SF_h (s eps)) (unzip1 (SF_t (s eps))))).
    intros eps.
    rewrite -(last_unif_part 0 a b (n eps)) ; simpl.
    apply f_equal.
    elim: {2 4}(n eps) (a + 1 * (b - a) / (INR (n eps) + 1))%R (2%nat) => [ | m IH] //= x0 k.
    by rewrite -IH.
  destruct (filterlim_RInt f_eps a b F FF f If_eps) as [If HI].
  - intros eps.
    rewrite (Ha eps) (Hb eps).
    eapply is_RInt_ext.
    2: apply (is_RInt_SF f (s eps)).
    rewrite -Hb -Ha.
    rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x [Hax Hxb].
    rewrite /f_eps.
    case: Rle_dec (Rlt_le _ _ Hax) => // _ _.
    case: Rle_dec (Rlt_le _ _ Hxb) => // _ _.
    rewrite /s /SF_sorted SF_lx_f2.
    by apply unif_part_sort, Rlt_le.
    by apply lt_O_Sn.
  - apply (filterlim_locally f_eps) => /= eps.
    rewrite /ball /= /fct_ball.
    eapply filter_imp.
    intros x Hx t.
    apply (norm_compat1 (f t) (f_eps x t) eps).
    move: t ; by apply Hx.
    destruct (norm_compat2 (V := V)) as [M HM].
    assert (0 < eps / M).
      apply Rdiv_lt_0_compat ; apply cond_pos.
    destruct (H (mkposreal _ H0)) as [d Hd].
    exists d => e He t.
    rewrite /f_eps.
    case: Rle_dec => Hat.
    case: Rle_dec => Hta.
    rewrite SF_fun_incr.
    rewrite SF_map_lx SF_lx_f2.
    by apply unif_part_sort, Rlt_le.
    by apply lt_O_Sn.
    rewrite SF_map_lx SF_lx_f2.
    rewrite last_unif_part head_unif_part.
    by split.
    by apply lt_O_Sn.
    intros Hsort Ht.
    case: sorted_dec.
    rewrite SF_map_lx SF_lx_f2.
    replace (head 0 (unif_part a b (n e)) :: behead (unif_part a b (n e)))
      with (unif_part a b (n e)) by auto.
    intros i.
    rewrite SF_map_ly (nth_map 0).
    apply Rnot_le_lt => H1.
    apply (Hd (nth 0 (SF_ly (s e)) (projT1 i)) t).
    split ; eapply Rle_trans.
    2: apply ptd_f2.
    rewrite SF_lx_f2 {1}(Ha e).
    apply sorted_head.
    apply unif_part_sort.
    by apply Rlt_le.
    eapply lt_trans, (projT2 i).
    eapply lt_trans ; apply lt_n_Sn.
    by apply lt_O_Sn.
    by apply unif_part_sort, Rlt_le.
    intros x y Hxy.
    pattern y at 3 ;
    replace y with ((y+y)/2)%R by field.
    pattern x at 1 ;
    replace x with ((x+x)/2)%R by field.
    split ; apply Rmult_le_compat_r ; intuition.
    rewrite SF_size_f2.
    move: (proj2 (projT2 i)).
    case: (size (unif_part a b (n e))) (projT1 i) => [ | m] /= k Hk.
    by apply lt_n_O in Hk.
    apply lt_S_n.
    eapply lt_trans, Hk.
    by apply lt_n_Sn.
    apply ptd_f2.
    by apply unif_part_sort, Rlt_le.
    intros x y Hxy.
    pattern y at 3 ;
    replace y with ((y+y)/2)%R by field.
    pattern x at 1 ;
    replace x with ((x+x)/2)%R by field.
    split ; apply Rmult_le_compat_r ; intuition.
    rewrite SF_size_f2.
    move: (proj2 (projT2 i)).
    case: (size (unif_part a b (n e))) (projT1 i) => [ | m] /= k Hk.
    by apply lt_n_O in Hk.
    apply lt_S_n.
    eapply lt_trans, Hk.
    by apply lt_n_Sn.
    rewrite SF_lx_f2 ; try by apply lt_O_Sn.
    rewrite {8}(Hb e).
    eapply Rle_trans, (sorted_last _ (projT1 i)).
    apply Req_le.
    unfold s ; simpl.
    elim: {1 3 6}(n e) (2%nat) (a + 1 * (b - a) / (INR (n e) + 1))%R (projT1 i) (proj2 (projT2 i)) => [ | m IH] // k x0 j Hj.
    simpl in Hj ;
    by apply lt_S_n, lt_S_n, lt_n_O in Hj.
    case: j Hj => [ | j] Hj //=.
    rewrite -IH //.
    apply lt_S_n.
    rewrite size_mkseq.
    by rewrite size_mkseq in Hj.
    move: (unif_part_sort a b (n e) (Rlt_le _ _ Hab)).
    unfold s.
    elim: (unif_part a b (n e)) => [ | h] //=.
    
  admit.
  now exists If.
Admitted.


Lemma prop5_R (f g : R -> V) (a b : R) :
  (forall z, Rmin a b <= z <= Rmax a b -> filterdiff g (locally z) (fun y => scal y (f z)))
  -> (forall z, Rmin a b <= z <= Rmax a b -> continuous f z)
  -> is_RInt f a b (minus (g b) (g a)).
Proof.
Admitted.

End Prop5_RInt.

Lemma filterdiff_R2_C (f : C -> C) (z : C) (l : C) :
  is_C_derive f z l -> filterdiff (V := C_R_NormedModule) f (locally z) (fun z : C => scal z l).
Admitted.

Lemma C_complete :
  forall F : (C -> Prop) -> Prop,
  ProperFilter F -> cauchy F ->
  {x : C | forall eps : posreal, F (ball x eps)}.
Proof.
  intros.

  set (F1 := fun (P : R -> Prop) => exists Q, F Q /\ forall z : C, Q z -> P (fst z)).
  destruct (complete_cauchy F1) as [x Hx].
  repeat split.
  - intros P [Q [HQ HP]].
    destruct (filter_ex Q HQ).
    exists (fst x).
    by apply HP.
  - exists (fun _ => True) ; split => //.
    by apply filter_forall.
  - intros P1 P2 [Q1 [HQ1 HP1]] [Q2 [HQ2 HP2]].
    exists (fun x => Q1 x /\ Q2 x) ; split.
    by apply filter_and.
    split ; intuition.
  - intros P1 P2 H1 [Q1 [HQ1 HP1]].
    exists Q1 ; split ; intuition.
  - intros eps.
    destruct (H0 eps).
    exists (fst x).
    eexists ; split.
    apply H1.
    simpl ; intros.
    by apply H2.

  set (F2 := fun (P : R -> Prop) => exists Q, F Q /\ forall z : C, Q z -> P (snd z)).
  destruct (complete_cauchy F2) as [y Hy].
  repeat split.
  - intros P [Q [HQ HP]].
    destruct (filter_ex Q HQ).
    exists (snd x0).
    by apply HP.
  - exists (fun _ => True) ; split => //.
    by apply filter_forall.
  - intros P1 P2 [Q1 [HQ1 HP1]] [Q2 [HQ2 HP2]].
    exists (fun x => Q1 x /\ Q2 x) ; split.
    by apply filter_and.
    split ; intuition.
  - intros P1 P2 H1 [Q1 [HQ1 HP1]].
    exists Q1 ; split ; intuition.
  - intros eps.
    destruct (H0 eps).
    exists (snd x0).
    eexists ; split.
    apply H1.
    simpl ; intros.
    by apply H2.

  exists (x,y) => eps.
  destruct (Hx eps) as [Qx [HQx HPx]].
  destruct (Hy eps) as [Qy [HQy HPy]].
  generalize (filter_and _ _ HQx HQy).
  apply filter_imp => z [Qxz Qyz].
  split.
  by apply HPx.
  by apply HPy.
Qed.

Definition C_CompleteSpace_mixin :=
  CompleteSpace.Mixin C_UniformSpace C_complete.

Canonical C_CompleteSpace :=
  CompleteSpace.Pack C (CompleteSpace.Class _ _ C_CompleteSpace_mixin) C.

Canonical C_R_CompleteNormedModule :=
  CompleteNormedModule.Pack R_AbsRing C (CompleteNormedModule.Class _ _ (NormedModule.class _ C_R_NormedModule) (CompleteSpace.class C_CompleteSpace)) C.

Lemma prop5 (f g : C -> C) (z1 z2 : C) :
  (forall z, is_C_derive g z (f z))
  -> (forall z, filterlim f (locally z) (locally (f z)))
  -> is_C_RInt_segm f z1 z2 (g z2 - g z1).
Proof.
  intros Dg Cf.
  unfold is_C_RInt_segm.
    replace (g z2 - g z1)
      with (minus (g ((1 - 1) * z1 + 1 * z2)) (g ((1 - 0) * z1 + 0 * z2))).
    2: simpl ; congr (g _- g _) ; ring.
    apply (prop5_R (fun t : R => (z2 - z1) * f ((1 - t) * z1 + t * z2)) (fun t => g ((1 - t) * z1 + t * z2)) 0 1).
    + intros z Hz.
      eapply filterdiff_ext_lin.
      apply (filterdiff_comp (fun t : R => (1 - t) * z1 + t * z2) g (fun y : R => scal y (z2 - z1)) (fun t : C => scal t (f ((1 - z) * z1 + z * z2)))).
      apply filterdiff_ext with (fun t : R => z1 + scal t (z2 - z1)).
      simpl => y.
      rewrite scal_R_Cmult.
      change eq with (@eq C).
      ring.
      apply filterdiff_ext_lin with (fun y : R => plus zero (scal y (z2 - z1))).
      apply: filterdiff_plus_fct.
      apply: filterdiff_const.
      apply filterdiff_linear.
      by apply: is_linear_scal_l.
      simpl => y.
      by apply plus_zero_l.
      unfold is_C_derive in Dg.
      destruct (Dg ((1 - z) * z1 + z * z2)) as [Lf Dg'].
      apply filterdiff_locally with ((1 - z) * z1 + z * z2).
      apply (is_filter_lim_filtermap _ _ (fun t : R => (1 - t) * z1 + t * z2)).
      admit.
      now intros P HP.
      apply (filterdiff_R2_C g ((1 - z) * z1 + z * z2) (f ((1 - z) * z1 + z * z2))).
      apply (Dg ((1 - z) * z1 + z * z2)).
      simpl => y.
      rewrite !scal_R_Cmult.
      apply sym_eq, Cmult_assoc.

  admit.
Qed.

Require Import seq.

Lemma ex_RInt_norm {V : CompleteNormedModule R_AbsRing} (f : R -> V) (a b : R) :
  ex_RInt f a b -> ex_RInt (fun x => norm (f x)) a b.
Proof.
  wlog: a b / (a <= b) => [Hw | Hab] Hf.
    case: (Rle_lt_dec a b) => Hab.
    by apply Hw.
    apply ex_RInt_swap in Hf ; apply ex_RInt_swap.
    apply Hw.
    by apply Rlt_le.
    by [].
  destruct (ex_RInt_ub f a b Hf) as [Mf Hm].
  move: Hm ; rewrite /Rmin /Rmax ; case: Rle_dec => //= _ Hm.
  case: Hab => Hab.
  destruct (proj1 (filterlim_locally_cauchy (fun ptd : SF_seq =>
     scal (sign (b - a)) (Riemann_sum (fun x : R => norm (f x)) ptd))
     (F := Riemann_fine a b))) ; [ | exists x ; by apply H].

  simpl ; intros.

Admitted.