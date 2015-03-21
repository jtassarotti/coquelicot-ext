Require Import Reals Ssreflect.ssreflect.
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

Lemma is_C_RInt_segm_norm (f : C -> C) (z1 z2 : C) lf (m : R) :
  is_C_RInt_segm f z1 z2 lf
  -> (forall z, complex_segment z1 z2 z ->  Cmod (f z) <= m)
  -> Cmod lf <= m * (Cmod (z1 - z2)).
Proof.
  intros Cf Hm.
  rewrite 2!Cmod_norm.
  apply: (norm_RInt_le (fun t => (z2 - z1) * f ((1 - t) * z1 + t * z2)) (fun _ => Rmult (Cmod (z2 - z1)) m) 0 1).
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
Lemma C_RInt_segm_norm f z1 z2 m :
  ex_C_RInt_segm f z1 z2
  -> (forall z, complex_segment z1 z2 z ->  Cmod (f z) <= m)
  -> Cmod (C_RInt_segm f z1 z2) <= m * (Cmod (z1 - z2)).
Proof.
  intros.
  apply is_C_RInt_segm_norm with f.
  by apply C_RInt_segm_correct.
  by [].
Qed.

(** * Proposition 5 *)

Lemma RtoC_plus (x y : R) :
  RtoC (x + y) = RtoC x + RtoC y.
Proof.
  unfold RtoC, Cplus ; simpl.
  by rewrite Rplus_0_r.
Qed.
Lemma RtoC_opp (x : R) :
  RtoC (- x) = - RtoC x.
Proof.
  unfold RtoC, Copp ; simpl.
  by rewrite Ropp_0.
Qed.
Lemma RtoC_minus (x y : R) :
  RtoC (x - y) = RtoC x - RtoC y.
Proof.
  by rewrite /Cminus -RtoC_opp -RtoC_plus.
Qed.
Lemma RtoC_mult (x y : R) :
  RtoC (x * y) = RtoC x * RtoC y.
Proof.
  unfold RtoC, Cmult ; simpl.
  apply injective_projections ; simpl ; ring.
Qed.

Lemma is_linear_ext {K : AbsRing} {U V : NormedModule K} (l1 l2 : U -> V) :
  (forall x, l1 x = l2 x) -> is_linear l1 -> is_linear l2.
Proof.
  intros Hl Hl1.
  split.
  intros ; rewrite -!Hl ; apply Hl1.
  intros ; rewrite -!Hl ; apply Hl1.
  case: Hl1 => _ _ [M Hl1].
  exists M ; split.
  by apply Hl1.
  intros ; rewrite -!Hl ; apply Hl1.
Qed.

Lemma is_linear_C_R (l : C -> C) :
  is_linear (U := C_NormedModule) (V := C_NormedModule) l ->
  is_linear (U := C_R_NormedModule) (V := C_R_NormedModule) l.
Proof.
  intros Lf.
  split.
  intros ; apply Lf.
  simpl ; intros.
  rewrite !scal_R_Cmult ; by apply Lf.
  case: Lf => _ _ [M Lf].
  exists M ; split.
  by apply Lf.
  intros.
  rewrite -!Cmod_norm.
  apply Lf.
Qed.

Lemma is_C_derive_filterdiff f x df:
  is_C_derive f x df
  -> filterdiff (U := C_R_NormedModule) (V := C_R_NormedModule) f (locally x) (fun u => scal u df).
Proof.
  case => Lf Hf.
  split.
  by apply is_linear_C_R.
  intros y Hy.
  apply Hf in Hy => {Hf}.
  intros eps.
  case: (Hy eps) => {Hy} /= delta Hy.
  assert (Hd : 0 < delta / sqrt 2).
    apply Rdiv_lt_0_compat.
    by apply delta.
    apply sqrt_lt_R0, Rlt_0_2.
  eexists (mkposreal _ Hd) => /= z [Hz1 Hz2].
  rewrite -!Cmod_norm.
  apply Hy.
  apply C_NormedModule_mixin_compat1.
  eapply Rle_lt_trans.
  apply Cmod_2Rmax.
  apply Rmax_case ; rewrite Rmult_comm ; apply Rlt_div_r.
  apply sqrt_lt_R0, Rlt_0_2.
  apply Hz1.
  apply sqrt_lt_R0, Rlt_0_2.
  apply Hz2.
Qed.

Lemma is_derive_RInt_0 {V : NormedModule R_AbsRing} (f If : R -> V) (x : R) :
  locally x (fun b => is_RInt f x b (If b))
  -> continuous f x
  -> is_derive If x (f x).
Proof.
  intros HIf Hf.
  split ; simpl.
  apply is_linear_scal_l.
  intros y Hy.
  apply @is_filter_lim_locally_unique in Hy.
  rewrite -Hy {y Hy}.
  intros eps.
  generalize (proj1 (filterlim_locally _ _) Hf) => {Hf} Hf.
  eapply filter_imp.
  simpl ; intros y Hy.
  replace (If x) with (@zero V).
  rewrite @minus_zero_r.
  rewrite Rmult_comm ; eapply norm_RInt_le_const_abs ; last first.
  apply is_RInt_minus.
  instantiate (1 := f).
  eapply (proj1 Hy).
  apply is_RInt_const.
  simpl.
  apply (proj2 Hy).
  apply locally_singleton in HIf.
  set (HIf_0 := is_RInt_point f x).
  apply (filterlim_locally_unique _ _ _ HIf_0 HIf).

  apply filter_and.
  by apply HIf.
  assert (0 < eps / @norm_factor _ V).
    apply Rdiv_lt_0_compat.
    by apply eps.
    by apply norm_factor_gt_0.
  case: (Hf (mkposreal _ H)) => {Hf} delta Hf.
  exists delta ; intros y Hy z Hz.
  eapply Rle_trans.
  apply Rlt_le, norm_compat2.
  apply Hf.
  apply Rabs_lt_between'.
  move/Rabs_lt_between': Hy => Hy.
  rewrite /Rmin /Rmax in Hz ; destruct (Rle_dec x y) as [Hxy | Hxy].
  split.
  eapply Rlt_le_trans, Hz.
  apply Rminus_lt_0 ; ring_simplify.
  by apply delta.
  eapply Rle_lt_trans, Hy.
  by apply Hz.
  split.
  eapply Rlt_le_trans, Hz.
  by apply Hy.
  eapply Rle_lt_trans.
  apply Hz.
  apply Rminus_lt_0 ; ring_simplify.
  by apply delta.
  simpl ; apply Req_le.
  field.
  apply Rgt_not_eq, norm_factor_gt_0.
Qed.
Lemma is_derive_RInt {V : NormedModule R_AbsRing} (f If : R -> V) (a x : R) :
  locally x (fun b => is_RInt f a b (If b))
  -> continuous f x
  -> is_derive If x (f x).
Proof.
  intros HIf Hf.
  apply is_derive_ext with (fun y => (plus (minus (If y) (If x)) (If x))).
  simpl ; intros.
  rewrite /minus -plus_assoc plus_opp_l.
  by apply plus_zero_r.
  evar_last.
  apply is_derive_plus.
  apply is_derive_RInt_0.
  2: apply Hf.
  eapply filter_imp.
  intros y Hy.
  evar_last.
  apply is_RInt_Chasles with a.
  apply is_RInt_swap.
  3: by apply plus_comm.
  by apply locally_singleton in HIf.
  by apply Hy.
  by apply HIf.
  apply is_derive_const.
  by apply plus_zero_r.
Qed.

Lemma MVT (f g : R -> R) (a b : R) (df dg : R -> R) :
  (forall c : R, a < c < b -> is_derive f c (df c)) ->
  (forall c : R, a < c < b -> is_derive g c (dg c)) ->
  a < b ->
  (forall c : R, a <= c <= b -> continuous f c) ->
  (forall c : R, a <= c <= b -> continuous g c) ->
  exists (c : R) (P : a < c < b),
    ((g b - g a) * df c = (f b - f a) * dg c)%R.
Proof. (** depend of Reals *)
  intros Df Dg Hab Cf Cg.
  assert (pr1 : forall c : R, a < c < b -> derivable_pt f c).
    intros ; eexists ; by apply is_derive_Reals, Df.
  assert (pr2 : forall c : R, a < c < b -> derivable_pt g c).
    intros ; eexists ; by apply is_derive_Reals, Dg.
  destruct (MVT f g a b pr1 pr2) as [c [Hc H]] => //.
  by intros ; apply continuity_pt_filterlim, Cf.
  by intros ; apply continuity_pt_filterlim, Cg.
  exists c, Hc.
  rewrite -(is_derive_unique _ _ _ (Df _ Hc)) -(Derive_Reals _ _ (pr1 _ Hc)).
  rewrite -(is_derive_unique _ _ _ (Dg _ Hc)) -(Derive_Reals _ _ (pr2 _ Hc)).
  by [].
Qed.
Lemma MVT_1 (f : R -> R) (a b : R) (df : R -> R) :
  (forall c : R, a < c < b -> is_derive f c (df c)) ->
  a < b ->
  (forall c : R, a <= c <= b -> continuous f c) ->
  exists (c : R) (P : a < c < b),
    ((b - a) * df c = (f b - f a))%R.
Proof.
  intros.
  destruct (MVT f (fun x => x) a b df (fun _ => 1)) as [c [Hc H2]] => //.
  intros ; by apply @is_derive_id.
  intros ; by apply filterlim_id.
  exists c, Hc.
  by rewrite H2 Rmult_1_r.
Qed.

Lemma is_RInt_derive (f df : R -> R) (a b : R) :
  (forall x : R, Rmin a b <= x <= Rmax a b -> is_derive f x (df x)) ->
  (forall x : R, Rmin a b <= x <= Rmax a b -> continuous df x) ->
    is_RInt df a b (f b - f a)%R.
Proof.
  intros Hf Hdf.
  wlog: a b Hf Hdf / (a < b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.
    rewrite Hab Rminus_eq_0.
    by apply @is_RInt_point.
    evar_last.
    apply is_RInt_swap.
    apply Hw => //.
    by rewrite Rmin_comm Rmax_comm.
    by rewrite Rmin_comm Rmax_comm.
    change opp with Ropp ; simpl ; ring.
  apply filterlim_locally.
  rewrite (proj1 (sign_0_lt _)).
  2: by apply Rminus_lt_0 in Hab.
  intros.
  eapply filter_imp.
  intros x Hx ; rewrite scal_one ; by apply norm_compat1, Hx.
  rewrite /Rmin /Rmax in Hf, Hdf ;
  destruct (Rle_dec a b) as [_ | Hab'].
  2: contradict Hab' ; by apply Rlt_le.
  
  assert (He : 0 < eps / (b - a)).
    apply Rdiv_lt_0_compat.
    by apply eps.
    by apply Rminus_lt_0 in Hab.
  set (e := mkposreal _ He).
  destruct (unifcont_normed_1d _ _ _ Hdf e) as [delta Hd] ; clear Hdf.
  exists delta.
  rewrite /Rmin /Rmax ;
  destruct (Rle_dec a b) as [_ | Hab'].
  2: contradict Hab' ; by apply Rlt_le.
  intros y Hstep [Hptd [Ha Hb]].
  replace (pos eps) with (e * (b - a))%R.
  move: e Hd => {eps He} e Hd.
  rewrite -Ha {a Ha} in Hf Hd Hab |- *.
  rewrite -Hb {b Hb} in Hf Hd Hab |- *.
  move: Hab Hstep Hptd Hf Hd.
  apply SF_cons_ind with (s := y) => {y} [x0 | x0 y IHy] /= Hab Hstep Hptd Hf Hd.
  by apply Rlt_irrefl in Hab.
  rewrite Riemann_sum_cons.
  change minus with Rminus ;
  change plus with Rplus ;
  change scal with Rmult.
  
  assert (Hab_0 : fst x0 <= SF_h y).
    eapply Rle_trans ; apply (Hptd _ (lt_O_Sn _)).
  assert (Hab_1 : SF_h y <= seq.last (SF_h y) (SF_lx y)).
    apply (sorted_last (SF_lx y) O).
    apply ptd_sort.
    by apply ptd_cons with x0.
    by apply lt_O_Sn.
  assert (Hstep_0 : Rabs (SF_h y - fst x0) < delta).
    eapply Rle_lt_trans, Hstep.
    by apply Rmax_l.
  assert (Hstep_1 : seq_step (SF_lx y) < delta).
    eapply Rle_lt_trans, Hstep.
    by apply Rmax_r.
  assert (Hptd_0 : fst x0 <= snd x0 <= SF_h y).
    by apply (Hptd _ (lt_O_Sn _)).
  assert (Hptd_1 : pointed_subdiv y).
    by apply ptd_cons with x0.
  assert (Hf_0 : forall x : R, fst x0 <= x <= (SF_h y) -> is_derive f x (df x)).
    intros ; apply Hf ; split.
    by apply H.
    eapply Rle_trans, Hab_1 ; by apply H.
  assert (Hf_1 : forall x : R,
    SF_h y <= x <= seq.last (SF_h y) (SF_lx y) -> is_derive f x (df x)).
    intros ; apply Hf ; split.
    by eapply Rle_trans, H.
    by apply H.
  assert (Hd_0 : forall x y0 : R,
    fst x0 <= x <= (SF_h y) -> fst x0 <= y0 <= (SF_h y) ->
    ball x delta y0 -> ball_norm (df x) e (df y0)).
    intros ; apply Hd => // ; split.
    by apply H.
    eapply Rle_trans, Hab_1 ; by apply H.
    apply H0.
    eapply Rle_trans, Hab_1 ; by apply H0.
  assert (Hd_1 : forall x y0 : R,
    SF_h y <= x <= seq.last (SF_h y) (SF_lx y) ->
    SF_h y <= y0 <= seq.last (SF_h y) (SF_lx y) ->
    ball x delta y0 -> ball_norm (df x) e (df y0)).
    intros ; apply Hd => // ; split.
    by eapply Rle_trans, H.
    by apply H.
    by eapply Rle_trans, H0.
    by apply H0.
  move: (fun H => IHy H Hstep_1 Hptd_1 Hf_1 Hd_1) => {IHy Hstep Hptd Hf Hd Hstep_1 Hf_1 Hd_1} IHy.
  assert (((SF_h y - fst x0) * df (snd x0) + Riemann_sum df y -
    (f (seq.last (SF_h y) (seq.unzip1 (SF_t y))) - f (fst x0)))%R
    = (((SF_h y - fst x0) * df (snd x0) - (f (SF_h y) - f (fst x0)))
        + (Riemann_sum df y - (f (seq.last (SF_h y) (seq.unzip1 (SF_t y))) - f (SF_h y))))%R)
    by ring.
  rewrite H {H}.
  eapply Rle_lt_trans.
  apply @norm_triangle.
  replace (e * (seq.last (SF_h y) (seq.unzip1 (SF_t y)) - fst x0))%R
    with ((SF_h y - fst x0) * e +
         (e * (seq.last (SF_h y) (seq.unzip1 (SF_t y)) - SF_h y)))%R
    by ring.

  case: Hab_0 => Hab_0 ; last first.
  rewrite Hab_0 !Rminus_eq_0 !Rmult_0_l Rminus_eq_0 norm_zero !Rplus_0_l.
  apply IHy.
  by rewrite -Hab_0.
  
  destruct (MVT_1 f (fst x0) (SF_h y) df) as [c [Hc Hdf]] => //.
  intros c Hc ; apply Hf_0.
  by split ; apply Rlt_le ; apply Hc.
  intros c Hc ; apply @ex_derive_continuous.
  by eexists ; apply Hf_0.
  rewrite -Hdf {Hdf} -Rmult_minus_distr_l.
  eapply Rle_lt_trans.
  apply Rplus_le_compat_r.
  apply @norm_scal.
  change abs with Rabs.
  rewrite Rabs_pos_eq.
  2: by apply Rminus_lt_0, Rlt_le in Hab_0.
  apply Rplus_lt_le_compat.
  apply Rmult_lt_compat_l.
  by apply Rminus_lt_0 in Hab_0.
  apply Hd_0 => //.
  split ; by apply Rlt_le ; apply Hc.
  eapply Rle_lt_trans, Hstep_0.
  rewrite Rabs_pos_eq.
  2: by apply Rminus_lt_0, Rlt_le in Hab_0.
  apply Rabs_le_between ; split.
  rewrite Ropp_minus_distr.
  apply Rplus_le_compat.
  by apply Hptd_0.
  by apply Ropp_le_contravar, Rlt_le, Hc.
  apply Rplus_le_compat.
  by apply Hptd_0.
  by apply Ropp_le_contravar, Rlt_le, Hc.
  
  case: Hab_1 => /= Hab_1 ; last first.
  rewrite -Hab_1 !Rminus_eq_0 Rmult_0_r.
  rewrite Riemann_sum_zero //.
  rewrite Rminus_eq_0 norm_zero.
  by apply Rle_refl.
  by apply ptd_sort.
  
  by apply Rlt_le, IHy.

  unfold e ; simpl ; field.
  apply Rgt_not_eq.
  by apply Rminus_lt_0 in Hab.
Qed.

Lemma is_C_RInt_derive (f df : R -> C) (a b : R) :
  (forall x : R, Rmin a b <= x <= Rmax a b -> filterdiff f (locally x) (fun y => scal y (df x))) ->
  (forall x : R, Rmin a b <= x <= Rmax a b -> continuous (U := C_R_NormedModule) df x) ->
    is_RInt df a b (f b - f a).
Proof.
  intros.
  apply is_RInt_fct_extend_pair ; simpl.
  
  apply (is_RInt_derive (fun y => fst (f y)) (fun y => fst (df y))).
  intros x Hx.
  unfold is_derive.
  evar_last.
  apply (filterdiff_comp' f (@fst R R)).
  by apply H.
  apply filterdiff_linear, is_linear_fst.
  by simpl.
  intros x Hx.
  apply continuous_comp.
  by apply H0.
  apply continuous_fst.
  
  apply (is_RInt_derive (fun y => snd (f y)) (fun y => snd (df y))).
  intros x Hx.
  unfold is_derive.
  evar_last.
  apply (filterdiff_comp' f (@snd R R)).
  by apply H.
  apply filterdiff_linear, is_linear_snd.
  by simpl.
  intros x Hx.
  apply continuous_comp.
  by apply H0.
  apply continuous_snd.
Qed.

Lemma is_linear_RtoC : is_linear RtoC.
Proof.
  split => //=.
  by intros ; rewrite RtoC_plus.
  intros ; rewrite {2}/scal /= /prod_scal /= scal_zero_r.
  reflexivity.
  exists (sqrt 2) ; split.
  apply Rlt_sqrt2_0.
  intros.
  eapply Rle_trans.
  rewrite -Cmod_norm.
  apply Cmod_2Rmax.
  simpl.
  rewrite Rabs_R0.
  rewrite Rmax_left.
  apply Rle_refl.
  apply Rabs_pos.
Qed.

Lemma continuous_RtoC x : continuous RtoC x.
Proof.
  apply filterlim_locally.
  intros eps ; exists eps => /= y Hy.
  split => //=.
  by apply ball_center.
Qed.
Lemma continuous_scal_r {U : UniformSpace} {K : AbsRing} {V : NormedModule K}
 (k : K) (f : U -> V) (x : U) :
  continuous f x -> continuous (fun y => scal k (f y)) x.
Proof.
  intros.
  by apply continuous_comp, filterlim_scal.
Qed.
Lemma scal_minus_distr_l {K : Ring} {V : ModuleSpace K}
  (x : K) (u v : V) :
   scal x (minus u v) = minus (scal x u) (scal x v).
Proof.
  by rewrite /minus scal_distr_l scal_opp_r.
Qed.
Lemma scal_minus_distr_r {K : Ring} {V : ModuleSpace K}
  (x y : K) (u : V) :
   scal (minus x y) u = minus (scal x u) (scal y u).
Proof.
  by rewrite /minus scal_distr_r scal_opp_l.
Qed.
Lemma filterlim_scal_l {K : AbsRing} {V : NormedModule K}
  (k : K) (u : V) :
  filterlim (fun y => scal y u) (locally k) (locally (scal k u)).
Proof.
  intros.
  apply filterlim_locally => eps.
  case: (Req_dec (norm u) 0) => Hk.
  exists eps => /= y Hy.
  apply norm_compat1.
  rewrite -scal_minus_distr_r.
  eapply Rle_lt_trans.
  apply norm_scal.
  rewrite Hk Rmult_0_r.
  by apply eps.
  assert (Hd : 0 < eps / (norm u * norm_factor (V := AbsRing_NormedModule K))).
    apply Rdiv_lt_0_compat.
    by apply eps.
    apply Rmult_lt_0_compat.
    case: (norm_ge_0 u) => // Hk0.
    by apply sym_eq in Hk0.
    by apply norm_factor_gt_0.
  exists (mkposreal _ Hd) => /= y Hy.
  apply norm_compat1.
  rewrite -scal_minus_distr_r.
  eapply Rle_lt_trans.
  apply norm_scal.
  apply Rlt_div_r.
  case: (norm_ge_0 u) => // Hk0.
  by apply sym_eq in Hk0.
  replace (eps / norm u)%R with (norm_factor (V := AbsRing_NormedModule K) * mkposreal _ Hd)%R.
  by apply (@norm_compat2 _ (AbsRing_NormedModule K)) => /=.
  simpl ; field.
  split ; apply Rgt_not_eq.
  case: (norm_ge_0 u) => // Hk0.
  by apply sym_eq in Hk0.
  by apply norm_factor_gt_0.
Qed.
Lemma continuous_scal_l {U : UniformSpace} {K : AbsRing} {V : NormedModule K}
  (f : U -> K) (k : V) (x : U) :
  continuous f x -> continuous (fun y => scal (f y) k) x.
Proof.
  intros.
  apply (continuous_comp f (fun y => scal y k)) => //.
  apply filterlim_scal_l.
Qed.
Lemma filterlim_mult {K : AbsRing} (x y : K) :
  filterlim (fun z => mult (fst z) (snd z)) (locally (x,y)) (locally (mult x y)).
Admitted.
Lemma continuous_mult {U : UniformSpace} {K : AbsRing}
  (f g : U -> K) (x : U) :
  continuous f x -> continuous g x
  -> continuous (fun y => mult (f y) (g y)) x.
Proof.
  intros.
  apply continuous_comp_2 => //.
  apply filterlim_mult.
Qed.
Lemma continuous_const {U V : UniformSpace} (c : V) (x : U) :
  continuous (fun _ => c) x.
Proof.
  apply filterlim_const.
Qed.
Lemma continuous_id {U : UniformSpace} (x : U) :
  continuous (fun y => y) x.
Proof.
  apply filterlim_id.
Qed.

Lemma locally_C x P :
  locally (T := C_UniformSpace) x P <-> locally (T := AbsRing_UniformSpace C_AbsRing) x P.
Proof.
  split => [[e He] | [e He]].
  - exists e => /= y Hy.
    apply He.
    split.
    eapply Rle_lt_trans, Hy.
    eapply Rle_trans, Rmax_Cmod.
    apply Rmax_l.
    eapply Rle_lt_trans, Hy.
    eapply Rle_trans, Rmax_Cmod.
    apply Rmax_r.
  - assert (Hd : 0 < e / sqrt 2).
    apply Rdiv_lt_0_compat.
    by apply e.
    apply Rlt_sqrt2_0.
    exists (mkposreal _ Hd) => /= y [Hy1 Hy2].
    apply He.
    eapply Rle_lt_trans.
    apply Cmod_2Rmax.
    rewrite Rmult_comm ; apply Rlt_div_r.
    apply Rlt_sqrt2_0.
    apply Rmax_case.
    by apply Hy1.
    by apply Hy2.
Qed.
Lemma is_C_RInt_segm_derive (f g : C -> C) (z1 z2 : C) :
  (forall z, complex_segment z1 z2 z -> is_C_derive g z (f z))
  -> (forall z, complex_segment z1 z2 z -> continuous f z)
  -> is_C_RInt_segm f z1 z2 (g z2 - g z1).
Proof.
  intros Dg Cf.
  unfold is_C_RInt_segm.
  evar_last.
  apply (is_C_RInt_derive (fun t : R => g ((1 - t) * z1 + t * z2))
                          (fun t => (z2 - z1) * f ((1 - t) * z1 + t * z2))).
    rewrite /Rmin /Rmax ; case: Rle_dec Rle_0_1 => // _ _.
    intros.
    eapply filterdiff_ext_lin.
    apply (filterdiff_comp' (U := R_NormedModule) (V := C_R_NormedModule) (fun t : R => ((1 - t) * z1 + t * z2)%C) g).
    apply @filterdiff_plus_fct.
    apply locally_filter.
    eapply filterdiff_ext.
    2: apply (filterdiff_scal_l_fct (K := R_AbsRing) (U := R_NormedModule) (V := C_R_NormedModule)
      z1 (fun u : R => (1 - u)%R)).
    simpl ; intros.
    by rewrite scal_R_Cmult RtoC_minus.
    apply @filterdiff_minus_fct.
    by apply locally_filter.
    apply filterdiff_const.
    apply filterdiff_id.
    apply filterdiff_linear.
    move: (is_linear_scal_l (K := R_AbsRing) (V := C_R_NormedModule) z2) => //=.
    apply is_linear_ext.
    intros ; apply scal_R_Cmult.
    apply is_C_derive_filterdiff, Dg.
    exists x ; by split.
  rewrite /= /scal /= /mult /= /prod_scal.
  change scal with Rmult.
  change plus with Cplus.
  change minus with Rminus.
  change zero with R0.
  intros y ; apply injective_projections ; simpl ; ring.
  
  rewrite /Rmin /Rmax ; case: Rle_dec Rle_0_1 => // _ _.
  intros x Hx.
  apply (continuous_comp RtoC ((fun t : C => (z2 - z1) * f ((1 - t) * z1 + t * z2)))).
  apply continuous_RtoC.
  apply @continuous_scal_r.
  apply continuous_comp.
  apply @continuous_plus.
  apply @continuous_scal_l.
  apply (continuous_minus (U := C_UniformSpace) (V := (AbsRing_NormedModule C_AbsRing)) (fun _ => RtoC 1) (fun x => x) (RtoC x)).
  apply continuous_const.
  intros P HP.
  unfold filtermap.
  by apply locally_C.
  apply @continuous_scal_l.
  intros P HP.
  unfold filtermap.
  by apply locally_C.
  apply Cf.
  by exists x.
  ring_simplify ((1 - 1) * z1 + 1 * z2).
  ring_simplify ((1 - 0) * z1 + 0 * z2).
  reflexivity.
Qed.

(** * Corollaire 6 *)

Lemma C_RInt_segm_derive (f : C -> C) (z1 z2 : C) :
  (forall z, complex_segment z1 z2 z -> ex_C_derive f z)
  -> (forall z, complex_segment z1 z2 z -> continuous (C_derive f) z)
  -> is_C_RInt_segm (C_derive f) z1 z2 (f z2 - f z1).
Proof.
  intros.
  apply is_C_RInt_segm_derive => //.
  intros z Hz.
  case: (H z Hz) => [df Hdf].
  by rewrite (C_derive_unique _ _ _ Hdf).
Qed.

(** * Corolaire 7 *)

Lemma is_C_RInt_segm_triangle (f g : C -> C) (z1 z2 z3 : C) :
  (forall z, complex_segment z1 z2 z -> is_C_derive g z (f z))
  -> (forall z, complex_segment z2 z3 z -> is_C_derive g z (f z))
  -> (forall z, complex_segment z3 z1 z -> is_C_derive g z (f z))
  -> (forall z, complex_segment z1 z2 z -> continuous f z)
  -> (forall z, complex_segment z2 z3 z -> continuous f z)
  -> (forall z, complex_segment z3 z1 z -> continuous f z)
  -> C_RInt_segm f z1 z2 + C_RInt_segm f z2 z3 + C_RInt_segm f z3 z1 = 0.
Proof.
  intros.
  erewrite !is_C_RInt_segm_unique ; last first.
  apply is_C_RInt_segm_derive ; eassumption.
  apply is_C_RInt_segm_derive ; eassumption.
  apply is_C_RInt_segm_derive ; eassumption.
  ring.
Qed.

(** * Proposition 8 *)



Require Import Ssreflect.seq.

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
