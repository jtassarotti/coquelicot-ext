From Coq Require Import Reals Psatz ssreflect.

Require Import Rcomplements Rbar Lub Markov Hierarchy Continuity Lim_seq.
Local Set Default Goal Selector "!".
Local Set Bullet Behavior "Strict Subproofs".

Definition is_lim_seq_Rbar (u : nat -> Rbar) (l : Rbar) :=
  filterlim u eventually (locally l).

Definition is_lim_seq_Rbar' (u : nat -> Rbar) (l : Rbar) :=
  match l with
    | Finite l => forall eps : posreal, eventually (fun n => is_finite (u n) /\ Rabs (u n - l) < eps)
    | p_infty => forall M : R, eventually (fun n => Rbar_le M (u n))
    | m_infty => forall M : R, eventually (fun n => Rbar_le (u n) M)
  end.
Definition ex_lim_seq_Rbar (u : nat -> Rbar) :=
  exists l, is_lim_seq_Rbar u l.
Definition ex_finite_lim_seq_Rbar (u : nat -> Rbar) :=
  exists l : R, is_lim_seq_Rbar u l.

Definition R_to_interval_inv_aux (y : R) : R := sqrt (4 * (1 - y) * y) / (2 * (1 - y)).
Definition R_to_interval_inv (y : R) : R :=
  match Rle_dec 0 y with
  | left _ => R_to_interval_inv_aux y
  | _ => Ropp (R_to_interval_inv_aux (Ropp y))
  end.

Lemma R_to_interval_ineq2 (x : R) : ~ 0 <= x -> x * - x / (1 + x * x) < 0.
Proof.
  intros.
  apply Ropp_lt_cancel.
  rewrite Ropp_0.
  field_simplify; last nra.
  apply Rdiv_lt_0_compat; try nra.
Qed.

Lemma R_to_interval_inv_spec_inv1 x :
  R_to_interval_inv (R_to_interval x) = x.
Proof.
  rewrite /R_to_interval_inv/R_to_interval.
  destruct (Rle_dec 0 x).
  - rewrite Rabs_right; last nra.
    destruct (Rle_dec 0 _); last first.
    { exfalso. apply n. apply Rdiv_le_0_compat; try nra. }
    rewrite /R_to_interval_inv_aux.
    match goal with
    | [ |- sqrt ?a / ?y = ?x ] =>
      assert (sqrt a = x * y) as ->
    end; last first.
    { field; split; try nra. }
    destruct (R_to_interval_ineq1 x); auto.
    apply sqrt_lem_1; try nra.
    field. nra.
  - rewrite Rabs_left; last nra.
    pose proof (R_to_interval_ineq2 x).
    destruct (Rle_dec 0 _); first nra.
    rewrite /R_to_interval_inv_aux.
    match goal with
    | [ |- - (sqrt ?a / ?y) = ?x ] =>
      assert (sqrt a = (- x) * y) as ->
    end; last first.
    { field; split; try nra. }
    destruct (R_to_interval_ineq1 (Ropp x)); auto; try nra.
    apply sqrt_lem_1; try nra.
    { field_simplify; try  nra.
      apply Rdiv_le_0_compat; try nra. }
    * assert (- (x * - x / (1 + x * x)) < 1).
      { eapply Rle_lt_trans; last eauto.  right. field; nra. }
      nra.
    * field. nra.
Qed.

Lemma R_to_interval_inv_cont_pt x:
  -1 < x < 1 -> continuity_pt R_to_interval_inv x.
Proof.
  intros Hrange.
  
  Search Continuous.
  Search continuity_pt.
Search continuity_pt "recip".
intros; eapply (Ranalysis5.continuity_pt_recip_interv R_to_interval R_to_interval_inv
               (R_to_interval_inv -1) (R_to_interva).

Definition Rbar_to_interval_inv (y : R) : Rbar :=
  match Req_EM_T (-1) y with
  | left _ => m_infty
  | _ =>
    match Req_EM_T 1 y with
    | left _ => p_infty
    | _ => R_to_interval_inv y
    end
  end.

Lemma R_to_interval_cont :
  continuity R_to_interval.
Proof.
  rewrite /R_to_interval => z.
  apply continuity_div; last first.
  { intros ?. nra. }
  - apply continuity_plus.
    { apply continuity_const => ?? => //=. }
    apply continuity_mult.
    * apply derivable_continuous, derivable_id.
    * apply derivable_continuous, derivable_id.
  -  apply continuity_mult.
    * apply derivable_continuous, derivable_id.
    * apply Rcontinuity_abs.
Qed.

Search continuity.

Lemma R_to_interval_inv_cont :
  continuity R_to_interval_inv.
Proof.
  rewrite /R_to_interval_inv => z.
  rewrite /continuity_pt/continue_in/limit1_in/limit_in.
  intros eps Hgt0.
  {
    rewr
    intors ?
           Rewr
  Search continuity_pt.
  apply continuity_div; last first.
  { intros ?. nra. }
  - apply continuity_plus.
    { apply continuity_const => ?? => //=. }
    apply continuity_mult.
    * apply derivable_continuous, derivable_id.
    * apply derivable_continuous, derivable_id.
  -  apply continuity_mult.
    * apply derivable_continuous, derivable_id.
    * apply Rcontinuity_abs.
Qed.
Lemma Rbar_dist_fin_cont l : continuity (fun y => Rbar_dist (Finite y) (Finite l)).
Proof.
  rewrite /Rbar_dist/Rbar_to_interval//=.
  apply (continuity_comp _ (Rabs)); last apply Rcontinuity_abs.
  apply continuity_minus; last first.
  { apply continuity_const => ?? => //=. }
  apply R_to_interval_cont.
Qed.

Lemma is_lim_seq_Rbar_spec :
  forall u l,
  is_lim_seq_Rbar' u l <-> is_lim_seq_Rbar u l.
Proof.
destruct l as [l| |] ; split.
- intros H P [eps LP].
  assert (exists delta : posreal, forall y, Rabs (y - l) < delta -> Rbar_dist (Finite y) (Finite l) < eps)
    as Hdelt.
  { pose proof (R_to_interval_cont l) as Hcont.
    apply is_lim_continuity in Hcont.
    edestruct (Hcont (fun y => Rabs (y - R_to_interval l) < eps)) as (delt&Hdelt).
    { rewrite //= /locally. exists eps => ?. eauto. }
    { exists delt. intros. destruct (Req_dec y l); subst.
      * rewrite Rbar_dist_same_eq_0 //. destruct eps; auto.
      * apply Hdelt; eauto.
    }
  }
  destruct Hdelt as (delt&Hdelt_spec).
  destruct (H delt) as [N HN].
  exists N => n Hn.
  apply LP.
  specialize (Hdelt_spec (u n)). destruct (HN n) as (Hfin&Hdn); auto.
  specialize (Hdelt_spec Hdn).
  rewrite /ball/Rbar_UniformSpace//=.
  rewrite Rbar_dist_sym; auto. rewrite -Hfin. apply Hdelt_spec.
- intros LP eps.
  specialize (LP (fun y => is_finite y /\ Rabs (y - l) < eps)).
  destruct LP as (N&Hspec).
  {
    exists 
    exists delt.
    intros l.

    admit. }
  exists N => n Hn. eapply Hspec; eauto.
  *
  apply LP.
  now exists eps.
   *)
- intros H P [M LP].
  destruct (H M) as [N HN].
  exists N => n Hn.
  apply LP.
  now apply HN.
- intros LP M.
  specialize (LP (fun y => M < y)).
  apply LP.
  now exists M.
- intros H P [M LP].
  destruct (H M) as [N HN].
  exists N => n Hn.
  apply LP.
  now apply HN.
- intros LP M.
  specialize (LP (fun y => y < M)).
  apply LP.
  now exists M.
Qed.

(** Equivalence with standard library Reals *)

Lemma is_lim_seq_Reals (u : nat -> R) (l : R) :
  is_lim_seq u l <-> Un_cv u l.
Proof.
  split => Hl.
  move => e He.
  apply (Hl (fun y => R_dist y l < e)).
  now exists (mkposreal _ He).
  unfold is_lim_seq.
  change (Rbar_locally l) with (locally l).
  apply (filterlim_locally u l).
  case => e He.
  case: (Hl e He) => {Hl} /= N Hl.
  exists N => n Hn.
  by apply (Hl n Hn).
Qed.
Lemma is_lim_seq_p_infty_Reals (u : nat -> R) :
  is_lim_seq u p_infty <-> cv_infty u.
Proof.
  split => Hl.
  move => M.
  case: (Hl (fun x => M < x)) => {Hl} [ | N Hl].
  by exists M.
  by exists N.
  move => P [M HP].
  eapply filter_imp.
  by apply HP.
  case: (Hl M) => {Hl} N HN.
  by exists N.
Qed.

Lemma is_lim_LimSup_seq (u : nat -> R) (l : Rbar) :
  is_lim_seq u l -> is_LimSup_seq u l.
Proof.
  move /is_lim_seq_spec.
  case: l => [l | | ] /= Hu.
  move => eps ; case: (Hu eps) => {Hu} N Hu ; split.
  move => N0.
  exists (N + N0)%nat ; split.
  by apply le_plus_r.
  by apply Rabs_lt_between', Hu, le_plus_l.
  exists N => n Hn.
  by apply Rabs_lt_between', Hu.
  move => M N0.
  case: (Hu M) => {Hu} N Hu.
  exists (N + N0)%nat ; split.
  by apply le_plus_r.
  by apply Hu, le_plus_l.
  by [].
Qed.
Lemma is_lim_LimInf_seq (u : nat -> R) (l : Rbar) :
  is_lim_seq u l -> is_LimInf_seq u l.
Proof.
  move /is_lim_seq_spec.
  case: l => [l | | ] /= Hu.
  move => eps ; case: (Hu eps) => {Hu} N Hu ; split.
  move => N0.
  exists (N + N0)%nat ; split.
  by apply le_plus_r.
  by apply Rabs_lt_between', Hu, le_plus_l.
  exists N => n Hn.
  by apply Rabs_lt_between', Hu.
  by [].
  move => M N0.
  case: (Hu M) => {Hu} N Hu.
  exists (N + N0)%nat ; split.
  by apply le_plus_r.
  by apply Hu, le_plus_l.
Qed.
Lemma is_LimSup_LimInf_lim_seq (u : nat -> R) (l : Rbar) :
  is_LimSup_seq u l -> is_LimInf_seq u l -> is_lim_seq u l.
Proof.
  case: l => [l | | ] /= Hs Hi ; apply is_lim_seq_spec.
  move => eps.
  case: (proj2 (Hs eps)) => {Hs} Ns Hs.
  case: (proj2 (Hi eps)) => {Hi} Ni Hi.
  exists (Ns + Ni)%nat => n Hn.
  apply Rabs_lt_between' ; split.
  apply Hi ; intuition.
  apply Hs ; intuition.
  exact Hi.
  exact Hs.
Qed.

Lemma ex_lim_LimSup_LimInf_seq (u : nat -> R) :
  ex_lim_seq u <-> LimSup_seq u = LimInf_seq u.
Proof.
  split => Hl.
  case: Hl => l Hu.
  transitivity l.
  apply is_LimSup_seq_unique.
  by apply is_lim_LimSup_seq.
  apply sym_eq, is_LimInf_seq_unique.
  by apply is_lim_LimInf_seq.
  exists (LimSup_seq u).
  apply is_LimSup_LimInf_lim_seq.
  rewrite /LimSup_seq ; by case: ex_LimSup_seq.
  rewrite Hl /LimInf_seq ; by case: ex_LimInf_seq.
Qed.

(** Extensionality *)

Lemma is_lim_seq_ext_loc (u v : nat -> R) (l : Rbar) :
  eventually (fun n => u n = v n) ->
  is_lim_seq u l -> is_lim_seq v l.
Proof.
  apply filterlim_ext_loc.
Qed.
Lemma ex_lim_seq_ext_loc (u v : nat -> R) :
  eventually (fun n => u n = v n) ->
  ex_lim_seq u -> ex_lim_seq v.
Proof.
  move => H [l H0].
  exists l ; by apply is_lim_seq_ext_loc with u.
Qed.
Lemma Lim_seq_ext_loc (u v : nat -> R) :
  eventually (fun n => u n = v n) ->
  Lim_seq u = Lim_seq v.
Proof.
  intros.
  rewrite /Lim_seq.
  apply (f_equal (fun x => Rbar_div_pos x _)).
  apply f_equal2 ; apply sym_eq.
  apply is_LimSup_seq_unique.
  apply is_LimSup_seq_ext_loc with u.
  by [].
  rewrite /LimSup_seq ; by case: ex_LimSup_seq.
  apply is_LimInf_seq_unique.
  apply is_LimInf_seq_ext_loc with u.
  by [].
  rewrite /LimInf_seq ; by case: ex_LimInf_seq.
Qed.

Lemma is_lim_seq_ext (u v : nat -> R) (l : Rbar) :
  (forall n, u n = v n) -> is_lim_seq u l -> is_lim_seq v l.
Proof.
  move => Hext.
  apply is_lim_seq_ext_loc.
  by exists O.
Qed.
Lemma ex_lim_seq_ext (u v : nat -> R) :
  (forall n, u n = v n) -> ex_lim_seq u -> ex_lim_seq v.
Proof.
  move => H [l H0].
  exists l ; by apply is_lim_seq_ext with u.
Qed.
Lemma Lim_seq_ext (u v : nat -> R) :
  (forall n, u n = v n) ->
  Lim_seq u = Lim_seq v.
Proof.
  move => Hext.
  apply Lim_seq_ext_loc.
  by exists O.
Qed.

(** Unicity *)

Lemma is_lim_seq_unique (u : nat -> R) (l : Rbar) :
  is_lim_seq u l -> Lim_seq u = l.
Proof.
  move => Hu.
  rewrite /Lim_seq.
  replace l with (Rbar_div_pos (Rbar_plus l l) {| pos := 2; cond_pos := Rlt_R0_R2 |})
    by (case: (l) => [x | | ] //= ; apply f_equal ; field).
  apply (f_equal (fun x => Rbar_div_pos x _)).
  apply f_equal2.
  apply is_LimSup_seq_unique.
  by apply is_lim_LimSup_seq.
  apply is_LimInf_seq_unique.
  by apply is_lim_LimInf_seq.
Qed.
Lemma Lim_seq_correct (u : nat -> R) :
  ex_lim_seq u -> is_lim_seq u (Lim_seq u).
Proof.
  intros (l,H).
  cut (Lim_seq u = l).
    intros ; rewrite H0 ; apply H.
  apply is_lim_seq_unique, H.
Qed.
Lemma Lim_seq_correct' (u : nat -> R) :
  ex_finite_lim_seq u -> is_lim_seq u (real (Lim_seq u)).
Proof.
  intros (l,H).
  cut (real (Lim_seq u) = l).
    intros ; rewrite H0 ; apply H.
  replace l with (real l) by auto.
  apply f_equal, is_lim_seq_unique, H.
Qed.

Lemma ex_finite_lim_seq_correct (u : nat -> R) :
  ex_finite_lim_seq u <-> ex_lim_seq u /\ is_finite (Lim_seq u).
Proof.
  split.
  case => l Hl.
  split.
  by exists l.
  by rewrite (is_lim_seq_unique _ _ Hl).
  case ; case => l Hl H.
  exists l.
  rewrite -(is_lim_seq_unique _ _ Hl).
  by rewrite H (is_lim_seq_unique _ _ Hl).
Qed.

Lemma ex_lim_seq_dec (u : nat -> R) :
  {ex_lim_seq u} + {~ex_lim_seq u}.
Proof.
  case: (Rbar_eq_dec (LimSup_seq u) (LimInf_seq u)) => H.
  left ; by apply ex_lim_LimSup_LimInf_seq.
  right ; contradict H ; by apply ex_lim_LimSup_LimInf_seq.
Qed.

Lemma ex_finite_lim_seq_dec (u : nat -> R) :
  {ex_finite_lim_seq u} + {~ ex_finite_lim_seq u}.
Proof.
  case: (ex_lim_seq_dec u) => H.
  apply Lim_seq_correct in H.
  case: (Lim_seq u) H => [l | | ] H.
  left ; by exists l.
  right ; rewrite ex_finite_lim_seq_correct.
  rewrite (is_lim_seq_unique _ _ H) /is_finite //= ; by case.
  right ; rewrite ex_finite_lim_seq_correct.
  rewrite (is_lim_seq_unique _ _ H) /is_finite //= ; by case.
  right ; rewrite ex_finite_lim_seq_correct.
  contradict H ; by apply H.
Qed.

Definition ex_lim_seq_cauchy (u : nat -> R) :=
  forall eps : posreal, exists N : nat, forall n m,
    (N <= n)%nat -> (N <= m)%nat -> Rabs (u n - u m) < eps.
Lemma ex_lim_seq_cauchy_corr (u : nat -> R) :
  (ex_finite_lim_seq u) <-> ex_lim_seq_cauchy u.
Proof.
  split => Hcv.

  apply Lim_seq_correct' in Hcv.
  apply is_lim_seq_spec in Hcv.
  move => eps.
  case: (Hcv (pos_div_2 eps)) => /= {Hcv} N H.
  exists N => n m Hn Hm.
  replace (u n - u m) with ((u n - (real (Lim_seq u))) - (u m - (real (Lim_seq u)))) by ring.
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite Rabs_Ropp (double_var eps).
  apply Rplus_lt_compat ; by apply H.

  exists (LimSup_seq u).
  apply is_lim_seq_spec.
  intros eps.
  rewrite /LimSup_seq ; case: ex_LimSup_seq => /= l Hl.
  case: (Hcv (pos_div_2 eps)) => {Hcv} /= Ncv Hcv.
  case: l Hl => [l | | ] /= Hl.
  case: (Hl (pos_div_2 eps)) => {Hl} /= H1 [Nl H2].
  exists (Ncv + Nl)%nat => n Hn.
  apply Rabs_lt_between' ; split.
  case: (H1 Ncv) => {H1} m [Hm H1].
  replace (l - eps) with ((l - eps / 2) - eps / 2) by field.
  apply Rlt_trans with (u m - eps / 2).
  by apply Rplus_lt_compat_r.
  apply Rabs_lt_between'.
  apply Hcv ; intuition.
  apply Rlt_trans with (l + eps / 2).
  apply H2 ; intuition.
  apply Rminus_lt_0 ; field_simplify ; rewrite ?Rdiv_1.
  by apply is_pos_div_2.
  move: (fun n Hn => proj2 (proj1 (Rabs_lt_between' _ _ _) (Hcv n Ncv Hn (le_refl _))))
  => {Hcv} Hcv.
  case: (Hl (u Ncv + eps / 2) Ncv) => {Hl} n [Hn Hl].
  contradict Hl ; apply Rle_not_lt, Rlt_le.
  by apply Hcv.
  move: (fun n Hn => proj1 (proj1 (Rabs_lt_between' _ _ _) (Hcv n Ncv Hn (le_refl _))))
  => {Hcv} Hcv.
  case: (Hl (u Ncv - eps / 2)) => {Hl} N Hl.
  move: (Hcv _ (le_plus_l Ncv N)) => H.
  contradict H ; apply Rle_not_lt, Rlt_le, Hl, le_plus_r.
Qed.

(** ** Arithmetic operations and order *)

(** Identity *)

Lemma is_lim_seq_INR :
  is_lim_seq INR p_infty.
Proof.
  apply is_lim_seq_spec.
  move => M.
  suff Hm : 0 <= Rmax 0 M.
  exists (S (nfloor (Rmax 0 M) Hm)) => n Hn.
  apply Rlt_le_trans with (2 := le_INR _ _ Hn).
  rewrite /nfloor S_INR.
  case: nfloor_ex => {n Hn} /= n Hn.
  apply Rle_lt_trans with (1 := Rmax_r 0 M).
  by apply Hn.
  apply Rmax_l.
Qed.
Lemma ex_lim_seq_INR :
  ex_lim_seq INR.
Proof.
  exists p_infty ; by apply is_lim_seq_INR.
Qed.
Lemma Lim_seq_INR :
  Lim_seq INR = p_infty.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply is_lim_seq_INR.
Qed.

(** Constants *)

Lemma is_lim_seq_const (a : R) :
  is_lim_seq (fun n => a) a.
Proof.
apply filterlim_const.
Qed.
Lemma ex_lim_seq_const (a : R) :
  ex_lim_seq (fun n => a).
Proof.
  exists a ; by apply is_lim_seq_const.
Qed.
Lemma Lim_seq_const (a : R) :
  Lim_seq (fun n => a) = a.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply is_lim_seq_const.
Qed.

(** Subsequences *)

Lemma eventually_subseq_loc :
  forall phi,
  eventually (fun n => (phi n < phi (S n))%nat) ->
  filterlim phi eventually eventually.
Proof.
intros phi [M Hphi] P [N HP].
exists (N+M)%nat.
intros n Hn.
apply HP.
apply plus_le_reg_l with M.
rewrite Arith.Plus.plus_comm ; apply le_trans with (1:=Hn).
apply le_trans with (1:=le_plus_r (phi M) _).
assert (H:(forall x, M+phi M + x <= M+phi (x+M))%nat).
induction x as [|x IH].
rewrite plus_0_l plus_0_r.
apply le_refl.
rewrite <- plus_n_Sm.
apply lt_le_S.
apply le_lt_trans with (1:=IH).
apply plus_lt_compat_l.
apply Hphi.
apply le_plus_r.
assert (M <= n)%nat.
apply le_trans with (2:=Hn); apply le_plus_r.
specialize (H (n-M)%nat).
replace (n-M+M)%nat with n in H.
apply le_trans with (2:=H).
rewrite (Arith.Plus.plus_comm _ (phi M)) -Arith.Plus.plus_assoc.
apply plus_le_compat_l.
rewrite le_plus_minus_r.
apply le_refl.
exact H0.
rewrite Arith.Plus.plus_comm.
now apply sym_eq, le_plus_minus_r.
Qed.
Lemma eventually_subseq :
  forall phi,
  (forall n, (phi n < phi (S n))%nat) ->
  filterlim phi eventually eventually.
Proof.
intros phi Hphi.
apply eventually_subseq_loc.
by apply filter_forall.
Qed.

Lemma is_lim_seq_subseq (u : nat -> R) (l : Rbar) (phi : nat -> nat) :
  filterlim phi eventually eventually ->
  is_lim_seq u l ->
  is_lim_seq (fun n => u (phi n)) l.
Proof.
intros Hphi.
now apply filterlim_comp.
Qed.
Lemma ex_lim_seq_subseq (u : nat -> R) (phi : nat -> nat) :
  filterlim phi eventually eventually ->
  ex_lim_seq u ->
  ex_lim_seq (fun n => u (phi n)).
Proof.
  move => Hphi [l Hu].
  exists l.
  by apply is_lim_seq_subseq.
Qed.
Lemma Lim_seq_subseq (u : nat -> R) (phi : nat -> nat) :
  filterlim phi eventually eventually ->
  ex_lim_seq u ->
  Lim_seq (fun n => u (phi n)) = Lim_seq u.
Proof.
  move => Hphi Hu.
  apply is_lim_seq_unique.
  apply is_lim_seq_subseq.
  exact Hphi.
  by apply Lim_seq_correct.
Qed.

Lemma is_lim_seq_incr_1 (u : nat -> R) (l : Rbar) :
  is_lim_seq u l <-> is_lim_seq (fun n => u (S n)) l.
Proof.
split ; intros H P HP ; destruct (H P HP) as [N HN].
- exists N.
  intros n Hn.
  apply HN.
  now apply le_S.
- exists (S N).
  intros n Hn.
  destruct n as [|n] ; try easy.
  apply HN.
  now apply le_S_n.
Qed.
Lemma ex_lim_seq_incr_1 (u : nat -> R) :
  ex_lim_seq u <-> ex_lim_seq (fun n => u (S n)).
Proof.
  split ; move => [l H] ; exists l.
  by apply -> is_lim_seq_incr_1.
  by apply is_lim_seq_incr_1.
Qed.
Lemma Lim_seq_incr_1 (u : nat -> R) :
  Lim_seq (fun n => u (S n)) = Lim_seq u.
Proof.
  rewrite /Lim_seq.
  replace (LimSup_seq (fun n : nat => u (S n)))
    with (LimSup_seq u).
  replace (LimInf_seq (fun n : nat => u (S n)))
    with (LimInf_seq u).
  by [].
(* LimInf *)
  rewrite /LimInf_seq ;
  case: ex_LimInf_seq => l1 H1 ;
  case: ex_LimInf_seq => l2 H2 /= ;
  case: l1 H1 => [l1 | | ] /= H1 ;
  case: l2 H2 => [l2 | | ] /= H2.
  apply Rbar_finite_eq, Rle_antisym ;
  apply le_epsilon => e He ; set eps := mkposreal e He ;
  apply Rlt_le.
  case: (proj2 (H1 (pos_div_2 eps))) => /= {H1} N H1.
  case: (proj1 (H2 (pos_div_2 eps)) N) => /= {H2} n [Hn H2].
  apply Rlt_trans with (u (S n) + e/2).
  replace l1 with ((l1-e/2)+e/2) by ring.
  apply Rplus_lt_compat_r.
  apply H1.
  apply le_trans with (1 := Hn).
  apply le_n_Sn.
  replace (l2+e) with ((l2+e/2)+e/2) by field.
  by apply Rplus_lt_compat_r, H2.
  case: (proj2 (H2 (pos_div_2 eps))) => /= {H2} N H2.
  case: (proj1 (H1 (pos_div_2 eps)) (S N)) => /= {H1} .
  case => [ | n] [Hn H1].
  by apply le_Sn_0 in Hn.
  apply Rlt_trans with (u (S n) + e/2).
  replace l2 with ((l2-e/2)+e/2) by ring.
  apply Rplus_lt_compat_r.
  apply H2.
  by apply le_S_n, Hn.
  replace (l1+e) with ((l1+e/2)+e/2) by field.
  by apply Rplus_lt_compat_r, H1.
  have : False => //.
  case: (H2 (l1+1)) => {H2} N /= H2.
  case: (proj1 (H1 (mkposreal _ Rlt_0_1)) (S N)) ;
  case => /= {H1} [ | n] [Hn].
  by apply le_Sn_0 in Hn.
  apply Rle_not_lt, Rlt_le, H2.
  by apply le_S_n.
  have : False => //.
  case: (proj2 (H1 (mkposreal _ Rlt_0_1))) => {H1} N /= H1.
  case: ((H2 (l1-1)) N) => /= {H2}  n [Hn].
  apply Rle_not_lt, Rlt_le, H1.
  by apply le_trans with (2 := le_n_Sn _).
  have : False => //.
  case: (H1 (l2+1)) => {H1} N /= H1.
  case: (proj1 (H2 (mkposreal _ Rlt_0_1)) N) => /= {H2}  n [Hn].
  apply Rle_not_lt, Rlt_le, H1.
  by apply le_trans with (2 := le_n_Sn _).
  by [].
  have : False => //.
  case: (H1 0) => {H1} N H1.
  case: (H2 0 N)=> {H2} n [Hn].
  apply Rle_not_lt, Rlt_le, H1.
  by apply le_trans with (2 := le_n_Sn _).
  have : False => //.
  case: (proj2 (H2 (mkposreal _ Rlt_0_1))) => /= {H2} N H2.
  case: (H1 (l2-1) (S N)) ;
  case => [ | n] [Hn].
  by apply le_Sn_0 in Hn.
  by apply Rle_not_lt, Rlt_le, H2, le_S_n.
  have : False => //.
  case: (H2 0) => {H2} N H2.
  case: (H1 0 (S N)) ;
  case => [ | n] [Hn].
  by apply le_Sn_0 in Hn.
  by apply Rle_not_lt, Rlt_le, H2, le_S_n.
  by [].
(* LimSup *)
  rewrite /LimSup_seq ;
  case: ex_LimSup_seq => l1 H1 ;
  case: ex_LimSup_seq => l2 H2 /= ;
  case: l1 H1 => [l1 | | ] /= H1 ;
  case: l2 H2 => [l2 | | ] /= H2.
  apply Rbar_finite_eq, Rle_antisym ;
  apply le_epsilon => e He ; set eps := mkposreal e He ;
  apply Rlt_le.
  case: (proj2 (H2 (pos_div_2 eps))) => /= {H2} N H2.
  case: ((proj1 (H1 (pos_div_2 eps))) (S N)) ;
  case => /= {H1} [ | n] [Hn H1].
  by apply le_Sn_0 in Hn.
  replace l1 with ((l1-e/2)+e/2) by ring.
  replace (l2+e) with ((l2+e/2)+e/2) by field.
  apply Rplus_lt_compat_r.
  apply Rlt_trans with (1 := H1).
  by apply H2, le_S_n.
  case: (proj2 (H1 (pos_div_2 eps))) => /= {H1} N H1.
  case: ((proj1 (H2 (pos_div_2 eps))) N) => /= {H2} n [Hn H2].
  replace l2 with ((l2-e/2)+e/2) by ring.
  replace (l1+e) with ((l1+e/2)+e/2) by field.
  apply Rplus_lt_compat_r.
  apply Rlt_trans with (1 := H2).
  by apply H1, le_trans with (2 := le_n_Sn _).
  have : False => //.
  case: (proj2 (H1 (mkposreal _ Rlt_0_1))) => /= {H1} N H1.
  case: (H2 (l1+1) N) => n [Hn].
  by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
  have : False => //.
  case: (H2 (l1-1)) => {H2} N H2.
  case: (proj1 (H1 (mkposreal _ Rlt_0_1)) (S N)) ;
  case => [ | n] [Hn] /= .
  by apply le_Sn_0 in Hn.
  by apply Rle_not_lt, Rlt_le, H2, le_S_n.
  have : False => //.
  case: (proj2 (H2 (mkposreal _ Rlt_0_1))) => {H2} /= N H2.
  case: (H1 (l2+1) (S N)) ;
  case => [ | n] [Hn] /= .
  by apply le_Sn_0 in Hn.
  by apply Rle_not_lt, Rlt_le, H2, le_S_n.
  by [].
  have : False => //.
  case: (H2 0) => {H2} N H2.
  case: (H1 0 (S N)) ;
  case => [ | n] [Hn] /= .
  by apply le_Sn_0 in Hn.
  by apply Rle_not_lt, Rlt_le, H2, le_S_n.
  have : False => //.
  case: (H1 (l2-1)) => {H1} N H1.
  case: (proj1 (H2 (mkposreal _ Rlt_0_1)) N) => /= {H2} n [Hn].
  by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
  have : False => //.
  case: (H1 0) => {H1} N H1.
  case: (H2 0 N) => {H2} n [Hn].
  by apply Rle_not_lt, Rlt_le, H1, le_trans with (2 := le_n_Sn _).
  by [].
Qed.

Lemma is_lim_seq_incr_n (u : nat -> R) (N : nat) (l : Rbar) :
  is_lim_seq u l <-> is_lim_seq (fun n => u (n + N)%nat) l.
Proof.
  split.
  elim: N u => [ | N IH] u Hu.
  move: Hu ; apply is_lim_seq_ext => n ; by rewrite plus_0_r.
  apply is_lim_seq_incr_1, IH in Hu.
  move: Hu ; by apply is_lim_seq_ext => n ; by rewrite plus_n_Sm.
  elim: N u => [ | N IH] u Hu.
  move: Hu ; apply is_lim_seq_ext => n ; by rewrite plus_0_r.
  apply is_lim_seq_incr_1, IH.
  move: Hu ; by apply is_lim_seq_ext => n ; by rewrite plus_n_Sm.
Qed.
Lemma ex_lim_seq_incr_n (u : nat -> R) (N : nat) :
  ex_lim_seq u <-> ex_lim_seq (fun n => u (n + N)%nat).
Proof.
  split ; move => [l H] ; exists l.
  by apply -> is_lim_seq_incr_n.
  by apply is_lim_seq_incr_n in H.
Qed.
Lemma Lim_seq_incr_n (u : nat -> R) (N : nat) :
  Lim_seq (fun n => u (n + N)%nat) = Lim_seq u.
Proof.
  elim: N u => [ | N IH] u.
  apply Lim_seq_ext => n ; by rewrite plus_0_r.
  rewrite -(Lim_seq_incr_1 u) -(IH (fun n => u (S n))).
  apply Lim_seq_ext => n ; by rewrite plus_n_Sm.
Qed.

(** *** Order *)

Lemma filterlim_le :
  forall {T F} {FF : ProperFilter' F} (f g : T -> R) (lf lg : Rbar),
  F (fun x => f x <= g x) ->
  filterlim f F (Rbar_locally lf) ->
  filterlim g F (Rbar_locally lg) ->
  Rbar_le lf lg.
Proof.
intros T F FF f g lf lg H Hf Hg.
apply Rbar_not_lt_le.
intros Hl.
apply filter_not_empty.
destruct lf as [lf| |] ; destruct lg as [lg| |] ; try easy.
- assert (Hl' : 0 < (lf - lg) / 2).
    apply Rdiv_lt_0_compat.
    now apply -> Rminus_lt_0.
    apply Rlt_R0_R2.
  assert (Hlf : locally lf (fun y => (lf + lg) / 2 < y)).
    apply open_gt.
    replace ((lf + lg) / 2) with (lf - (lf - lg) / 2) by field.
    apply Rabs_lt_between'.
    by rewrite /Rminus Rplus_opp_r Rabs_R0.
  assert (Hlg : locally lg (fun y => y < (lf + lg) / 2)).
    apply open_lt.
    replace ((lf + lg) / 2) with (lg + (lf - lg) / 2) by field.
    apply Rabs_lt_between'.
    by rewrite /Rminus Rplus_opp_r Rabs_R0.
  specialize (Hf _ Hlf).
  specialize (Hg _ Hlg).
  unfold filtermap in Hf, Hg.
  generalize (filter_and _ _ (filter_and _ _ Hf Hg) H).
  apply filter_imp.
  intros x [[H1 H2] H3].
  apply Rle_not_lt with (1 := H3).
  now apply Rlt_trans with ((lf + lg) / 2).
- assert (Hlf : locally lf (fun y => lf - 1 < y)).
    apply open_gt.
    apply Rabs_lt_between'.
    rewrite /Rminus Rplus_opp_r Rabs_R0.
    apply Rlt_0_1.
  assert (Hlg : Rbar_locally m_infty (fun y => Rbar_lt y (lf - 1))).
    now apply open_Rbar_lt'.
  specialize (Hf _ Hlf).
  specialize (Hg _ Hlg).
  unfold filtermap in Hf, Hg.
  generalize (filter_and _ _ (filter_and _ _ Hf Hg) H).
  apply filter_imp.
  intros x [[H1 H2] H3].
  apply Rle_not_lt with (1 := H3).
  now apply Rlt_trans with (lf - 1).
- assert (Hlf : Rbar_locally p_infty (fun y => Rbar_lt (lg + 1) y)).
    now apply open_Rbar_gt'.
  assert (Hlg : locally lg (fun y => y < lg + 1)).
    apply open_lt.
    apply Rabs_lt_between'.
    rewrite /Rminus Rplus_opp_r Rabs_R0.
    apply Rlt_0_1.
  specialize (Hf _ Hlf).
  specialize (Hg _ Hlg).
  unfold filtermap in Hf, Hg.
  generalize (filter_and _ _ (filter_and _ _ Hf Hg) H).
  apply filter_imp.
  intros x [[H1 H2] H3].
  apply Rle_not_lt with (1 := H3).
  now apply Rlt_trans with (lg + 1).
- assert (Hlf : Rbar_locally p_infty (fun y => Rbar_lt 0 y)).
    now apply open_Rbar_gt'.
  assert (Hlg : Rbar_locally m_infty (fun y => Rbar_lt y 0)).
    now apply open_Rbar_lt'.
  specialize (Hf _ Hlf).
  specialize (Hg _ Hlg).
  unfold filtermap in Hf, Hg.
  generalize (filter_and _ _ (filter_and _ _ Hf Hg) H).
  apply filter_imp.
  intros x [[H1 H2] H3].
  apply Rle_not_lt with (1 := H3).
  now apply Rlt_trans with 0.
Qed.

Lemma is_lim_seq_le_loc (u v : nat -> R) (l1 l2 : Rbar) :
  eventually (fun n => u n <= v n) ->
  is_lim_seq u l1 -> is_lim_seq v l2 ->
  Rbar_le l1 l2.
Proof.
  apply filterlim_le.
Qed.
Lemma Lim_seq_le_loc (u v : nat -> R) :
  eventually (fun n => u n <= v n) ->
  Rbar_le (Lim_seq u) (Lim_seq v).
Proof.
  intros.
  move: (LimSup_le _ _ H) (LimInf_le _ _ H).
  move: (LimSup_LimInf_seq_le u) (LimSup_LimInf_seq_le v).
  unfold Lim_seq.
  case: (LimSup_seq u) => [lsu | | ] //= ;
  case: (LimInf_seq u) => [liu | | ] //= ;
  case: (LimSup_seq v) => [lsv | | ] //= ;
  case: (LimInf_seq v) => [liv | | ] //= ;
  intros.
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat, Rlt_0_2.
  by apply Rplus_le_compat.
  by apply Req_le.
Qed.

Lemma is_lim_seq_le (u v : nat -> R) (l1 l2 : Rbar) :
  (forall n, u n <= v n) -> is_lim_seq u l1 -> is_lim_seq v l2 -> Rbar_le l1 l2.
Proof.
  intros H.
  apply filterlim_le.
  now apply filter_forall.
Qed.

Lemma filterlim_ge_p_infty :
  forall {T F} {FF : Filter F} (f g : T -> R),
  F (fun x => f x <= g x) ->
  filterlim f F (Rbar_locally p_infty) ->
  filterlim g F (Rbar_locally p_infty).
Proof.
intros T F FF f g H Hf.
intros P [M HM].
assert (H' : Rbar_locally p_infty (fun y => M < y)).
  now exists M.
unfold filtermap.
generalize (filter_and (fun x : T => f x <= g x) _ H (Hf (fun y : R => M < y) H')).
apply filter_imp.
intros x [H1 H2].
apply HM.
now apply Rlt_le_trans with (f x).
Qed.

Lemma filterlim_le_m_infty :
  forall {T F} {FF : Filter F} (f g : T -> R),
  F (fun x => g x <= f x) ->
  filterlim f F (Rbar_locally m_infty) ->
  filterlim g F (Rbar_locally m_infty).
Proof.
intros T F FF f g H Hf.
intros P [M HM].
pose ineq (y : R) := y < M.
assert (H' : Rbar_locally m_infty ineq).
  now exists M.
unfold filtermap.
generalize (filter_and _ (fun x : T => ineq (f x)) H (Hf ineq H')).
apply filter_imp.
intros x [H1 H2].
apply HM.
now apply Rle_lt_trans with (f x).
Qed.

Lemma filterlim_le_le :
  forall {T F} {FF : Filter F} (f g h : T -> R) (l : Rbar),
  F (fun x => f x <= g x <= h x) ->
  filterlim f F (Rbar_locally l) ->
  filterlim h F (Rbar_locally l) ->
  filterlim g F (Rbar_locally l).
Proof.
intros T F FF f g h l H Hf Hh.
destruct l as [l| |].
- intros P [eps He].
  assert (H' : Rbar_locally l (fun y => Rabs (y - l) < eps)).
    now exists eps.
  unfold filterlim, filter_le, filtermap in Hf, Hh |- *.
  generalize (filter_and _ _ H (filter_and _ _ (Hf _ H') (Hh _ H'))).
  apply filter_imp.
  intros x [H1 [H2 H3]].
  apply He.
  apply Rabs_lt_between'.
  split.
  apply Rlt_le_trans with (2 := proj1 H1).
  now apply Rabs_lt_between'.
  apply Rle_lt_trans with (1 := proj2 H1).
  now apply Rabs_lt_between'.
- apply filterlim_ge_p_infty with (2 := Hf).
  apply: filter_imp H.
  now intros x [H _].
- apply filterlim_le_m_infty with (2 := Hh).
  apply: filter_imp H.
  now intros x [_ H].
Qed.

Lemma is_lim_seq_le_le_loc (u v w : nat -> R) (l : Rbar) :
  eventually (fun n => u n <= v n <= w n) -> is_lim_seq u l -> is_lim_seq w l -> is_lim_seq v l.
Proof.
  apply filterlim_le_le.
Qed.

Lemma is_lim_seq_le_le (u v w : nat -> R) (l : Rbar) :
  (forall n, u n <= v n <= w n) -> is_lim_seq u l -> is_lim_seq w l -> is_lim_seq v l.
Proof.
  intros H.
  apply filterlim_le_le.
  now apply filter_forall.
Qed.

Lemma is_lim_seq_le_p_loc (u v : nat -> R) :
  eventually (fun n => u n <= v n) ->
  is_lim_seq u p_infty ->
  is_lim_seq v p_infty.
Proof.
  apply filterlim_ge_p_infty.
Qed.

Lemma is_lim_seq_le_m_loc (u v : nat -> R) :
  eventually (fun n => v n <= u n) ->
  is_lim_seq u m_infty ->
  is_lim_seq v m_infty.
Proof.
  apply filterlim_le_m_infty.
Qed.

Lemma is_lim_seq_decr_compare (u : nat -> R) (l : R) :
  is_lim_seq u l
  -> (forall n, (u (S n)) <= (u n))
  -> forall n, l <= u n.
Proof.
  move /is_lim_seq_spec => Hu H n.
  apply Rnot_lt_le => H0.
  apply Rminus_lt_0 in H0.
  case: (Hu (mkposreal _ H0)) => {Hu} /= Nu Hu.
  move: (Hu _ (le_plus_r n Nu)).
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rabs_maj2 _).
  rewrite Ropp_minus_distr'.
  apply Rplus_le_compat_l.
  apply Ropp_le_contravar.
  elim: (Nu) => [ | m IH].
  rewrite plus_0_r ; by apply Rle_refl.
  rewrite -plus_n_Sm.
  apply Rle_trans with (2 := IH).
  by apply H.
Qed.
Lemma is_lim_seq_incr_compare (u : nat -> R) (l : R) :
  is_lim_seq u l
  -> (forall n, (u n) <= (u (S n)))
  -> forall n, u n <= l.
Proof.
  move /is_lim_seq_spec => Hu H n.
  apply Rnot_lt_le => H0.
  apply Rminus_lt_0 in H0.
  case: (Hu (mkposreal _ H0)) => {Hu} /= Nu Hu.
  move: (Hu _ (le_plus_r n Nu)).
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rplus_le_compat_r.
  elim: (Nu) => [ | m IH].
  rewrite plus_0_r ; by apply Rle_refl.
  rewrite -plus_n_Sm.
  apply Rle_trans with (1 := IH).
  by apply H.
Qed.

Lemma ex_lim_seq_decr (u : nat -> R) :
  (forall n, (u (S n)) <= (u n))
    -> ex_lim_seq u.
Proof.
  move => H.
  exists (Inf_seq u).
  apply is_lim_seq_spec.
  rewrite /Inf_seq ; case: ex_inf_seq ; case => [l | | ] //= Hl.
  move => eps ; case: (Hl eps) => Hl1 [N Hl2].
  exists N => n Hn.
  apply Rabs_lt_between' ; split.
  by apply Hl1.
  apply Rle_lt_trans with (2 := Hl2).
  elim: n N {Hl2} Hn => [ | n IH] N Hn.
  rewrite (le_n_O_eq _ Hn).
  apply Rle_refl.
  apply le_lt_eq_dec in Hn.
  case: Hn => [Hn | ->].
  apply Rle_trans with (1 := H _), IH ; intuition.
  by apply Rle_refl.
  move => M ; exists O => n _ ; by apply Hl.
  move => M.
  case: (Hl M) => {Hl} N Hl.
  exists N => n Hn.
  apply Rle_lt_trans with (2 := Hl).
  elim: Hn => [ | {n} n Hn IH].
  by apply Rle_refl.
  apply Rle_trans with (2 := IH).
  by apply H.
Qed.
Lemma ex_lim_seq_incr (u : nat -> R) :
  (forall n, (u n) <= (u (S n)))
    -> ex_lim_seq u.
Proof.
  move => H.
  exists (Sup_seq u).
  apply is_lim_seq_spec.
  rewrite /Sup_seq ; case: ex_sup_seq ; case => [l | | ] //= Hl.
  move => eps ; case: (Hl eps) => Hl1 [N Hl2].
  exists N => n Hn.
  apply Rabs_lt_between' ; split.
  apply Rlt_le_trans with (1 := Hl2).
  elim: Hn => [ | {n} n Hn IH].
  by apply Rle_refl.
  apply Rle_trans with (1 := IH).
  by apply H.
  by apply Hl1.
  move => M.
  case: (Hl M) => {Hl} N Hl.
  exists N => n Hn.
  apply Rlt_le_trans with (1 := Hl).
  elim: Hn => [ | {n} n Hn IH].
  by apply Rle_refl.
  apply Rle_trans with (1 := IH).
  by apply H.
  move => M ; exists O => n Hn ; by apply Hl.
Qed.

Lemma ex_finite_lim_seq_decr (u : nat -> R) (M : R) :
  (forall n, (u (S n)) <= (u n)) -> (forall n, M <= u n)
    -> ex_finite_lim_seq u.
Proof.
  intros.
  apply ex_finite_lim_seq_correct.
  have H1 : ex_lim_seq u.
  exists (real (Inf_seq u)).
  apply is_lim_seq_spec.
  rewrite /Inf_seq ; case: ex_inf_seq ; case => [l | | ] //= Hl.
  move => eps ; case: (Hl eps) => Hl1 [N Hl2].
  exists N => n Hn.
  apply Rabs_lt_between' ; split.
  by apply Hl1.
  apply Rle_lt_trans with (2 := Hl2).
  elim: n N {Hl2} Hn => [ | n IH] N Hn.
  rewrite (le_n_O_eq _ Hn).
  apply Rle_refl.
  apply le_lt_eq_dec in Hn.
  case: Hn => [Hn | ->].
  apply Rle_trans with (1 := H _), IH ; intuition.
  by apply Rle_refl.
  move: (Hl (u O) O) => H1 ; by apply Rlt_irrefl in H1.
  case: (Hl M) => {Hl} n Hl.
  apply Rlt_not_le in Hl.
  by move: (Hl (H0 n)).
  split => //.
  apply Lim_seq_correct in H1.
  case: (Lim_seq u) H1 => [l | | ] /= Hu.
  by [].
  apply is_lim_seq_spec in Hu.
  case: (Hu (u O)) => {Hu} N Hu.
  move: (Hu N (le_refl _)) => {Hu} Hu.
  contradict Hu ; apply Rle_not_lt.
  elim: N => [ | N IH].
  by apply Rle_refl.
  by apply Rle_trans with (1 := H _).
  apply is_lim_seq_spec in Hu.
  case: (Hu M) => {Hu} N Hu.
  move: (Hu N (le_refl _)) => {Hu} Hu.
  contradict Hu ; by apply Rle_not_lt.
Qed.
Lemma ex_finite_lim_seq_incr (u : nat -> R) (M : R) :
  (forall n, (u n) <= (u (S n))) -> (forall n, u n <= M)
    -> ex_finite_lim_seq u.
Proof.
  intros.
  case: (ex_finite_lim_seq_decr (fun n => - u n) (- M)).
  move => n ; by apply Ropp_le_contravar.
  move => n ; by apply Ropp_le_contravar.
  move => l ; move => Hu.
  exists (- l).
  apply is_lim_seq_spec in Hu.
  apply is_lim_seq_spec.
  intros eps.
  case: (Hu eps) => {Hu} N Hu.
  exists N => n Hn.
  replace (u n - - l) with (-(- u n - l)) by ring.
  rewrite Rabs_Ropp ; by apply Hu.
Qed.

(** *** Additive operators *)

(** Opposite *)

Lemma filterlim_Rbar_opp :
  forall x,
  filterlim Ropp (Rbar_locally x) (Rbar_locally (Rbar_opp x)).
Proof.
intros [x| |] P [eps He].
- exists eps.
  intros y Hy.
  apply He.
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  by rewrite Ropp_involutive Rplus_comm Rabs_minus_sym.
- exists (-eps).
  intros y Hy.
  apply He.
  apply Ropp_lt_cancel.
  by rewrite Ropp_involutive.
- exists (-eps).
  intros y Hy.
  apply He.
  apply Ropp_lt_cancel.
  by rewrite Ropp_involutive.
Qed.

Lemma is_lim_seq_opp (u : nat -> R) (l : Rbar) :
  is_lim_seq u l <-> is_lim_seq (fun n => -u n) (Rbar_opp l).
Proof.
  split ; move => Hu.
  apply is_LimSup_LimInf_lim_seq.
  apply is_LimSup_opp_LimInf_seq.
  by apply is_lim_LimInf_seq.
  apply is_LimInf_opp_LimSup_seq.
  by apply is_lim_LimSup_seq.
  apply is_LimSup_LimInf_lim_seq.
  apply is_LimInf_opp_LimSup_seq.
  by apply is_lim_LimInf_seq.
  apply is_LimSup_opp_LimInf_seq.
  by apply is_lim_LimSup_seq.
Qed.

Lemma ex_lim_seq_opp (u : nat -> R) :
  ex_lim_seq u <-> ex_lim_seq (fun n => -u n).
Proof.
  split ; case => l Hl ; exists (Rbar_opp l).
  by apply -> is_lim_seq_opp.
  apply is_lim_seq_ext with (fun n => - - u n).
  move => n ; by apply Ropp_involutive.
  by apply -> is_lim_seq_opp.
Qed.

Lemma Lim_seq_opp (u : nat -> R) :
  Lim_seq (fun n => - u n) = Rbar_opp (Lim_seq u).
Proof.
  rewrite /Lim_seq.
  rewrite LimSup_seq_opp LimInf_seq_opp.
  case: (LimInf_seq u) => [li | | ] ;
  case: (LimSup_seq u) => [ls | | ] //= ;
  apply f_equal ; field.
Qed.

(** Addition *)

Lemma filterlim_Rbar_plus :
  forall x y z,
  is_Rbar_plus x y z ->
  filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally x) (Rbar_locally y)) (Rbar_locally z).
Proof.
  intros x y z.
  wlog: x y z / (Rbar_le 0 z).
    intros Hw.
    case: (Rbar_le_lt_dec 0 z) => Hz Hp.
    by apply Hw.
    apply (filterlim_ext (fun z => - (- fst z + - snd z))).
    intros t.
    ring.
    rewrite -(Rbar_opp_involutive z).
    eapply filterlim_comp.
    2: apply filterlim_Rbar_opp.
    assert (Hw' : filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally (Rbar_opp x)) (Rbar_locally (Rbar_opp y))) (Rbar_locally (Rbar_opp z))).
    apply Hw.
    rewrite -Ropp_0 -/(Rbar_opp 0).
    apply <- Rbar_opp_le.
    now apply Rbar_lt_le.
    revert Hp.
    clear.
    destruct x as [x| |] ; destruct y as [y| |] ; destruct z as [z| |] => //=.
    unfold is_Rbar_plus ; simpl => H.
    injection H => <-.
    apply f_equal, f_equal ; ring.
    clear Hw.
    intros P HP.
    specialize (Hw' P HP).
    destruct Hw' as [Q R H1 H2 H3].
    exists (fun x => Q (- x)) (fun x => R (- x)).
    now apply filterlim_Rbar_opp.
    now apply filterlim_Rbar_opp.
    intros u v HQ HR.
    exact (H3 _ _ HQ HR).

  unfold is_Rbar_plus.
  case: z => [z| |] Hz Hp ;
  try by case: Hz.

(* x + y \in R *)
  case: x y Hp Hz => [x| |] ; case => [y| |] //= ; case => <- Hz.
  intros P [eps He].
  exists (fun u => Rabs (u - x) < pos_div_2 eps) (fun v => Rabs (v - y) < pos_div_2 eps).
  now exists (pos_div_2 eps).
  now exists (pos_div_2 eps).
  intros u v Hu Hv.
  apply He.
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  replace (u + v + - (x + y)) with ((u - x) + (v - y)) by ring.
  rewrite (double_var eps) ;
  apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_compat.
  now apply Hu.
  now apply Hv.

(* x + y = p_infty *)
  wlog: x y Hp {Hz} / (is_finite x) => [Hw|Hx].
    case: x y Hp {Hz} => [x| |] ;
    case => [y| |] // _.
    now apply (Hw x p_infty).
    assert (Hw': filterlim (fun z => fst z + snd z) (filter_prod (Rbar_locally y) (Rbar_locally p_infty)) (Rbar_locally p_infty)).
    exact: Hw.
    intros P HP.
    specialize (Hw' P HP).
    destruct Hw' as [Q R H1 H2 H3].
    exists R Q ; try assumption.
    intros u v Hu Hv.
    rewrite Rplus_comm.
    now apply (H3 v u).
    clear Hw.
    intros P [N HN].
    exists (fun x => N/2 < x) (fun x => N/2 < x).
    now exists (N/2).
    now exists (N/2).
    intros x y Hx Hy.
    simpl.
    apply HN.
    rewrite (double_var N).
    now apply Rplus_lt_compat.
  case: x y Hp Hx => [x| |] ;
  case => [y| | ] //= _ _.
  intros P [N HN].
  exists (fun u => Rabs (u - x) < 1) (fun v => N - x + 1 < v).
  now exists (mkposreal _ Rlt_0_1).
  now exists (N - x + 1).
  intros u v Hu Hv.
  simpl.
  apply HN.
  replace N with (x - 1 + (N - x + 1)) by ring.
  apply Rplus_lt_compat.
  now apply Rabs_lt_between'.
  exact Hv.
Qed.

Lemma is_lim_seq_plus (u v : nat -> R) (l1 l2 l : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 ->
  is_Rbar_plus l1 l2 l ->
  is_lim_seq (fun n => u n + v n) l.
Proof.
intros Hu Hv Hl.
eapply filterlim_comp_2 ; try eassumption.
now apply filterlim_Rbar_plus.
Qed.
Lemma is_lim_seq_plus' (u v : nat -> R) (l1 l2 : R) :
  is_lim_seq u l1 -> is_lim_seq v l2 ->
  is_lim_seq (fun n => u n + v n) (l1 + l2).
Proof.
intros Hu Hv.
eapply is_lim_seq_plus.
by apply Hu.
by apply Hv.
by [].
Qed.

Lemma ex_lim_seq_plus (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v ->
  ex_Rbar_plus (Lim_seq u) (Lim_seq v) ->
  ex_lim_seq (fun n => u n + v n).
Proof.
  intros [lu Hu] [lv Hv] Hl ; exists (Rbar_plus lu lv).
  apply is_lim_seq_plus with lu lv ; try assumption.
  rewrite -(is_lim_seq_unique u lu) //.
  rewrite -(is_lim_seq_unique v lv) //.
  by apply Rbar_plus_correct.
Qed.

Lemma Lim_seq_plus (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v ->
  ex_Rbar_plus (Lim_seq u) (Lim_seq v) ->
  Lim_seq (fun n => u n + v n) = Rbar_plus (Lim_seq u) (Lim_seq v).
Proof.
  intros Hu Hv Hl.
  apply is_lim_seq_unique.
  eapply is_lim_seq_plus ; try apply Lim_seq_correct ; try assumption.
  by apply Rbar_plus_correct.
Qed.

(** Subtraction *)

Lemma is_lim_seq_minus (u v : nat -> R) (l1 l2 l : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 ->
  is_Rbar_minus l1 l2 l ->
  is_lim_seq (fun n => u n - v n) l.
Proof.
  intros H1 H2 Hl.
  eapply is_lim_seq_plus ; try eassumption.
  apply -> is_lim_seq_opp ; apply H2.
Qed.
Lemma is_lim_seq_minus' (u v : nat -> R) (l1 l2 : R) :
  is_lim_seq u l1 -> is_lim_seq v l2 ->
  is_lim_seq (fun n => u n - v n) (l1 - l2).
Proof.
intros Hu Hv.
eapply is_lim_seq_minus ; try eassumption.
by [].
Qed.

Lemma ex_lim_seq_minus (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v ->
  ex_Rbar_minus (Lim_seq u) (Lim_seq v) ->
  ex_lim_seq (fun n => u n - v n).
Proof.
  intros [lu Hu] [lv Hv] Hl ; exists (Rbar_minus lu lv).
  eapply is_lim_seq_minus ; try eassumption.
  rewrite -(is_lim_seq_unique u lu) //.
  rewrite -(is_lim_seq_unique v lv) //.
  by apply Rbar_plus_correct.
Qed.

Lemma Lim_seq_minus (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v ->
  ex_Rbar_minus (Lim_seq u) (Lim_seq v) ->
  Lim_seq (fun n => u n - v n) = Rbar_minus (Lim_seq u) (Lim_seq v).
Proof.
  intros Hu Hv Hl.
  apply is_lim_seq_unique.
  eapply is_lim_seq_minus ; try apply Lim_seq_correct ; try assumption.
  by apply Rbar_plus_correct.
Qed.

(** *** Multiplicative operators *)

(** Inverse *)

Lemma filterlim_Rbar_inv :
  forall l : Rbar, l <> 0 ->
  filterlim Rinv (Rbar_locally l) (Rbar_locally (Rbar_inv l)).
Proof.
  intros l.
  wlog: l / (Rbar_lt 0 l).
    intros Hw.
    case: (Rbar_lt_le_dec 0 l) => Hl.
    by apply Hw.
    case: (Rbar_le_lt_or_eq_dec _ _ Hl) => // {Hl} Hl Hl0.
    rewrite -(Rbar_opp_involutive (Rbar_inv l)).
    replace (Rbar_opp (Rbar_inv l)) with (Rbar_inv (Rbar_opp l))
    by (case: (l) Hl0 => [x | | ] //= Hl0 ; apply f_equal ;
      field ; contradict Hl0 ; by apply f_equal).
    apply (filterlim_ext_loc (fun x => (- / - x))).
    case: l Hl {Hl0} => [l| |] //= Hl.
    apply Ropp_0_gt_lt_contravar in Hl.
    exists (mkposreal _ Hl) => /= x H.
    field ; apply Rlt_not_eq.
    rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /= in H.
    apply Rabs_lt_between' in H.
    apply Rlt_le_trans with (1 := proj2 H), Req_le.
    apply Rplus_opp_r.
    exists 0 => x H.
    field ; by apply Rlt_not_eq.
    eapply filterlim_comp.
    2: apply filterlim_Rbar_opp.
    eapply filterlim_comp.
    apply filterlim_Rbar_opp.
    apply Hw.
    apply Rbar_opp_lt.
    rewrite Rbar_opp_involutive /= Ropp_0 ; by apply Hl.
    contradict Hl0.
    rewrite -(Rbar_opp_involutive l) Hl0 /= ; apply f_equal ; ring.
  case: l => [l| |] //= Hl _.
  (* l \in R *)
  assert (H1: 0 < l / 2).
  apply Rdiv_lt_0_compat with (1 := Hl).
  apply Rlt_R0_R2.
  intros P [eps HP].
  suff He : 0 < Rmin (eps * ((l / 2) * l)) (l / 2).
  exists (mkposreal _ He) => x /= Hx.
  apply HP.
  assert (H2: l / 2 < x).
  apply Rle_lt_trans with (l - l / 2).
  apply Req_le ; field.
  apply Rabs_lt_between'.
  apply Rlt_le_trans with (1 := Hx).
  apply Rmin_r.
  assert (H3: 0 < x).
  now apply Rlt_trans with (l / 2).
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  replace (/ x + - / l) with (- (x - l) / (x * l)).
  rewrite Rabs_div.
  rewrite Rabs_Ropp.
  apply Rlt_div_l.
  apply Rabs_pos_lt, Rgt_not_eq.
  now apply Rmult_lt_0_compat.
  apply Rlt_le_trans with (eps * ((l / 2) * l)).
  apply Rlt_le_trans with (1 := Hx).
  apply Rmin_l.
  apply Rmult_le_compat_l.
  apply Rlt_le, eps.
  rewrite Rabs_mult.
  rewrite (Rabs_pos_eq l).
  apply Rmult_le_compat_r.
  now apply Rlt_le.
  apply Rle_trans with (2 := Rle_abs _).
  now apply Rlt_le.
  now apply Rlt_le.
  apply Rgt_not_eq.
  now apply Rmult_lt_0_compat.
  field ; split ; apply Rgt_not_eq => //.
  apply Rmin_case.
  apply Rmult_lt_0_compat.
  apply cond_pos.
  now apply Rmult_lt_0_compat.
  exact H1.
  (* l = p_infty *)
  intros P [eps HP].
  exists (/eps) => n Hn.
  apply HP.
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  rewrite Ropp_0 Rplus_0_r Rabs_Rinv.
  rewrite -(Rinv_involutive eps).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat, eps.
  apply Rabs_pos_lt, Rgt_not_eq, Rlt_trans with (/eps).
  apply Rinv_0_lt_compat, eps.
  exact Hn.
  apply Rlt_le_trans with (2 := Rle_abs _).
  exact Hn.
  apply Rgt_not_eq, eps.
  apply Rgt_not_eq, Rlt_trans with (/eps).
  apply Rinv_0_lt_compat, eps.
  exact Hn.
Qed.

Lemma is_lim_seq_inv (u : nat -> R) (l : Rbar) :
  is_lim_seq u l -> l <> 0 ->
  is_lim_seq (fun n => / u n) (Rbar_inv l).
Proof.
intros Hu Hl.
apply filterlim_comp with (1 := Hu).
now apply filterlim_Rbar_inv.
Qed.

Lemma ex_lim_seq_inv (u : nat -> R) :
  ex_lim_seq u
  -> Lim_seq u <> 0
    -> ex_lim_seq (fun n => / u n).
Proof.
  intros.
  apply Lim_seq_correct in H.
  exists (Rbar_inv (Lim_seq u)).
  by apply is_lim_seq_inv.
Qed.

Lemma Lim_seq_inv (u : nat -> R) :
  ex_lim_seq u -> (Lim_seq u <> 0)
    -> Lim_seq (fun n => / u n) = Rbar_inv (Lim_seq u).
Proof.
  move => Hl Hu.
  apply is_lim_seq_unique.
  apply is_lim_seq_inv.
  by apply Lim_seq_correct.
  by apply Hu.
Qed.

(** Multiplication *)

Lemma filterlim_Rbar_mult :
  forall x y z,
  is_Rbar_mult x y z ->
  filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally x) (Rbar_locally y)) (Rbar_locally z).
Proof.
  intros x y z.
  wlog: x y z / (Rbar_le 0 x).
    intros Hw.
    case: (Rbar_le_lt_dec 0 x) => Hx Hp.
    by apply Hw.
    apply (filterlim_ext (fun z => - (- fst z * snd z))).
    intros t.
    ring.
    rewrite -(Rbar_opp_involutive z).
    eapply filterlim_comp.
    2: apply filterlim_Rbar_opp.
    assert (Hw' : filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally (Rbar_opp x)) (Rbar_locally y)) (Rbar_locally (Rbar_opp z))).
    apply Hw.
    replace (Finite 0) with (Rbar_opp 0) by apply (f_equal Finite), Ropp_0.
    apply Rbar_opp_le.
    by apply Rbar_lt_le.
    by apply is_Rbar_mult_opp_l.
    clear Hw.
    intros P HP.
    specialize (Hw' P HP).
    destruct Hw' as [Q R H1 H2 H3].
    exists (fun x => Q (- x)) R.
    now apply filterlim_Rbar_opp.
    exact H2.
    intros u v HQ HR.
    exact (H3 _ _ HQ HR).
  wlog: x y z / (Rbar_le 0 y).
    intros Hw.
    case: (Rbar_le_lt_dec 0 y) => Hy Hx Hp.
    by apply Hw.
    apply (filterlim_ext (fun z => - (fst z * -snd z))).
    intros t.
    ring.
    rewrite -(Rbar_opp_involutive z).
    eapply filterlim_comp.
    2: apply filterlim_Rbar_opp.
    assert (Hw' : filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally x) (Rbar_locally (Rbar_opp y))) (Rbar_locally (Rbar_opp z))).
    apply Hw.
    replace (Finite 0) with (Rbar_opp 0) by apply (f_equal Finite), Ropp_0.
    apply Rbar_opp_le.
    by apply Rbar_lt_le.
    by [].
    by apply is_Rbar_mult_opp_r.
    clear Hw.
    intros P HP.
    specialize (Hw' P HP).
    destruct Hw' as [Q R H1 H2 H3].
    exists Q (fun x => R (- x)).
    exact H1.
    now apply filterlim_Rbar_opp.
    intros u v HQ HR.
    exact (H3 _ _ HQ HR).
  wlog: x y z / (Rbar_le x y).
    intros Hw.
    case: (Rbar_le_lt_dec x y) => Hl Hx Hy Hp.
    by apply Hw.
    assert (Hw' : filterlim (fun z => fst z * snd z) (filter_prod (Rbar_locally y) (Rbar_locally x)) (Rbar_locally z)).
    apply Hw ; try assumption.
    by apply Rbar_lt_le.
    by apply is_Rbar_mult_sym.
    intros P HP.
    specialize (Hw' P HP).
    destruct Hw' as [Q R H1 H2 H3].
    exists R Q ; try assumption.
    intros u v HR HQ.
    simpl.
    rewrite Rmult_comm.
    exact (H3 _ _ HQ HR).
  case: x => [x| | ] ; case: y => [y| | ] ; case: z => [z| | ] Hl Hy Hx Hp ;
  try (by case: Hl) || (by case: Hx) || (by case: Hy).
(* x, y \in R *)
  case: Hp => <-.
  intros P [eps HP].
  assert (He: 0 < eps / (x + y + 1)).
  apply Rdiv_lt_0_compat.
  apply cond_pos.
  apply Rplus_le_lt_0_compat.
  now apply Rplus_le_le_0_compat.
  apply Rlt_0_1.
  set (d := mkposreal _ (Rmin_stable_in_posreal (mkposreal _ Rlt_0_1) (mkposreal _ He))).
  exists (fun u => Rabs (u - x) < d) (fun v => Rabs (v - y) < d).
  now exists d.
  now exists d.
  simpl.
  intros u v Hu Hv.
  apply HP.
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  replace (u * v + - (x * y)) with (x * (v - y) + y * (u - x) + (u - x) * (v - y)) by ring.
  replace (pos eps) with (x * (eps / (x + y + 1)) + y * (eps / (x + y + 1)) + 1 * (eps / (x + y + 1))).
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rplus_le_lt_compat.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply Rplus_le_compat.
  rewrite Rabs_mult Rabs_pos_eq //.
  apply Rmult_le_compat_l with (1 := Hx).
  apply Rlt_le.
  apply Rlt_le_trans with (1 := Hv).
  apply Rmin_r.
  rewrite Rabs_mult Rabs_pos_eq //.
  apply Rmult_le_compat_l with (1 := Hy).
  apply Rlt_le.
  apply Rlt_le_trans with (1 := Hu).
  apply Rmin_r.
  rewrite Rabs_mult.
  apply Rmult_le_0_lt_compat ; try apply Rabs_pos.
  apply Rlt_le_trans with (1 := Hu).
  apply Rmin_l.
  apply Rlt_le_trans with (1 := Hv).
  apply Rmin_r.
  field.
  apply Rgt_not_eq.
  apply Rplus_le_lt_0_compat.
  now apply Rplus_le_le_0_compat.
  apply Rlt_0_1.
(* x \in R and y = p_infty *)
  move: Hp ; unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec => // Hx'.
  case: Rle_lt_or_eq_dec => {Hl Hx Hy Hx'} // Hx.
  move: Hp ; unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec => // Hx'.
  case: Rle_lt_or_eq_dec => {Hl Hx Hy Hx'} // Hx _.
  intros P [N HN].
  exists (fun u => Rabs (u - x) < x / 2) (fun v => Rmax 0 (N / (x / 2)) < v).
  now exists (pos_div_2 (mkposreal _ Hx)).
  now exists (Rmax 0 (N / (x / 2))).
  intros u v Hu Hv.
  simpl.
  apply HN.
  apply Rle_lt_trans with ((x - x / 2) * Rmax 0 (N / (x / 2))).
  apply Rmax_case_strong => H.
  rewrite Rmult_0_r ; apply Rnot_lt_le ; contradict H ; apply Rlt_not_le.
  repeat apply Rdiv_lt_0_compat => //.
  by apply Rlt_R0_R2.
  apply Req_le ; field.
  by apply Rgt_not_eq.
  apply Rmult_le_0_lt_compat.
  lra.
  apply Rmax_l.
  now apply Rabs_lt_between'.
  exact Hv.
  move: Hp ; unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec => // Hx'.
  case: Rle_lt_or_eq_dec => {Hl Hx Hy Hx'} // Hx.
(* l1 = l2 = p_infty *)
  clear.
  intros P [N HN].
  exists (fun u => 1 < u) (fun v => Rabs N < v).
  now exists 1.
  now exists (Rabs N).
  intros u v Hu Hv.
  simpl.
  apply HN.
  apply Rle_lt_trans with (1 := Rle_abs _).
  rewrite -(Rmult_1_l (Rabs N)).
  apply Rmult_le_0_lt_compat.
  by apply Rle_0_1.
  by apply Rabs_pos.
  exact Hu.
  exact Hv.
Qed.

Lemma is_lim_seq_mult (u v : nat -> R) (l1 l2 l : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 ->
  is_Rbar_mult l1 l2 l ->
  is_lim_seq (fun n => u n * v n) l.
Proof.
intros Hu Hv Hp.
eapply filterlim_comp_2 ; try eassumption.
now apply filterlim_Rbar_mult.
Qed.
Lemma is_lim_seq_mult' (u v : nat -> R) (l1 l2 : R) :
  is_lim_seq u l1 -> is_lim_seq v l2 ->
  is_lim_seq (fun n => u n * v n) (l1 * l2).
Proof.
intros Hu Hv.
eapply is_lim_seq_mult ; try eassumption.
by [].
Qed.

Lemma ex_lim_seq_mult (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v ->
  ex_Rbar_mult (Lim_seq u) (Lim_seq v) ->
  ex_lim_seq (fun n => u n * v n).
Proof.
  intros [lu Hu] [lv Hv] H ; exists (Rbar_mult lu lv).
  eapply is_lim_seq_mult ; try eassumption.
  rewrite -(is_lim_seq_unique u lu) //.
  rewrite -(is_lim_seq_unique v lv) //.
  by apply Rbar_mult_correct.
Qed.

Lemma Lim_seq_mult (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v ->
  ex_Rbar_mult (Lim_seq u) (Lim_seq v) ->
  Lim_seq (fun n => u n * v n) = Rbar_mult (Lim_seq u) (Lim_seq v).
Proof.
  move => H1 H2 Hl.
  apply is_lim_seq_unique.
  eapply is_lim_seq_mult ; try apply Lim_seq_correct ; try eassumption.
  by apply Rbar_mult_correct.
Qed.

(** Multiplication by a scalar *)

Lemma filterlim_Rbar_mult_l :
  forall (a : R) (l : Rbar),
  filterlim (Rmult a) (Rbar_locally l) (Rbar_locally (Rbar_mult a l)).
Proof.
  intros a l.
  case: (Req_dec a 0) => [->|Ha].
  apply (filterlim_ext (fun _ => 0)).
  intros x.
  apply sym_eq, Rmult_0_l.
  rewrite Rbar_mult_0_l.
  apply filterlim_const.
  eapply filterlim_comp_2.
  apply filterlim_const.
  apply filterlim_id.
  eapply (filterlim_Rbar_mult a l).
  apply Rbar_mult_correct ; by case: l.
Qed.

Lemma filterlim_Rbar_mult_r :
  forall (a : R) (l : Rbar),
  filterlim (fun x => Rmult x a) (Rbar_locally l) (Rbar_locally (Rbar_mult l a)).
Proof.
intros a l.
apply (filterlim_ext (fun x => a * x)).
apply Rmult_comm.
rewrite Rbar_mult_comm.
apply filterlim_Rbar_mult_l.
Qed.

Lemma is_lim_seq_scal_l (u : nat -> R) (a : R) (lu : Rbar) :
  is_lim_seq u lu ->
  is_lim_seq (fun n => a * u n) (Rbar_mult a lu).
Proof.
intros Hu H.
apply filterlim_comp with (1 := Hu).
by apply filterlim_Rbar_mult_l.
Qed.

Lemma ex_lim_seq_scal_l (u : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq (fun n => a * u n).
Proof.
  move => [l H].
  exists (Rbar_mult a l).
  eapply is_lim_seq_scal_l ; try eassumption.
Qed.

Lemma Lim_seq_scal_l (u : nat -> R) (a : R) :
  Lim_seq (fun n => a * u n) = Rbar_mult a (Lim_seq u).
Proof.
  case: (Req_dec a 0) => [ -> | Ha].
  rewrite -(Lim_seq_ext (fun _ => 0)) /=.
  rewrite Lim_seq_const.
  case: (Lim_seq u) => [x | | ] //=.
  by rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  case: Rle_dec (Rle_refl 0) => // H _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => // _ _.
  move => n ; by rewrite Rmult_0_l.

  wlog: a u Ha / (0 < a) => [Hw | {Ha} Ha].
    case: (Rlt_le_dec 0 a) => Ha'.
    by apply Hw.
    case: Ha' => // Ha'.
    rewrite -(Lim_seq_ext (fun n => - a * - u n)).
    rewrite -Rbar_mult_opp.
    rewrite -Lim_seq_opp.
    apply Hw.
    contradict Ha ; rewrite -(Ropp_involutive a) Ha ; ring.
    apply Ropp_lt_cancel ; by rewrite Ropp_0 Ropp_involutive.
    move => n ; ring.
  rewrite /Lim_seq.
  rewrite {2}/LimSup_seq ; case: ex_LimSup_seq => ls Hs ;
  rewrite {2}/LimInf_seq ; case: ex_LimInf_seq => li Hi ; simpl proj1_sig.
  apply (is_LimSup_seq_scal_pos a) in Hs => //.
  apply (is_LimInf_seq_scal_pos a) in Hi => //.
  rewrite (is_LimSup_seq_unique _ _ Hs).
  rewrite (is_LimInf_seq_unique _ _ Hi).
  case: ls {Hs} => [ls | | ] ; case: li {Hi} => [li | | ] //= ;
  case: (Rle_dec 0 a) (Rlt_le _ _ Ha) => // Ha' _ ;
  case: (Rle_lt_or_eq_dec 0 a Ha') (Rlt_not_eq _ _ Ha) => //= _ _ ;
  apply f_equal ; field.
Qed.

Lemma is_lim_seq_scal_r (u : nat -> R) (a : R) (lu : Rbar) :
  is_lim_seq u lu ->
    is_lim_seq (fun n => u n * a) (Rbar_mult lu a).
Proof.
  move => Hu Ha.
  apply is_lim_seq_ext with ((fun n : nat => a * u n)).
  move => n ; by apply Rmult_comm.
  rewrite Rbar_mult_comm.
  apply is_lim_seq_scal_l.
  by apply Hu.
Qed.

Lemma ex_lim_seq_scal_r (u : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq (fun n => u n * a).
Proof.
  move => Hu.
  apply ex_lim_seq_ext with ((fun n : nat => a * u n)) ; try by intuition.
  apply ex_lim_seq_scal_l.
  by apply Hu.
Qed.

Lemma Lim_seq_scal_r (u : nat -> R) (a : R) :
  Lim_seq (fun n => u n * a) = Rbar_mult (Lim_seq u) a.
Proof.
  rewrite Rbar_mult_comm -Lim_seq_scal_l.
  apply Lim_seq_ext ; by intuition.
Qed.

(** Division *)

Lemma is_lim_seq_div (u v : nat -> R) (l1 l2 l : Rbar) :
  is_lim_seq u l1 -> is_lim_seq v l2 -> l2 <> 0 ->
  is_Rbar_div l1 l2 l ->
  is_lim_seq (fun n => u n / v n) l.
Proof.
  intros.
  eapply is_lim_seq_mult ; try eassumption.
  now apply is_lim_seq_inv.
Qed.
Lemma is_lim_seq_div' (u v : nat -> R) (l1 l2 : R) :
  is_lim_seq u l1 -> is_lim_seq v l2 -> l2 <> 0 ->
  is_lim_seq (fun n => u n / v n) (l1 / l2).
Proof.
  intros.
  eapply is_lim_seq_div ; try eassumption.
  now contradict H1 ; case: H1 => ->.
  by [].
Qed.
Lemma ex_lim_seq_div (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v -> Lim_seq v <> 0 ->
  ex_Rbar_div (Lim_seq u) (Lim_seq v) ->
  ex_lim_seq (fun n => u n / v n).
Proof.
  intros.
  apply Lim_seq_correct in H.
  apply Lim_seq_correct in H0.
  exists (Rbar_div (Lim_seq u) (Lim_seq v)).
  eapply is_lim_seq_div ; try eassumption.
  by apply Rbar_mult_correct.
Qed.
Lemma Lim_seq_div (u v : nat -> R) :
  ex_lim_seq u -> ex_lim_seq v -> (Lim_seq v <> 0) ->
  ex_Rbar_div (Lim_seq u) (Lim_seq v) ->
  Lim_seq (fun n => u n / v n) = Rbar_div (Lim_seq u) (Lim_seq v).
Proof.
  move => H0 H1 H2 H3.
  apply is_lim_seq_unique.
  eapply is_lim_seq_div ; try apply Lim_seq_correct ; try eassumption.
  by apply Rbar_mult_correct.
Qed.

(** *** Additional limits *)

Lemma ex_lim_seq_adj (u v : nat -> R) :
  (forall n, u n <= u (S n)) -> (forall n, v (S n) <= v n)
  -> is_lim_seq (fun n => v n - u n) 0
  -> ex_finite_lim_seq u /\ ex_finite_lim_seq v /\ Lim_seq u = Lim_seq v.
Proof.
  move => Hu Hv H0.
  suff H : forall n, u n <= v n.
  suff Eu : ex_finite_lim_seq u.
    split ; try auto.
  suff Ev : ex_finite_lim_seq v.
    split ; try auto.

  apply is_lim_seq_unique in H0.
  rewrite Lim_seq_minus in H0 ; try by intuition.
  apply ex_finite_lim_seq_correct in Eu.
  apply ex_finite_lim_seq_correct in Ev.
  rewrite -(proj2 Eu) -(proj2 Ev) /= in H0 |- *.
  apply Rbar_finite_eq in H0 ; apply Rbar_finite_eq.
  by apply sym_eq, Rminus_diag_uniq, H0.
  by apply ex_finite_lim_seq_correct.
  by apply ex_finite_lim_seq_correct.
  apply ex_finite_lim_seq_correct in Eu.
  apply ex_finite_lim_seq_correct in Ev.
  by rewrite -(proj2 Eu) -(proj2 Ev).
  apply ex_finite_lim_seq_decr with (u O) => //.
  move => n ; apply Rle_trans with (2 := H _).
  elim: n => [ | n IH].
  by apply Rle_refl.
  by apply Rle_trans with (2 := Hu _).
  apply ex_finite_lim_seq_incr with (v O) => //.
  move => n ; apply Rle_trans with (1 := H _).
  elim: n => [ | n IH].
  by apply Rle_refl.
  by apply Rle_trans with (1 := Hv _).
  move => n0 ; apply Rnot_lt_le ; move/Rminus_lt_0 => H.
  apply is_lim_seq_spec in H0.
  case: (H0 (mkposreal _ H)) => /= {H0} N H0.
  move: (H0 _ (le_plus_r n0 N)) ; apply Rle_not_lt.
  rewrite Rminus_0_r ; apply Rle_trans with (2 := Rabs_maj2 _).
  rewrite Ropp_minus_distr'.
  apply Rplus_le_compat, Ropp_le_contravar.
  elim: (N) => [ | m IH].
  rewrite plus_0_r ; apply Rle_refl.
  rewrite -plus_n_Sm ; by apply Rle_trans with (2 := Hu _).
  elim: (N) => [ | m IH].
  rewrite plus_0_r ; apply Rle_refl.
  rewrite -plus_n_Sm ; by apply Rle_trans with (1 := Hv _).
Qed.

(** Image by a continuous function *)

Lemma is_lim_seq_continuous (f : R -> R) (u : nat -> R) (l : R) :
  continuity_pt f l -> is_lim_seq u l
  -> is_lim_seq (fun n => f (u n)) (f l).
Proof.
  move => Cf Hu.
  apply continuity_pt_filterlim in Cf.
  apply filterlim_comp with (1 := Hu).
  exact Cf.
Qed.

(** Absolute value *)

Lemma filterlim_Rabs :
  forall l : Rbar,
  filterlim Rabs (Rbar_locally l) (Rbar_locally (Rbar_abs l)).
Proof.
  case => [l| |] /=.

  apply @filterlim_norm.

  intros P [N HP].
  exists N => x Hx.
  apply HP.
  apply Rlt_le_trans with (1 := Hx).
  apply Rle_abs.

  intros P [N HP].
  exists (-N) => x Hx.
  apply HP.
  apply Rlt_le_trans with (2 := Rabs_maj2 _), Ropp_lt_cancel.
  by rewrite Ropp_involutive.
Qed.

Lemma is_lim_seq_abs (u : nat -> R) (l : Rbar) :
  is_lim_seq u l -> is_lim_seq (fun n => Rabs (u n)) (Rbar_abs l).
Proof.
intros Hu.
apply filterlim_comp with (1 := Hu).
apply filterlim_Rabs.
Qed.
Lemma ex_lim_seq_abs (u : nat -> R) :
  ex_lim_seq u -> ex_lim_seq (fun n => Rabs (u n)).
Proof.
  move => [l Hu].
  exists (Rbar_abs l) ; by apply is_lim_seq_abs.
Qed.
Lemma Lim_seq_abs (u : nat -> R) :
  ex_lim_seq u ->
  Lim_seq (fun n => Rabs (u n)) = Rbar_abs (Lim_seq u).
Proof.
  intros.
  apply is_lim_seq_unique.
  apply is_lim_seq_abs.
  by apply Lim_seq_correct.
Qed.

Lemma is_lim_seq_abs_0 (u : nat -> R) :
  is_lim_seq u 0 <-> is_lim_seq (fun n => Rabs (u n)) 0.
Proof.
  split => Hu.
  rewrite -Rabs_R0.
  by apply (is_lim_seq_abs _ 0).
  apply is_lim_seq_spec in Hu.
  apply is_lim_seq_spec.
  move => eps.
  case: (Hu eps) => {Hu} N Hu.
  exists N => n Hn.
  move: (Hu n Hn) ;
  by rewrite ?Rminus_0_r Rabs_Rabsolu.
Qed.

(** Geometric sequences *)

Lemma is_lim_seq_geom (q : R) :
  Rabs q < 1 -> is_lim_seq (fun n => q ^ n) 0.
Proof.
  intros Hq.
  apply is_lim_seq_spec.
  move => [e He] /=.
  case: (pow_lt_1_zero q Hq e He) => N H.
  exists N => n Hn.
  rewrite Rminus_0_r ; by apply H.
Qed.
Lemma ex_lim_seq_geom (q : R) :
  Rabs q < 1 -> ex_lim_seq (fun n => q ^ n).
Proof.
  move => Hq ; exists 0 ; by apply is_lim_seq_geom.
Qed.
Lemma Lim_seq_geom (q : R) :
  Rabs q < 1 -> Lim_seq (fun n => q ^ n) = 0.
Proof.
  intros.
  apply is_lim_seq_unique.
  by apply is_lim_seq_geom.
Qed.

Lemma is_lim_seq_geom_p (q : R) :
  1 < q -> is_lim_seq (fun n => q ^ n) p_infty.
Proof.
  intros Hq.
  apply is_lim_seq_spec.
  move => M /=.
  case: (fun Hq => Pow_x_infinity q Hq (M+1)) => [ | N H].
  by apply Rlt_le_trans with (1 := Hq), Rle_abs.
  exists N => n Hn.
  apply Rlt_le_trans with (M+1).
  rewrite -{1}(Rplus_0_r M) ; by apply Rplus_lt_compat_l, Rlt_0_1.
  rewrite -(Rabs_pos_eq (q^n)).
  by apply Rge_le, H.
  by apply pow_le, Rlt_le, Rlt_trans with (1 := Rlt_0_1).
Qed.
Lemma ex_lim_seq_geom_p (q : R) :
  1 < q -> ex_lim_seq (fun n => q ^ n).
Proof.
  move => Hq ; exists p_infty ; by apply is_lim_seq_geom_p.
Qed.
Lemma Lim_seq_geom_p (q : R) :
  1 < q -> Lim_seq (fun n => q ^ n) = p_infty.
Proof.
  intros.
  apply is_lim_seq_unique.
  by apply is_lim_seq_geom_p.
Qed.

Lemma ex_lim_seq_geom_m (q : R) :
  q <= -1 -> ~ ex_lim_seq (fun n => q ^ n).
Proof.
  intros Hq [l H].
  apply is_lim_seq_spec in H.
  destruct l as [l| |].
  case: Hq => Hq.
(* ~ is_lim_seq (q^n) l *)
  case: (H (mkposreal _ Rlt_0_1)) => /= {H} N H.
  move: (fun n Hn => Rabs_lt_between_Rmax _ _ _ (proj1 (Rabs_lt_between' _ _ _) (H n Hn))).
  set M := Rmax (l + 1) (- (l - 1)) => H0.
  case: (fun Hq => Pow_x_infinity q Hq M) => [ | N0 H1].
  rewrite Rabs_left.
  apply Ropp_lt_cancel ; by rewrite Ropp_involutive.
  apply Rlt_trans with (1 := Hq) ;
  apply Ropp_lt_cancel ;
  rewrite Ropp_involutive Ropp_0 ;
  by apply Rlt_0_1.
  move: (H0 _ (le_plus_l N N0)).
  by apply Rle_not_lt, Rge_le, H1, le_plus_r.
(* ~ is_lim_seq ((-1)^n) l *)
  case: (H (mkposreal _ Rlt_0_1)) => /= {H} N H.
  rewrite Hq in H => {q Hq}.
  move: (H _ (le_n_2n _)) ; rewrite pow_1_even ; case/Rabs_lt_between' => _ H1.
  have H2 : (N <= S (2 * N))%nat.
    by apply le_trans with (1 := le_n_2n _), le_n_Sn.
  move: (H _ H2) ; rewrite pow_1_odd ; case/Rabs_lt_between' => {H H2} H2 _.
  move: H1 ; apply Rle_not_lt, Rlt_le.
  pattern 1 at 2 ; replace (1) with ((-1)+2) by ring.
  replace (l+1) with ((l-1)+2) by ring.
  by apply Rplus_lt_compat_r.
(* ~ Rbar_is_lim_seq (q^n) p_infty *)
  case: (H 0) => {H} N H.
  have H0 : (N <= S (2 * N))%nat.
    by apply le_trans with (1 := le_n_2n _), le_n_Sn.
  move: (H _ H0) ; apply Rle_not_lt ; rewrite /pow -/pow.
  apply Rmult_le_0_r.
  apply Rle_trans with (1 := Hq), Ropp_le_cancel ;
  rewrite Ropp_involutive Ropp_0 ;
  by apply Rle_0_1.
  apply Ropp_le_contravar in Hq ; rewrite Ropp_involutive in Hq.
  rewrite pow_sqr -Rmult_opp_opp ; apply pow_le, Rmult_le_pos ;
  apply Rle_trans with (2 := Hq), Rle_0_1.
(* ~ Rbar_is_lim_seq (q^n) m_infty *)
  case: (H 0) => {H} N H.
  move: (H _ (le_n_2n _)).
  apply Rle_not_lt.
  apply Ropp_le_contravar in Hq ; rewrite Ropp_involutive in Hq.
  rewrite pow_sqr -Rmult_opp_opp ; apply pow_le, Rmult_le_pos ;
  apply Rle_trans with (2 := Hq), Rle_0_1.
Qed.

(** Rbar_loc_seq converges *)

Lemma is_lim_seq_Rbar_loc_seq (x : Rbar) :
  is_lim_seq (Rbar_loc_seq x) x.
Proof.
  intros P HP.
  apply filterlim_Rbar_loc_seq.
  now apply Rbar_locally'_le.
Qed.
