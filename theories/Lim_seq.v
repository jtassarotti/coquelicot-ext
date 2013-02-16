Require Import Reals Rcomplements Markov Floor.
Require Import Sup_seq Rbar_theory Total_sup ssreflect.
Open Scope R_scope.

(** * Limit sequence *)

Definition is_lim_seq (u : nat -> R) (l : R) :=
  forall eps : posreal, exists N : nat, forall n : nat,
    (N <= n)%nat -> Rabs (u n - l) < eps.
Definition ex_lim_seq (u : nat -> R) :=
  exists l, is_lim_seq u l.
Definition Lim_seq (u : nat -> R) : R := (real (Rbar_plus (LimSup_seq u) (LimInf_seq u)))/2.

Lemma is_lim_seq_correct (u : nat -> R) (l : R) :
  is_lim_seq u l <-> Rbar_is_lim_seq (fun n => Finite (u n)) (Finite l).
Proof.
  split => /= Hl eps ; case: (Hl eps) => {Hl} N Hl ; exists N => n Hn ;
  by apply Rabs_lt_between', Hl.
Qed.
Lemma Lim_seq_Rbar (u : nat -> R) :
  Lim_seq u = real (Rbar_lim_seq (fun n => Finite (u n))).
Proof.
  rewrite /Lim_seq /Rbar_lim_seq.
  rewrite (LimSup_seq_correct u) (LimInf_seq_correct u) /= ;
  case: (Rbar_plus _ _) => //= ; field.
Qed.

(** ** Correction of Lim_seq *)

Lemma is_lim_seq_unique (u : nat -> R) :
  forall l, is_lim_seq u l -> Lim_seq u = l.
Proof.
  move => l ; move/is_lim_seq_correct => Hl ; rewrite Lim_seq_Rbar ;
  by rewrite (Rbar_is_lim_correct _ _ Hl).
Qed.
Lemma Lim_seq_correct (u : nat -> R) :
  ex_lim_seq u -> is_lim_seq u (Lim_seq u).
Proof.
  intros (l,H).
  cut (Lim_seq u = l).
    intros ; rewrite H0 ; apply H.
  apply is_lim_seq_unique, H.
Qed.

(** * Usual rewritings *)
(** ** Extentionality *)

Lemma is_lim_seq_ext : forall u v l, 
  (forall n, u n = v n) -> is_lim_seq u l -> is_lim_seq v l.
Proof.
  intros.
  move => eps.
  case: (H0 eps) => {H0} N H0.
  exists N => n H1.
  rewrite -(H n).
  by apply H0.
Qed.
Lemma ex_lim_seq_ext : forall u v, 
  (forall n, u n = v n) -> ex_lim_seq u -> ex_lim_seq v.
Proof.
  move => u v H [l H0].
  exists l ; by apply is_lim_seq_ext with u.
Qed.
Lemma Lim_seq_ext:  forall u v, 
  (forall n, u n = v n) -> 
  Lim_seq u = Lim_seq v.
Proof.
intros u v H.
unfold Lim_seq, LimSup_seq, LimInf_seq.
destruct (ex_LimSup_seq u) as (lu1,Hlu1).
destruct (ex_LimSup_seq v) as (lv1,Hlv1).
destruct (ex_LimInf_seq u) as (lu2,Hlu2).
destruct (ex_LimInf_seq v) as (lv2,Hlv2).
simpl.
rewrite (is_LimSup_seq_eq _ _ _ _ H Hlu1 Hlv1).
rewrite (is_LimInf_seq_eq _ _ _ _ H Hlu2 Hlv2).
easy.
Qed.

(** ** Sub-sequences *)

Lemma is_lim_seq_subseq (u : nat -> R) (l : R) (phi : nat -> nat) :
  (forall n, (phi n < phi (S n))%nat) -> is_lim_seq u l
    -> is_lim_seq (fun n => u (phi n)) l.
Proof.
  move => Hphi Hu eps.
  case: (Hu eps) => {Hu} N Hu.
  exists N => n Hn.
  apply Hu.
  apply le_trans with (1 := Hn).
  elim: n {Hn} => [ | n IH].
  by apply le_O_n.
  apply lt_le_S.
  apply le_lt_trans with (1 := IH).
  by apply Hphi.
Qed.
Lemma ex_lim_seq_subseq (u : nat -> R) (phi : nat -> nat) :
  (forall n, (phi n < phi (S n))%nat) -> ex_lim_seq u
    -> ex_lim_seq (fun n => u (phi n)).
Proof.
  move => Hphi [l Hu].
  exists l.
  by apply is_lim_seq_subseq.
Qed.
Lemma Lim_seq_subseq (u : nat -> R) (phi : nat -> nat) :
  (forall n, (phi n < phi (S n))%nat) -> ex_lim_seq u
    -> Lim_seq (fun n => u (phi n)) = Lim_seq u.
Proof.
  move => Hphi Hu.
  apply is_lim_seq_unique.
  apply is_lim_seq_subseq.
  by apply Hphi.
  by apply Lim_seq_correct.
Qed. 
Lemma is_lim_seq_incr (u : nat -> R) (l : R) :
  is_lim_seq u l -> is_lim_seq (fun n => u (S n)) l.
Proof.
  move => H.
  apply is_lim_seq_subseq.
  move => n ; by apply lt_n_Sn.
  by apply H.
Qed.
Lemma ex_lim_seq_incr (u : nat -> R) :
  ex_lim_seq u -> ex_lim_seq (fun n => u (S n)).
Proof.
  move => [l H].
  exists l.
  by apply is_lim_seq_incr.
Qed.
Lemma Lim_seq_incr (u : nat -> R) :
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

(** * Operations *)
(** ** Linear combination *)

Lemma is_lim_seq_CL (u v : nat -> R) (a l1 l2 : R) {l : R} :
  is_lim_seq u l1 -> is_lim_seq v l2 -> l = l1 + a * l2 ->
    is_lim_seq (fun n => u n + a * v n) l.
Proof.
  intros Hf Hg Hl e0 ; rewrite Hl ; clear Hl.
  assert (He : 0 < e0 / (1 + Rabs a)).
    unfold Rdiv ; apply Rmult_lt_0_compat ; [apply e0 | apply Rinv_0_lt_compat] ;
    apply Rlt_le_trans with (1 := Rlt_0_1) ; rewrite -{1}(Rplus_0_r 1) ;
    apply Rplus_le_compat_l, Rabs_pos.
  set (eps := mkposreal _ He).
  move: (Hf eps) => {Hf} [Nf Hf].
  move: (Hg eps) => {Hg} [Ng Hg].
  exists (Nf+Ng)%nat ; intros.
  assert (Rw : u n + a * v n - (l1 + a * l2) = (u n - l1) + a * (v n - l2)) ; 
  [ ring | rewrite Rw ; clear Rw].
  assert (Rw : (pos e0) = eps + Rabs a * eps) ;
  [ simpl ; field ; apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1) ; 
    rewrite -{1}(Rplus_0_r 1) ; apply Rplus_le_compat_l, Rabs_pos
  | rewrite Rw ; clear Rw].
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  apply Rplus_lt_le_compat.
  apply Hf, le_trans with (2 := H) ; intuition.
  rewrite Rabs_mult ; apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le, Hg, le_trans with (2 := H) ; intuition.
Qed.
Lemma ex_lim_seq_CL (u v : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq v -> ex_lim_seq (fun n => u n + a * v n).
Proof.
  intros (lf,Hf) (lg,Hg).
  exists (lf + a * lg) ; apply (is_lim_seq_CL u v a lf lg) ; [apply Hf | apply Hg | ring].
Qed.
Lemma Lim_seq_CL (u v : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq v -> Lim_seq (fun n => u n + a * v n) = Lim_seq u + a * Lim_seq v.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply (is_lim_seq_CL _ _ _ (Lim_seq u) (Lim_seq v)).
  apply Lim_seq_correct, H.
  apply Lim_seq_correct, H0.
  reflexivity.
Qed.

(** ** Addition *)

Lemma is_lim_seq_plus (u v : nat -> R) {l : R} (l1 l2 : R) :
  is_lim_seq u l1 -> is_lim_seq v l2 -> l = l1 + l2 ->
    is_lim_seq (fun n => u n + v n) l.
Proof.
  intros.
  rewrite H1 ; clear H1 ; intros eps.
  assert (He2 : 0 < eps / 2) ; 
    [unfold Rdiv ; destruct eps ; apply Rmult_lt_0_compat ; intuition | ].
  elim (H (mkposreal _ He2)) ; clear H ; simpl ; intros N1 H.
  elim (H0 (mkposreal _ He2)) ; clear H0 ; simpl ; intros N2 H0.
  exists (N1+N2)%nat ; intros.
  assert (Rw : (u n + v n - (l1 + l2)) = (u n - l1) + (v n - l2)) ;
    [ring | rewrite Rw ; clear Rw].
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite (double_var eps) ; apply Rplus_lt_compat ; intuition.
Qed.
Lemma Lim_seq_plus (u v : nat -> R) :
  let w := fun n => u n + v n in
  ex_lim_seq u -> ex_lim_seq v -> Lim_seq w = Lim_seq u + Lim_seq v.
Proof.
  intros w (l1,Hu) (l2,Hv).
  apply is_lim_seq_unique.
  rewrite (is_lim_seq_unique _ _ Hu).
  rewrite (is_lim_seq_unique _ _ Hv).
  apply is_lim_seq_plus with (l1 := l1) (l2 := l2) ; intuition.
Qed.

(** ** Constant sequences *)

Lemma is_lim_seq_const (a : R) :
  is_lim_seq (fun n => a) a.
Proof.
  intros eps ; exists O ; intros.
  unfold Rminus ; rewrite (Rplus_opp_r a) Rabs_R0 ; apply eps.
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

(** ** Scalar multiplication *)

Lemma is_lim_seq_scal (u : nat -> R) (a l : R) :
  is_lim_seq u l -> is_lim_seq (fun n => a * u n) (a * l).
Proof.
  move => H.
  apply is_lim_seq_ext with (fun n => 0 + a * u n).
  intro ; ring.
  apply is_lim_seq_CL with 0 l.
  by apply is_lim_seq_const.
  by apply H.
  ring.
Qed.
Lemma ex_lim_seq_scal (u : nat -> R) (a : R) :
  ex_lim_seq u -> ex_lim_seq (fun n => a * u n).
Proof.
  move => [l H].
  exists (a * l).
  by apply is_lim_seq_scal.
Qed.
Lemma Lim_seq_scal (u : nat -> R) (a : R) :
  Lim_seq (fun n => a * u n) = a * Lim_seq u.
Proof.
  wlog: u a / (0 <= a) => [Hw | Ha].
    case: (Rle_lt_dec 0 a) => Ha.
    by apply Hw.
    apply Ropp_0_gt_lt_contravar, Rlt_le in Ha ; 
    move: (Hw (fun n => - u n) _ Ha) => {Hw}.
    rewrite /Lim_seq.
    have H : (forall u, Rbar_limsup_seq u = 
      Rbar_inf_seq (fun n => Rbar_sup_seq (fun m => u (n+m)%nat))).
      move => u0 ; rewrite /Rbar_limsup_seq ; case: Rbar_ex_limsup_seq => ls Hls ;
      rewrite /Rbar_inf_seq ; case: Rbar_ex_inf_seq => i Hi /=.
      apply (Rbar_is_inf_seq_rw (fun n : nat => Rbar_sup_seq (fun m : nat => u0 (n + m)%nat)) 
      (fun n : nat => Rbar_sup_seq (fun m : nat => u0 (n + m)%nat))) => //.
      by apply Rbar_limsup_caract_1.
    rewrite ?LimSup_seq_correct ?H => {H}.
    have H : (forall u, Rbar_liminf_seq u = 
      Rbar_sup_seq (fun n => Rbar_inf_seq (fun m => u (n+m)%nat))).
      move => u0 ; rewrite /Rbar_liminf_seq ; case: Rbar_ex_liminf_seq => ls Hls ;
      rewrite /Rbar_sup_seq ; case: Rbar_ex_sup_seq => i Hi /=.
      apply (Rbar_is_sup_seq_rw (fun n : nat => Rbar_inf_seq (fun m : nat => u0 (n + m)%nat)) 
      (fun n : nat => Rbar_inf_seq (fun m : nat => u0 (n + m)%nat))) => //.
      by apply Rbar_liminf_caract_1.
    rewrite ?LimInf_seq_correct ?H => {H}.
    move => Hw.
    rewrite (Rbar_inf_seq_rw (fun n : nat =>
      Rbar_sup_seq (fun m : nat => Finite (a * u (n + m)%nat))) 
      (fun n : nat =>
      Rbar_sup_seq (fun m : nat => Finite (-a * -u (n + m)%nat)))).
    rewrite (Rbar_sup_seq_rw (fun n : nat =>
      Rbar_inf_seq (fun m : nat => Finite (a * u (n + m)%nat))) 
      (fun n : nat =>
      Rbar_inf_seq (fun m : nat => Finite (-a * -u (n + m)%nat)))).
    rewrite Hw => {Hw} ;
    rewrite Ropp_mult_distr_l_reverse -Ropp_mult_distr_r_reverse ;
    apply Rmult_eq_compat_l ; rewrite -Ropp_mult_distr_l_reverse ;
    apply Rmult_eq_compat_r.
    rewrite -Rbar_opp_real.
    have : (forall x y, Rbar_opp (Rbar_plus x y) = Rbar_plus (Rbar_opp x) (Rbar_opp y)).
      case => [x | | ] ; case => [y | | ] //= ; apply Rbar_finite_eq ; intuition.
    move => ->.
    rewrite Rbar_plus_comm.
    rewrite Rbar_inf_opp_sup Rbar_opp_involutive ;
    rewrite Rbar_sup_opp_inf Rbar_opp_involutive.
    rewrite (Rbar_inf_seq_rw (fun n : nat =>
      Rbar_opp (Rbar_inf_seq (fun m : nat => Finite (- u (n + m)%nat))))
      (fun n : nat => Rbar_sup_seq (fun m : nat => Finite (u (n + m)%nat)))).
    rewrite (Rbar_sup_seq_rw (fun n : nat =>
      Rbar_opp (Rbar_sup_seq (fun m : nat => Finite (- u (n + m)%nat))))
      (fun n : nat => Rbar_inf_seq (fun m : nat => Finite (u (n + m)%nat)))) //.
    move => n ; by rewrite -(Rbar_inf_opp_sup (fun m => Finite (u (n+m)%nat))).
    move => n ; by rewrite -(Rbar_sup_opp_inf (fun m => Finite (u (n+m)%nat))).
    move => n ; apply Rbar_inf_seq_rw => m ; apply Rbar_finite_eq ; ring.
    move => n ; apply Rbar_sup_seq_rw => m ; apply Rbar_finite_eq ; ring.
  
  rewrite /Lim_seq /LimSup_seq /LimInf_seq ;
  case: ex_LimSup_seq => ls' Hls' ; case: ex_LimSup_seq => ls Hls ;
  case: ex_LimInf_seq => li' Hli' ; case: ex_LimInf_seq => li Hli /=.
  apply Rle_lt_or_eq_dec in Ha ; case: Ha => Ha.
(* 0 < a *)
  replace ls' with (Rbar_mult_pos ls (mkposreal _ Ha)).
  replace li' with (Rbar_mult_pos li (mkposreal _ Ha)).
  case: (ls) ; case: (li) => //= ; intros ; field.
(* a*li = li'*)
  apply (is_LimInf_seq_eq (fun n => a * u n) (fun n => a * u n)) => // ;
  case: li Hli => [li | | ] /= Hli.
  move => eps ; have He : (0 < eps / a) ; 
  [apply Rdiv_lt_0_compat => // ; apply eps | set e := mkposreal _ He ].
  move: (Hli e) => {Hli} Hli.
  split ; [case: Hli => Hli _ | case: Hli => _ [N Hli]].
  move => N ; case: (Hli N) => {Hli} n Hli ; exists n ; intuition.
  replace (_*_+_) with (a * (li+e)).
  by apply Rmult_lt_compat_l.
  simpl ; field ; by apply Rgt_not_eq.
  exists N => n Hn.
  replace (_*_-_) with (a * (li-e)).
  by apply Rmult_lt_compat_l, Hli.
  simpl ; field ; by apply Rgt_not_eq.
  move => M ; case: (Hli (M/a)) => {Hli} N Hli ; 
  exists N => n Hn.
  replace M with (a*(M/a)).
  by apply Rmult_lt_compat_l, Hli.
  field ; by apply Rgt_not_eq.
  move => M N ; case: (Hli (M/a) N) => {Hli} n Hli.
  exists n ; replace M with (a*(M/a)) ; intuition.
  field ; by apply Rgt_not_eq.
  (* a*ls = ls'*)
  apply (is_LimSup_seq_eq (fun n => a * u n) (fun n => a * u n)) => // ;
  case: ls Hls => [ls | | ] /= Hls.
  move => eps ; have He : (0 < eps / a) ; 
  [apply Rdiv_lt_0_compat => // ; apply eps | set e := mkposreal _ He ].
  move: (Hls e) => {Hls} Hls.
  split ; [case: Hls => Hls _ | case: Hls => _ [N Hls]].
  move => N ; case: (Hls N) => {Hls} n Hls ; exists n ; intuition.
  replace (_*_-_) with (a * (ls-e)).
  by apply Rmult_lt_compat_l.
  simpl ; field ; by apply Rgt_not_eq.
  exists N => n Hn.
  replace (_*_+_) with (a * (ls+e)).
  by apply Rmult_lt_compat_l, Hls.
  simpl ; field ; by apply Rgt_not_eq.
  move => M N ; case: (Hls (M/a) N) => {Hls} n Hls.
  exists n ; replace M with (a*(M/a)) ; intuition.
  field ; by apply Rgt_not_eq.
  move => M ; case: (Hls (M/a)) => {Hls} N Hls ; 
  exists N => n Hn.
  replace M with (a*(M/a)).
  by apply Rmult_lt_compat_l, Hls.
  field ; by apply Rgt_not_eq.
(* a = 0 *)
  rewrite -Ha in Hls' Hli' |- *.
  replace ls' with (Finite 0).
  replace li' with (Finite 0).
  simpl ; field.
(* li' = 0*)
  apply (is_LimInf_seq_eq (fun n => 0 * u n) (fun n => 0 * u n)) => //= ;
  intuition ; [exists N | exists O] ; intuition ; ring_simplify ; 
  case: eps ; intuition.
(* ls' = 0*)
  apply (is_LimSup_seq_eq (fun n => 0 * u n) (fun n => 0 * u n)) => //= ;
  intuition ; [exists N | exists O] ; intuition ; ring_simplify ; 
  case: eps ; intuition.
Qed.

(** ** Opposite *)

Lemma is_lim_seq_opp (u : nat -> R) (l : R) :
  is_lim_seq u l -> is_lim_seq (fun n => -u n) (-l).
Proof.
  move => H eps ; case: (H eps) => {H} N H ; exists N => n Hn.
  replace (-u n--l) with (-(u n-l)) by ring ;
  rewrite Rabs_Ropp ; by apply H.
Qed.
Lemma ex_lim_seq_opp (u : nat -> R) :
  ex_lim_seq u -> ex_lim_seq (fun n => -u n).
Proof.
  case => l Hl ; exists (-l) ; by apply is_lim_seq_opp.
Qed.
Lemma Lim_seq_opp :
  forall u,
  Lim_seq (fun n => - u n) = - Lim_seq u.
Proof.
intros u.
rewrite -(Rmult_1_l (Lim_seq u)) -Ropp_mult_distr_l_reverse.
rewrite -Lim_seq_scal.
apply Lim_seq_ext => n.
now rewrite Ropp_mult_distr_l_reverse Rmult_1_l.
Qed.

(** ** A particular limit *)

Lemma is_lim_seq_inv_n :
  is_lim_seq (fun n => /INR n) 0.
Proof.
  intros eps.
  assert (He : 0 <= /eps) ; 
    [apply Rlt_le, Rinv_0_lt_compat, eps|].
  destruct (nfloor_ex _ He) as (N,HN).
  exists (S N) ; intros.
  assert (Rw : (pos eps) = INR n * (eps / INR n)) ; 
    [field ; apply Rgt_not_eq, Rlt_gt, lt_0_INR, lt_le_trans with (2 := H), lt_O_Sn 
    | rewrite Rw ; clear Rw].
  assert (Rw : Rabs (/ INR n - 0) = /eps * (eps/INR n)) ; 
    [rewrite Rminus_0_r Rabs_right ; intuition ; field ; split ; 
    [ apply Rgt_not_eq ; intuition | apply Rgt_not_eq, eps ]
    | rewrite Rw ; clear Rw ].
  apply Rmult_lt_compat_r.
  unfold Rdiv ; apply Rmult_lt_0_compat ; intuition ; apply eps.
  apply Rlt_le_trans with (1 := proj2 HN).
  rewrite <- S_INR ; apply le_INR, H.
Qed.
Lemma Lim_seq_inv_n (a : R) :
  Lim_seq (fun n => /INR n) = 0.
Proof.
  intros.
  apply is_lim_seq_unique.
  apply is_lim_seq_inv_n.
Qed.




