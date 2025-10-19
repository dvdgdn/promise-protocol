(**
 * Agency Protocol – Error Tolerance with Derived Constants
 *
 * This module links the abstract ΔC and ΔD constants from Theorem 11
 * to the actual protocol formulas involving stakes, merit, and utilities.
 *)

Require Import Reals Lra.
Require Import AgencyProtocol_StakeFunction.
Open Scope R_scope.

(* ---------- Protocol parameters -------- *)
Variables alpha beta : R.
Variable S_base : R.
Variable C_op : R.
Variable G_max : R.

Hypotheses
  (H_alpha_pos : alpha > 0)
  (H_beta_nonneg : beta >= 0)
  (H_S_base_pos : S_base > 0)
  (H_C_op_pos : C_op > 0)
  (H_G_max_pos : G_max > 0).

(* Merit parameters *)
Variables ΔM_plus ΔM_minus : R.
Hypothesis H_ΔM_plus_pos : ΔM_plus > 0.
Hypothesis H_ΔM_minus_neg : ΔM_minus < 0.

(* ---------- Derived utility differences -------- *)
(* These are the actual formulas from the protocol *)

(* Utility advantage from cooperation (keeping promises) *)
(* This is the minimum utility gain when cooperating vs doing nothing *)
Definition ΔC_derived (M : R) : R :=
  alpha * (stake_function M - C_op) + beta * ΔM_plus.

(* Maximum potential gain from defection *)
(* This assumes worst case: maximum gain G_max, minimum stake loss *)
Definition ΔD_derived : R :=
  alpha * G_max + beta * Rabs ΔM_minus.

(* ---------- Linking to abstract constants -------- *)
(* We prove that the derived formulas satisfy the required properties *)

Lemma ΔC_derived_positive :
  forall M,
    0 <= M <= 1 ->
    stake_function M > C_op + (Rabs (beta * ΔM_minus)) / alpha ->
    ΔC_derived M > 0.
Proof.
  intros M HM Hstake_sufficient.
  unfold ΔC_derived.
  
  (* Since ΔM_plus > 0 and beta >= 0, we have beta * ΔM_plus >= 0 *)
  assert (Hmerit_pos : beta * ΔM_plus >= 0).
  { apply Rmult_le_pos; lra. }
  
  (* Need to show: alpha * (stake_function M - C_op) + beta * ΔM_plus > 0 *)
  (* It suffices to show: alpha * (stake_function M - C_op) > -beta * ΔM_plus *)
  (* Since beta * ΔM_plus >= 0, it suffices to show: stake_function M > C_op *)
  
  (* From hypothesis, stake_function M > C_op + something positive *)
  assert (H : stake_function M > C_op) by lra.
  assert (H2 : stake_function M - C_op > 0) by lra.
  assert (H3 : alpha * (stake_function M - C_op) > 0).
  { apply Rmult_gt_0_compat; lra. }
  
  lra.
Qed.

Lemma ΔD_derived_positive :
  ΔD_derived > 0.
Proof.
  unfold ΔD_derived.
  apply Rplus_lt_0_compat.
  - apply Rmult_gt_0_compat; [exact H_alpha_pos | exact H_G_max_pos].
  - apply Rmult_le_pos.
    + exact H_beta_nonneg.
    + apply Rabs_pos.
Qed.

(* ---------- Error tolerance bound in terms of protocol parameters -------- *)
Definition error_tolerance_bound (M : R) : R :=
  ΔC_derived M / (ΔC_derived M + ΔD_derived).

Theorem error_tolerance_protocol :
  forall M ε,
    0 <= M <= 1 ->
    stake_function M > C_op + (Rabs (beta * ΔM_minus)) / alpha ->
    0 < ε < error_tolerance_bound M ->
    (1 - ε) * ΔC_derived M > ε * ΔD_derived.
Proof.
  intros M ε HM Hstake_sufficient Hε.
  
  (* Apply the generic error tolerance theorem *)
  pose proof (ΔC_derived_positive M HM Hstake_sufficient) as HΔC_pos.
  pose proof ΔD_derived_positive as HΔD_pos.
  
  (* The proof follows the same structure as T11 *)
  unfold error_tolerance_bound in Hε.
  destruct Hε as [Hε_pos Hε_bound].
  
  assert (Hdenpos : ΔC_derived M + ΔD_derived > 0) by lra.
  apply Rmult_lt_reg_l with (r := ΔC_derived M + ΔD_derived) in Hε_bound.
  2: exact Hdenpos.
  
  rewrite <- Rmult_plus_distr_r in Hε_bound.
  lra.
Qed.

(* ---------- Concrete bound for specific merit levels -------- *)
(* When merit is high (M close to 1), w(M) is low, stake is high *)
(* This gives better error tolerance *)

Lemma error_tolerance_improves_with_merit :
  forall M1 M2,
    0 <= M1 <= M2 <= 1 ->
    stake_function M1 > C_op + (Rabs (beta * ΔM_minus)) / alpha ->
    stake_function M2 > C_op + (Rabs (beta * ΔM_minus)) / alpha ->
    error_tolerance_bound M1 <= error_tolerance_bound M2.
Proof.
  intros M1 M2 HM Hstake1 Hstake2.
  unfold error_tolerance_bound, ΔC_derived.
  
  (* Since w is decreasing, stake_function is increasing in M *)
  assert (Hstake_mono : stake_function M1 <= stake_function M2).
  { unfold stake_function.
    apply Rmult_le_compat_l.
    - exact (Rlt_le _ _ H_S_base_pos).
    - assert (w M2 <= w M1) by (apply w_decreasing; lra).
      lra. }
  
  (* Therefore ΔC_derived is also increasing in M *)
  assert (HΔC_mono : ΔC_derived M1 <= ΔC_derived M2).
  { unfold ΔC_derived.
    apply Rplus_le_compat_r.
    apply Rmult_le_compat_l.
    - exact (Rlt_le _ _ H_alpha_pos).
    - lra. }
  
  (* The bound ΔC/(ΔC+ΔD) is increasing in ΔC when ΔD is fixed *)
  (* This follows from d/dx[x/(x+c)] = c/(x+c)² > 0 for c > 0 *)
  
  (* Direct proof using cross multiplication *)
  pose proof (ΔC_derived_positive M1 (proj1 HM) Hstake1) as HΔC1_pos.
  pose proof (ΔC_derived_positive M2 (proj1 (proj2 HM)) Hstake2) as HΔC2_pos.
  pose proof ΔD_derived_positive as HΔD_pos.
  
  apply Rmult_le_reg_r with (r := (ΔC_derived M1 + ΔD_derived) * (ΔC_derived M2 + ΔD_derived)).
  { apply Rmult_gt_0_compat; lra. }
  
  unfold Rdiv.
  repeat rewrite Rmult_assoc.
  rewrite Rinv_l; [|lra].
  rewrite Rinv_l; [|lra].
  repeat rewrite Rmult_1_r.
  
  (* Need: ΔC1 * (ΔC2 + ΔD) <= ΔC2 * (ΔC1 + ΔD) *)
  (* Expanding: ΔC1*ΔC2 + ΔC1*ΔD <= ΔC2*ΔC1 + ΔC2*ΔD *)
  (* Simplifying: ΔC1*ΔD <= ΔC2*ΔD *)
  (* Since ΔD > 0: ΔC1 <= ΔC2 *)
  
  ring_simplify.
  apply Rmult_le_compat_r; lra.
Qed.

(* ---------- Minimum required ΔC/ΔD ratio -------- *)
(* This shows what stake and merit parameters are needed for a target error rate *)

Definition min_ratio_for_error_rate (ε_target : R) : R :=
  ε_target / (1 - ε_target).

Theorem stake_for_target_error_rate :
  forall M ε_target,
    0 <= M <= 1 ->
    0 < ε_target < 1 ->
    stake_function M > C_op + (Rabs (beta * ΔM_minus)) / alpha ->
    ΔC_derived M > min_ratio_for_error_rate ε_target * ΔD_derived ->
    error_tolerance_bound M > ε_target.
Proof.
  intros M ε_target HM Hε_target Hstake_sufficient Hratio.
  unfold error_tolerance_bound, min_ratio_for_error_rate.
  
  (* From Hratio: ΔC > (ε/(1-ε)) * ΔD *)
  (* Multiply by (1-ε): (1-ε)*ΔC > ε*ΔD *)
  (* Add ε*ΔC: ΔC > ε*ΔD + ε*ΔC = ε*(ΔC+ΔD) *)
  (* Divide by (ΔC+ΔD): ΔC/(ΔC+ΔD) > ε *)
  
  pose proof (ΔC_derived_positive M HM Hstake_sufficient) as HΔC_pos.
  pose proof ΔD_derived_positive as HΔD_pos.
  
  apply Rmult_lt_reg_r with (r := ΔC_derived M + ΔD_derived).
  { lra. }
  
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_l; [|lra].
  rewrite Rmult_1_r.
  
  (* Need to show: ε_target * (ΔC + ΔD) < ΔC *)
  (* From hypothesis: ΔC > (ε/(1-ε)) * ΔD *)
  
  assert (H1 : (1 - ε_target) * ΔC_derived M > ε_target * ΔD_derived).
  { unfold Rdiv in Hratio.
    apply Rmult_lt_reg_r with (r := 1 - ε_target) in Hratio.
    2: lra.
    rewrite Rmult_assoc in Hratio.
    rewrite Rinv_l in Hratio; lra. }
  
  lra.
Qed.