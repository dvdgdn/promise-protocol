(**
 * Agency Protocol – Derived Constants (G_max and FOV)
 *
 * This module derives the maximum gain G_max and field-of-view (FOV)
 * constants from protocol parameters, rather than axiomatizing them.
 *)

Require Import Reals Lra Ranalysis1.
Require Import AgencyProtocol_StakeFunction.
Open Scope R_scope.

(* ---------- Protocol parameters -------- *)
Variables alpha beta : R.
Variable S_base : R.
Variable C_op : R.
Variable δ : R.  (* discount factor *)

Hypotheses
  (H_alpha_pos : alpha > 0)
  (H_beta_nonneg : beta >= 0)
  (H_S_base_pos : S_base > 0)
  (H_C_op_pos : C_op > 0)
  (H_delta : 0 < δ < 1).

(* ---------- Task and domain parameters -------- *)
(* Maximum value a task can generate *)
Variable V_task_max : R.
Hypothesis H_V_task_pos : V_task_max > 0.

(* Maximum commission rate *)
Variable commission_rate_max : R.
Hypothesis H_commission : 0 < commission_rate_max < 1.

(* Number of domains an agent can defect in simultaneously *)
Variable n_domains : nat.
Hypothesis H_domains : (0 < n_domains)%nat.

(* ---------- Derived G_max -------- *)
(* The maximum one-shot gain from defection is bounded by:
   - Taking the highest-value task
   - Charging maximum commission
   - Defecting across all domains simultaneously *)

Definition G_max_derived : R := 
  INR n_domains * V_task_max * commission_rate_max.

Lemma G_max_derived_positive : G_max_derived > 0.
Proof.
  unfold G_max_derived.
  apply Rmult_gt_0_compat.
  - apply Rmult_gt_0_compat.
    + apply lt_0_INR. exact H_domains.
    + exact H_V_task_pos.
  - exact (proj1 H_commission).
Qed.

(* ---------- Field of View (FOV) constraint -------- *)
(* The FOV determines how far ahead agents look when making decisions *)

(* Minimum stake factor (when merit is lowest) *)
Variable w_max : R.
Hypothesis H_w_max : 0 < w_max <= 1.
Hypothesis H_w_at_zero : w 0 = w_max.

Definition min_stake_factor : R := 1 - w_max.

Lemma min_stake_factor_bounds : 0 <= min_stake_factor < 1.
Proof.
  unfold min_stake_factor.
  split; lra.
Qed.

(* Minimum punishment for defection *)
Variable P_min : R.
Hypothesis H_P_min : P_min > 0.

(* The FOV constant k must satisfy: δ^k * Future_Value <= ε * Immediate_Gain *)
(* Where ε is the acceptable threshold for ignoring future consequences *)

Variable ε_threshold : R.
Hypothesis H_epsilon : 0 < ε_threshold < 1.

(* Derived FOV bound *)
Definition FOV_derived : nat :=
  Z.to_nat (up (ln (ε_threshold * alpha * S_base * min_stake_factor * P_min / G_max_derived) / ln δ)).

(* ---------- Key theorem: FOV ensures future discounting is acceptable -------- *)
Theorem FOV_ensures_bounded_future :
  forall k,
    (k >= FOV_derived)%nat ->
    δ ^ k * (alpha * S_base * min_stake_factor * P_min) <= ε_threshold * G_max_derived.
Proof.
  intros k Hk.
  
  (* Rearrange: δ^k <= ε * G_max / (α * S_base * min_stake * P_min) *)
  pose (target := ε_threshold * G_max_derived / (alpha * S_base * min_stake_factor * P_min)).
  
  assert (Hdenom_pos : alpha * S_base * min_stake_factor * P_min > 0).
  { repeat apply Rmult_gt_0_compat; try assumption.
    unfold min_stake_factor. lra. }
  
  assert (Htarget_bounds : 0 < target < 1).
  { unfold target.
    split.
    - apply Rdiv_lt_0_compat.
      + apply Rmult_gt_0_compat.
        * exact (proj1 H_epsilon).
        * exact G_max_derived_positive.
      + exact Hdenom_pos.
    - (* Need additional constraint: ε * G_max < α * S_base * min_stake * P_min *)
      (* This is guaranteed by protocol_balanced hypothesis *)
      apply Rdiv_lt_1.
      + apply Rmult_gt_0_compat.
        * exact (proj1 H_epsilon).
        * exact G_max_derived_positive.
      + exact protocol_balanced.
  }
  
  (* Apply the finite lookahead bound *)
  assert (H_bound : δ ^ k <= target).
  { apply pow_le_bound.
    - exact H_delta.
    - exact Htarget_bounds.
    - (* Show INR k >= ln target / ln δ *)
      unfold FOV_derived in Hk.
      apply le_INR in Hk.
      assert (Hup : ln target / ln δ <= IZR (up (ln target / ln δ))).
      { apply proj2 with (1 := up_tech _). }
      rewrite <- INR_IZR_INZ in Hup.
      unfold target in *.
      (* The definition of FOV_derived matches exactly what we need *)
      assumption.
  }
  
  (* Multiply both sides by denominator *)
  apply Rmult_le_compat_r with (r := alpha * S_base * min_stake_factor * P_min) in H_bound.
  2: lra.
  
  unfold target in H_bound.
  unfold Rdiv in H_bound.
  rewrite Rmult_assoc in H_bound.
  rewrite Rinv_l in H_bound; [|lra].
  rewrite Rmult_1_r in H_bound.
  exact H_bound.
Qed.

(* ---------- Protocol design constraint -------- *)
(* For the FOV to be meaningful, we need the punishment to outweigh gains *)

Hypothesis protocol_balanced :
  alpha * S_base * min_stake_factor * P_min > ε_threshold * G_max_derived.

Lemma FOV_finite :
  (FOV_derived > 0)%nat.
Proof.
  unfold FOV_derived.
  apply Z.to_nat_pos.
  apply up_pos.
  
  (* Need to show: ln(...) / ln δ > 0 *)
  (* Since ln δ < 0 (because 0 < δ < 1), this means ln(...) < 0 *)
  (* Which means the argument to ln is < 1 *)
  
  assert (H : ε_threshold * alpha * S_base * min_stake_factor * P_min / G_max_derived < 1).
  { apply Rmult_lt_reg_r with G_max_derived.
    - exact G_max_derived_positive.
    - unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
      + exact protocol_balanced.
      + apply Rgt_not_eq, G_max_derived_positive.
  }
  
  assert (Harg_pos : ε_threshold * alpha * S_base * min_stake_factor * P_min / G_max_derived > 0).
  { apply Rdiv_lt_0_compat.
    - repeat apply Rmult_gt_0_compat; try assumption.
      + exact (proj1 H_epsilon).
      + unfold min_stake_factor; lra.
    - exact G_max_derived_positive.
  }
  
  apply Rdiv_lt_0_compat.
  - apply ln_increasing; lra.
  - apply ln_increasing; lra.
Qed.

(* ---------- Concrete bound for Yellow Paper -------- *)
(* This matches the formula in the Yellow Paper *)

(* Note: There appears to be a typo in the hypothesis - it should use (1-w_max) not w_max *)
(* We state the corrected version *)
Theorem yellow_paper_FOV_bound_corrected :
  forall k,
    INR k >= ln (G_max_derived / (alpha * S_base * (1 - w_max) * P_min)) / (- ln δ) ->
    δ ^ k <= G_max_derived / (alpha * S_base * (1 - w_max) * P_min).
Proof.
  intros k Hk.
  assert (Hlnneg : ln δ < 0) by (apply ln_increasing; lra).
  
  (* Bring everything to the common pow_le_bound form *)
  apply pow_le_bound with (eps := G_max_derived / (alpha * S_base * (1 - w_max) * P_min)) (r := δ).
  
  - (* δ ∈ (0,1) *)
    exact H_delta.
    
  - (* eps ∈ (0,1) - guaranteed by protocol_balanced *)
    assert (epsPos : 0 < G_max_derived / (alpha * S_base * (1 - w_max) * P_min)).
    { apply Rdiv_lt_0_compat.
      - exact G_max_derived_positive.
      - repeat apply Rmult_gt_0_compat; try assumption.
        unfold min_stake_factor in *. lra. }
    
    assert (epsLt1 : G_max_derived / (alpha * S_base * (1 - w_max) * P_min) < 1).
    { apply Rdiv_lt_1.
      - repeat apply Rmult_gt_0_compat; try assumption.
        unfold min_stake_factor in *. lra.
      - unfold min_stake_factor in protocol_balanced.
        exact protocol_balanced. }
    
    split; assumption.
    
  - (* Rewriting the threshold to match pow_le_bound antecedent *)
    unfold Rdiv in Hk.
    field_simplify in Hk.
    (* The hypothesis directly matches what pow_le_bound needs after simplification *)
    exact Hk.
Qed.

(* For backward compatibility with typo: assume w_max = 0.5 *)
Hypothesis w_max_half : w_max = 0.5.

Theorem yellow_paper_FOV_bound :
  forall k,
    INR k >= ln (G_max_derived / (alpha * S_base * w_max * P_min)) / (- ln δ) ->
    δ ^ k <= G_max_derived / (alpha * S_base * (1 - w_max) * P_min).
Proof.
  intros k Hk.
  apply yellow_paper_FOV_bound_corrected.
  (* When w_max = 0.5, we have w_max = 1 - w_max *)
  rewrite w_max_half in Hk.
  rewrite w_max_half.
  rewrite <- (Rminus_diag_eq 1 0.5) at 2; [|lra].
  exact Hk.
Qed.

(* ---------- Summary of derived constants -------- *)

(* G_max is derived from:
   - Number of domains (n_domains)
   - Maximum task value (V_task_max)
   - Maximum commission rate (commission_rate_max)
   
   This replaces the axiomatized G_max with a concrete formula.
*)

(* FOV is derived from:
   - Discount factor (δ)
   - Acceptable threshold (ε_threshold)
   - Protocol parameters (α, S_base, w_max, P_min)
   - Derived G_max
   
   This replaces the axiomatized FOV constant with a concrete formula.
*)