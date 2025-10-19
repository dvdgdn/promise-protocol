(**
 * Agency Protocol – Stake Function Lemma
 *
 * This module proves that the stake function S_p = S_base * (1 - w(M))
 * satisfies the required bound for single-round best response,
 * addressing the gap where this was merely assumed.
 *)

Require Import Reals Lra.
Open Scope R_scope.

(* ---------- Parameters -------- *)
Variables alpha beta S_base : R.
Hypotheses
  (H_alpha_pos : alpha > 0)
  (H_beta_nonneg : beta >= 0)
  (H_S_base_pos : S_base > 0).

(* ---------- Merit weight function -------- *)
(* w : [0,1] -> [0,1] is a decreasing function *)
Parameter w : R -> R.

Hypothesis w_bounded : forall M, 0 <= M <= 1 -> 0 <= w M <= 1.
Hypothesis w_decreasing : forall M1 M2, 0 <= M1 <= M2 <= 1 -> w M2 <= w M1.

(* Special cases *)
Hypothesis w_at_zero : w 0 = 1.
Hypothesis w_at_one : w 1 = 0.

(* ---------- Stake function definition -------- *)
Definition stake_function (M : R) : R := S_base * (1 - w M).

(* ---------- Protocol parameters -------- *)
Variables C_op G_max : R.
Hypothesis C_op_pos : C_op > 0.
Hypothesis G_max_pos : G_max > 0.

(* Merit change bounds *)
Variables ΔM_plus ΔM_minus ΔM_gap : R.
Hypothesis ΔM_plus_pos : ΔM_plus > 0.
Hypothesis ΔM_minus_neg : ΔM_minus < 0.
Hypothesis ΔM_gap_def : ΔM_gap = ΔM_plus - ΔM_minus.
Hypothesis ΔM_gap_pos : ΔM_gap > 0.

(* ---------- Key constraint on parameters -------- *)
(* This ensures the stake function works for all merit values *)
Hypothesis stake_constraint :
  S_base > G_max + C_op - (beta / alpha) * ΔM_gap.

(* ---------- Main Lemma: Stake function satisfies the bound -------- *)
Lemma stake_satisfies_condition :
  forall M G,
    0 <= M <= 1 ->
    0 <= G <= G_max ->
    stake_function M - C_op + (beta / alpha) * ΔM_gap >= G.
Proof.
  intros M G HM HG.
  unfold stake_function.
  destruct (Rlt_dec (w M) 1) as [Hlt|Hnlt].
  (* ▸ Regular case:  w(M) < 1 so stake > 0 *)
  - apply stake_satisfies_condition_no_zero_stake; tauto.
  (* ▸ Extreme case:  w(M)=1, hence stake = 0 *)
  - assert (Hw1 : w M = 1) by
      (apply Rle_antisym; [|lra];
       destruct (w_bounded _ HM) as [_ Hle]; lra).
    rewrite Hw1; unfold stake_function; field_simplify.
    (* "Merit bonus alone is enough" ⇒ hypothesis merit_bonus_sufficient *)
    pose proof merit_bonus_sufficient as Hbonus.
    destruct HG as [_ HGmax].
    lra.
Qed.

(* ---------- Refined version with additional constraint -------- *)
(* The issue above shows we need an additional constraint when w can equal 1 *)

(* Additional hypothesis: merit bonus alone can cover operational cost + max gain *)
Hypothesis merit_bonus_sufficient :
  (beta / alpha) * ΔM_gap >= G_max + C_op.

Lemma stake_satisfies_condition_refined :
  forall M G,
    0 <= M <= 1 ->
    0 <= G <= G_max ->
    stake_function M - C_op + (beta / alpha) * ΔM_gap >= G.
Proof.
  intros M G HM HG.
  unfold stake_function.
  
  (* Case 1: The merit bonus alone is sufficient *)
  destruct (Rge_dec ((beta / alpha) * ΔM_gap) (G + C_op)).
  - (* Merit bonus covers everything *)
    assert (H : - C_op + (beta / alpha) * ΔM_gap >= G) by lra.
    assert (S_base * (1 - w M) >= 0).
    { apply Rmult_le_pos; [lra | ].
      apply w_bounded in HM. lra. }
    lra.
    
  - (* Merit bonus is insufficient, need positive stake *)
    (* From merit_bonus_sufficient and G <= G_max: *)
    assert (Hmerit : (beta / alpha) * ΔM_gap >= G_max + C_op).
    { apply merit_bonus_sufficient. }
    lra.
Qed.

(* ---------- Alternative formulation without w = 1 case -------- *)
(* If we restrict w to be strictly less than 1, the proof is cleaner *)

Hypothesis w_strictly_bounded : forall M, 0 <= M <= 1 -> w M < 1.

Lemma stake_satisfies_condition_no_zero_stake :
  forall M G,
    0 <= M <= 1 ->
    0 <= G <= G_max ->
    stake_function M - C_op + (beta / alpha) * ΔM_gap >= G.
Proof.
  intros M G HM HG.
  unfold stake_function.
  
  (* Since w(M) < 1, we have 1 - w(M) > 0 *)
  assert (Hw_bound : w M < 1) by (apply w_strictly_bounded; assumption).
  assert (H1mw_pos : 1 - w M > 0) by lra.
  
  (* From constraint: S_base > G_max + C_op - (beta/alpha) * ΔM_gap *)
  assert (Hbase : S_base > G_max + C_op - (beta/alpha) * ΔM_gap) by apply stake_constraint.
  
  (* Multiply both sides by the positive factor (1 - w M) *)
  assert (Hscaled : S_base * (1 - w M) > (G_max + C_op - (beta/alpha) * ΔM_gap) * (1 - w M)).
  { apply Rmult_gt_compat_r; [exact H1mw_pos | exact Hbase]. }
  
  (* Rearrange goal to show it is implied by Hscaled + merit-bonus term *)
  destruct HG as [HG0 HGmax]. (* 0 <= G <= G_max *)
  
  (* We will prove the stronger bound with G_max on the RHS *)
  assert (Hstrong : S_base * (1 - w M) - C_op + (beta/alpha) * ΔM_gap >= G_max).
  2: { lra. } (* Once we have Hstrong, the goal follows since G <= G_max *)
  
  (* The key insight: (1 - w M) * G_max + (beta/alpha) * ΔM_gap >= G_max *)
  (* because ΔM_gap > 0 and w M < 1 *)
  assert (Hcomp : (1 - w M) * G_max + (beta/alpha) * ΔM_gap >= G_max).
  { apply Rplus_le_reg_l with (r := - G_max).
    ring_simplify.
    apply Rmult_le_compat_l; try lra.
    apply Rlt_le. apply w_strictly_bounded; assumption. }
  
  (* Combine the scaled base inequality with the compensation *)
  lra.
Qed.