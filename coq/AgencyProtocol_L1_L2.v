
(**
 * Agency Protocol – Mechanisation of Lemma 1 and Lemma 2
 *
 * Lemma 1:  For M' > M in [0,1],  FOV(n, M') > FOV(n, M).
 * Lemma 2:  With ΔM_plus > 0 and ΔM_minus < 0,
 *           FOV(M + ΔM_plus) – FOV(M + ΔM_minus) > 0.
 *
 * We abstract away the full geometric‑series constant and simply
 * model FOV(n, M) as K·w(M) where K>0 and w is a strictly
 * increasing merit‑discount function on [0,1].  This captures the
 * monotonic property the Yellow Paper relies on.
 *
 * Dependencies: Coq Reals.
 *)

Require Import Reals.
Open Scope R_scope.

(* -------- Parameters ---------- *)
Variable K : R.                 (* positive constant factor        *)
Hypothesis K_pos : K > 0.

Variable w : R -> R.            (* merit-discount function         *)

(* Strict monotonicity on [0,1]                                    *)
Hypothesis w_strict_inc :
  forall x y, 0 <= x <= 1 -> 0 <= y <= 1 -> x < y -> w x < w y.

(* Future‑Opportunity‑Value function (n suppressed – absorbed in K) *)
Definition FOV (M:R) : R := K * w M.

(* ---------------- Lemma 1 ---------------- *)
Lemma L1_FOV_monotone :
  forall M M',
    0 <= M <= 1 ->
    0 <= M' <= 1 ->
    M < M' ->
    FOV M < FOV M'.
Proof.
  intros M M' HM HM' Hlt.
  unfold FOV.
  apply Rmult_lt_compat_l; try apply K_pos.
  apply w_strict_inc; assumption.
Qed.

(* ------------- Lemma 2 ------------------- *)
Variables ΔM_plus ΔM_minus : R.

Hypotheses
  (H_plus_pos  : ΔM_plus  > 0)              (* merit gain on keep  *)
  (H_minus_neg : ΔM_minus < 0).             (* merit loss on break *)

Variable M0 : R.
Hypothesis H_range : 0 <= M0 <= 1.
(* Need resulting merits stay in [0,1] for monotonic hypothesis   *)
Hypothesis H_range_plus  : 0 <= M0 + ΔM_plus  <= 1.
Hypothesis H_range_minus : 0 <= M0 + ΔM_minus <= 1.

Lemma L2_FOV_difference_positive :
  FOV (M0 + ΔM_plus) - FOV (M0 + ΔM_minus) > 0.
Proof.
  unfold FOV.
  (* Use monotonic lemma with points in correct order *)
  assert (H_lt : M0 + ΔM_minus < M0 + ΔM_plus) by lra.
  specialize (L1_FOV_monotone (M:= M0 + ΔM_minus) (M':= M0 + ΔM_plus)).
  intro Hmono.
  assert (Hcond := Hmono H_range_minus H_range_plus H_lt).
  lra.
Qed.
