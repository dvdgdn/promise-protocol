
(**
 * Agency Protocol – Theorem 8 (Trust Reinforcement Feedback)
 *
 * Simplified formalisation:
 *   Merit ∈ [0,1].  Stake(M) = S_base · (1 − w(M))
 *   with w:[0,1]→[0,1) strictly increasing.
 *
 *   Merit update when honest:  M' = M + Δ  (Δ>0, keep in [0,1])
 *
 * Claim:
 *   Stake(M') < Stake(M).  I.e., honesty lowers future stake, providing
 *   positive feedback.
 *)

Require Import Reals Lra.
Open Scope R_scope.

Variable S_base : R.  Hypothesis Spos : S_base > 0.
Variable w : R -> R.
Hypothesis w_mon :
  forall x y, 0<=x<=1 -> 0<=y<=1 -> x<y -> w x < w y.
Hypothesis w_range : forall m, 0<=m<=1 -> 0 <= w m < 1.

Definition Stake (M:R) : R := S_base * (1 - w M).

Variables M Δ : R.
Hypotheses (H_M_range : 0 <= M <= 1)
           (H_Dpos : Δ > 0)
           (H_Mp_range : 0 <= M+Δ <= 1).

Lemma T8_stake_decreases :
  Stake (M + Δ) < Stake M.
Proof.
  unfold Stake.
  apply Rmult_lt_compat_l; try exact Spos.
  (* compare 1-w(M+Δ)  vs  1-w(M)  *)
  assert (Hwm : w M < w (M+Δ)).
  { apply w_mon; try lra.
    - exact H_M_range.
    - exact H_Mp_range.
    - lra.
  }
  lra.
Qed.
