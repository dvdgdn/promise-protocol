
(**
 * Agency Protocol – Theorem 11 (Error‑Tolerance Bound)
 * ----------------------------------------------------
 * Simplified statement used in Yellow Paper section 6:
 *
 *   Let
 *        ΔC  > 0   — utility advantage of cooperation
 *        ΔD  > 0   — potential gain from defection
 *
 *   An agent with deviation probability ε ∈ (0,1) obtains expected
 *   incremental utility
 *
 *       EU_coop  = (1−ε)·ΔC          (cooperate most of the time)
 *       EU_def   = ε·ΔD              (defect in ε fraction of moves)
 *
 *   If      ε  <  ΔC / (ΔC + ΔD)
 *   then    EU_coop > EU_def.
 *
 * Therefore cooperation remains the best stochastic strategy as long
 * as the error‑rate ε is below  ΔC/(ΔC+ΔD), matching the bound quoted
 * in the Yellow Paper:
 *
 *        ε < ΔU_min(cooperate) / ΔU_max(defect)
 *
 * Dependencies: Coq Reals.
 *)

Require Import Reals Lra.
Open Scope R_scope.

Variables ΔC ΔD ε : R.
Hypotheses (HΔC : ΔC > 0) (HΔD : ΔD > 0).
Hypothesis  (Hε  : 0 < ε < ΔC / (ΔC + ΔD)).

(* Expected incremental utilities ------------------------------------- *)
Definition EU_coop : R := (1 - ε) * ΔC.
Definition EU_def  : R := ε * ΔD.

Lemma T11_error_bound :
  EU_coop > EU_def.
Proof.
  unfold EU_coop, EU_def.
  assert (Hdenpos : ΔC + ΔD > 0) by lra.
  destruct Hε as [Hεpos Hεub].
  (* Multiply inequality by positive denominator to clear fraction *)
  apply Rmult_lt_reg_l with (r:=ΔC + ΔD) in Hεub; try lra.
  (* ε(ΔC+ΔD) < ΔC  ->  εΔC + εΔD < ΔC *)
  rewrite <- Rmult_plus_distr_r in Hεub.
  (* Rearrange to show target inequality *)
  lra.
Qed.
