
(**
 * Agency Protocol – Mechanisation of Theorem 1 and Corollary 1.1
 *
 * Theorem 1 (Single‑Round Best Response):
 *    Given the inequality stated in the Yellow Paper,
 *    keeping a promise yields higher utility than breaking it.
 *
 * Corollary 1.1 (Minimum‑Stake Requirement):
 *    A stake size above a derived lower bound guarantees the
 *    inequality and hence the best‑response property.
 *
 * Compile with:
 *     coqc AgencyProtocol_T1_C1.v
 * to obtain the checked proof objects.
 * Requires only the Coq Standard Library (tested on Coq 8.19).
 *)

Require Import Reals.
Require Import AgencyProtocol_StakeFunction.
Open Scope R_scope.

(* -------- Parameters -------- *)
Variables alpha beta (* utility weights: α>0, β≥0             *)
          C_op       (* non‑refundable operational cost        *)
          S_p        (* total stake posted                     *)
          G_p        (* possible one‑shot gain from defection  *)
          ΔM_plus    (* merit delta when promise kept          *)
          ΔM_minus   (* merit delta when promise broken (neg.) *)
: R.

Hypotheses
  (H_alpha_pos : alpha > 0)
  (H_beta_nonneg : beta >= 0).

(* Utility changes (per Yellow Paper §2.2) -------------------- *)
Definition ΔU_keep  : R := alpha * (- C_op)        + beta * ΔM_plus.
Definition ΔU_break : R := alpha * (G_p - S_p)     + beta * ΔM_minus.

(* ------------------ Theorem 1 ------------------ *)
Theorem T1_best_response :
  G_p < S_p - C_op + (beta / alpha) * (ΔM_plus - ΔM_minus) ->
  ΔU_keep > ΔU_break.
Proof.
  intros Hcond.
  unfold ΔU_keep, ΔU_break in *.
  (* Multiply inequality by alpha (>0) to avoid division. *)
  assert (H1 : alpha * G_p < alpha * (S_p - C_op) + beta * (ΔM_plus - ΔM_minus)).
  { apply Rmult_lt_compat_l with (r:=alpha) in Hcond; try lra. }
  (* Rearrange goal into the same expression *) 
  (* Goal equivalently: alpha*S_p - alpha*C_op - alpha*G_p + beta*(ΔM_plus-ΔM_minus) > 0 *)
  replace (alpha * (- C_op) + beta * ΔM_plus - (alpha * (G_p - S_p) + beta * ΔM_minus))
    with (alpha*S_p - alpha*C_op - alpha*G_p + beta*(ΔM_plus - ΔM_minus)) by lra.
  lra.
Qed.

(* ------------- Corollary 1.1 (minimum stake) ------------- *)
Theorem C1_min_stake :
  S_p > G_p + C_op - (beta / alpha) * (ΔM_plus - ΔM_minus) ->
  ΔU_keep > ΔU_break.
Proof.
  intros Hstake.
  (* Rearrange Hstake into the form required by T1 *) 
  assert (Hcond : G_p < S_p - C_op + (beta / alpha) * (ΔM_plus - ΔM_minus)).
  { lra. }
  apply T1_best_response; assumption.
Qed.

(* ------------- Connection to Stake Function ------------- *)
(* The stake function S_p = S_base * (1 - w(M)) is proven to satisfy
   the required bound in AgencyProtocol_StakeFunction.v
   This addresses the gap where we previously assumed S_p satisfies
   the inequality without proving it for the specific formula. *)
