
(**
 * Agency Protocol – Corollary 4.1 (Pareto Optimality) in narrow model
 *
 * Claim: Under the same inequality  ΔK > (1−δ)ΔB, the cooperative
 *         profile (Keep,Keep) yields strictly higher *total discounted
 *         welfare* than any profile where at least one player always
 *         Breaks, hence no other feasible constant profile Pareto‑dominates it.
 *
 * For simplicity we compare against:
 *   • always‑break by both,    (Break,Break)
 *   • asymmetric (Break,Keep)  or (Keep,Break).
 *
 * Because pay‑offs are independent of opponent, “someone breaks ever”
 * already lowers *that* person’s own utility below U_coop; therefore
 * social welfare (sum) is lower.
 *)

Require Import Reals.
Require Import Lra.
Open Scope R_scope.

Load AgencyProtocol_SPE_Narrow.  (* reuse parameters & lemmas *)

(* Utilities for constant break profile *)
Definition U_break : R := ΔB / (1 - δ).

(* Welfare (sum) definitions *)
Definition W_coop  : R := 2 * U_coop.
Definition W_bothB : R := 2 * U_break.
Definition W_asym  : R := U_break + U_coop.  (* one breaks, one keeps *)

Lemma coop_vs_break_single : U_coop > U_break.
Proof.
  unfold U_coop, U_break.
  assert (Dpos: 1 - δ > 0) by (destruct Hδ; lra).
  apply Rmult_lt_reg_r with (r:=1-δ) in Dpos.
  2:{ exact Dpos. }
  field_simplify in Dpos. lra.
Qed.

(* ---------- Corollary 4.1: Pareto optimality ---------- *)
Theorem C41_Pareto :
  W_coop > W_bothB /\ W_coop > W_asym.
Proof.
  unfold W_coop, W_bothB, W_asym.
  split.
  - (* both break case *)
    apply Rmult_lt_compat_l with (r:=2); lra using coop_vs_break_single.
  - (* asymmetric case *)
    unfold Rplus.
    assert (U_coop + U_coop > U_break + U_coop) by lra using coop_vs_break_single.
    lra.
Qed.
