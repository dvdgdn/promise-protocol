
(**
 * Agency Protocol – Mechanisation of Theorem 2 and Theorem 3 (simplified)
 *
 *  • T2_Nash :  If each agent’s “keep” utility exceeds their “break” utility
 *               given the other keeps, then (keep,keep) is a Nash equilibrium
 *               in the 2‑player promise game.
 *
 *  • T3_Honesty :  With positive detection probability and penalties, the
 *               expected utility of a dishonest assessment is strictly lower
 *               than that of an honest one, hence honesty is a best response.
 *
 *  The proofs avoid heavy probability libraries by modelling expectation
 *  algebraically, which suffices for the Yellow‑Paper inequality.
 *)

Require Import Reals.
Open Scope R_scope.

(* ---------- Simple 2‑player promise game ---------- *)
Inductive strat : Type := Keep | Break.

(* Parameters for agent A and B *)
Variables ΔU_keep_A  ΔU_break_A  : R.
Variables ΔU_keep_B  ΔU_break_B  : R.

(* Utilities given a strategy profile *)
Definition U_A (sA sB : strat) : R :=
  match sA with
  | Keep  => ΔU_keep_A
  | Break => ΔU_break_A
  end.

Definition U_B (sA sB : strat) : R :=
  match sB with
  | Keep  => ΔU_keep_B
  | Break => ΔU_break_B
  end.

(* Nash equilibrium definition for 2 players *)
Definition Nash (sA sB : strat) : Prop :=
  (U_A sA sB >= U_A Break sB) (* A can’t gain by deviating *)
  /\ (U_B sA sB >= U_B sA Break). (* B can’t gain by deviating *)

Hypotheses
  (H_A_pref : ΔU_keep_A > ΔU_break_A)
  (H_B_pref : ΔU_keep_B > ΔU_break_B).

Theorem T2_Nash :
  Nash Keep Keep.
Proof.
  unfold Nash, U_A, U_B.
  split; lra.
Qed.

(* ---------- Simplified Honest‑assessment theorem ---------- *)

(* Parameters *)
Variables P_detect        (* probability dishonest act is detected *)
          penalty_merit   (* β⋅|ΔM| merit penalty when caught      *)
          future_cost     (* δ·ΔFOV lost opportunity for dishonesty *)
  : R.

Hypotheses
  (H_Pd_pos  : 0 < P_detect <= 1)
  (H_pen_pos : penalty_merit > 0)
  (H_fut_pos : future_cost   > 0).

(* Expected utility: honest assessment baseline = 0 *)
Definition EU_honest   : R := 0.
Definition EU_dishonest : R :=
  - P_detect * penalty_merit - future_cost.

Theorem T3_Honesty : EU_honest > EU_dishonest.
Proof.
  unfold EU_honest, EU_dishonest.
  assert (P_detect * penalty_merit > 0) by (apply Rmult_lt_0_compat; lra).
  lra.
Qed.
