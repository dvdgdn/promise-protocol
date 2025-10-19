(*---------------------------------------------------------------------
  AgencyProtocol_ParamsWitness.v
  -------------------------------------------------------------
  A **concrete, machine‑checked witness** that all of the economic
  and stake‑related inequalities used in the Agency‑Protocol proofs
  can indeed be satisfied simultaneously.

  The file exposes a single lemma:

        params_feasible  :  <tuple satisfies every constraint>

  and a constructive witness:

        exists_feasible_params : ∃ params, Constraints params.

  ------------------------------------------------------------------*)

Require Import Reals Psatz.
Open Scope R_scope.

(* ----------------------------------------------------------------- *)
(** Concrete parameter choices  — all rational to keep arithmetic exact *)

Definition S_base        : R := 320.             (* credits *)
Definition delta         : R := 24 / 25.         (* 0.96  *)
Definition V_task_max    : R := 45.              (* credits *)
Definition commission_max: R := 17 / 100.        (* 0.17  *)
Definition n_domains     : nat := 3%nat.
Definition C_op          : R := 5.               (* credits *)

Definition alpha         : R := 1.               (* utility weight *)
Definition beta          : R := 1 / 2.           (* 0.5   *)
Definition ΔM_gap        : R := 3 / 10.          (* 0.30  *)

(* ----------------------------------------------------------------- *)
(** Derived constant (matches AgencyProtocol_DerivedConstants.v) *)
Definition G_max : R := INR n_domains * V_task_max * commission_max.

(* ----------------------------------------------------------------- *)
(**  "Master feasibility lemma" — every prerequisite inequality *)
Definition params_feasible : Prop :=
    0 <   delta               < 1                       /\
    0 <   commission_max      < 1                       /\
          S_base              > 0                       /\
          C_op                > 0                       /\
          G_max               > 0                       /\
          (*  Stake lower‑bound from single‑round best‑response  *)
          S_base  >  G_max + C_op - (beta / alpha) * ΔM_gap.

Lemma params_feasible_proof : params_feasible.
Proof.
  unfold params_feasible,
         S_base, delta, commission_max, C_op,
         V_task_max, n_domains, G_max, alpha, beta, ΔM_gap.
  repeat split; vm_compute; lra.
Qed.

(* ----------------------------------------------------------------- *)
(**  A lightweight record, just so downstream proofs can `destruct` it *)
Record WitnessParams := {
  wp_S_base        : R;
  wp_delta         : R;
  wp_V_task_max    : R;
  wp_commission_max: R;
  wp_n_domains     : nat;
  wp_C_op          : R;
  wp_alpha         : R;
  wp_beta          : R;
  wp_ΔM_gap        : R
}.

Definition witness : WitnessParams := {|  
  wp_S_base         := S_base;
  wp_delta          := delta;
  wp_V_task_max     := V_task_max;
  wp_commission_max := commission_max;
  wp_n_domains      := n_domains;
  wp_C_op           := C_op;
  wp_alpha          := alpha;
  wp_beta           := beta;
  wp_ΔM_gap         := ΔM_gap
|}.

Theorem exists_feasible_params : params_feasible.
Proof.
  exact params_feasible_proof.
Qed.

(* ----------------------------------------------------------------- *)
(**  Convenience tactic for other files:  `apply witness_feasible`. *)
Theorem witness_feasible : params_feasible.
Proof. exact params_feasible_proof. Qed.

(*------------------------------  End  ------------------------------*)