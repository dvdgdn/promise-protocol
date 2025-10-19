(**
 * Agency Protocol – Theorem 10 (Coalition-Proof Equilibrium) – Generalized
 *
 * This extends the coalition-proof equilibrium to handle:
 *   - Heterogeneous payoffs (ΔK_i, ΔB_i vary by agent)
 *   - Variable stakes S_i per agent
 *   - Merit weights that differ across agents
 *
 * The key insight is that if the stake condition holds for each agent
 * individually, then no coalition can achieve a Pareto improvement.
 *)

Require Import Reals Lra List.
Require Import AgencyProtocol_StakeFunction.
Import ListNotations.
Open Scope R_scope.

(* ---------- Agent-specific parameters ----------------------------------- *)
Record Agent := {
  id : nat;
  alpha_i : R;
  beta_i : R;
  stake_i : R;
  merit_i : R;
  ΔK_i : R;  (* payoff from keeping promise *)
  ΔB_i : R;  (* payoff from breaking promise *)
  C_op_i : R (* operational cost *)
}.

(* ---------- Well-formed agent conditions -------------------------------- *)
Definition well_formed_agent (a : Agent) : Prop :=
  alpha_i a > 0 /\
  beta_i a >= 0 /\
  stake_i a > 0 /\
  0 <= merit_i a <= 1 /\
  ΔK_i a > 0 /\
  ΔB_i a > ΔK_i a /\
  C_op_i a > 0.

(* ---------- Individual rationality constraint --------------------------- *)
(* Each agent must satisfy the stake condition from Theorem 1 *)
Definition satisfies_stake_condition (a : Agent) (δ : R) : Prop :=
  ΔK_i a > (1 - δ) * ΔB_i a /\
  stake_i a > ΔB_i a - ΔK_i a + C_op_i a.

(* ---------- Utility calculations ---------------------------------------- *)
Variable δ : R.
Hypothesis Hδ : 0 < δ < 1.

(* Utility from always cooperating *)
Definition U_coop_i (a : Agent) : R :=
  (ΔK_i a - C_op_i a) / (1 - δ).

(* Utility from defecting once then cooperating *)
Definition U_defect_once_i (a : Agent) : R :=
  (ΔB_i a - stake_i a) + δ * U_coop_i a.

(* ---------- Individual deviation is unprofitable ------------------------ *)
Lemma individual_deviation_unprofitable :
  forall a,
    well_formed_agent a ->
    satisfies_stake_condition a δ ->
    U_defect_once_i a < U_coop_i a.
Proof.
  intros a Hwf [HSPE Hstake].
  unfold U_defect_once_i, U_coop_i.
  
  (* Multiply through by (1 - δ) > 0 *)
  assert (Dpos : 1 - δ > 0) by lra.
  apply Rmult_lt_reg_r with (r := 1 - δ).
  { exact Dpos. }
  
  field_simplify.
  (* Need to show: (ΔB_i - stake_i)(1-δ) + δ(ΔK_i - C_op_i) < ΔK_i - C_op_i *)
  (* Rearranging: (ΔB_i - stake_i)(1-δ) < (1-δ)(ΔK_i - C_op_i) *)
  (* Dividing by (1-δ): ΔB_i - stake_i < ΔK_i - C_op_i *)
  (* Rearranging: stake_i > ΔB_i - ΔK_i + C_op_i *)
  
  (* This is exactly our stake condition! *)
  lra.
Qed.

(* ---------- Coalition model --------------------------------------------- *)
(* A coalition is a list of agents *)
Definition Coalition := list Agent.

(* Coalition members all defect in period 0, then everyone cooperates *)
Definition coalition_utility (a : Agent) (C : Coalition) : R :=
  if In_dec (fun x y => Nat.eq_dec (id x) (id y)) a C
  then U_defect_once_i a
  else U_coop_i a.

(* Pareto improvement: all coalition members strictly better off *)
Definition pareto_improves (C : Coalition) : Prop :=
  forall a, In a C -> coalition_utility a C > U_coop_i a.

(* ---------- Main coalition-proofness theorem ---------------------------- *)
Theorem T10_coalition_proof_generalized :
  forall (agents : list Agent) (C : Coalition),
    (* All agents are well-formed *)
    Forall well_formed_agent agents ->
    (* All agents satisfy their individual stake conditions *)
    Forall (fun a => satisfies_stake_condition a δ) agents ->
    (* Coalition is non-empty subset of agents *)
    C <> [] ->
    Forall (fun c => In c agents) C ->
    (* Then coalition cannot achieve Pareto improvement *)
    ~ pareto_improves C.
Proof.
  intros agents C Hwf_all Hstake_all Hnonempty Hsubset.
  unfold pareto_improves, coalition_utility.
  intro Hpareto.
  
  (* Pick any member of the coalition *)
  destruct C as [|c cs] eqn:EC.
  { contradiction. }
  
  (* Agent c is in the coalition *)
  assert (Hin_c : In c (c :: cs)) by (left; reflexivity).
  
  (* c is also in the original agent list *)
  assert (Hin_agents : In c agents).
  { rewrite <- EC in Hsubset.
    rewrite Forall_forall in Hsubset.
    apply Hsubset. exact Hin_c. }
  
  (* c is well-formed and satisfies stake condition *)
  assert (Hwf_c : well_formed_agent c).
  { rewrite Forall_forall in Hwf_all. apply Hwf_all. exact Hin_agents. }
  
  assert (Hstake_c : satisfies_stake_condition c δ).
  { rewrite Forall_forall in Hstake_all. apply Hstake_all. exact Hin_agents. }
  
  (* c gets coalition utility = defect utility *)
  assert (Hutil_c : coalition_utility c (c :: cs) = U_defect_once_i c).
  { unfold coalition_utility.
    destruct (In_dec _ c (c :: cs)).
    - reflexivity.
    - contradiction n. exact Hin_c. }
  
  (* By Pareto improvement, c should be better off *)
  specialize (Hpareto c Hin_c).
  rewrite <- EC in Hutil_c.
  rewrite Hutil_c in Hpareto.
  
  (* But individual deviation is unprofitable *)
  pose proof (individual_deviation_unprofitable c Hwf_c Hstake_c).
  
  (* Contradiction *)
  lra.
Qed.

(* ---------- Special case: homogeneous agents ---------------------------- *)
(* When all agents are identical, we recover the original result *)

Definition homogeneous_agents (n : nat) (ΔK ΔB C_op stake : R) : list Agent :=
  map (fun i => {|
    id := i;
    alpha_i := 1;
    beta_i := 0;
    stake_i := stake;
    merit_i := 0;
    ΔK_i := ΔK;
    ΔB_i := ΔB;
    C_op_i := C_op
  |}) (seq 0 n).

Theorem T10_homogeneous_special_case :
  forall n ΔK ΔB C_op stake,
    n > 0 ->
    ΔK > 0 ->
    ΔB > ΔK ->
    C_op > 0 ->
    stake > ΔB - ΔK + C_op ->
    ΔK > (1 - δ) * ΔB ->
    forall C : Coalition,
      C <> [] ->
      Forall (fun c => In c (homogeneous_agents n ΔK ΔB C_op stake)) C ->
      ~ pareto_improves C.
Proof.
  intros n ΔK ΔB C_op stake Hn HΔK HΔB HC_op Hstake HSPE C Hnonempty Hsubset.
  apply T10_coalition_proof_generalized with (agents := homogeneous_agents n ΔK ΔB C_op stake).
  - (* All agents well-formed *)
    apply Forall_forall. intros a Ha.
    unfold homogeneous_agents in Ha.
    apply in_map_iff in Ha.
    destruct Ha as [i [Hi Ha]].
    rewrite <- Hi.
    unfold well_formed_agent. simpl.
    repeat split; lra.
  - (* All satisfy stake condition *)
    apply Forall_forall. intros a Ha.
    unfold homogeneous_agents in Ha.
    apply in_map_iff in Ha.
    destruct Ha as [i [Hi Ha]].
    rewrite <- Hi.
    unfold satisfies_stake_condition. simpl.
    split; assumption.
  - exact Hnonempty.
  - exact Hsubset.
Qed.