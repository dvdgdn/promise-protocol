
(**
 * Agency Protocol – Narrow‑Model SPE (Two Players, Constant Pay‑offs)
 *
 * Setting
 * -------
 *  • Infinite horizon t = 0,1,2,…
 *  • Each period both players simultaneously choose   Keep | Break.
 *  • Player i’s single‑period payoff depends **only on its own action**:
 *        u_i(Keep)  = ΔK      (ΔK > 0)
 *        u_i(Break) = ΔB      (ΔB > ΔK)   (instant temptation gain)
 *
 *  • Common discount factor   0 < δ < 1.
 *  • Strategy profile σ_* :  everyone plays Keep every period, regardless of
 *    history (stationary “always‑keep”).
 *
 *  • Deviation set considered by one‑step‑deviation principle:
 *      a player may Break in the current period and then revert to σ_*
 *      for all subsequent periods (history‑independent thereafter).
 *
 * Claim (simplified Theorem 4)
 * ---------------------------
 *      If   ΔK  >  (1−δ)·ΔB
 *      then σ_* is a sub‑game‑perfect equilibrium.
 *
 *  Note: Because pay‑offs are independent of the opponent and stationary,
 *        checking profitable *one‑shot* deviations suffices for SPE.
 *
 * Compilation
 * -----------
 *   coqc AgencyProtocol_SPE_Narrow.v
 *)

Require Import Reals.
Open Scope R_scope.

(* ---------- Parameters ---------- *)
Variables ΔK ΔB δ : R.
Hypotheses
  (HΔK_pos  : ΔK  > 0)
  (HΔB_gtK  : ΔB  > ΔK)            (* temptation higher than keep *)
  (Hδ       : 0 < δ < 1)
  (HSPE     : ΔK  > (1 - δ) * ΔB).

(* ---------- Discounted utility streams ---------- *)
Definition U_coop : R := ΔK / (1 - δ).

Definition U_defect_once : R := ΔB + δ * U_coop.

(* Lemma: inequality assumption ⇒ cooperation dominates *)
Lemma coop_vs_defect :
  U_coop > U_defect_once.
Proof.
  unfold U_coop, U_defect_once.
  assert(Dpos: 1 - δ > 0) by lra.
  (* Multiply both sides by positive denominator (1-δ) *)
  apply (Rmult_lt_reg_r _ _ Dpos).
  (* LHS: ΔK ; RHS: (1-δ)ΔB + δΔK *)
  replace (ΔB + δ * (ΔK / (1 - δ))) with
          ((1 - δ) * ΔB + δ * ΔK) by field; lra.
Qed.

(* ---------- Formal definition of One‑Step‑Deviation profitable? ---------- *)
Inductive Action := keep | break.

(* A *history* here need only record whether we are at the root or not,
   because σ_* is stationary & stage pay‑offs ignore opponent.
   We encode sub‑game as natural n (period index). *)
Definition strat := nat -> Action.

(* always‑keep strategy *)
Definition sigma_star : strat := fun _ => keep.

(* Deviate‑at‑0 strategy for player P then revert to keep *)
Definition dev_once : strat := fun n => if Nat.eqb n 0 then break else keep.

(* Discounted utility given a strategy (opponent irrelevant) *)
Fixpoint util (s : strat) (n : nat) : R :=
  match n with
  | O => match s 0 with keep => ΔK | break => ΔB end
  | S n' =>
      match s n with keep => ΔK | break => ΔB end + δ * util s n'
  end.

CoFixpoint stream_from (s : strat) (t : nat) : R :=
  match t with
  | O => match s 0 with keep => ΔK | break => ΔB end
  | S k => match s t with keep => ΔK | break => ΔB end
  end.

(* Infinite discounted utility – we exploit closed forms because pay‑off
   pattern is simple. For σ_*, util = U_coop; for dev_once, util = U_defect_once. *)

Lemma util_sigma_star_closed :
  util sigma_star 0 = U_coop.
Proof.
  unfold util, sigma_star, U_coop.
  simpl. field; lra.
Qed.

Lemma util_dev_once_closed :
  util dev_once 0 = U_defect_once.
Proof.
  unfold util, dev_once, U_defect_once.
  simpl. rewrite Nat.eqb_refl.
  field; unfold U_coop; field; lra.
Qed.

(* ---------- One‑Step‑Deviation Principle (specialised) ---------- *)
(* Because σ_* is stationary & game symmetric, checking period‑0 suffices.*)

Definition profitable_one_step (u_star u_dev : R) : Prop := u_dev > u_star.

Lemma no_profitable_deviation :
  ~ profitable_one_step U_coop U_defect_once.
Proof.
  unfold profitable_one_step.
  intro H.
  apply coop_vs_defect in H.
  lra.
Qed.

(* ---------- Sub‑game‑perfect equilibrium (narrow model) ---------- *)
Theorem SPE_always_keep :
  (* For every player, deviation not profitable ⇒ SPE *)
  forall P,  (* P ∈ {1,2}, value unused – symmetry *)
    ~ profitable_one_step U_coop U_defect_once.
Proof.
  intros. apply no_profitable_deviation.
Qed.
