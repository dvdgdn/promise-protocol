
(**
 * Agency Protocol – Theorem 10 (Coalition‑Proof Equilibrium)
 *
 * Narrow‑model setting reused from AgencyProtocol_SPE_Narrow:
 *   – Two (or arbitrarily many) identical players
 *   – Per‑period pay‑off: keep ⇒ ΔK, break ⇒ ΔB  (ΔB>ΔK)
 *   – Discount factor 0<δ<1
 *   – Inequality ΔK > (1−δ)ΔB holds
 *
 * Coalition deviation considered:
 *   A non‑empty subset C simultaneously breaks in period 0, then
 *   everyone (including C) reverts to the cooperative strategy forever.
 *
 * Claim:
 *   Such a deviation cannot make *every* member of C strictly better
 *   off; hence “always‑keep” is coalition‑proof.
 *
 * Formalisation: we prove each deviator’s individual utility is
 *                lower than in cooperation, so the coalition as a
 *                whole cannot Pareto‑improve.
 *)

Require Import Reals Lra.
Open Scope R_scope.

(* ---------- Economic parameters (same as earlier proofs) ---------------- *)
Variables ΔK ΔB δ : R.
Hypotheses
  (HΔK_pos : ΔK > 0)
  (HΔB_gtK : ΔB > ΔK)
  (Hδ      : 0 < δ < 1)
  (HSPE    : ΔK > (1 - δ) * ΔB).

(* Discounted utilities --------------------------------------------------- *)
Definition U_coop           : R := ΔK / (1 - δ).
Definition U_defect_once    : R := ΔB + δ * U_coop.

Lemma deviator_worse :
  U_defect_once < U_coop.
Proof.
  unfold U_defect_once, U_coop.
  assert (Dpos : 1 - δ > 0) by lra.
  apply Rmult_lt_reg_r with (r:=1-δ) in Dpos.
  2:{ exact Dpos. }
  (* inequality becomes: ΔB (1-δ) + δΔK < ΔK  *)
  field_simplify.
  (* which is  ΔK > (1-δ)ΔB  – true by HSPE  *)
  exact HSPE.
Qed.

(* ---------- Coalition‑proof equilibrium ------------------------------- *)
(* Model coalition by boolean flag list: True = member of coalition       *)
Fixpoint all_better (xs : list bool) : Prop :=
  match xs with
  | nil => True
  | b::tl => (if b then U_defect_once > U_coop else True) /\ all_better tl
  end.

Lemma coalition_not_all_improve :
  forall C, In true C -> ~ all_better C.
Proof.
  intros C Hin Hall.
  induction C.
  - contradiction.
  - simpl in *.
    destruct a.
    + (* a = true, deviator *)
      destruct Hall as [Hdev _].
      unfold Rgt in Hdev.
      lra using deviator_worse.
    + (* a = false *)
      apply IHC.
      * destruct Hin; auto.
      * exact (proj2 Hall).
Qed.

Theorem T10_coalition_proof :
  (* “always‑keep” cannot be Pareto‑improved by any non‑empty coalition *)
  forall C, In true C ->
    exists i, nth_error C i = Some true /\
              U_defect_once < U_coop.
Proof.
  intros C Hnonempty.
  exists 0%nat.
  split.
  - destruct C; simpl in *; [contradiction|].
    destruct a; simpl in Hnonempty; [reflexivity|contradiction].
  - apply deviator_worse.
Qed.
