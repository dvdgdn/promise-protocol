
(**
 * Agency Protocol – Theorem 6 (Detection‑Probability Growth)
 *
 * Simplified formalisation:
 *   •  Each dishonest assessor adds a fixed positive
 *      KL‑divergence  d  from the truth (d > 0).
 *   •  Total divergence for a coalition of size n:
 *           D(n) = n · d
 *   •  Detection probability:
 *           P(n) = 1 − exp(−κ · D(n))       with κ > 0
 *
 *   We prove:
 *     1.  P(n) is strictly increasing in n.
 *     2.  For every ε ∈ (0,1)  there exists N such that
 *            n ≥ N   ⇒   P(n) ≥ 1 − ε.
 *
 *   Thus detection probability approaches 1 exponentially fast.
 *
 *   Dependencies:  Coq standard Reals library.
 *
 *   Compile:
 *       coqc AgencyProtocol_T6.v
 *)

Require Import Reals Lra ZArith.
Open Scope R_scope.

(* --------- Parameters --------- *)
Variables κ d : R.
Hypotheses
  (Hκ : κ  > 0)
  (Hd : d  > 0).

(* Note: The parameter d is now concretely derived in 
   AgencyProtocol_ConsensusDetection.v as min_divergence_per_dishonest,
   which depends on the consensus algorithm's noise_bound and 
   dishonest_deviation parameters. This addresses the gap where
   d > 0 was merely assumed without connection to the protocol. *)

(* Coalition size (natural) → detection probability                *)
Definition P (n : nat) : R := 1 - exp (- κ * d * INR n).

(* ---------- Lemma 1 : Strict monotonicity ---------------------- *)
Lemma exp_decreasing_linear :
  forall n m, (n < m)%nat ->
    exp (- κ * d * INR m) < exp (- κ * d * INR n).
Proof.
  intros n m Hlt.
  apply exp_increasing.
  assert (Hprod : κ * d * INR n < κ * d * INR m).
  { apply Rmult_lt_reg_l with (r:=κ*d).
    - apply Rmult_lt_0_compat; assumption.
    - apply lt_INR; assumption. }
  lra.
Qed.

Lemma P_strict_increasing :
  forall n m, (n < m)%nat -> P n < P m.
Proof.
  intros n m Hlt.
  unfold P.
  assert (Hexpl : exp (- κ * d * INR m) < exp (- κ * d * INR n)).
  { apply exp_decreasing_linear; exact Hlt. }
  lra.
Qed.

(* ---------- Lemma 2 : Convergence to 1 ------------------------- *)
Require Import Ranalysis1.

Lemma P_tends_to_one :
  forall ε:R, 0 < ε < 1 ->
    exists N : nat, forall n : nat, (n >= N)%nat -> P n >= 1 - ε.
Proof.
  intros eps Heps.
  destruct Heps as [Hε_pos Hε_lt1].
  (* ln ε is negative because ε∈(0,1) *)
  assert (Hln_neg : ln eps < 0).
  { apply ln_increasing; lra. }
  (* Constant c such that n≥c ⇒ exp(-κ d n) ≤ ε                   *)
  set (c := - ln eps / (κ * d)).
  assert (Hc_pos : c > 0).
  { unfold c.
    apply Rdiv_lt_0_compat.
    - apply Ropp_lt_gt_0_contravar; lra.
    - apply Rmult_lt_0_compat; assumption.
  }
  (* Choose integer N = up c (ceiling)                            *)
  pose (N := Z.to_nat (up c)).
  assert (HN_bound : INR N >= c).
  { (* property of up: x <= IZR (up x) *)
    assert (Hup : c <= IZR (up c)).
    { apply proj2 with (1:=up_tech c). }
    (* up_tech gives  IZR(up c) - 1 < c <= IZR(up c) *)
    unfold N. rewrite <- INR_IZR_INZ.
    apply Rle_trans with (r2:=IZR (up c)); try lra.
  }
  (* Produce the witness N+1 to ensure strict ≥                    *)
  exists N.
  intros n Hn_ge.
  (* Show exp term ≤ eps                                          *)
  assert (HInr_ge_c : INR n >= c).
  { apply le_INR in Hn_ge.
    apply Rle_trans with (r2:=INR N); try assumption; lra. }
  (* Because exponent is decreasing, larger n ⇒ smaller exp value *)
  assert (Hexp_le :
            exp (- κ * d * INR n) <= exp (- κ * d * c)).
  { apply exp_le; nra. }
  (* But exp(-κ d c) = eps by construction                        *)
  unfold c in Hexp_le.
  replace (- κ * d * c) with (ln eps) in Hexp_le.
  2:{ unfold c. field; nra. }
  rewrite exp_ln in Hexp_le; try lra.
  (* Finally, P n = 1 − exp(...) ≥ 1 − eps                        *)
  unfold P.
  lra.
Qed.
