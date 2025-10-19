
(**
 * Agency Protocol – Theorem 12 (Finite‑Lookahead Bound)
 *
 * Abstract formulation:
 *   For 0 < r < 1 and ε ∈ (0,1), any integer
 *
 *        k ≥ ⌈ ln ε / ln r ⌉
 *
 *   satisfies            r^k ≤ ε.
 *
 * This lemma underpins the Yellow‑Paper bound
 *    k ≥ ln(G_max / (α·S_base·w_max·P_min)) / -ln δ
 * showing that a sufficiently long cognitive horizon guarantees
 * the tail-value of δ^k is small enough to preserve cooperation.
 *
 * Updated: G_max and FOV constants are now derived in AgencyProtocol_DerivedConstants.v
 *          rather than being axiomatized.
 *
 * Dependencies: only Coq `Reals`.
 *)

Require Import Reals Lra Ranalysis1.
Require Import AgencyProtocol_DerivedConstants.
Open Scope R_scope.

(* ---------- Core analytic inequality ------------------------------- *)
Lemma pow_le_bound :
  forall r eps:R, 0 < r < 1 -> 0 < eps < 1 ->
    forall k:nat,
      (INR k >= ln eps / ln r) -> r ^ k <= eps.
Proof.
  intros r eps [Hr_pos Hr_lt1] [Heps_pos Heps_lt1] k Hk.
  (* ln r is negative                                        *)
  assert (Hlnr_neg : ln r < 0).
  { apply ln_increasing; lra. }
  (* Take natural log of both sides                          *)
  apply (ln_le_inv _ _).
  - apply pow_lt; assumption.
  - exact Heps_pos.
  - (* ln (r^k)  =  k·ln r  *)
    rewrite ln_pow; try lra.
    (* multiply inequality by ln r (negative) flips sign      *)
    (* Given: INR k >= ln eps / ln r                          *)
    (* ⇒  INR k * ln r <= ln eps                              *)
    apply Rmult_le_reg_r with (r:=ln r).
    + lra.
    + lra.
Qed.

(* -------------- Existence of a concrete bound N -------------------- *)
Lemma exists_pow_small :
  forall r eps:R, 0 < r < 1 -> 0 < eps < 1 ->
    exists N:nat, forall k:nat, (k >= N)%nat -> r^k <= eps.
Proof.
  intros r eps Hr Heps.
  (* choose N = up( ln eps / ln r ) *)
  set (c := ln eps / ln r).
  pose (N := Z.to_nat (up c)).
  exists N.
  intros k Hk.
  (* show INR k >= c *)
  assert (Hk_ge_c : INR k >= c).
  { unfold N in Hk.
    apply le_INR in Hk.
    (* property of up: c <= IZR (up c) <= INR (Z.to_nat (up c))  *)
    assert (Hup : c <= IZR (up c)).
    { apply proj2 with (1:=up_tech c). }
    rewrite <- INR_IZR_INZ in Hup.
    lra.
  }
  (* apply previous lemma using bound                          *)
  apply pow_le_bound; try assumption.
  exact Hk_ge_c.
Qed.
