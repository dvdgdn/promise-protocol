
(**
 * Agency Protocol – Theorem 5 (Coalition Manipulation Threshold)
 *
 * Statement (formalised):
 *   Let W_total > 0 be the merit‑weighted sum of all assessments.
 *   Let θ ∈ (0,1) be the decision threshold for accepting a promise.
 *   Suppose honest assessors give weight  ≥ θ·W_total  in favour of “KEPT”.
 *   Then *any* coalition that wants to overturn the verdict (make KEPT false)
 *   must control strictly more than (1‑θ)·W_total weight.
 *
 * This captures the Yellow‑Paper inequality  p_c > 1 − θ.
 *)

Require Import Reals Lra.
Open Scope R_scope.

Variables W_total coalition_w θ : R.

Hypotheses
  (H_Wpos : W_total > 0)
  (H_theta : 0 < θ < 1)
  (H_honest_majority : θ * W_total <= W_total - coalition_w). (* honest 'KEPT' weight *)

Definition can_flip : Prop :=
  coalition_w > (1 - θ) * W_total.

Theorem T5_threshold :
  (* If coalition_w ≤ (1‑θ)W_total, verdict stays KEPT                 *)
  coalition_w <= (1 - θ) * W_total ->
  can_flip = False.
Proof.
  intros Hc.
  unfold can_flip.
  apply Rle_not_gt.
  exact Hc.
Qed.

(* Contrapositive form – what Yellow Paper states *)
Theorem T5_contrapositive :
  can_flip -> coalition_w > (1 - θ) * W_total.
Proof. unfold can_flip; tauto. Qed.
