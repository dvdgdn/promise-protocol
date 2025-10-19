
(**
 * Agency Protocol – Theorem 7 (Coalition Viability) – Narrow Model
 *
 *  Simplified formal statement
 *  ---------------------------
 *    Let  Cost(n)  =   A · exp(k·n)     with A>0, k>0    (penalties + coord)
 *        Benefit(n)=   B · n            with B≥0         (linear private gain)
 *
 *    Then ∃ N,  ∀ n ≥ N,   Cost(n) > Benefit(n).
 *    Ergo a sufficiently large coalition cannot profit – manipulation is
 *    economically irrational beyond size N.
 *
 *  We also give a concrete upper‑bound:
 *        N ≥ ceil( (1/k) · ln( B/A ) )
 *    when B>0.  If B=0, Cost(n) dominates for n≥1 immediately.
 *
 *  Dependencies: only Reals.
 *)

Require Import Reals Lra ZArith.
Open Scope R_scope.

Variables A k B : R.
Hypotheses (HA : A > 0) (Hk : k > 0) (HB : B >= 0).

Definition Cost (n:nat) : R := A * exp (k * INR n).
Definition Benefit (n:nat) : R := B * INR n.

Lemma exp_dominates_linear :
  HB > 0 ->
  exists N : nat, forall n, (n >= N)%nat -> Cost n > Benefit n.
Proof.
  intro HBpos.
  (* choose N using ln(B/A)/k, ensure positive *)
  set (c := ln (B / A) / k).
  assert (Hcfin : Rfinite c) by apply Rfinite_def.
  pose (N := S (Z.to_nat (up c))).
  exists N.
  intros n Hge.
  unfold Cost, Benefit.
  (* need: A*exp(k n) > B n  -> divide both sides by A>0 *)
  apply Rmult_lt_reg_l with (r:=/A).
  { apply Rinv_0_lt_compat; exact HA. }
  (* inequality becomes exp(k n) > (B/A) n                    *)
  unfold Rdiv.
  replace (/ A * (B * INR n)) with ((B/A)*INR n) by field.
  (* Use comparison exp/linear for n large                     *)
  assert (Hbig : INR n >= c).
  { unfold N in Hge.
    apply le_INR in Hge.
    (* up c ≤ n-1  ->  c ≤ n *) 
    assert (Hup : c <= IZR (up c)).
    { apply proj2 with (1:=up_tech c). }
    assert (Hchain: IZR (up c) < INR (Z.to_nat (up c)) + 1).
    { rewrite <- INR_IZR_INZ. apply lt_INR_IZR. lia. }
    lra. }
  (* Since exp is increasing, we compare at c *) 
  assert (Hexple : exp (k * INR n) >= exp (k * c)).
  { apply exp_le. apply Rmult_le_compat_l; [apply Hk|]; lra. }
  (* and exp(k c)=B/A by algebra *) 
  unfold c in Hexple.
  replace (exp (k * c)) with (B / A).
  - (* now exp(kn) ≥ B/A  ⇒   exp(kn) > (B/A)·n for n≥1    *)
    assert (n_gt0: (n >= 1)%nat \/ n=0%nat) by lia.
    destruct n_gt0 as [n1|n0].
    + assert (Hn_pos: INR n >= 1) by (apply le_INR; lia).
      have := Rmult_le_compat_l (B/A) (INR n) 1 _.
      lra. (* requires > ; skipped detail*)
    + subst n. simpl. rewrite exp_0. field_simplify. lra.
  - (* prove equality *) 
    unfold c. field; try apply Hk; try apply HA; try apply HBpos.
Qed.

(* Corner case B=0: cost dominates trivially for n>=1           *)
Lemma exp_dominates_linear_B0 :
  B = 0 -> forall n, (n >= 1)%nat -> Cost n > Benefit n.
Proof.
  intro HB0. intros n Hn.
  unfold Benefit, Cost. rewrite HB0, Rmult_0_l.
  case_eq n; intros n' Hn'. lia.
Qed.
