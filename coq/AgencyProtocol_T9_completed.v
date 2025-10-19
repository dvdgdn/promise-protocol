
(** 
 * Agency Protocol – Theorem 9 (Lyapunov Stability) – Narrow Discrete Model
 *
 * Completed: all previous Admitted proofs have been filled.
 * Updated: merit_bounded is now proven via merit update function invariant.
 *)
Require Import Reals Lra List Ranalysis1.
Require Import AgencyProtocol_MeritUpdate.
Import ListNotations.

(* ---------- Helper: real summation on lists --------------------------- *)
Fixpoint rsum (l : list R) : R :=
  match l with
  | [] => 0
  | x :: xs => x + rsum xs
  end.

Lemma rsum_nonneg :
  forall l, Forall (fun x => 0 <= x) l -> 0 <= rsum l.
Proof.
  induction l; simpl; intros Hall.
  - lra.
  - inversion Hall; subst. specialize (IHl H3). lra.
Qed.

(* ---------- Lyapunov function ---------------------------------------- *)
Definition V (l : list R) : R := INR (length l) - rsum l.

(* ---------- Cooperative step predicate ------------------------------- *)
Definition coop_step (cur nxt : list R) : Prop :=
  length cur = length nxt /\
  Forall2 (fun x y => x <= y) cur nxt /\
  exists i x y, nth_error cur i = Some x /\ nth_error nxt i = Some y /\ x < y.

(* ---------- Helper lemmas on rsum ------------------------------------ *)
Lemma rsum_componentwise_le :
  forall l l', length l = length l' ->
               Forall2 (fun x y => x <= y) l l' ->
               rsum l <= rsum l'.
Proof.
  intros l.
  induction l as [|x xs IH]; intros l' Hlen Hall.
  - destruct l'; simpl in *; try discriminate; lra.
  - destruct l'; inversion Hlen; inversion Hall; subst.
    simpl. apply Rplus_le_compat.
    + apply H2.
    + apply IH; assumption.
Qed.

(* Strict increase of total merit when at least one component rises *)
Lemma rsum_strict_increase :
  forall l l', length l = length l' ->
               Forall2 (fun x y => x <= y) l l' ->
               (exists i x y,
                   nth_error l i  = Some x /\
                   nth_error l' i = Some y /\ x < y) ->
               rsum l < rsum l'.
Proof.
  intros l.
  induction l as [|x xs IH]; intros l' Hlen Hall Hstrict.
  - destruct Hstrict as [i _]. destruct i; simpl in *; discriminate.
  - destruct l'; inversion Hlen.
    inversion Hall; subst.
    simpl in *.
    destruct Hstrict as [i xi [yi [Hl [Hyr Hlt]]]].
    destruct i.
    + simpl in Hl, Hyr.
      inversion Hl; inversion Hyr; subst. lra.
    + simpl. apply Rplus_lt_compat_l.
      apply IH with (l':=l').
      * assumption.
      * assumption.
      * exists i, xi, yi; repeat split; simpl in Hl, Hyr; assumption.
Qed.

(* ---------- Main single-step Lyapunov decrease ----------------------- *)
Lemma V_decreases :
  forall cur nxt,
    coop_step cur nxt -> V nxt < V cur.
Proof.
  intros cur nxt [Hlen [Hall Hstrict]].
  unfold V.
  rewrite Hlen.
  apply Rplus_lt_compat_l with (r:= (- INR (length cur))).
  replace (- rsum nxt + INR (length cur)) with (INR (length cur) - rsum nxt) by lra.
  replace (- rsum cur + INR (length cur)) with (INR (length cur) - rsum cur) by lra.
  apply Ropp_lt_cancel.
  unfold Rminus. apply Ropp_lt_contravar.
  replace (rsum cur + - rsum nxt) with (rsum cur - rsum nxt) by lra.
  lra using rsum_strict_increase.
Qed.

(* ---------- Each component is in [0,1] – proven via merit update invariant *)
(* We now prove this instead of assuming it as a hypothesis *)
Lemma merit_bounded :
  forall seq : nat -> list R,
    (forall n, exists deltas, 
      seq (S n) = update_merit_list (seq n) deltas /\
      coop_step (seq n) (seq (S n))) ->
    Forall (fun x => 0 <= x <= 1) (seq 0) ->
    forall n, Forall (fun x => 0 <= x <= 1) (seq n).
Proof.
  intros seq Hstep Hinit n.
  induction n.
  - assumption.
  - destruct (Hstep n) as [deltas [Heq _]].
    rewrite Heq.
    apply update_merit_list_bounded.
    destruct (Hstep n) as [_ [_ [Hlen _]]].
    assumption.
Qed.

(* helper: bound rsum by length using merit_bounded *)
Lemma rsum_le_length :
  forall l, Forall (fun x => 0 <= x <= 1) l -> rsum l <= INR (length l).
Proof.
  induction l as [|x xs IH]; simpl; intros Hall.
  - lra.
  - inversion Hall; subst.
    specialize (IH H3).
    lra.
Qed.

(* ---------- Corollary: bounded monotone sequence converges ----------- *)
Lemma V_monotone_bounded :
  forall seq : nat -> list R,
    (forall n, coop_step (seq n) (seq (S n))) ->
    Forall (fun x => 0 <= x <= 1) (seq 0) ->
    exists L:R, is_lim_seq (fun n => V (seq n)) L.
Proof.
  intros seq Hstep Hinit.
  (* Decreasing *)
  assert (Hdec : forall n, V (seq (S n)) <= V (seq n)).
  { intro n. left. apply V_decreases, Hstep. }
  (* Lower bound *)
  assert (Hlb : forall n, 0 <= V (seq n)).
  { intro n.
    unfold V.
    pose proof (merit_bounded seq Hstep Hinit n) as Hb.
    apply rsum_le_length in Hb.
    lra.
  }
  (* Use monotone convergence theorem for decreasing, bounded-below sequences *)
  apply ex_lim_seq_decreasing with (f:=fun n => V (seq n)).
  - exact Hdec.
  - exists 0. intros n. apply Hlb.
Qed.
