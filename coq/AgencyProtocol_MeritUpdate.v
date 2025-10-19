(**
 * Agency Protocol – Merit Update Function and Invariant
 *
 * This module defines the merit update function and proves that merit
 * values remain bounded in [0,1], addressing the gap identified in the
 * audit where merit_bounded was merely assumed as a hypothesis.
 *)

Require Import Reals Lra List.
Import ListNotations.
Open Scope R_scope.

(* ---------- Merit Update Function -------- *)
Definition update_merit (M : R) (delta : R) : R :=
  Rmax 0 (Rmin 1 (M + delta)).

(* ---------- Basic Properties of update_merit -------- *)
Lemma update_merit_bounded :
  forall M delta, 0 <= update_merit M delta <= 1.
Proof.
  intros M delta.
  unfold update_merit.
  split.
  - apply Rmax_l.
  - transitivity (Rmin 1 (M + delta)).
    + apply Rmax_r.
    + apply Rmin_l.
Qed.

Lemma update_merit_zero_lower :
  forall M delta, 0 <= update_merit M delta.
Proof.
  intros M delta.
  apply update_merit_bounded.
Qed.

Lemma update_merit_one_upper :
  forall M delta, update_merit M delta <= 1.
Proof.
  intros M delta.
  apply update_merit_bounded.
Qed.

(* ---------- Merit Update preserves bounds when starting in [0,1] -------- *)
Lemma update_merit_preserves_bounds :
  forall M delta,
    0 <= M <= 1 ->
    0 <= update_merit M delta <= 1.
Proof.
  intros M delta _.
  apply update_merit_bounded.
Qed.

(* ---------- List-based Merit Update -------- *)
Definition update_merit_list (merits : list R) (deltas : list R) : list R :=
  map2 update_merit merits deltas.

Lemma update_merit_list_bounded :
  forall merits deltas,
    length merits = length deltas ->
    Forall (fun m => 0 <= m <= 1) (update_merit_list merits deltas).
Proof.
  intros merits deltas Hlen.
  unfold update_merit_list.
  induction merits as [|m ms IH]; destruct deltas as [|d ds]; 
    simpl in *; try discriminate.
  - constructor.
  - inversion Hlen.
    constructor.
    + apply update_merit_bounded.
    + apply IH. assumption.
Qed.

(* ---------- Sequential Merit Updates -------- *)
(* This proves that starting from bounded merits, any sequence of updates
   maintains the [0,1] bounds, resolving the gap where merit_bounded was
   merely hypothesized *)

Fixpoint apply_updates (initial_merits : list R) (update_sequence : list (list R)) : list R :=
  match update_sequence with
  | [] => initial_merits
  | deltas :: rest => apply_updates (update_merit_list initial_merits deltas) rest
  end.

Theorem merit_invariant :
  forall initial_merits update_sequence,
    Forall (fun m => 0 <= m <= 1) initial_merits ->
    (forall deltas, In deltas update_sequence -> length deltas = length initial_merits) ->
    Forall (fun m => 0 <= m <= 1) (apply_updates initial_merits update_sequence).
Proof.
  intros initial_merits update_sequence.
  revert initial_merits.
  induction update_sequence as [|deltas rest IH]; intros initial_merits Hinit Hlen.
  - simpl. assumption.
  - simpl. apply IH.
    + apply update_merit_list_bounded.
      apply Hlen. left. reflexivity.
    + intros d Hd. apply Hlen. right. assumption.
Qed.

(* ---------- Connection to coop_step predicate -------- *)
(* This shows how merit updates relate to the cooperative step predicate
   used in the Lyapunov stability proof *)

Definition merit_coop_step (cur nxt : list R) : Prop :=
  length cur = length nxt /\
  exists deltas, nxt = update_merit_list cur deltas /\
  Forall2 (fun x y => x <= y) cur nxt /\
  exists i x y, nth_error cur i = Some x /\ nth_error nxt i = Some y /\ x < y.

Lemma merit_coop_step_preserves_bounds :
  forall cur nxt,
    Forall (fun m => 0 <= m <= 1) cur ->
    merit_coop_step cur nxt ->
    Forall (fun m => 0 <= m <= 1) nxt.
Proof.
  intros cur nxt Hcur [Hlen [deltas [Heq _]]].
  rewrite Heq.
  apply update_merit_list_bounded.
  assumption.
Qed.

(* ---------- Main theorem: merit_bounded is provable, not hypothetical -------- *)
Theorem merit_bounded_proved :
  forall seq : nat -> list R,
    (forall n, merit_coop_step (seq n) (seq (S n))) ->
    Forall (fun x => 0 <= x <= 1) (seq 0) ->
    forall n, Forall (fun x => 0 <= x <= 1) (seq n).
Proof.
  intros seq Hstep Hinit n.
  induction n.
  - assumption.
  - apply merit_coop_step_preserves_bounds with (seq n).
    + assumption.
    + apply Hstep.
Qed.