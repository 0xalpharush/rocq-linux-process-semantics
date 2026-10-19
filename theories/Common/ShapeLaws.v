(* Written by the OSS-Fuzz proof collaborators. *)
(** * Common.ShapeLaws — the [t_eq] algebra a proof needs to match executor-built
      shapes against a specification shape: the six laws no other Common file states.

    Pure shape algebra over [ShapeAlg] ([TSet], [t_eq], [t_emit], [t_alt2],
    [t_exit], [t_nil]); image-independent, imports [ShapeAlg] only.

    Companions elsewhere: [SrcShape.t_alt2_comm]/[t_alt2_nil_l]/[t_alt2_nil_r],
    [AgentLib.t_emit_app]/[t_alt2_congr], [RefNodes.t_alt2_idem]/[t_alt3_idem]
    ([t_alt3 A B C := t_alt2 A (t_alt2 B C)]), [ShapeAlg.t_emit_nil_eq]/
    [t_emit_has_nil]/[t_alt_wall] (short-write chunking is invisible — see
    [LibWritev.t_alt_wall_nat]), [AgentNodes.bv_and_255_small]. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.Common Require Import ShapeAlg.
Import ListNotations.
Open Scope bv_scope.

(* --------------------------------------------------------------------- *)
(** ** Binary choice: associative, absorbing                                 *)
(* --------------------------------------------------------------------- *)

Lemma t_alt2_assoc : forall A B C : TSet, t_eq (t_alt2 (t_alt2 A B) C) (t_alt2 A (t_alt2 B C)).
Proof. intros A B C tr. unfold t_alt2. tauto. Qed.

(** absorption: a repeated alternative anywhere in a right comb *)
Lemma t_alt2_absorb : forall A B : TSet, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.

(** A three-way node is a right comb of binary ones (definitional for
    [RefNodes.t_alt3]; restated on the unfolded form so no RefNodes import is
    needed). *)
Lemma t_alt3_as_alt2 : forall A B C : TSet,
  t_eq (t_alt2 A (t_alt2 B C)) (t_alt2 (t_alt2 A B) C).
Proof. intros A B C. apply t_eq_sym, t_alt2_assoc. Qed.

(* --------------------------------------------------------------------- *)
(** ** Fault leaves ([t_nil]) after a COMMON prefix are absorbed              *)
(* --------------------------------------------------------------------- *)

(** [t_emit e t_nil] is absorbed by a sibling that starts with the same block. *)
Lemma t_alt2_emit_nil_l : forall (e : list event) (T : TSet),
  T [] -> t_eq (t_alt2 (t_emit e t_nil) (t_emit e T)) (t_emit e T).
Proof.
  intros e T H0 tr. unfold t_alt2, t_emit, t_nil. split.
  - intros [[Hp | (tr' & -> & ->)] | H].
    + left. exact Hp.
    + right. exists []. split; [reflexivity | exact H0].
    + exact H.
  - intros H. right. exact H.
Qed.

(* --------------------------------------------------------------------- *)
(** ** Emission blocks                                                      *)
(* --------------------------------------------------------------------- *)

(** distributing a common prefix over a choice (needed when a node's
    alternatives are compared ABOVE an already-merged prefix) *)
Lemma t_emit_alt2_distr : forall (e : list event) (A B : TSet),
  t_eq (t_emit e (t_alt2 A B)) (t_alt2 (t_emit e A) (t_emit e B)).
Proof.
  intros e A B tr. unfold t_emit, t_alt2. split.
  - intros [Hp | (tr' & -> & [HA | HB])].
    + left. left. exact Hp.
    + left. right. exists tr'. auto.
    + right. right. exists tr'. auto.
  - intros [[Hp | (tr' & -> & HA)] | [Hp | (tr' & -> & HB)]].
    + left. exact Hp.
    + right. exists tr'. auto.
    + left. exact Hp.
    + right. exists tr'. auto.
Qed.

(* --------------------------------------------------------------------- *)
(** ** Leaves                                                               *)
(* --------------------------------------------------------------------- *)

(** the exit node's [bv_and .. 255] code on a small literal *)
Lemma bv_and_255_lit : forall c, (0 <= c < 256)%Z ->
  bv_and (Z_to_bv 64 c) (Z_to_bv 64 255) = Z_to_bv 64 c.
Proof.
  intros c Hc. apply bv_eq.
  rewrite bv_and_unsigned, !Z_to_bv_unsigned.
  rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64)%Z; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(** the reference's exit leaf with nothing pending on the channel and its
    [bv_and] code is the specification's exit leaf *)
Lemma exit_leaf_eq : forall (ch : word) c fs, (0 <= c < 256)%Z ->
  t_eq (t_emit (map (WriteEv ch) []) (t_exit (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) fs))
       (t_exit (Z_to_bv 64 c) fs).
Proof.
  intros ch c fs Hc. rewrite bv_and_255_lit by exact Hc. cbn [map].
  apply t_emit_nil_eq. unfold t_exit. apply t_emit_has_nil.
Qed.
