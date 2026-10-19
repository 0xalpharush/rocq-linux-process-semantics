(* Written by the OSS-Fuzz proof collaborators. *)
(** * StringsSpec — image-independent pure definitions for musl string-routine
      summaries ([memset], [memcmp])

    - [cb c]  : the byte [memset] stores = low byte of the value register [c];
      [cv c]  : its numeric value; [cb_zero] : [cb (Z_to_bv 64 0) = Z_to_bv 8 0].
    - [memcmp_res bl br] : what [memcmp]/[bcmp] return in a0 (as a Z; the register holds
      [Z_to_bv 64 (memcmp_res bl br)]): the difference of the first mismatching byte pair,
      0 if none.  [memcmp_a0_zero_iff] : the register is [Z_to_bv 64 0] iff [bl = br]. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Common Require Import PropExec.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================================================== *)
(** ** memset's fill byte                                                  *)
(* ===================================================================== *)

Definition cb (c : word) : byte := Z_to_bv 8 (bv_unsigned c).
Definition cv (c : word) : Z := bv_unsigned c mod 256.

Lemma cv_range : forall c, 0 <= cv c < 256.
Proof. intros. unfold cv. apply Z.mod_pos_bound. lia. Qed.

Lemma cb_cv : forall c, Z_to_bv 8 (cv c) = cb c.
Proof.
  intros c. unfold cb, cv. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. apply Z.mod_mod. lia.
Qed.

(** the common case [memset(p, 0, n)] (also holds by conversion) *)
Lemma cb_zero : cb (Z_to_bv 64 0) = Z_to_bv 8 0.
Proof. reflexivity. Qed.

Lemma cb_lit : forall z, cb (Z_to_bv 64 z) = Z_to_bv 8 z.
Proof.
  intros z. unfold cb. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
  apply Z.mod_mod_divide. exists (2^56). reflexivity.
Qed.

(* ===================================================================== *)
(** ** memcmp's result                                                     *)
(* ===================================================================== *)

Fixpoint memcmp_res (bl br : list byte) : Z :=
  match bl, br with
  | x :: bl', y :: br' =>
      if (bv_unsigned x =? bv_unsigned y)%Z then memcmp_res bl' br' else bv_unsigned x - bv_unsigned y
  | _, _ => 0
  end.

Lemma memcmp_res_range : forall bl br, -255 <= memcmp_res bl br <= 255.
Proof.
  induction bl as [|x bl IH]; intros [|y br]; cbn; try lia.
  pose proof (u8_range x). pose proof (u8_range y).
  destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)); [apply IH | lia].
Qed.

Lemma memcmp_res_zero_iff : forall bl br, length br = length bl ->
  (memcmp_res bl br = 0 <-> bl = br).
Proof.
  induction bl as [|x bl IH]; intros [|y br] Hlen; cbn in *; try (split; congruence).
  destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|E].
  - assert (x = y) by (apply bv_eq; exact E). subst y.
    rewrite (IH br) by lia. split; [intros ->; reflexivity | congruence].
  - split; [lia|]. intros H. injection H as -> ->. congruence.
Qed.

Lemma memcmp_res_refl : forall bl, memcmp_res bl bl = 0.
Proof. intros bl. apply (proj2 (memcmp_res_zero_iff bl bl eq_refl)). reflexivity. Qed.

(** The register-level test the callers perform ([beqz a0]/[bnez a0]). *)
Lemma memcmp_a0_zero_iff : forall bl br, length br = length bl ->
  (Z_to_bv 64 (memcmp_res bl br) = Z_to_bv 64 0 <-> bl = br).
Proof.
  intros bl br Hlen. rewrite <- (memcmp_res_zero_iff bl br Hlen).
  pose proof (memcmp_res_range bl br) as Hr.
  split; [|intros ->; reflexivity].
  intros E. apply (f_equal bv_unsigned) in E.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2^64) in E.
  rewrite Z.mod_0_l in E by lia.
  destruct (Z_lt_le_dec (memcmp_res bl br) 0).
  - replace (memcmp_res bl br) with ((memcmp_res bl br + 2^64) + (-1) * 2^64) in E by lia.
    rewrite Z.mod_add in E by lia. rewrite Z.mod_small in E by lia. lia.
  - rewrite Z.mod_small in E by lia. exact E.
Qed.

Lemma memcmp_u_nonzero : forall bl br, length br = length bl -> bl <> br ->
  bv_unsigned (Z_to_bv 64 (memcmp_res bl br)) <> 0.
Proof.
  intros bl br Hlen Hne Hu. apply Hne. apply (proj1 (memcmp_a0_zero_iff bl br Hlen)).
  apply bv_eq. rewrite Hu. reflexivity.
Qed.
