(** * Common.SymBranch — closing [SymExec]'s [SCBr] obligations.

    EXPLORATION / PROTOTYPE.  Image-INDEPENDENT proof library; nothing
    here is part of the trusted specification.

    [Common/SymTac.v]'s [sym_block] takes a branch SCRIPT (one [bool] per
    [Branch] the run meets) and turns every entry into an [SCBr]
    obligation, so no direction is ever assumed.  For a straight line
    with no input-dependent control flow — [modprint_ns], the file the
    combined stack was first exercised on — that list is EMPTY and this
    file would not exist.

    The moment a binary branches on [argc], on a parsed value, or on a
    loop counter, every block leaves one such obligation per branch, in
    one of exactly three spellings:

      [bv_lts a b = d]   (blt/bge)
      [bv_ltu a b = d]   (bltu/bgeu)
      [bv_eqb a b = d]   (beq/bne, and the [beqz]/[bnez] aliases)

    All three are [Z] comparisons under a [bv_signed]/[bv_unsigned]
    wrapper, and the caller invariably has the [Z] facts already
    ([bv_unsigned argcN = Z.of_nat (length av)], a loop bound, a window
    bound).  What is missing is only the step from [bv_signed] to
    [bv_unsigned]: [lia] treats [bv_signed x] and [bv_unsigned x] as
    UNRELATED atoms, so a goal about a [blt] cannot see a hypothesis
    about [bv_unsigned].

    [bv_signed_small] is that step, and [sym_br] is the whole closer:
    push the comparison down to [Z], drop the [bv_signed] wrapper on
    every operand small enough for it (which is decided by the caller's
    own bounds, through [lia]), and hand what is left to [lia].  In the
    example proofs that is a one-line discharge of every branch. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Common Require Import StepTac.
From stdpp Require Import bitvector.bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.Common Require Import PropExec.
Import ListNotations.
Local Open Scope Z_scope.

(** Below [2^63] the signed and unsigned readings agree.  This is the
    only fact in the file; everything else is [lia]. *)
Lemma bv_signed_small : forall (x : word),
  bv_unsigned x < 2 ^ 63 -> bv_signed x = bv_unsigned x.
Proof.
  intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Hr.
  unfold bv_signed. apply bv_swrap_small.
  assert (Hh : bv_half_modulus 64 = 9223372036854775808) by (vm_compute; reflexivity).
  rewrite Hh. change (2 ^ 63) with 9223372036854775808 in Hx. lia.
Qed.

(** The three comparisons, as [Z] comparisons.  Stated separately from
    the tactic so that a proof that wants to REASON about a branch (a
    loop invariant that has to name the exit condition) can rewrite with
    them instead of discharging a goal. *)
Lemma bv_lts_small : forall (a b : word),
  bv_unsigned a < 2 ^ 63 -> bv_unsigned b < 2 ^ 63 ->
  bv_lts a b = Z.ltb (bv_unsigned a) (bv_unsigned b).
Proof.
  intros a b Ha Hb. unfold bv_lts.
  rewrite (bv_signed_small a Ha), (bv_signed_small b Hb). reflexivity.
Qed.

Lemma bv_ltu_Z : forall (a b : word),
  bv_ltu a b = Z.ltb (bv_unsigned a) (bv_unsigned b).
Proof. reflexivity. Qed.

Lemma bv_eqb_Z : forall (a b : word),
  bv_eqb a b = Z.eqb (bv_unsigned a) (bv_unsigned b).
Proof. reflexivity. Qed.

(** Negative operands: a [blt] against a literal like [-9] (the [div]
    round-toward-zero fixup a signed division compiles to) has a
    [bv_signed] that is NOT the [bv_unsigned].  One rewrite handles the
    literal side. *)
Lemma bv_signed_lit : forall z : Z,
  - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small.
  assert (Hh : bv_half_modulus 64 = 9223372036854775808) by (vm_compute; reflexivity).
  rewrite Hh. change (2 ^ 63) with 9223372036854775808 in Hz. lia.
Qed.

(** [addiw] with a NEGATIVE immediate.  [SeqExec.v_addiw_small] carries
    an unused [0 <= imm] hypothesis, so it does not apply to the
    [addiw s1,a0,-2] every [argc]-relative index computation compiles
    to.  Same proof, without that hypothesis; the existing lemma is left
    alone. *)
Lemma v_addiw_range : forall (x : word) imm,
  0 <= bv_unsigned x + imm -> bv_unsigned x + imm < 2 ^ 31 ->
  bv_unsigned (v_addiw x imm) = bv_unsigned x + imm.
Proof.
  intros x imm Hlo Hhi. unfold v_addiw.
  rewrite Z_to_bv_unsigned.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(** The closer.  Deliberately [vm_compute]-free: an [SCBr] operand is
    routinely an OPEN [bv] term (a symbolic [sp], a read-back [argc]),
    and [vm_compute] on one of those does not fail — it allocates until
    the machine dies (see [StepTac.bveq]'s docstring). *)
Ltac sym_br :=
  rewrite ?negb_true_iff, ?negb_false_iff;
  unfold bv_lts, bv_ltu, bv_eqb;
  rewrite ?bv_signed_lit by lia;
  rewrite ?bv_signed_small by (rewrite ?v_addiw_range by lia; u_norm; lia);
  rewrite ?v_addiw_range by lia;
  u_norm;
  rewrite ?Z.ltb_ge, ?Z.ltb_lt, ?Z.eqb_eq, ?Z.eqb_neq;
  lia.
