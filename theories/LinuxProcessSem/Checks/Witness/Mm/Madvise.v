(** * LinuxProcessSem.Checks.Witness.Mm.Madvise — the madvise (233) witness, and its proof

    Mirrors [Sys/Mm/Madvise.v], which answers to Linux [mm/madvise.c]:
    this file holds the witness for the syscall defined there, and no
    other.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

(** madvise witness: the spec has no nondeterminism, so the witness is
    the spec's one answer at every gate — -EINVAL on a misaligned
    address or a wrapping range, 0 at zero length, the zero-fill with
    the returned charges on the answered shape, and [Unmodeled] (fail
    closed) on any other advice value or any range the ledger does not
    describe as one read-write anonymous mapping (see
    [Madvise.madvise_spec]). *)
Definition madvise_witness (addr len advice : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
  then ret_outcome (errno_ret EINVAL) m
  else if negb (madvise_dontneed_b advice) then Unmodeled
  else if w_is0 len then ret_outcome (Z_to_bv 64 0) m
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then ret_outcome (errno_ret EINVAL) m
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    if madvise_dontneed_ok (m_vmmaps m) addr n
    then Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)])
            (madvise_dontneed_next m addr n) []
    else Unmodeled.

Lemma madvise_witness_ok : forall addr len advice i m,
  madvise_spec addr len advice i m (madvise_witness addr len advice m).
Proof.
  intros. unfold madvise_spec, madvise_witness.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign;
    [apply pure_ok|].
  destruct (negb (madvise_dontneed_b advice)) eqn:Hadv;
    [apply unmodeled_intro|].
  destruct (w_is0 len) eqn:Hlen; [apply pure_ok|].
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig; [apply pure_ok|].
  cbv zeta.
  eapply bind_step; [apply get_model_ok|]. cbv beta zeta.
  destruct (madvise_dontneed_ok (m_vmmaps m) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  - eapply bind_step; [apply modify_ok|]. apply pure_ok.
  - apply unmodeled_intro.
Qed.
