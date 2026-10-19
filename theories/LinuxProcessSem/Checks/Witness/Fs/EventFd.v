(** * LinuxProcessSem.Checks.Witness.Fs.EventFd — the eventfd2 (19) witness, and its proof

    Mirrors [Sys/Fs/EventFd.v], which answers to Linux [fs/eventfd.c]:
    this file holds the witnesses for the syscalls defined there, and no
    others.

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

(** The gate is written out for the third time; [Checks/Sys/Fs/EventFd]
    says why the three layers restate it rather than share one
    predicate.

    [Unmodeled] IS an admissible outcome, so the declined half needs no
    invented answer — the spec's own arm is [unmodeled], and exhibiting
    it is what makes this total.  [timerfd_create_witness] takes the
    same shape for the same reason. *)
Definition eventfd2_witness (flags : word) (m : Model)
    : outcome SyscallEffect :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0)
  then ret_outcome (errno_ret EINVAL) m
  else Unmodeled.

Lemma eventfd2_witness_ok : forall flags i m,
  eventfd2_spec flags i m (eventfd2_witness flags m).
Proof.
  intros flags i m.
  unfold eventfd2_spec, eventfd2_einval_b, eventfd2_witness.
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0);
    cbn [negb];
    solve [ apply pure_ok | apply unmodeled_intro ].
Qed.
