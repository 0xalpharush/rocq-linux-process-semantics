(** * LinuxProcessSem.Checks.Witness.Fs.Timerfd — the timerfd_create (85) witness, and its proof

    Mirrors [Sys/Fs/Timerfd.v], which answers to Linux [fs/timerfd.c]:
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

(** The gate is written out for the third time; [Checks/Sys/Fs/Timerfd]
    says why the three layers restate it rather than share one
    predicate.

    [Unmodeled] IS an admissible outcome, so the declined half needs no
    invented answer — the spec's own arm is [unmodeled], and exhibiting
    it is what makes this total.  [socket_witness] takes the same shape
    for the same reason. *)
Definition timerfd_create_witness (clkid flags : word) (m : Model)
    : outcome SyscallEffect :=
  if orb (negb (Z.eqb (Z.ldiff (bv_unsigned flags) TFD_CREATE_FLAGS) 0))
         (negb (orb (Z.eqb (bv_unsigned clkid) CLOCK_REALTIME)
                (orb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)
                 (orb (Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME)
                  (orb (Z.eqb (bv_unsigned clkid) CLOCK_REALTIME_ALARM)
                       (Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME_ALARM))))))
  then ret_outcome (errno_ret EINVAL) m
  else Unmodeled.

Lemma timerfd_create_witness_ok : forall clkid flags i m,
  timerfd_create_spec clkid flags i m (timerfd_create_witness clkid flags m).
Proof.
  intros clkid flags i m.
  unfold timerfd_create_spec, timerfd_create_einval_b, timerfd_create_witness.
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) TFD_CREATE_FLAGS) 0),
           (Z.eqb (bv_unsigned clkid) CLOCK_REALTIME),
           (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC),
           (Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME),
           (Z.eqb (bv_unsigned clkid) CLOCK_REALTIME_ALARM),
           (Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME_ALARM);
    cbn [orb negb];
    solve [ apply pure_ok | apply unmodeled_intro ].
Qed.
