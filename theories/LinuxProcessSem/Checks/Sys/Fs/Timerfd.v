(** * LinuxProcessSem.Checks.Sys.Fs.Timerfd — the timerfd_create (85) checker, and its proofs

    Mirrors [Sys/Fs/Timerfd.v], which answers to Linux [fs/timerfd.c]:
    this file holds the checkers for the syscalls defined there, and no
    others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude.

(** The gate is WRITTEN OUT rather than taken from
    [Sys.Fs.Timerfd.timerfd_create_einval_b], and the four lemmas below
    are what make the repetition worth its cost: they force this
    statement and the spec's to coincide.  Importing the spec's
    predicate would leave a wrong gate agreeing with itself, which is
    the reason [Checks/Sys/Kernel/Time/PosixTimers] restates its
    envelope bound instead of sharing it.

    Note what the repetition does NOT buy, because the difference
    matters here more than usual: an identical MISTAKE made in both
    files still closes every proof.  These lemmas relate the checker to
    the spec and never either to Linux.  They do not show that the
    admitted set really is Linux's five. *)
Definition check_timerfd_create (clkid flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if orb (negb (Z.eqb (Z.ldiff (bv_unsigned flags) TFD_CREATE_FLAGS) 0))
         (negb (orb (Z.eqb (bv_unsigned clkid) CLOCK_REALTIME)
                (orb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)
                 (orb (Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME)
                  (orb (Z.eqb (bv_unsigned clkid) CLOCK_REALTIME_ALARM)
                       (Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME_ALARM))))))
  then check_ret_only eff (errno_ret EINVAL) m []
  else CheckUnmodeled.

(** Both sides of every proof below branch on the same six equalities.
    Splitting all six — rather than the assembled condition — is what
    keeps the tactic from depending on the two files spelling the
    disjunction with the same associativity, which is exactly the
    coincidence the restatement exists to avoid relying on. *)
Ltac timerfd_gate clkid flags :=
  unfold timerfd_create_spec, timerfd_create_einval_b in *;
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) TFD_CREATE_FLAGS) 0),
           (Z.eqb (bv_unsigned clkid) CLOCK_REALTIME),
           (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC),
           (Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME),
           (Z.eqb (bv_unsigned clkid) CLOCK_REALTIME_ALARM),
           (Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME_ALARM);
  cbn [orb negb] in *.

Lemma check_timerfd_create_sound_ok : forall clkid flags eff m m' evs i,
  check_timerfd_create clkid flags eff m = CheckOk m' evs ->
  timerfd_create_spec clkid flags i m (Ok eff m' evs).
Proof.
  intros clkid flags eff m m' evs i H.
  unfold check_timerfd_create in H. timerfd_gate clkid flags;
    try discriminate;
    apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
    apply pure_ok.
Qed.

Lemma check_timerfd_create_sound_unmodeled : forall clkid flags eff m i,
  check_timerfd_create clkid flags eff m = CheckUnmodeled ->
  timerfd_create_spec clkid flags i m Unmodeled.
Proof.
  intros clkid flags eff m i H.
  unfold check_timerfd_create in H. timerfd_gate clkid flags;
    try (now apply check_ret_only_no_unmodeled in H);
    apply unmodeled_intro.
Qed.

Lemma check_timerfd_create_complete_ok : forall clkid flags eff m m' evs i,
  timerfd_create_spec clkid flags i m (Ok eff m' evs) ->
  check_timerfd_create clkid flags eff m = CheckOk m' evs.
Proof.
  intros clkid flags eff m m' evs i H.
  unfold check_timerfd_create. timerfd_gate clkid flags;
    sys_unfold; inv_ok; apply check_ret_only_ok_iff; auto.
Qed.

Lemma check_timerfd_create_complete_unmodeled : forall clkid flags m i eff,
  timerfd_create_spec clkid flags i m Unmodeled ->
  check_timerfd_create clkid flags eff m = CheckUnmodeled.
Proof.
  intros clkid flags m i eff H.
  unfold check_timerfd_create. timerfd_gate clkid flags;
    sys_unfold; try reflexivity; inv_ok.
Qed.
