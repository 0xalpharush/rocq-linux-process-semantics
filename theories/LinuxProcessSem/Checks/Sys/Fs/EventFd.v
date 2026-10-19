(** * LinuxProcessSem.Checks.Sys.Fs.EventFd — the eventfd2 (19) checker, and its proofs

    Mirrors [Sys/Fs/EventFd.v], which answers to Linux [fs/eventfd.c]:
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
    [Sys.Fs.EventFd.eventfd2_einval_b], and the four lemmas below are
    what make the repetition worth its cost: they force this statement
    and the spec's to coincide.  Importing the spec's predicate would
    leave a wrong gate agreeing with itself, which is the reason
    [Checks/Sys/Fs/Timerfd] restates its own gate instead of sharing it.

    Note what the repetition does NOT buy, because the difference
    matters here more than usual: an identical MISTAKE made in both
    files still closes every proof.  These lemmas relate the checker to
    the spec and never either to Linux.  They do not show that the
    admitted mask really is Linux's [EFD_FLAGS_SET].

    [check_ret_only] carries the rest of the obligation: it rejects any
    effect with a non-empty write, zero, unmap, copy or copy-in ledger,
    which is what pins that a conforming run may not smuggle a store
    past an arm that stores nothing.  [eventfd2] reads no user memory
    and writes none, so all six ledgers are empty on the one answer this
    arm gives. *)
Definition check_eventfd2 (flags : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if negb (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else CheckUnmodeled.

(** Both sides of every proof below branch on the same equality.
    Splitting THAT — rather than the assembled condition — is what keeps
    the tactic from depending on the two files spelling the gate with
    the same negation, which is exactly the coincidence the restatement
    exists to avoid relying on. *)
Ltac eventfd2_gate flags :=
  unfold eventfd2_spec, eventfd2_einval_b in *;
  destruct (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0);
  cbn [negb] in *.

Lemma check_eventfd2_sound_ok : forall flags eff m m' evs i,
  check_eventfd2 flags eff m = CheckOk m' evs ->
  eventfd2_spec flags i m (Ok eff m' evs).
Proof.
  intros flags eff m m' evs i H.
  unfold check_eventfd2 in H. eventfd2_gate flags;
    try discriminate;
    apply check_ret_only_ok_iff in H; destruct H as (-> & -> & ->);
    apply pure_ok.
Qed.

Lemma check_eventfd2_sound_unmodeled : forall flags eff m i,
  check_eventfd2 flags eff m = CheckUnmodeled ->
  eventfd2_spec flags i m Unmodeled.
Proof.
  intros flags eff m i H.
  unfold check_eventfd2 in H. eventfd2_gate flags;
    try (now apply check_ret_only_no_unmodeled in H);
    apply unmodeled_intro.
Qed.

Lemma check_eventfd2_complete_ok : forall flags eff m m' evs i,
  eventfd2_spec flags i m (Ok eff m' evs) ->
  check_eventfd2 flags eff m = CheckOk m' evs.
Proof.
  intros flags eff m m' evs i H.
  unfold check_eventfd2. eventfd2_gate flags;
    sys_unfold; inv_ok; apply check_ret_only_ok_iff; auto.
Qed.

Lemma check_eventfd2_complete_unmodeled : forall flags m i eff,
  eventfd2_spec flags i m Unmodeled ->
  check_eventfd2 flags eff m = CheckUnmodeled.
Proof.
  intros flags m i eff H.
  unfold check_eventfd2. eventfd2_gate flags;
    sys_unfold; try reflexivity; inv_ok.
Qed.
