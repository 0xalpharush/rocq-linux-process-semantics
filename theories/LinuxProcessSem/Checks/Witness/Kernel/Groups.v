(** * LinuxProcessSem.Checks.Witness.Kernel.Groups — the getgroups (158) and setgroups (159) witnesses, and their proofs

    Mirrors [Sys/Kernel/Groups.v], which answers to Linux
    [kernel/groups.c]: this file holds the witnesses for the syscalls
    defined there, and no others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export Prelude.

(** [getgroups] (158) is deterministic on every branch, so the witness
    is the branch itself: the count, an -EINVAL, or the [Unmodeled] the
    writing path and the over-long-list guard both answer.  Failing
    closed is an admissible outcome, which is what makes progress hold
    on those two. *)
Definition getgroups_witness (gidsetsize : word) (m : Model)
    : outcome SyscallEffect :=
  let n := sint32 gidsetsize in
  if (n <? 0)%Z then ret_outcome (errno_ret EINVAL) m
  else
    let ng := Z.of_nat (length (cr_groups (m_creds m))) in
    if (NGROUPS_MAX <? ng)%Z then Unmodeled
    else if (n =? 0)%Z then ret_outcome (Z_to_bv 64 ng) m
    else if (n <? ng)%Z then ret_outcome (errno_ret EINVAL) m
    else if (ng =? 0)%Z then ret_outcome (Z_to_bv 64 0) m
    else Unmodeled.

Lemma getgroups_witness_ok : forall gidsetsize i m,
  getgroups_spec gidsetsize i m (getgroups_witness gidsetsize m).
Proof.
  intros. unfold getgroups_spec, getgroups_witness. cbv zeta.
  destruct (Z.ltb (sint32 gidsetsize) 0) eqn:Hneg;
    [unfold err_ret, ret_only; apply pure_ok|].
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (Z.ltb NGROUPS_MAX
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hmax;
    cbv beta iota zeta; [apply unmodeled_intro|].
  destruct (Z.eqb (sint32 gidsetsize) 0) eqn:Hzero;
    cbv beta iota zeta; [unfold ret_only; apply pure_ok|].
  destruct (Z.ltb (sint32 gidsetsize)
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hsmall;
    cbv beta iota zeta; [unfold err_ret, ret_only; apply pure_ok|].
  destruct (Z.eqb (Z.of_nat (length (cr_groups (m_creds m)))) 0) eqn:Hempty;
    cbv beta iota zeta; [unfold ret_only; apply pure_ok|].
  apply unmodeled_intro.
Qed.

(** [Unmodeled] is itself the admissible outcome on the privileged half:
    progress asks for an outcome the spec admits, and failing closed is
    one. *)
Definition setgroups_witness (m : Model) : outcome SyscallEffect :=
  if creds_privileged (m_creds m) then Unmodeled
  else ret_outcome (errno_ret EPERM) m.

Lemma setgroups_witness_ok : forall i m, setgroups_spec i m (setgroups_witness m).
Proof.
  intros. unfold setgroups_spec, setgroups_witness.
  eapply bind_step; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (creds_privileged (m_creds m)) eqn:Hp; cbv beta iota zeta.
  - apply unmodeled_intro.
  - apply pure_ok.
Qed.
