(** * LinuxProcessSem.Checks.Sys.Kernel.Groups — the getgroups (158) and setgroups (159) checkers, and their proofs

    Mirrors [Sys/Kernel/Groups.v], which answers to Linux
    [kernel/groups.c]: this file holds the checkers for the syscalls
    defined there, and no others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export Prelude.

(** [getgroups] (158): the count, or one of the two -EINVALs, and
    [CheckUnmodeled] on the writing path.  Mirrors
    [Kernel.Groups.getgroups_spec] branch for branch — read that spec
    for the kernel order the branches are in and why the [grouplist]
    pointer is not an argument here either. *)
Definition check_getgroups (gidsetsize : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  let n := sint32 gidsetsize in
  if (n <? 0)%Z then check_ret_only eff (errno_ret EINVAL) m []
  else
    let ng := Z.of_nat (length (cr_groups (m_creds m))) in
    if (NGROUPS_MAX <? ng)%Z then CheckUnmodeled
    else if (n =? 0)%Z then check_ret_only eff (Z_to_bv 64 ng) m []
    else if (n <? ng)%Z then check_ret_only eff (errno_ret EINVAL) m []
    else if (ng =? 0)%Z then check_ret_only eff (Z_to_bv 64 0) m []
    else CheckUnmodeled.

Lemma check_getgroups_sound_ok : forall gidsetsize eff m m' evs i,
  check_getgroups gidsetsize eff m = CheckOk m' evs ->
  getgroups_spec gidsetsize i m (Ok eff m' evs).
Proof.
  intros gidsetsize eff m m' evs i H.
  unfold check_getgroups in H. unfold getgroups_spec. cbv zeta in *.
  destruct (Z.ltb (sint32 gidsetsize) 0) eqn:Hneg.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (Z.ltb NGROUPS_MAX
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hmax;
    [discriminate|].
  destruct (Z.eqb (sint32 gidsetsize) 0) eqn:Hzero.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold ret_only. apply pure_ok. }
  destruct (Z.ltb (sint32 gidsetsize)
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hsmall.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    unfold err_ret, ret_only. apply pure_ok. }
  destruct (Z.eqb (Z.of_nat (length (cr_groups (m_creds m)))) 0) eqn:Hempty;
    [|discriminate].
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  unfold ret_only. apply pure_ok.
Qed.

(** Both declines are the writing path and the impossible-length guard;
    everything else answers. *)
Lemma check_getgroups_sound_unmodeled : forall gidsetsize eff m i,
  check_getgroups gidsetsize eff m = CheckUnmodeled ->
  getgroups_spec gidsetsize i m Unmodeled.
Proof.
  intros gidsetsize eff m i H.
  unfold check_getgroups in H. unfold getgroups_spec. cbv zeta in *.
  destruct (Z.ltb (sint32 gidsetsize) 0) eqn:Hneg.
  { now apply check_ret_only_no_unmodeled in H. }
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
  destruct (Z.ltb NGROUPS_MAX
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hmax;
    [apply unmodeled_intro|].
  destruct (Z.eqb (sint32 gidsetsize) 0) eqn:Hzero.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (Z.ltb (sint32 gidsetsize)
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hsmall.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (Z.eqb (Z.of_nat (length (cr_groups (m_creds m)))) 0) eqn:Hempty.
  { now apply check_ret_only_no_unmodeled in H. }
  apply unmodeled_intro.
Qed.

Lemma check_getgroups_complete_ok : forall gidsetsize eff m m' evs i,
  getgroups_spec gidsetsize i m (Ok eff m' evs) ->
  check_getgroups gidsetsize eff m = CheckOk m' evs.
Proof.
  intros gidsetsize eff m m' evs i H.
  unfold getgroups_spec in H. unfold check_getgroups. sys_unfold.
  cbv iota zeta in H. cbv zeta.
  destruct (Z.ltb (sint32 gidsetsize) 0) eqn:Hneg; hall Hneg; inv_ok;
    [cbn; rewrite bv_eqb_refl; reflexivity|].
  destruct (Z.ltb NGROUPS_MAX
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hmax;
    hall Hmax; inv_ok.
  destruct (Z.eqb (sint32 gidsetsize) 0) eqn:Hzero; hall Hzero; inv_ok;
    [cbn; rewrite bv_eqb_refl; reflexivity|].
  destruct (Z.ltb (sint32 gidsetsize)
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hsmall;
    hall Hsmall; inv_ok;
    [cbn; rewrite bv_eqb_refl; reflexivity|].
  destruct (Z.eqb (Z.of_nat (length (cr_groups (m_creds m)))) 0) eqn:Hempty;
    hall Hempty; inv_ok.
  cbn; rewrite bv_eqb_refl; reflexivity.
Qed.

Lemma check_getgroups_complete_unmodeled : forall gidsetsize m i eff,
  getgroups_spec gidsetsize i m Unmodeled ->
  check_getgroups gidsetsize eff m = CheckUnmodeled.
Proof.
  intros gidsetsize m i eff H.
  unfold getgroups_spec in H. unfold check_getgroups. sys_unfold.
  cbv iota zeta in H. cbv zeta.
  destruct (Z.ltb (sint32 gidsetsize) 0) eqn:Hneg; hall Hneg; inv_ok.
  destruct (Z.ltb NGROUPS_MAX
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hmax;
    hall Hmax; inv_ok; [reflexivity|].
  destruct (Z.eqb (sint32 gidsetsize) 0) eqn:Hzero; hall Hzero; inv_ok.
  destruct (Z.ltb (sint32 gidsetsize)
              (Z.of_nat (length (cr_groups (m_creds m))))) eqn:Hsmall;
    hall Hsmall; inv_ok.
  destruct (Z.eqb (Z.of_nat (length (cr_groups (m_creds m)))) 0) eqn:Hempty;
    hall Hempty; inv_ok; reflexivity.
Qed.

(** [setgroups] (159): an unprivileged caller is refused -EPERM before
    either argument is read, and a privileged one is DECLINED, because
    the model does not import the list it would write (Linux v6.18.46,
    commit 1f99e9ab748f, kernel/groups.c, [SYSCALL_DEFINE2(setgroups)] /
    [may_setgroups]).
    [Kernel.Groups.setgroups_spec] says what accepting the successful
    half would cost and what the decline costs. *)
Definition check_setgroups (eff : SyscallEffect) (m : Model) : check_result :=
  if creds_privileged (m_creds m) then CheckUnmodeled
  else check_ret_only eff (errno_ret EPERM) m [].

Lemma check_setgroups_sound_ok : forall eff m m' evs i,
  check_setgroups eff m = CheckOk m' evs -> setgroups_spec i m (Ok eff m' evs).
Proof.
  intros eff m m' evs i H.
  unfold check_setgroups in H. unfold setgroups_spec.
  destruct (creds_privileged (m_creds m)) eqn:Hp; [discriminate|].
  apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
  eapply bind_ok0; [apply get_model_ok|]. cbv beta iota. srw Hp. apply pure_ok.
Qed.

(** The privileged half is where both sides fail closed. *)
Lemma check_setgroups_sound_unmodeled : forall eff m i,
  check_setgroups eff m = CheckUnmodeled -> setgroups_spec i m Unmodeled.
Proof.
  intros eff m i H. unfold check_setgroups in H. unfold setgroups_spec.
  destruct (creds_privileged (m_creds m)) eqn:Hp.
  - eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota. srw Hp.
    apply unmodeled_intro.
  - now apply check_ret_only_no_unmodeled in H.
Qed.

Lemma check_setgroups_complete_ok : forall eff m m' evs i,
  setgroups_spec i m (Ok eff m' evs) -> check_setgroups eff m = CheckOk m' evs.
Proof.
  intros eff m m' evs i H.
  unfold setgroups_spec in H. unfold check_setgroups. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (creds_privileged (m_creds m)) eqn:Hp; hall Hp; inv_ok.
  cbn; try rewrite bv_eqb_refl; try rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma check_setgroups_complete_unmodeled : forall m i eff,
  setgroups_spec i m Unmodeled -> check_setgroups eff m = CheckUnmodeled.
Proof.
  intros m i eff H.
  unfold setgroups_spec in H. unfold check_setgroups. sys_unfold.
  cbv iota in H. inv_ok.
  destruct (creds_privileged (m_creds m)) eqn:Hp; hall Hp; inv_ok;
    first [reflexivity | discriminate].
Qed.
