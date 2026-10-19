(** * LinuxProcessSem.Checks.Sys.Fs.DPath — the getcwd (17) checker, and its proofs

    Mirrors [Sys/Fs/DPath.v], which answers to Linux [fs/d_path.c]: this
    file holds the checkers for the syscalls defined there, and no
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

(** [getcwd] (17): -ERANGE or one of the three injectable errnos when
    [size] is 0 or 1, and [CheckUnmodeled] for every larger buffer.
    Mirrors [Fs.DPath.getcwd_spec] branch for branch — read that spec
    for why the working directory cannot change the answer in the
    modeled band, and why [buf] is not an argument here either.

    All four admitted answers are a bare return with FIVE EMPTY ledgers:
    the kernel reaches its single [copy_to_user] only after the size
    comparison has passed, so nothing this band admits writes, zeroes,
    unmaps or copies a byte.  A kernel that claimed a write alongside
    one of these returns is rejected on the ledger rather than on the
    return value. *)
Definition check_getcwd (size : word) (eff : SyscallEffect) (m : Model)
    : check_result :=
  if (1 <? bv_unsigned size)%Z then CheckUnmodeled
  else
    match eff with
    | mkEffectU ret [] [] [] [] [] =>
        if errno_ret_in getcwd_errnos ret then CheckOk m []
        else if bv_eqb ret (errno_ret ERANGE) then CheckOk m []
        else CheckReject
    | _ => CheckReject
    end.

Lemma check_getcwd_sound_ok : forall size eff m m' evs i,
  check_getcwd size eff m = CheckOk m' evs ->
  getcwd_spec size i m (Ok eff m' evs).
Proof.
  intros size eff m m' evs i H.
  unfold check_getcwd in H. unfold getcwd_spec.
  destruct (Z.ltb 1 (bv_unsigned size)) eqn:Hs; [discriminate|].
  destruct eff as [ret ws zs us cs cis]; destruct ws as [|w ws'];
    [destruct zs as [|z zs']|]; destruct us as [|? ?];
    destruct cs as [|? ?]; destruct cis as [|? ?]; try discriminate.
  destruct (errno_ret_in getcwd_errnos ret) eqn:He.
  - inversion H; clear H; subst.
    apply errno_ret_in_true in He. destruct He as (e & HIn & ->).
    apply alt_l. eapply bind_ok0.
    { apply (choose_ok _ e). exact HIn. }
    apply pure_ok.
  - destruct (bv_eqb ret (errno_ret ERANGE)) eqn:Heq; [|discriminate].
    inversion H; clear H; subst. apply bv_eqb_eq in Heq; subst ret.
    apply alt_r. unfold err_ret, ret_only. apply pure_ok.
Qed.

(** The one decline is the size band the working directory would decide;
    inside it every effect shape is either accepted or rejected, never
    declined. *)
Lemma check_getcwd_sound_unmodeled : forall size eff m i,
  check_getcwd size eff m = CheckUnmodeled ->
  getcwd_spec size i m Unmodeled.
Proof.
  intros size eff m i H.
  unfold check_getcwd in H. unfold getcwd_spec.
  destruct (Z.ltb 1 (bv_unsigned size)) eqn:Hs; [apply unmodeled_intro|].
  exfalso.
  destruct eff as [ret ws zs us cs cis]; destruct ws; [destruct zs|];
    destruct us; destruct cs; destruct cis; try discriminate.
  destruct (errno_ret_in getcwd_errnos ret); [discriminate|].
  destruct (bv_eqb ret (errno_ret ERANGE)); discriminate.
Qed.

Lemma check_getcwd_complete_ok : forall size eff m m' evs i,
  getcwd_spec size i m (Ok eff m' evs) ->
  check_getcwd size eff m = CheckOk m' evs.
Proof.
  intros size eff m m' evs i H.
  unfold getcwd_spec in H. unfold check_getcwd. sys_unfold.
  destruct (Z.ltb 1 (bv_unsigned size)) eqn:Hs; cbv iota in H; [inv_ok|].
  (* The [alt], the [bind]'s own union and the [In] over [getcwd_errnos]
     are all disjunctions; peeling them leaves one leaf per admitted
     errno, and each is a closed term the checker computes on. *)
  repeat (destruct H as [H | H]; inv_ok);
    try contradiction; vm_compute; reflexivity.
Qed.

Lemma check_getcwd_complete_unmodeled : forall size m i eff,
  getcwd_spec size i m Unmodeled ->
  check_getcwd size eff m = CheckUnmodeled.
Proof.
  intros size m i eff H.
  unfold getcwd_spec in H. unfold check_getcwd. sys_unfold.
  destruct (Z.ltb 1 (bv_unsigned size)) eqn:Hs; cbv iota in H;
    [reflexivity|].
  (* Neither arm of the [alt] can be [Unmodeled]: a [choose] bound to a
     [pure] admits only [Ok]. *)
  exfalso. destruct H as [H | H]; inv_ok.
Qed.
