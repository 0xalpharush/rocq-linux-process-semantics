(** * LinuxProcessSem.Checks.Sys.Kernel.Time.Time — the gettimeofday (169) checker, and its proofs

    Mirrors [Sys/Kernel/Time/Time.v], which answers to Linux
    [kernel/time/time.c]: this file holds the checkers for the syscalls
    defined there, and no others.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checkers here are executable, and their proofs relate them to the
    relational specs in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Uaccess.

(** gettimeofday: a NULL [tz] (the model has no [sys_tz]), a non-NULL
    [tv], a fully writable 16 bytes there, and a reading
    [Time.timeval_ok_b] admits — the same boolean the spec
    chooses against.  The effect must be exactly one write of those
    bytes at [tv] and nothing else, with a 0 return.  No model state
    moves: the wall clock is chosen afresh per call, and
    [Time.gettimeofday_spec] says why there is nothing to
    record.  A [tv] whose first 8-byte [put_user] range [access_ok]
    refuses is -EFAULT with nothing written; the range test is asked
    through [State.copy_bytes_map] before the walk is consulted, and
    8 rather than 16 on the faulting arm for the reason
    [Time.gettimeofday_spec] gives. *)
Definition check_gettimeofday (i : SyscallInput) (tv tz : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if negb (w_is0 tz) then CheckUnmodeled
  else if w_is0 tv then CheckUnmodeled
  else
  match copy_bytes_map (in_wmem i) tv 16 with
  | None =>
      if negb (access_okb tv 8)
      then check_ret_only eff (errno_ret EFAULT) m []
      else CheckUnmodeled
  | Some _ =>
      match eff with
      | mkEffectU r [(a, bs)] [] [] [] [] =>
          if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tv && timeval_ok_b bs
          then CheckOk m []
          else CheckReject
      | _ => CheckReject
      end
  end.

Lemma check_gettimeofday_sound_ok : forall i tv tz eff m m' evs,
  check_gettimeofday i tv tz eff m = CheckOk m' evs ->
  gettimeofday_spec tv tz i m (Ok eff m' evs).
Proof.
  intros i tv tz [ret ws zs us cs copyins] m m' evs H.
  unfold check_gettimeofday in H. unfold gettimeofday_spec.
  destruct (negb (w_is0 tz)) eqn:Htz; [discriminate|]. cbv iota.
  destruct (w_is0 tv) eqn:Htv; [discriminate|]. cbv iota.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (copy_bytes_map (in_wmem i) tv 16) eqn:Hdst; cbv iota.
  2:{ destruct (negb (access_okb tv 8)) eqn:Ho; cbv iota; [|discriminate].
      apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
      apply pure_ok. }
  destruct ws as [|[a bs] ws']; [discriminate|].
  destruct ws' as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tv && timeval_ok_b bs)
    eqn:Hok; [|discriminate].
  inversion H; clear H; subst.
  apply andb_true_iff in Hok as [Hok1 Htv2].
  apply andb_true_iff in Hok1 as [Hr Ha].
  apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst.
  eapply bind_ok0; [apply (choose_ok _ bs); exact Htv2|].
  apply pure_ok.
Qed.

Lemma check_gettimeofday_sound_unmodeled : forall i tv tz eff m,
  check_gettimeofday i tv tz eff m = CheckUnmodeled ->
  gettimeofday_spec tv tz i m Unmodeled.
Proof.
  intros i tv tz [ret ws zs us cs copyins] m H.
  unfold check_gettimeofday in H. unfold gettimeofday_spec.
  destruct (negb (w_is0 tz)) eqn:Htz; cbv iota; [apply unmodeled_intro|].
  destruct (w_is0 tv) eqn:Htv; cbv iota; [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (copy_bytes_map (in_wmem i) tv 16) eqn:Hdst; cbv iota.
  2:{ destruct (negb (access_okb tv 8)) eqn:Ho; cbv iota in H |- *;
        [now apply check_ret_only_no_unmodeled in H|apply unmodeled_intro]. }
  exfalso. cbv iota in H.
  destruct ws as [|[a bs] ws']; [discriminate|].
  destruct ws' as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tv && timeval_ok_b bs);
    discriminate.
Qed.

Lemma check_gettimeofday_complete_ok : forall i tv tz eff m m' evs,
  gettimeofday_spec tv tz i m (Ok eff m' evs) ->
  check_gettimeofday i tv tz eff m = CheckOk m' evs.
Proof.
  intros i tv tz eff m m' evs H.
  unfold gettimeofday_spec in H. unfold check_gettimeofday.
  destruct (negb (w_is0 tz)) eqn:Htz; cbv iota in *; sys_unfold; inv_ok.
  destruct (w_is0 tv) eqn:Htv; cbv iota in *; inv_ok.
  destruct (copy_bytes_map (in_wmem i) tv 16) eqn:Hdst; cbv iota in *.
  2:{ destruct (negb (access_okb tv 8)) eqn:Ho; cbv iota in *.
      - inv_ok. cbn. bool_true. reflexivity.
      - inv_ok. }
  inv_ok. cbv iota. bool_true. reflexivity.
Qed.

Lemma check_gettimeofday_complete_unmodeled : forall i tv tz m eff,
  gettimeofday_spec tv tz i m Unmodeled ->
  check_gettimeofday i tv tz eff m = CheckUnmodeled.
Proof.
  intros i tv tz m eff H.
  unfold gettimeofday_spec in H. unfold check_gettimeofday.
  destruct (negb (w_is0 tz)) eqn:Htz; cbv iota in *; [reflexivity|].
  sys_unfold; inv_ok.
  destruct (w_is0 tv) eqn:Htv; cbv iota in *; [reflexivity|]. inv_ok.
  destruct (copy_bytes_map (in_wmem i) tv 16) eqn:Hdst; cbv iota in *.
  - inv_ok.
  - destruct (negb (access_okb tv 8)) eqn:Ho; cbv iota in *; [inv_ok|reflexivity].
Qed.
