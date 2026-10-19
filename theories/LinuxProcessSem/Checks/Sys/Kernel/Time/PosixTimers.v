(** * LinuxProcessSem.Checks.Sys.Kernel.Time.PosixTimers — the clock_gettime (113) checker, and its proofs

    Mirrors [Sys/Kernel/Time/PosixTimers.v], which answers to Linux
    [kernel/time/posix-timers.c]: this file holds the checkers for the
    syscalls defined there, and no others.

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

(** clock_gettime: CLOCK_MONOTONIC, CLOCK_PROCESS_CPUTIME_ID or one of
    the per-call ids ([Kernel.Time.PosixTimers.clockid_percall_b] —
    CLOCK_REALTIME and the raw, coarse and boottime ids), only a fully
    writable 16-byte destination, and only a reading
    [Kernel.Time.PosixTimers.timespec_ok_b] (respectively
    [Kernel.Time.PosixTimers.realtime_ok_b],
    [Kernel.Time.PosixTimers.cputime_ok_b]) admits — the same booleans
    the spec chooses against, so acceptor and spec cannot drift apart.
    The effect must be exactly one write of those bytes at [tp] and
    nothing else: no zeros, no unmaps, no copies, no copy-ins.

    The three arms differ in three places, and each is the point.  Only
    the monotonic arm tests an envelope on [m_clock], because it is the
    only one that reads it, and only it answers
    [CheckOk (with_clock ...) ...] rather than [CheckOk m] — an
    accepted per-call or [CLOCK_PROCESS_CPUTIME_ID] call leaves
    the model where it was.  Those two are then separated by the
    predicate alone. *)
Definition check_clock_gettime (i : SyscallInput) (clkid tp : word)
    (eff : SyscallEffect) (m : Model) : check_result :=
  if clockid_percall_b clkid then
    match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
    | None => CheckUnmodeled
    | Some _ =>
        match eff with
        | mkEffectU r [(a, bs)] [] [] [] [] =>
            if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp && realtime_ok_b bs
            then CheckOk m []
            else CheckReject
        | _ => CheckReject
        end
    end
  else if Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID then
    match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
    | None => CheckUnmodeled
    | Some _ =>
        match eff with
        | mkEffectU r [(a, bs)] [] [] [] [] =>
            if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp && cputime_ok_b bs
            then CheckOk m []
            else CheckReject
        | _ => CheckReject
        end
    end
  else if negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC) then CheckUnmodeled
  else if negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)
  then CheckUnmodeled
  else
  match read_bytes_map (in_wmem i) tp (Z_to_bv 64 16) with
  | None => CheckUnmodeled
  | Some _ =>
      match eff with
      | mkEffectU r [(a, bs)] [] [] [] [] =>
          if bv_eqb r (Z_to_bv 64 0) && bv_eqb a tp
             && timespec_ok_b bs (m_clock m)
          then CheckOk (with_clock (Z_to_bv 64 (timespec_ns bs)) m) []
          else CheckReject
      | _ => CheckReject
      end
  end.

Lemma check_clock_gettime_sound_ok : forall i clkid tp eff m m' evs,
  check_clock_gettime i clkid tp eff m = CheckOk m' evs ->
  clock_gettime_spec clkid tp i m (Ok eff m' evs).
Proof.
  intros i clkid tp [ret ws zs us cs copyins] m m' evs H.
  unfold check_clock_gettime in H. unfold clock_gettime_spec.
  destruct (clockid_percall_b clkid) eqn:Hrt; cbv iota.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst0;
      [|discriminate]. cbv iota in H.
    destruct ws as [|[a bs] ws']; [discriminate|].
    destruct ws' as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
              && realtime_ok_b bs) eqn:Hok; [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in Hok as [Hok1 Hts].
    apply andb_true_iff in Hok1 as [Hr Ha].
    apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst.
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    rewrite Hdst0. cbv iota.
    eapply bind_ok0; [apply (choose_ok _ bs); exact Hts|].
    apply pure_ok. }
  destruct (Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID) eqn:Hcp;
    cbv iota.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst1;
      [|discriminate]. cbv iota in H.
    destruct ws as [|[a bs] ws']; [discriminate|].
    destruct ws' as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
              && cputime_ok_b bs) eqn:Hok; [|discriminate].
    inversion H; clear H; subst.
    apply andb_true_iff in Hok as [Hok1 Hts].
    apply andb_true_iff in Hok1 as [Hr Ha].
    apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst.
    eapply bind_ok0; [apply input_ok|]. cbv beta.
    rewrite Hdst1. cbv iota.
    eapply bind_ok0; [apply (choose_ok _ bs); exact Hts|].
    apply pure_ok. }
  destruct (negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)) eqn:Hid;
    [discriminate|]. cbv iota.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta.
  destruct (negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)) eqn:Henv;
    [discriminate|]. cbv iota.
  eapply bind_ok0; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst;
    [|discriminate]. cbv iota.
  destruct ws as [|[a bs] ws']; [discriminate|].
  destruct ws' as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
            && timespec_ok_b bs (m_clock m)) eqn:Hok; [|discriminate].
  inversion H; clear H; subst.
  apply andb_true_iff in Hok as [Hok1 Hts].
  apply andb_true_iff in Hok1 as [Hr Ha].
  apply bv_eqb_eq in Hr. apply bv_eqb_eq in Ha. subst.
  eapply bind_ok0; [apply (choose_ok _ bs); exact Hts|].
  eapply bind_ok0; [apply modify_ok|].
  apply pure_ok.
Qed.

Lemma check_clock_gettime_sound_unmodeled : forall i clkid tp eff m,
  check_clock_gettime i clkid tp eff m = CheckUnmodeled ->
  clock_gettime_spec clkid tp i m Unmodeled.
Proof.
  intros i clkid tp [ret ws zs us cs copyins] m H.
  unfold check_clock_gettime in H. unfold clock_gettime_spec.
  destruct (clockid_percall_b clkid) eqn:Hrt; cbv iota.
  { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst0;
      cbv iota; [|apply unmodeled_intro].
    exfalso. cbv iota in H.
    destruct ws as [|[a bs] ws']; [discriminate|].
    destruct ws' as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
              && realtime_ok_b bs); discriminate. }
  destruct (Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID) eqn:Hcp;
    cbv iota.
  { eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
    destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst1;
      cbv iota; [|apply unmodeled_intro].
    exfalso. cbv iota in H.
    destruct ws as [|[a bs] ws']; [discriminate|].
    destruct ws' as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
              && cputime_ok_b bs); discriminate. }
  destruct (negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)) eqn:Hid;
    cbv iota; [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta.
  destruct (negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)) eqn:Henv;
    cbv iota; [apply unmodeled_intro|].
  eapply bind_unmodeled2; [apply input_ok|]. cbv beta.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst;
    cbv iota; [|apply unmodeled_intro].
  exfalso. cbv iota in H.
  destruct ws as [|[a bs] ws']; [discriminate|].
  destruct ws' as [|? ?]; [|discriminate].
  destruct zs as [|? ?]; [|discriminate].
  destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct copyins as [|? ?]; [|discriminate].
  destruct (bv_eqb ret (Z_to_bv 64 0) && bv_eqb a tp
            && timespec_ok_b bs (m_clock m)); discriminate.
Qed.

Lemma check_clock_gettime_complete_ok : forall i clkid tp eff m m' evs,
  clock_gettime_spec clkid tp i m (Ok eff m' evs) ->
  check_clock_gettime i clkid tp eff m = CheckOk m' evs.
Proof.
  intros i clkid tp eff m m' evs H.
  unfold clock_gettime_spec in H. unfold check_clock_gettime.
  destruct (clockid_percall_b clkid) eqn:Hrt;
    cbv iota in *; sys_unfold; inv_ok.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst0;
      cbv iota in *; inv_ok.
    cbv iota. bool_true. reflexivity. }
  destruct (Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID) eqn:Hcp;
    cbv iota in *; sys_unfold; inv_ok.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst1;
      cbv iota in *; inv_ok.
    cbv iota. bool_true. reflexivity. }
  destruct (negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)) eqn:Hid;
    cbv iota in *; inv_ok.
  destruct (negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)) eqn:Henv;
    cbv iota in *; inv_ok.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst;
    cbv iota in *; inv_ok.
  cbv iota. bool_true. reflexivity.
Qed.

Lemma check_clock_gettime_complete_unmodeled : forall i clkid tp m eff,
  clock_gettime_spec clkid tp i m Unmodeled ->
  check_clock_gettime i clkid tp eff m = CheckUnmodeled.
Proof.
  intros i clkid tp m eff H.
  unfold clock_gettime_spec in H. unfold check_clock_gettime.
  destruct (clockid_percall_b clkid) eqn:Hrt;
    cbv iota in *; sys_unfold; inv_ok.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst0;
      cbv iota in *; [|reflexivity]. inv_ok. }
  destruct (Z.eqb (bv_unsigned clkid) CLOCK_PROCESS_CPUTIME_ID) eqn:Hcp;
    cbv iota in *; sys_unfold; inv_ok.
  { destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst1;
      cbv iota in *; [|reflexivity]. inv_ok. }
  destruct (negb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)) eqn:Hid;
    cbv iota in *; [reflexivity|]. inv_ok.
  destruct (negb (Z.ltb (bv_unsigned (m_clock m)) CLOCK_NS_ENVELOPE)) eqn:Henv;
    cbv iota in *; [reflexivity|]. inv_ok.
  destruct (read_bytes_map (in_wmem i) tp (Z_to_bv 64 16)) eqn:Hdst;
    cbv iota in *; [|reflexivity]. inv_ok.
Qed.
