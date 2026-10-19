(** * LinuxProcessSem.Checks.Witness.Kernel.Time.Time — the gettimeofday (169) witness, and its proof

    Mirrors [Sys/Kernel/Time/Time.v], which answers to Linux
    [kernel/time/time.c]: this file holds the witnesses for the
    syscalls defined there, and no others.

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

(** gettimeofday: the witness reports the epoch — [tv_sec = 0],
    [tv_usec = 0].  A wall-clock reading is constrained against nothing
    the model remembers, so one constant serves every input and every
    model state, and the witness moves no state at all. *)
Definition timeval_zero : list byte :=
  Z_to_le_bytes 8 0 ++ Z_to_le_bytes 8 0.

Definition gettimeofday_witness (tv tz : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (w_is0 tz) then Unmodeled
  else if w_is0 tv then Unmodeled
  else match copy_bytes_map (in_wmem i) tv 16 with
       | None =>
           (* 8, not 16: see [Time.gettimeofday_spec]'s None arm *)
           if negb (access_okb tv 8) then ret_outcome (errno_ret EFAULT) m
           else Unmodeled
       | Some _ =>
           Ok (mkEffect (Z_to_bv 64 0) [(tv, timeval_zero)] []) m []
       end.

Lemma gettimeofday_witness_ok : forall i tv tz m,
  gettimeofday_spec tv tz i m (gettimeofday_witness tv tz i m).
Proof.
  intros. unfold gettimeofday_spec, gettimeofday_witness.
  destruct (negb (w_is0 tz)) eqn:Htz; [apply unmodeled_intro|].
  destruct (w_is0 tv) eqn:Htv; [apply unmodeled_intro|].
  eapply bind_step; [apply input_ok|]. cbv beta.
  destruct (copy_bytes_map (in_wmem i) tv 16) eqn:Hw; cbv iota.
  2:{ destruct (negb (access_okb tv 8)) eqn:Ho; cbv iota;
        [|apply unmodeled_intro].
      unfold err_ret, ret_only, ret_outcome. apply pure_ok. }
  eapply bind_step.
  { apply (choose_ok _ timeval_zero). vm_compute. reflexivity. }
  apply pure_ok.
Qed.
