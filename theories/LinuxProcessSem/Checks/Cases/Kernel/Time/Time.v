(** * LinuxProcessSem.Checks.Cases.Kernel.Time.Time — worked examples over gettimeofday (169)

    Mirrors [Sys/Kernel/Time/Time.v], which answers to Linux
    [kernel/time/time.c]: this file holds the worked examples for the
    syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary.

    What is here is of three kinds:
    the QUANTIFIED claims — every timezone pointer declines, every
    accepted call leaves the model alone — the two boundaries of the
    [KTIME_SEC_MAX] ceiling, which a real wall clock never lands on,
    and the destinations at the top of the address space, which no real
    Sv48 run can map. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.
(* [wmem_ts] and [clock_model] are this subsystem's shared fixtures: the
   sixteen writable bytes a time struct lands in, and a model whose clock
   reads a given nanosecond count.  They are defined beside
   [clock_gettime]'s cases rather than duplicated here. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases.Kernel.Time
  Require Import PosixTimers.

(** [gettimeofday(4096, tz)]: sixteen writable bytes at 4096, nothing
    readable, and the timezone pointer left free. *)
Definition gettimeofday_input (tz : word) : SyscallInput :=
  mkInput 169 [4096; tz; 0; 0; 0; 0] (fun _ => None) wmem_ts.

(** UNIVERSALLY QUANTIFIED.  Every non-NULL timezone pointer declines,
    whatever the destination, the effect or the model.  The kernel would
    answer from [sys_tz], eight bytes of mutable global state the model
    has nowhere to carry, so the only honest answer is to decline — and
    this is what stops a future arm quietly answering [{0, 0}] from a
    guess about the deployment.  [tz] is tested before anything else,
    which is why no hypothesis about [tv] or [eff] is needed. *)
Lemma gettimeofday_declines_every_timezone :
  forall i tv tz eff m,
    w_is0 tz = false ->
    check_gettimeofday i tv tz eff m = CheckUnmodeled.
Proof.
  intros i tv tz eff m H.
  unfold check_gettimeofday. rewrite H. reflexivity.
Qed.

(** UNIVERSALLY QUANTIFIED, and the pin on the central design decision.
    There is deliberately no realtime field in [Model]: the reading is
    chosen afresh per call and related to nothing, because relating
    realtime to monotonic would need a per-run offset that stops being
    constant the moment anything sets the clock.  The consequence is
    that an accepted [gettimeofday] moves NOTHING — not the clock, not
    the fds, not the maps — and emits no event.  No trace can establish
    that: a trace shows what an execution did, not that a whole class of
    executions left the model alone. *)
Lemma gettimeofday_never_moves_the_model :
  forall i tv tz eff m m' evs,
    check_gettimeofday i tv tz eff m = CheckOk m' evs ->
    m' = m /\ evs = [].
Proof.
  intros i tv tz eff m m' evs H.
  unfold check_gettimeofday in H.
  destruct (negb (w_is0 tz)); [discriminate|].
  destruct (w_is0 tv); [discriminate|].
  destruct (copy_bytes_map (in_wmem i) tv 16).
  2:{ destruct (negb (access_okb tv 8)); [|discriminate].
      apply check_ret_only_ok_iff in H. destruct H as (_ & -> & ->).
      split; reflexivity. }
  destruct eff as [r ws zs us cs copyins].
  destruct ws as [|[a bs] ws']; [discriminate|].
  destruct ws'; [|discriminate].
  destruct zs; [|discriminate].
  destruct us; [|discriminate].
  destruct cs; [|discriminate].
  destruct copyins; [|discriminate].
  destruct (bv_eqb r (Z_to_bv 64 0) && bv_eqb a tv && timeval_ok_b bs);
    [inversion H; subst; split; reflexivity | discriminate].
Qed.

(** tv_sec = KTIME_SEC_MAX - 1 = 9223372035, tv_usec = 999999 — the
    latest wall-clock instant [timeval_ok_b] admits. *)
Definition tv_ceiling_minus : list byte :=
  [3; 125; 193; 37; 2; 0; 0; 0] ++ [63; 66; 15; 0; 0; 0; 0; 0].
(** The same microsecond one second later: tv_sec = KTIME_SEC_MAX. *)
Definition tv_at_ceiling : list byte :=
  [4; 125; 193; 37; 2; 0; 0; 0] ++ [63; 66; 15; 0; 0; 0; 0; 0].

(** THE ENVIRONMENT CANNOT BE MADE TO PRODUCE IT.  [timeval_ok_b]'s
    third conjunct bounds tv_sec by [KTIME_SEC_MAX], and a real run
    never reaches the boundary from either side: a real reading is a
    wall clock of roughly 1.7e9 seconds, five times under it.  So these
    two cases are the only thing that exercises the conjunct.

    The admitted side first: the last microsecond below the ceiling. *)
Example gettimeofday_reading_below_ceiling_admissible :
  check_syscall (gettimeofday_input 0) (mkEffect 0 [(4096, tv_ceiling_minus)] [])
    (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

(** One second further is refused.  [KTIME_SEC_MAX] is
    [(2^63 - 1) / 10^9]: a [tv_sec] at or above it is a wall clock
    [ktime_t] cannot hold once converted to nanoseconds, which is the
    same ceiling [nanosleep] declines a request at, reached from the
    other direction. *)
Example gettimeofday_reading_at_ceiling_rejected :
  check_syscall (gettimeofday_input 0) (mkEffect 0 [(4096, tv_at_ceiling)] [])
    (clock_model 0) = CheckReject.
Proof. check_eq. Qed.

(** THE DESTINATION THAT WALKS OFF THE TOP OF THE ADDRESS SPACE, and the
    bands on either side of [TASK_SIZE].
    What belongs here is the THIRD of the four reasons at the top of
    [Checks.Examples] — it pins [in_wmem] and the constant
    [State.TASK_SIZE].  A real Sv48 run maps nothing at or above 2^47,
    so there a wrapping range is unwritable
    twice over and a spec that merely walked would reach the same
    verdict as one that asks the range first; the two separate only in
    the DEFINITION, which is what [Equivalence.strong_universal]
    quantifies over.  So the memories below map the wrapped range IN
    FULL, the bare walk is shown reading it back, and the range test is
    shown refusing it anyway — which is what tells
    [State.copy_bytes_map] from [State.read_bytes_map], and what makes
    the widths 8 and 16 a measurement against [State.TASK_SIZE] rather
    than against what happened to be mapped.

    Same shape as [Checks.Cases.Net.Socket]'s socketpair groups, with
    the widths 4 and 8 scaled to 8 and 16. *)

(** The last eight bytes of the address space, so the 16-byte walk
    covers them and then the eight at 0. *)
Definition gettimeofday_wrap_tv : word := Z_to_bv 64 (2 ^ 64 - 8).

(** A memory that maps EXACTLY the wrapped range and nothing else, which
    is what makes the walk Example below tight. *)
Definition gettimeofday_wrap_mem : word -> option byte :=
  fun a => if ((bv_unsigned a <? 8)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

(** THE MUTATION TEST, MADE PERMANENT.  This is the walk alone, which
    WRAPS because [State.read_bytes_map] advances in word arithmetic,
    and which reads all sixteen bytes back off a memory that maps only
    those sixteen.  It says "writable", so an arm that consulted only
    the walk would answer 0 and a 16-byte write — where Linux's first
    [put_user] is refused by [access_ok] and the call is -EFAULT with
    nothing written.  Without this beside them the
    two Examples below would also pass if [gettimeofday_wrap_tv] stopped
    wrapping or [gettimeofday_wrap_mem] stopped mapping the range. *)
Example gettimeofday_wrap_would_pass_the_bare_walk :
  read_bytes_map gettimeofday_wrap_mem gettimeofday_wrap_tv (Z_to_bv 64 16)
    <> None.
Proof. vm_compute. discriminate. Qed.

(** [State.copy_bytes_map] refuses it before the walk is consulted. *)
Example gettimeofday_wrap_is_refused_before_the_walk :
  copy_bytes_map gettimeofday_wrap_mem gettimeofday_wrap_tv 16 = None.
Proof. vm_compute. reflexivity. Qed.

(** THE ONE THAT MATTERS, at the checker: -EFAULT with nothing written
    is the answer, and the write a bare walk would admit — a reading
    landing at [2^64 - 8] and, after the word wraps, at 0 — is
    refused.  The second half is the negative direction. *)
Example gettimeofday_wrapping_tv_is_efault :
  check_syscall (mkInput 169 [gettimeofday_wrap_tv; 0; 0; 0; 0; 0]
                   (fun _ => None) gettimeofday_wrap_mem)
    (mkEffect (errno_ret EFAULT) [] []) (clock_model 0)
  = CheckOk (clock_model 0) []
  /\ check_syscall (mkInput 169 [gettimeofday_wrap_tv; 0; 0; 0; 0; 0]
                     (fun _ => None) gettimeofday_wrap_mem)
       (mkEffect 0 [(gettimeofday_wrap_tv, tv_ceiling_minus)] [])
       (clock_model 0)
     = CheckReject.
Proof. split; check_eq. Qed.

(** PAST [TASK_SIZE] WITHOUT WRAPPING, and still refused: [tv = 2^63]
    with sixteen bytes sums to 2^63 + 16, under 2^64, so a bare no-wrap
    test would admit it and the walk reads it in full.  riscv64's
    [access_ok] refuses it because [__access_ok] tests
    [addr <= TASK_SIZE - size] (include/asm-generic/access_ok.h at
    v6.18.46, with [TASK_SIZE_MAX] falling back to [TASK_SIZE] since
    arch/riscv defines no other).  Without this pair the three Examples
    above pass under either spelling of the guard. *)
Definition gettimeofday_high_tv : word := Z_to_bv 64 (2 ^ 63).

Definition gettimeofday_high_mem : word -> option byte :=
  fun a => if ((2 ^ 63 <=? bv_unsigned a)%Z && (bv_unsigned a <? 2 ^ 63 + 16)%Z)%bool
           then Some (Z_to_bv 8 0) else None.

Example gettimeofday_high_range_reads :
  read_bytes_map gettimeofday_high_mem gettimeofday_high_tv (Z_to_bv 64 16)
    <> None.
Proof. vm_compute. discriminate. Qed.

Example gettimeofday_high_range_would_pass_a_no_wrap_test :
  (two_pow_64 <=? bv_unsigned gettimeofday_high_tv + 16)%Z = false.
Proof. vm_compute. reflexivity. Qed.

Example gettimeofday_past_task_size_is_efault :
  check_syscall (mkInput 169 [gettimeofday_high_tv; 0; 0; 0; 0; 0]
                   (fun _ => None) gettimeofday_high_mem)
    (mkEffect (errno_ret EFAULT) [] []) (clock_model 0)
  = CheckOk (clock_model 0) []
  /\ check_syscall (mkInput 169 [gettimeofday_high_tv; 0; 0; 0; 0; 0]
                     (fun _ => None) gettimeofday_high_mem)
       (mkEffect 0 [(gettimeofday_high_tv, tv_ceiling_minus)] [])
       (clock_model 0)
     = CheckReject.
Proof. split; check_eq. Qed.

(** THE TWO WIDTHS, 8 AND 16, measured over a memory that maps
    everything, so the walk is settled for every destination at once
    and the verdict turns on the range tests alone.  Four [tv]s, one
    step apart at each edge of the band the spec declines:

    - [TASK_SIZE - 16]: both stores inside, the reading is delivered.
      This is the control that keeps the refusals above honest — they
      would also pass under a guard that refused every [tv].
    - [TASK_SIZE - 15] and [TASK_SIZE - 8], the two ends of the torn
      band: the first [put_user] passes its own 8-byte test and the
      second does not, so the arm declines whatever the effect says.
    - [TASK_SIZE - 7]: the FIRST store is refused, so -EFAULT with
      nothing written is the answer and a delivered reading is not.

    Move either width by one and one of these flips. *)
Definition gettimeofday_open_mem : word -> option byte := fun _ => Some 0.

Definition gettimeofday_at (tv : word) : SyscallInput :=
  mkInput 169 [tv; 0; 0; 0; 0; 0] (fun _ => None) gettimeofday_open_mem.

Definition task_size_minus (k : Z) : word := Z_to_bv 64 (TASK_SIZE - k).

Example gettimeofday_last_admitted_tv_is_delivered :
  check_syscall (gettimeofday_at (task_size_minus 16))
    (mkEffect 0 [(task_size_minus 16, tv_ceiling_minus)] []) (clock_model 0)
  = CheckOk (clock_model 0) [].
Proof. check_eq. Qed.

Example gettimeofday_torn_band_declines :
  check_syscall (gettimeofday_at (task_size_minus 15))
    (mkEffect (errno_ret EFAULT) [] []) (clock_model 0) = CheckUnmodeled
  /\ check_syscall (gettimeofday_at (task_size_minus 8))
       (mkEffect (errno_ret EFAULT) [] []) (clock_model 0) = CheckUnmodeled.
Proof. split; check_eq. Qed.

Example gettimeofday_first_store_refused_is_efault :
  check_syscall (gettimeofday_at (task_size_minus 7))
    (mkEffect (errno_ret EFAULT) [] []) (clock_model 0)
  = CheckOk (clock_model 0) []
  /\ check_syscall (gettimeofday_at (task_size_minus 7))
       (mkEffect 0 [(task_size_minus 7, tv_ceiling_minus)] []) (clock_model 0)
     = CheckReject.
Proof. split; check_eq. Qed.
