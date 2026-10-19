(** * LinuxProcessSem.Checks.Cases.Drivers.Char.Random — worked examples over getrandom (278)

    Mirrors [Sys/Drivers/Char/Random.v], which answers to Linux
    [drivers/char/random.c]: this file holds the worked examples for
    the syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

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

(** A writable landing zone at 4096, wide enough for a request above
    [Random.getrandom_small_max]. *)

Definition getrandom_dest : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4608 then Some 0 else None.

Definition getrandom_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(** One getrandom(4096, buflen, 0) over that zone. *)

Definition getrandom_call (buflen : Z) : SyscallInput :=
  mkInput 278 [4096; Z_to_bv 64 buflen; 0; 0; 0; 0] getrandom_dest getrandom_dest.

(** [n] environment bytes, all the same. *)

Definition some_bytes (n : nat) : list byte := repeat (Z_to_bv 8 7) n.

(** A SMALL REQUEST IS DELIVERED IN FULL, AND ONLY IN FULL.  ADMISSION
    REASON: the environment cannot be made to produce what this
    REJECTS.  A real kernel never cuts a request of at most
    [Random.getrandom_small_max] bytes short and never interrupts it,
    so no execution can show the short count or the -EINTR being
    refused; this pins them against the checker directly.

    The first conjunct is what makes the rejections say something: the
    full delivery on the same call is ACCEPTED, so the rejections are
    of the count and the errno, not of the call. *)

Example getrandom_small_request_is_delivered_in_full :
  check_syscall (getrandom_call 16)
    (mkEffect 16 [(4096, some_bytes 16)] []) getrandom_model
  = CheckOk getrandom_model []
  (* the short count Linux cannot produce below the bound *)
  /\ check_syscall (getrandom_call 16)
       (mkEffect 5 [(4096, some_bytes 5)] []) getrandom_model
     = CheckReject
  (* nor the interrupted return *)
  /\ check_syscall (getrandom_call 16)
       (mkEffect (errno_ret EINTR) [] []) getrandom_model
     = CheckReject
  (* and over-delivery stays out, as everywhere *)
  /\ check_syscall (getrandom_call 16)
       (mkEffect 17 [(4096, some_bytes 17)] []) getrandom_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** THE BOUND IS INCLUSIVE.  ADMISSION REASON: it pins the exact edge
    of the narrowing, which no execution reaches — a real kernel
    delivers both of these requests in full.
    A request of exactly [Random.getrandom_small_max] bytes is small;
    one byte more is large, and its short count is admitted again. *)

Example getrandom_small_bound_is_inclusive :
  check_syscall (getrandom_call 256)
    (mkEffect 255 [(4096, some_bytes 255)] []) getrandom_model
  = CheckReject
  /\ check_syscall (getrandom_call 256)
       (mkEffect 256 [(4096, some_bytes 256)] []) getrandom_model
     = CheckOk getrandom_model []
  /\ check_syscall (getrandom_call 257)
       (mkEffect 255 [(4096, some_bytes 255)] []) getrandom_model
     = CheckOk getrandom_model [].
Proof. repeat split; check_eq. Qed.

(** A LARGE REQUEST STILL ADMITS THE SHORT COUNT AND -EINTR, and still
    refuses the bare 0.  ADMISSION REASON: the environment cannot be
    made to produce it — with no signal, a real kernel delivers a
    large request in full too, and the admissions below are
    what keep a signal-interrupted large request from being rejected
    as impossible. *)

Example getrandom_large_request_still_admits_the_short_count :
  check_syscall (getrandom_call 300)
    (mkEffect 300 [(4096, some_bytes 300)] []) getrandom_model
  = CheckOk getrandom_model []
  /\ check_syscall (getrandom_call 300)
       (mkEffect 5 [(4096, some_bytes 5)] []) getrandom_model
     = CheckOk getrandom_model []
  /\ check_syscall (getrandom_call 300)
       (mkEffect (errno_ret EINTR) [] []) getrandom_model
     = CheckOk getrandom_model []
  (* a nonzero request never "succeeds" with nothing delivered *)
  /\ check_syscall (getrandom_call 300)
       (mkEffect 0 [] []) getrandom_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.
