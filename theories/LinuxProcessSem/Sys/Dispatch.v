(** * LinuxProcessSem.Sys.Dispatch — a syscall as a value, and the dispatcher over them

    Every other file under [Sys/] answers to one kernel SOURCE file; this
    one answers to none, like [Sys/Syscall.v], [Sys/Uapi.v] and
    [Sys/Uaccess.v].  It is the mechanism a number reaches a spec by —
    what [arch/riscv/kernel/traps.c] does with [regs->a7] before the
    table is consulted.  NAME: this file is deliberately NOT called
    [Arm], which beside [Sys/Fs/], [Sys/Mm/] and [Sys/Kernel/] would
    read as an architecture directory; an ARM here is a dispatcher arm,
    which is what [SpecArm] stays called.

    TRUST BOUNDARY: this file is part of the trusted specification.

    An arm is a value: its number and what it admits.  Dispatch
    is a lookup in a list, so the dispatcher is written once and does
    not grow, and adding a syscall is one entry in one list.  The
    relational spec, the executable checker and the progress witness all
    read the same list.

    The list is the ONLY thing that grows, and it is kept in syscall-number
    order so two changes that add two syscalls land at different lines;
    appending both to the end would make them collide. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** One modeled syscall: the number it answers to, and the effects it
    admits given the raw [SyscallInput].  The arm reads its own arguments
    out of the input rather than being handed them, which is what lets one
    lookup serve every syscall whatever its arity. *)
Record SpecArm := mkSpecArm {
  sa_no   : Z;
  sa_spec : Sys SyscallEffect;
}.

(** The first arm answering to [n], if any.  A [None] is the fail-closed
    case and there is exactly one of it. *)
Fixpoint lookup_arm (t : list SpecArm) (n : Z) : option SpecArm :=
  match t with
  | [] => None
  | a :: r => if Z.eqb (sa_no a) n then Some a else lookup_arm r n
  end.

(** Dispatch: the arm for this input's syscall number, or [unmodeled].

    FAIL CLOSED, in one place.  A number with no arm yields [unmodeled],
    and the three layers
    cannot disagree about which numbers those are, because they read the
    same list. *)
Definition dispatch (t : list SpecArm) : Sys SyscallEffect :=
  fun i m o =>
    match lookup_arm t (bv_unsigned (in_sysno i)) with
    | Some a => sa_spec a i m o
    | None   => unmodeled i m o
    end.

(** The numbers a table covers, in the table's order. *)
Definition arm_numbers (t : list SpecArm) : list Z := map sa_no t.

(** A number the table does not carry is declined.  This is the general
    form of the per-number decline lemmas [Checks/ProcessCreation.v]
    proves, and it needs no case analysis over the table. *)
Lemma dispatch_unmodeled : forall t i m,
  lookup_arm t (bv_unsigned (in_sysno i)) = None -> dispatch t i m Unmodeled.
Proof. intros t i m H. unfold dispatch. rewrite H. apply unmodeled_intro. Qed.

(** And a number it does carry is answered by that arm, both ways. *)
Lemma dispatch_arm : forall t i m o a,
  lookup_arm t (bv_unsigned (in_sysno i)) = Some a ->
  (dispatch t i m o <-> sa_spec a i m o).
Proof. intros t i m o a H. unfold dispatch. rewrite H. reflexivity. Qed.
