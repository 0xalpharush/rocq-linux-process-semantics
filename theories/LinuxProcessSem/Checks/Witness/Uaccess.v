(** * LinuxProcessSem.Checks.Witness.Uaccess — the user-buffer boundary witnesses

    Mirrors [Sys/Uaccess.v], the spec side of the same boundary.

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

Definition access_ok_zero_witness (buf count : word)
    (m : Model) (k : outcome SyscallEffect) : outcome SyscallEffect :=
  if access_okb buf (bv_unsigned count) then k
  else ret_outcome (errno_ret EFAULT) m.
