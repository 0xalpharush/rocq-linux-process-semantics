(** * LinuxProcessSem.Checks.Witness.Fs.DPath — the getcwd (17) witness, and its proof

    Mirrors [Sys/Fs/DPath.v], which answers to Linux [fs/d_path.c]: this
    file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export Prelude.

(** The witness takes -ERANGE rather than an injected errno: it is the
    answer the model actually derives from [size], while the other three
    are conditions no modeled state decides.  Above the band, failing
    closed is itself the admissible outcome. *)
Definition getcwd_witness (size : word) (m : Model) : outcome SyscallEffect :=
  if (1 <? bv_unsigned size)%Z then Unmodeled
  else ret_outcome (errno_ret ERANGE) m.

Lemma getcwd_witness_ok : forall size i m,
  getcwd_spec size i m (getcwd_witness size m).
Proof.
  intros size i m. unfold getcwd_spec, getcwd_witness.
  destruct (Z.ltb 1 (bv_unsigned size)) eqn:Hs; [apply unmodeled_intro|].
  apply alt_r. unfold err_ret, ret_only, ret_outcome. apply pure_ok.
Qed.
