(* Written by the OSS-Fuzz proof collaborators. *)
(** * SpecConsts — the ONE place where numeric values of trusted-spec
    constants are exposed to the proofs.

    [Uaccess.rw_bytes_max] = 2^17 = 131072.  No other file may unfold it. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.

Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.

Lemma rw_bytes_max_nonneg : (0 <= rw_bytes_max)%Z.
Proof. pose proof rw_bytes_max_ge17. lia. Qed.
