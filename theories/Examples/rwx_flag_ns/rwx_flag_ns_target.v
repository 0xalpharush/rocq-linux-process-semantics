(** * rwx-flag-ns TARGET binary (zig/lld, ordinary r-x code).

    PROOF-SIDE FILE (not part of the trusted specification).

    Delivers the one [to_wexit] derivation of the target binary: no
    output, exit 5, on every input.  The target's code is an ordinary
    immutable r-x segment, so this side is the standard static-fetch
    machinery — six instructions: form the data address, store 5 into
    the writable global, load it back, exit with it. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import rwx_flag_ns_code rwx_flag_ns_defs.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

Section TargetProof.

Variable av ev : list (list byte).

(** The initial stack pointer is QUANTIFIED (ASLR). *)
Variable asp : word.

(** The target run's own AT_RANDOM draw, independent of the source's
    (the [ed_random] half of [Run.ExecEntry]'s [en_draw]; see the source file). *)
Variable arnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned asp)%Z.
Hypothesis Hsp_hi : (bv_unsigned asp <= sp_window_hi)%Z.

Variable uid : word.

Variable hw : word.

Lemma asp_lo_num : (0x7fff80000000 <= bv_unsigned asp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma asp_hi_num : (bv_unsigned asp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

Lemma target_wexit :
  to_wexit target_segs
    (init_machine_state target_segs 0x1001190 target_phdrs asp arnd av ev uid hw)
    [] (Z_to_bv 64 5).
Proof.
  pose proof asp_lo_num as Hlo. pose proof asp_hi_num as Hhi.
  rewrite init_mkst. norm_pc.
  (* 0x1001190 lui a0, 0x1002 *)
  eapply tw_step;
    [ reflexivity
    | exact (step_lui _ _ _ _ _ _ _ _ TF_1001190 eq_refl TD_1001190)
    | step_simpl ].
  (* 0x1001194 li a1, 5 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 5);
      [ exact TF_1001194 | reflexivity | exact TD_1001194 | reflexivity
      | getr_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x1001198 sb a1, 424(a0) — the writable global := 5 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_sb_at with (a := Z_to_bv 64 0x10021a8)
        (v := Z_to_bv 64 5) (b := Z_to_bv 8 5);
      [ exact TF_1001198 | reflexivity | exact TD_1001198
      | getr_resolve; regupd_resolve; imm_norm; bveq
      | getr_resolve; regupd_resolve; reflexivity
      | bveq
      | apply target_store_ok; u_norm; cbn [Z.of_nat]; lia ]
    | step_simpl ].
  (* 0x100119c lbu a0, 424(a0) — read it back *)
  eapply tw_step;
    [ reflexivity
    | eapply step_lbu with (b := Z_to_bv 8 5);
      [ exact TF_100119c | reflexivity | exact TD_100119c
      | getr_resolve; regupd_resolve; imm_norm; wlits_closed;
        change 1%nat with (length [Z_to_bv 8 5]);
        apply rdn_wbytes_hit; u_norm; cbn [length]; lia ]
    | step_simpl ].
  (* 0x10011a0 li a7, 93 *)
  eapply tw_step;
    [ reflexivity
    | eapply step_addi_at with (v := Z_to_bv 64 93);
      [ exact TF_10011a0 | reflexivity | exact TD_10011a0 | reflexivity
      | getr_resolve; imm_norm; bveq ]
    | step_simpl ].
  (* 0x10011a4 ecall — exit(5) *)
  eapply tw_step;
    [ reflexivity
    | apply (step_ecall _ _ _ _ _ _ TF_10011a4 eq_refl)
    | ].
  apply tw_exit_coden.
  - getr_resolve; regupd_resolve; u_norm; lia.
  - regupd_resolve; bveq.
  - u_norm; lia.
Qed.

End TargetProof.
