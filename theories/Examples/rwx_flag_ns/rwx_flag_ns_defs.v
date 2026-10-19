(** * rwx-flag-ns: shared definitions and image facts.

    PROOF-SIDE FILE (not part of the trusted specification).

    Both binaries store 5 into a writable global byte, load it back, and
    exit with it: no output, exit code 5, on every input.

    What the example is FOR is the source binary's layout: it is linked
    (source/rwx.lds, via source/ldflags.txt) into a SINGLE RWX LOAD
    segment holding the ELF headers, .text, and the writable data — the
    merged layout GNU ld's default [-z noseparate-code] produces — so
    every instruction fetch goes through the model's overlay-aware w+x
    fetch ([RiscvSemantics.code_read_ov]), and both of its
    stores (musl's [__environ] slot in .bss, and [flag]) land in the
    same segment the code executes from.  The proof carries
    [WxExec.mem_clear] — "the overlay misses the .text range
    [0x10078, 0x100e4)" — as the frame invariant that lets the
    generated static [fetch_word_wx] facts close each step's fetch.
    The target is an ordinary lld-linked binary (immutable r-x code),
    so its side of the proof is the standard static-fetch machinery. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StreamSim StoreOk MmapSim WxExec.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import rwx_flag_ns_code.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import SourceMemImage.
From LinuxProcessSemantics.Examples.rwx_flag_ns Require Import TargetMemImage.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Import ListNotations.
Open Scope bv_scope.

(* ######################################################################### *)
(* Entry points                                                              *)
(* ######################################################################### *)

Lemma source_init_pc_val : SourceMemImage_init_pc = 0x10078%N.
Proof. vm_compute. reflexivity. Qed.

Lemma target_init_pc_val : TargetMemImage_init_pc = 0x1001190%N.
Proof. vm_compute. reflexivity. Qed.

(* ######################################################################### *)
(* The source image is ALL w+x: the static fetch declines everywhere         *)
(* ######################################################################### *)

Lemma source_no_ro_exec : no_ro_exec source_segs = true.
Proof. vm_compute. reflexivity. Qed.

(** The source's .text range: the [mem_clear] frame invariant is stated
    over it, and every fetched pc lies inside it. *)
Definition stext_lo : Z := 0x10078%Z.
Definition stext_hi : Z := 0x100e4%Z.

(* ######################################################################### *)
(* Store legality                                                            *)
(* ######################################################################### *)

(** The source's one RWX segment covers [0x10000, 0x11000) (page-rounded)
    and is writable with a snapshot byte for every address, so [wview]
    is defined on all of it — both stores ([__environ] at 0x100e8,
    [flag] at 0x100e4) are legal. *)
Lemma source_wseg : wseg_ok source_segs (0x10000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma source_store_ok : forall (m : word -> option byte) (a : word) (n : nat),
  (0x10000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x11000)%Z ->
  store_ok source_segs m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply store_ok_window with (base := 0x10000%Z) (hi := 0x11000%Z);
    [ | | | exact source_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.

(** The target's rw- data segment covers [0x1002000, 0x1003000). *)
Lemma target_wseg : wseg_ok target_segs (0x1002000 : word) 4096 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma target_store_ok : forall (m : word -> option byte) (a : word) (n : nat),
  (0x1002000 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 0x1003000)%Z ->
  store_ok target_segs m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply store_ok_window with (base := 0x1002000%Z) (hi := 0x1003000%Z);
    [ | | | exact target_wseg | | ];
    [ vm_compute; reflexivity | vm_compute; reflexivity | lia
    | exact Hlo | exact Hhi ].
Qed.
