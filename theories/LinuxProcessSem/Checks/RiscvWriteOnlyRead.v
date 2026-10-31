(** * LinuxProcessSem.Checks.RiscvWriteOnlyRead — a writable segment is readable

    [MemImageType.seg_readable] holds for a segment with 'r' or with 'w'.
    These checks run one load, [ld a0, 512(x0)], at 0x100 in an "r-x"
    segment, against an 8-byte segment at 0x200 with each permission:

    - "-w-" (PF_W alone): the load runs and reads the segment's bytes.
      On riscv Linux v6.18.46 the load page fault on a VM_WRITE-only VMA
      is not an access error (arch/riscv/mm/fault.c:257-262, "Write
      implies read"), so the process reads the page.
    - "r--": the load runs, as before.
    - "--x" (execute-only) and "---" (PROT_NONE): the load faults.  The
      same handler refuses a load from a VMA with neither VM_READ nor
      VM_WRITE.

    The source-buffer view of a syscall ([memory_read], through
    [Run.init_machine_state]'s [ms_rom]) reads the write-only segment
    too, as Linux's copy_from_user does. *)

From Stdlib Require Import ZArith NArith List String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope string_scope.

(** [ld a0, 512(x0)] = 0x20003503, little-endian. *)
Definition ld_text : Segment := {|
  seg_base := 0x100;
  seg_size := 4;
  seg_perms := "r-x";
  seg_bytes := ["03350020"%pstring]
|}.

Definition data_at_0x200 (perms : String.string) : Segment := {|
  seg_base := 0x200;
  seg_size := 8;
  seg_perms := perms;
  seg_bytes := ["3333333333333333"%pstring]
|}.

Definition segs (perms : String.string) : list Segment :=
  [ld_text; data_at_0x200 perms].

Definition st0 (pc : word) : machine_state := {|
  ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
  ms_pc_val := pc;
  ms_svc_pending := None;
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun _ => None;
  ms_rom := fun _ => None
|}.

(** The load result as (pc, a0), or (0, 0) if the step did not succeed. *)
Definition ld_result (perms : String.string) : Z * Z :=
  match step (segs perms) (st0 (Z_to_bv 64 0x100)) with
  | MachineOk ms' => (bv_unsigned (ms_pc ms'), bv_unsigned (ms_gpr ms' 0))
  | _ => (0, 0)
  end%Z.

Example write_only_segment_is_readable :
  seg_readable (data_at_0x200 "-w-") = true.
Proof. vm_compute. reflexivity. Qed.

Example load_from_write_only_segment_runs :
  ld_result "-w-" = (0x104, 0x3333333333333333)%Z.
Proof. vm_compute. reflexivity. Qed.

(** The 'r' case is unchanged. *)
Example load_from_read_only_segment_runs :
  ld_result "r--" = (0x104, 0x3333333333333333)%Z.
Proof. vm_compute. reflexivity. Qed.

Example load_from_execute_only_segment_faults :
  step (segs "--x") (st0 (Z_to_bv 64 0x100)) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

Example load_from_prot_none_segment_faults :
  step (segs "---") (st0 (Z_to_bv 64 0x100)) = MachineFault.
Proof. vm_compute. reflexivity. Qed.

(** The view a syscall reads its source buffer through. *)
Example write_only_segment_is_a_readable_source_buffer :
  memory_read (segs "-w-") (Z_to_bv 64 0x200) 8 =
    Some (repeat (Z_to_bv 8 0x33) 8).
Proof. vm_compute. reflexivity. Qed.

Example execute_only_segment_is_not_a_source_buffer :
  memory_read (segs "--x") (Z_to_bv 64 0x200) 8 = None.
Proof. vm_compute. reflexivity. Qed.
