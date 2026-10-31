(** * LinuxProcessSem.Checks.RiscvReservationTrap — the model has no trap between lr and sc

    SCOPE.md, "Supported systems": the reservation survives a trap that
    Linux handles and returns from, and the model has no page fault of
    that kind.  This check pins the model's side on the case SCOPE.md
    names, an [lr.w; sc.w] pair on a writable page the process has not
    written: the [sc.w] succeeds (rd = 0) and writes its value.  On
    Linux v6.18.46 the store faults (the page is not mapped writable
    yet), [ret_from_exception] clears the reservation
    (arch/riscv/kernel/entry.S:251-269), and the retried [sc.w] fails
    with rd = 1. *)

From Stdlib Require Import ZArith NArith List String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope string_scope.

(** [li t0, 0x200; li t2, 7; lr.w t1, (t0); sc.w t1, t2, (t0)],
    little-endian. *)
Definition lrsc_text : Segment := {|
  seg_base := 0x100;
  seg_size := 16;
  seg_perms := "r-x";
  seg_bytes := ["93020020930370002fa302102fa37218"%pstring]
|}.

Definition fresh_rw_page : Segment := {|
  seg_base := 0x200;
  seg_size := 4;
  seg_perms := "rw-";
  seg_bytes := ["5a5a5a5a"%pstring]
|}.

Definition lrsc_segments : list Segment := [lrsc_text; fresh_rw_page].

Definition st0 (pc : word) : machine_state := {|
  ms_regs := bvmap_empty; ms_fregs := bvmap_empty;
  ms_pc_val := pc;
  ms_svc_pending := None;
  ms_resv := None; ms_fcsr := Z_to_bv 32 0;
  ms_mem := fun _ => None;
  ms_rom := fun _ => None
|}.

Fixpoint run (n : nat) (ms : machine_state) : option machine_state :=
  match n with
  | O => Some ms
  | S k => match step lrsc_segments ms with
           | MachineOk ms' => run k ms'
           | _ => None
           end
  end.

(** After the four instructions: pc, t1 (the [sc.w] result), and the
    word now at 0x200. *)
Definition lrsc_result : option (Z * Z * Z) :=
  match run 4 (st0 (Z_to_bv 64 0x100)) with
  | Some ms =>
      match ms_read_bytes ms (Z_to_bv 64 0x200) (Z_to_bv 64 4) with
      | Some bs =>
          Some (bv_unsigned (ms_pc ms), bv_unsigned (ms_reg ms (Z_to_bv 5 6)),
                bv_unsigned (le_bytes_to_word bs))
      | None => None
      end
  | None => None
  end%Z.

Example lr_sc_on_an_unwritten_page_succeeds :
  lrsc_result = Some (0x110, 0, 7)%Z.
Proof. vm_compute. reflexivity. Qed.
