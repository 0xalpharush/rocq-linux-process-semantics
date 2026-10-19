(** * Common.AllocIfaceToy — the planted positive for [AllocIface].

    A degenerate layout and instance that DISCHARGES every field of
    [AllocIface], proving the class is consistent and instantiable
    against our spec.  It is deliberately NOT a usable allocator model:
    [toy_env] is False, so the three CPS rules hold vacuously, and
    [live] is empty.  What this file certifies is exactly (and only)
    that the interface's law set has a model — an inconsistent class
    would let a proof derive False from Context {AI : AllocIface}, and
    this file is what rules that out.  A usable instance is a
    per-binary refinement proof (for example of mallocng); this library
    does not contain one. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import
  PropExec CatExec CatSim Hoare ShapeAlg AllocIface.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

#[local] Instance toy_layout : AllocLayout := {|
  al_segs := [];
  al_rom := fun _ => None;
  al_malloc_pc := Z_to_bv 64 0;
  al_free_pc := Z_to_bv 64 0;
  al_gp := Z_to_bv 64 0;
  al_globals := fun _ => False;
  al_errno_slot := fun _ => False;
  al_grantable := fun _ => False;
  al_ceiling := 0;
  al_image_hi := 0;
  al_in_ro := fun _ => False;
  al_in_rw := fun _ => False;
  al_ret_ok := fun _ => False;
  al_env := fun _ _ _ _ => False;
  al_init_vm := fun brk => mkVmMaps [] [] brk brk 0;
  al_mmap_threshold := 0
|}.

#[local] Program Instance toy_alloc : @AllocIface toy_layout := {|
  AS := unit;
  ainv := fun _ _ _ => True;
  live := fun _ _ => None;
  owned := fun _ _ => False;
  A0 := tt;
  fresh_small := fun _ _ => True
|}.
Solve All Obligations with (intros; easy).
