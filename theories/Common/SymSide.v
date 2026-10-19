(** * Common.SymSide — nested-window normalization for [SymExec]'s
      address side conditions.

    EXPLORATION / PROTOTYPE.  Image-INDEPENDENT proof library; nothing
    here is part of the trusted specification.

    [Common/SymTac.v]'s [sym_sc_auto] closes an [SCFlat] / [SCDisjoint]
    with [repeat split; lia] once the addresses are [Z] expressions over
    the caller's symbolic bases.  [StepTac.u_norm] is what gets them
    there — it collapses [bv_unsigned (Z_to_bv 64 z)] to [z] — and for a
    binary with ONE frame it is enough, because every address is
    [Z_to_bv 64 (bv_unsigned sp + k)] and the projection is one level
    deep.

    It stops working the moment a block crosses a CALL.  [main]'s frame
    is [Z_to_bv 64 (bv_unsigned rsp - 96)], [print_array]'s is
    [Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) - 160)],
    and a spill inside it is one level deeper again.  [u_norm] is
    [repeat rewrite u_Z2bv by lia], and [rewrite] takes the OUTERMOST
    match: its side condition is
    [0 <= bv_unsigned (Z_to_bv 64 (bv_unsigned rsp - 96)) - 160 < 2^64],
    which [lia] cannot see is true, because the inner projection is
    still an opaque atom.  So [u_norm] fails on the outside and never
    reaches the inside, and every cross-call [SCDisjoint] is left for
    the caller.

    [u_norm_deep] rewrites INNERMOST-first, so each side condition is
    posed only over projections that have already been collapsed.  That
    single change is what makes a block spanning
    [main -> print_array -> write_all] cost the same per instruction as
    a block inside one function. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Common Require Import StepTac SymBranch CatExec.
Import ListNotations.
Local Open Scope Z_scope.

(** Collapse [bv_unsigned (Z_to_bv 64 _)] innermost-first.  The [lia]
    side conditions see a fully normalized argument, so the caller's
    window bounds ([sp_window_lo <= bv_unsigned rsp], a grant's
    [alloc_top] bound) are enough. *)
Ltac u_norm_deep :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [Z_to_bv 64 _] => fail
      | _ => rewrite (u_Z2bv z) by lia
      end
  end.

(** The same, in a hypothesis. *)
Ltac u_norm_deep_in H :=
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [Z_to_bv 64 _] => fail
      | _ => rewrite (u_Z2bv z) in H by lia
      end
  end.

(** A [vm_compute] closer that REFUSES to run on an open goal.

    [SymTac.sym_close]'s last alternative is [StepTac.bveq], which is
    [vm_compute]-based, and a symbolic [sp] or [mmap] grant base reaching
    it does not make it fail — it makes it allocate until the process is
    OOM-killed, with no Rocq error and no useful diagnostic (the build
    just reports "Command got signal KILL").  Inside an
    [all: try solve [...]] list that is fatal in a new way: [try solve]
    is exactly the idiom that hands a tactic goals it was not written
    for, so ONE open goal in a list of thirty kills the build.

    [check_closed_term] is the guard, and it is cheap: it fails
    immediately if the goal mentions any local hypothesis.  Use this,
    never a bare [vm_compute], in a [try solve] list. *)
Ltac vm_closed :=
  lazymatch goal with
  | |- ?g => check_closed_term g
  end;
  vm_compute; reflexivity.

(** [SymTac.sym_close] with the [bveq] alternative removed, for the same
    reason. *)
Ltac sym_close_open :=
  first [ reflexivity | (f_equal; lia) | (apply bv_eq; u_norm; lia) ].

(** The whole address-side-condition closer for a cross-call block. *)
Ltac sym_sc := imm_norm; u_norm_deep; u_norm; imm_norm; repeat split; lia.

(** The side-condition script the [rdn] peeling lemmas want: the same
    normalization, plus the list-length rewrites their bounds mention. *)
Ltac rdn_side :=
  rewrite ?length_N_to_le_bytes; cbn [length];
  imm_norm; u_norm_deep; u_norm; imm_norm; lia.
