(** * LinuxProcessSem.Checks.Cases.Brk — where the initial program break can be

    Mirrors [State.brk_aslr_max] and the predicate that reads it,
    [Run.valid_brk].  What there is to pin is the EDGE of the band, in
    both directions: the last placement the band admits, and the next
    page up, which it refuses.  A bound only says something where it is
    tight, and a bound nothing sits against can be widened without a
    single proof going red.

    The cap IS the kernel's reach: [arch_randomize_brk] stops exactly
    1 GiB above the page-rounded image top and attains it (the derivation
    is on [State.brk_aslr_max]).  So the two numbers here are that reach,
    admitted, and the page above it, refused.  Widening the band — to a
    round number such as 2 GiB, or to the reach plus one spare page —
    turns the refusal red, which is the point of writing it down.

    These are worked cases, not the trusted specification: they are read
    off the definitions without running a binary.  [Checks/Examples.v]
    re-exports this module the way it re-exports the rest of
    [Checks/Cases/]. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase State MemImageType Run.
Import ListNotations.
Open Scope bv_scope.

(** An image whose LOAD reservations put the page-rounded top at
    0x14000, the top three of this tree's examples are written against
    ([Examples/brk_rev_ns], [Examples/alloc_join_ns]).  The statements
    below are about any [MemImageType.Segment] list that reserves this,
    rather than about a segment value, for the reason
    [Checks/VmMapsDisjoint.v]'s witness gives: a [Segment] carries a
    primitive-string payload, and naming one would put
    [PrimString.string] into these cases' [Print Assumptions]. *)
Definition brk_edge_reserved : list (word * word) :=
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x4000)].

Example brk_edge_reserved_top : reserved_top brk_edge_reserved = 0x14000%Z.
Proof. vm_compute. reflexivity. Qed.

(** The furthest a kernel reaches: one page above the image top, plus the
    largest displacement [randomize_page(_, SZ_1G)] can draw, which is
    1 GiB less one page.  The two cancel, so the reach is exactly 1 GiB
    above the top. *)
Definition brk_at_kernel_reach : word :=
  Z_to_bv 64 (0x14000 + 1024 * 1024 * 1024)%Z.

(** And the page past the reach, which the band refuses. *)
Definition brk_past_band_cap : word :=
  Z_to_bv 64 (0x14000 + 1024 * 1024 * 1024 + 4096)%Z.

Example brk_at_the_kernels_reach_is_admitted : forall segs,
  segments_reserved segs = brk_edge_reserved ->
  valid_brk segs brk_at_kernel_reach.
Proof.
  intros segs Hs. unfold valid_brk. rewrite Hs.
  unfold brk_edge_reserved, brk_at_kernel_reach, brk_aslr_max, page_size.
  repeat split; vm_compute; try discriminate; reflexivity.
Qed.

Example brk_one_page_past_the_kernels_reach_is_refused : forall segs,
  segments_reserved segs = brk_edge_reserved ->
  ~ valid_brk segs brk_past_band_cap.
Proof.
  intros segs Hs. unfold valid_brk. rewrite Hs.
  unfold brk_edge_reserved, brk_past_band_cap, brk_aslr_max, page_size.
  intros (_ & Hhi & _). vm_compute in Hhi. exact (Hhi eq_refl).
Qed.

(** The refusal above is by the CAP, not by alignment: the page past the
    reach is page-aligned and above the image top, so the two conjuncts
    the statement is not about are both satisfied and cannot be what
    refuses it. *)
Example brk_past_the_band_cap_meets_the_other_two_conjuncts :
  (reserved_top brk_edge_reserved <= bv_unsigned brk_past_band_cap)%Z
  /\ (bv_unsigned brk_past_band_cap mod page_size = 0)%Z.
Proof.
  unfold brk_edge_reserved, brk_past_band_cap, page_size.
  split; vm_compute; try discriminate; reflexivity.
Qed.

(** The floor is the image top itself, which is where a kernel with
    randomisation off leaves the break, and the page below it is
    refused. *)
Example brk_at_the_image_top_is_admitted : forall segs,
  segments_reserved segs = brk_edge_reserved ->
  valid_brk segs (Z_to_bv 64 0x14000).
Proof.
  intros segs Hs. unfold valid_brk. rewrite Hs.
  unfold brk_edge_reserved, brk_aslr_max, page_size.
  repeat split; vm_compute; try discriminate; reflexivity.
Qed.

Example brk_one_page_below_the_image_top_is_refused : forall segs,
  segments_reserved segs = brk_edge_reserved ->
  ~ valid_brk segs (Z_to_bv 64 0x13000).
Proof.
  intros segs Hs. unfold valid_brk. rewrite Hs.
  unfold brk_edge_reserved, brk_aslr_max, page_size.
  intros (Hlo & _ & _). vm_compute in Hlo. exact (Hlo eq_refl).
Qed.
