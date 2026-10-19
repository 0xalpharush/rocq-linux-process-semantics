(** * Common.AsanCeil — the reflective ASan plan checker's CONSTANT allocation
      ceiling and floor, bridged to the run-dependent spec.

    The reflective ASan automation (AsanPlanCore / AsanPlan / AsanPlanSound /
    the AsanNodes* files) assumes that every anonymous grant ends below the
    CONSTANT [alloc_ceiling = 0x7fff7f800000] and that first-fit placement
    starts at [bottomup_floor = 0x2aaaaaaab000].  The spec instead bounds
    grants by [State.alloc_top h = vm_init_sp h - stack_max_size] (the RUN's
    stack pointer) and has no floor (placement is admissibility, not a
    search).  The checker keeps its numeric constants
    ([AsanPlanCore.CEIL] / [FLOOR]); soundness needs only that the constant
    ceiling lies at or below the spec's: for every admissible run
    [sp >= sp_window_lo = 0x7fff80000000] ([Run.valid_sp]), hence
    [alloc_top h = sp - 8 MiB >= 0x7fff7f800000 = alloc_ceiling], exactly, and the
    stack pointer field of the ledger never changes after [init_model].

    [init_sp_ok h] is the invariant the node soundness proofs carry (it is a
    conjunct of [BackingAlgebra.model_ivs_wf]); [alloc_ceiling_le_alloc_top]
    turns a [<= alloc_ceiling] side condition into the spec's [<= alloc_top h].
    [hint_placement_ok_b] is the first-fit placement gate that the checker's
    boolean grant tests use; the spec has no such gate. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State StackLayout Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Common Require Import PlacementSearch.
Import ListNotations.
Open Scope Z_scope.

(** the checker's constant ceiling *)
Definition alloc_ceiling : Z := 0x7fff7f800000.
Lemma alloc_ceiling_val : alloc_ceiling = 0x7fff7f800000.
Proof. reflexivity. Qed.

(** the bottom-up placement floor [page_round_up_Z (task_size_min / 3)] for
    an Sv48 task size (2^47 / 3 rounded up = 0x2aaaaaaab000).  The spec has no
    such floor.  Equals the
    checker's [AsanPlanCore.FLOOR]; the ASan layout lemma
    [AsanPlacement.kHighMemBeg_below_mmap_base_min] needs [mmap_base_min < bottomup_floor]. *)
Definition bottomup_floor : Z := 0x2aaaaaaab000.
Lemma bottomup_floor_val : bottomup_floor = 0x2aaaaaaab000.
Proof. reflexivity. Qed.

(** ** A first-fit placement gate, stated over [Common.PlacementSearch]

    The gate [hint_placement_ok_b]: a NULL-hint
    grant lands at or above the bottom-up floor, or no higher free gap exists below the
    recorded [vm_mmap_base] (the top-down search's postcondition).  In the spec,
    placement is pure admissibility, with no such gate.  The ASan plan checker
    RELIES on the gate (every NULL-hint grant is modelled above [kHighMemBeg], below
    [alloc_ceiling]), so the node-soundness layer takes it as ONE named hypothesis,
    [placement_policy], instead of reading it off the spec.  Discharging that hypothesis
    is a question about the spec, not a proof step. *)
Definition placement_ok (h : VmMaps) (aZ nZ : Z) : Prop :=
  bottomup_floor <= aZ
  \/ no_higher_fit (vm_reserved h ++ vm_maps h) aZ nZ (bv_unsigned (vm_mmap_base h)).

Definition placement_ok_b (h : VmMaps) (aZ nZ : Z) : bool :=
  (bottomup_floor <=? aZ)%Z
  || negb (higher_fit_b (vm_reserved h ++ vm_maps h) aZ nZ (bv_unsigned (vm_mmap_base h))).

Lemma placement_ok_b_iff : forall h aZ nZ,
  0 <= aZ -> 0 < nZ -> aZ mod page_size = 0 -> nZ mod page_size = 0 ->
  placement_ok_b h aZ nZ = true <-> placement_ok h aZ nZ.
Proof.
  intros h aZ nZ HaPos HnPos HaAl HnAl. unfold placement_ok_b, placement_ok.
  pose proof (bv_unsigned_in_range 64 (vm_mmap_base h)) as [_ Hbase].
  assert (Hb : bv_unsigned (vm_mmap_base h) < two_pow_64) by (unfold two_pow_64; exact Hbase).
  rewrite orb_true_iff, Z.leb_le, negb_true_iff.
  rewrite (no_higher_fit_iff _ _ _ _ HaPos HnPos HaAl HnAl Hb). reflexivity.
Qed.

Lemma placement_ok_b_of_floor : forall h aZ nZ,
  bottomup_floor <= aZ -> placement_ok_b h aZ nZ = true.
Proof. intros h aZ nZ H. unfold placement_ok_b. rewrite (proj2 (Z.leb_le _ _) H). reflexivity. Qed.

Definition hint_placement_ok_b (addr : word) (h : VmMaps) (aZ nZ : Z) : bool :=
  if w_is0 addr then placement_ok_b h aZ nZ else true.

Lemma hint_placement_ok_b_of_floor : forall addr h aZ nZ,
  bottomup_floor <= aZ -> hint_placement_ok_b addr h aZ nZ = true.
Proof. intros addr h aZ nZ H. unfold hint_placement_ok_b. destruct (w_is0 addr); [now apply placement_ok_b_of_floor|reflexivity]. Qed.

Lemma hint_placement_ok_b_nonnull : forall addr h aZ nZ,
  w_is0 addr = false -> hint_placement_ok_b addr h aZ nZ = true.
Proof. intros addr h aZ nZ H. unfold hint_placement_ok_b. now rewrite H. Qed.

(** THE HYPOTHESIS.  Every admissible NULL-hint grant of the spec ([Mmap.mmap_spec]:
    page-aligned, nonzero, ending at or below [alloc_top h], free) also (i) ends at or
    below the constant ceiling [alloc_ceiling] and (ii) satisfies the first-fit gate.
    Both describe a kernel's placement
    POLICY, which the spec does not pin down.  The ASan node soundness
    ([AsanNodesMmLib]/[AsanNodesMmA]) is parametric in it. *)
Definition placement_policy : Prop :=
  forall (h : VmMaps) (a : word) (nZ : Z),
    0 < nZ -> nZ mod page_size = 0 ->
    bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a ->
    bv_unsigned a + nZ <= alloc_top h ->
    region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true ->
    bv_unsigned a + nZ <= alloc_ceiling /\ placement_ok_b h (bv_unsigned a) nZ = true.

(** the ledger's stack pointer is an admissible one *)
Definition init_sp_ok (h : VmMaps) : Prop := sp_window_lo <= bv_unsigned (vm_init_sp h).

Lemma alloc_ceiling_le_alloc_top : forall h, init_sp_ok h -> alloc_ceiling <= alloc_top h.
Proof. intros h H. unfold init_sp_ok, sp_window_lo in H. unfold alloc_top, alloc_ceiling, stack_max_size. lia. Qed.

Lemma alloc_top_ge_of_ceiling : forall h z, init_sp_ok h -> z <= alloc_ceiling -> z <= alloc_top h.
Proof. intros h z H Hz. pose proof (alloc_ceiling_le_alloc_top h H). lia. Qed.

Lemma init_sp_ok_init_model : forall reserved brk0 mbase sp lim inp,
  valid_sp sp -> init_sp_ok (m_vmmaps (init_model reserved brk0 mbase sp lim inp)).
Proof. intros reserved brk0 mbase sp lim inp (Hlo & _ & _). unfold init_sp_ok. cbn. exact Hlo. Qed.

(** every ledger update of the spec and of the checker copies [vm_init_sp] *)
Lemma init_sp_ok_same : forall h h', vm_init_sp h' = vm_init_sp h -> init_sp_ok h -> init_sp_ok h'.
Proof. intros h h' E H. unfold init_sp_ok in *. rewrite E. exact H. Qed.

Lemma init_sp_ok_mkVmMapsFull : forall h r m na sb b l mb,
  init_sp_ok h -> init_sp_ok (mkVmMapsFull r m na sb b l mb (vm_init_sp h)).
Proof. intros. unfold init_sp_ok in *. cbn. assumption. Qed.

(** [State.page_round_up_Z_ge] has a [0 <= z] hypothesis; the bound holds for every [z]. *)
Lemma page_round_up_Z_ge_all : forall z, z <= page_round_up_Z z.
Proof.
  intros z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hr. lia.
Qed.

(** ** Two [check_mmap] gates, for the node lemmas that unfold the checker *)
Lemma mmap_off_aligned_b_0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.

(** [MAP_ANONYMOUS] (bit 5) survives [mmap_flags_core] (which only clears MAP_NORESERVE, bit 14) *)
Lemma mmap_anon_b_of_core : forall flags c,
  mmap_flags_core flags = c -> Z.testbit c 5 = true -> mmap_anon_b flags = true.
Proof.
  intros flags c Hc Hb. unfold mmap_anon_b. apply negb_true_iff. apply Z.eqb_neq. intro H0.
  unfold mmap_flags_core in Hc.
  pose proof (Z.land_spec (bv_unsigned flags) MAP_ANONYMOUS 5) as HL. rewrite H0, Z.bits_0 in HL.
  pose proof (Z.ldiff_spec (bv_unsigned flags) MAP_NORESERVE 5) as HD. rewrite Hc, Hb in HD.
  change (Z.testbit MAP_ANONYMOUS 5) with true in HL. change (Z.testbit MAP_NORESERVE 5) with false in HD.
  destruct (Z.testbit (bv_unsigned flags) 5); discriminate.
Qed.

(** rounding facts the node files use (see also Common.AllocSim/PlacementSearch) *)
Lemma page_round_up_Z_aligned' : forall z, page_round_up_Z z mod page_size = 0.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.
Lemma page_round_up_Z_pos' : forall z, 0 < z -> 0 < page_round_up_Z z.
Proof. intros z Hz. pose proof (page_round_up_Z_ge z). lia. Qed.

(* ------------------------------------------------------------------------- *)
(** ** The AT_RANDOM bytes are a draw                                         *)
(* ------------------------------------------------------------------------- *)
(** The 16 bytes the auxv AT_RANDOM entry points at are the fourth [Run.ExecEntry]
    field [en_random], quantified per binary.  The initial knowledge
    [AsanPlanCore.init_kn_zero] asserts that they are ZERO.  The soundness lemma for that entry
    ([AsanInit.atrandom_zero_ok]) therefore holds only under this NAMED hypothesis, which is
    FALSE on every real run: a certificate built on the base [init_kn_zero] proves a
    conditional statement that establishes nothing about the real binary.  Its only purpose is
    to keep certificates built on that base checkable.  The DEFAULT base [init_kn]
    is faithful — the block is byte string [AsanPlanCore.K_RND], bound to the draw — and needs
    no hypothesis. *)
Definition zero_random_draw (rdraw : bv 128) : Prop := rdraw = Z_to_bv 128 0.

Lemma at_random_bytes_zero : at_random_bytes (Z_to_bv 128 0) = repeat (Z_to_bv 8 0) 16.
Proof. vm_compute. reflexivity. Qed.

(** one byte of a byte string, as the slice [RefLayout.at_random_off] reads it *)
Lemma firstn1_skipn_nth : forall (l : list byte) (i : nat) (d : byte),
  (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.
