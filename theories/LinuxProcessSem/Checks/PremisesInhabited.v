(** * LinuxProcessSem.Checks.PremisesInhabited — a pair's launch premises hold together

    Not part of the trusted specification: QA on the definitions, in the
    style of [Checks/EntryStackFits.v].

    A statement about two images quantifies over one entry per image
    ([Run.valid_entry]) and one shared input.  If no entry pair and input
    satisfy its premises together, the statement holds and says nothing.
    [Equivalence.image_brk_satisfiable_entry] and
    [Equivalence.image_brk_satisfiable_entry_va] give an entry for one
    image under an input whose abort declaration is off.  This file adds:

    - [image_brk_satisfiable_entry_abort], the same under
      [Run.valid_input_abort];
    - one concrete input per abort stance, argv ["prog"] with an empty
      environment and an empty standard input, valid under
      [Run.valid_input_hwcap_rv64gc] and
      [Run.valid_input_abort_hwcap_rv64gc] respectively, and hence under
      [Run.valid_input] and [Run.valid_input_abort];
    - [pair_premises_inhabited] and [pair_premises_inhabited_abort]: for
      any two images that pass [Equivalence.image_brk_satisfiable], a
      concrete entry for each together with that input satisfy both
      [valid_entry] premises and the input premise of a pair statement
      over any of those four input predicates.

    The hypothesis is one of the three checks [Equivalence.IMAGE_WF]
    already asks for.  The budget premises ([Equivalence.source_within_budget] and
    its siblings) are about the run, not the launch, and this file does
    not cover them. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Run StackLayout MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Import ListNotations.

(** The entry: the bottom of the sp window, the break that
    [Equivalence.image_brk_satisfiable] checks, the top of the mmap-base
    band, and an all-zero draw. *)
Definition witness_entry (segs : list Segment) : ExecEntry :=
  mkEntry (Z_to_bv 64 sp_window_lo) (Z_to_bv 64 (image_brk_witness segs))
    (Z_to_bv 64 mmap_base_max) (mkDraw (Z_to_bv 128 0) (fun _ => Z_to_bv 8 0)).

Lemma image_brk_witness_valid : forall segs,
  image_brk_satisfiable segs = true ->
  valid_brk segs (Z_to_bv 64 (image_brk_witness segs)).
Proof.
  intros segs H. apply Z.ltb_lt in H.
  destruct (image_brk_witness_bounds segs) as [Hwin Hmod].
  pose proof (reserved_top_nonneg (segments_reserved segs)).
  unfold valid_brk.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold brk_aslr_max, page_size in *. lia.
Qed.

(** The entry is valid for every image that passes the check, on every
    Sv48 input whose argv and envp are valid.  Both abort stances carry
    those three clauses. *)
Lemma witness_entry_valid : forall img inp,
  valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  in_va_size inp = Sv48 ->
  image_brk_satisfiable (img_segments img) = true ->
  valid_entry img (witness_entry (img_segments img)) inp.
Proof.
  intros [segs pc ph] inp Hargv Henvp Hsize H. cbn [img_segments] in *.
  pose proof (entry_stack_span_bound _ _ Hargv Henvp) as Hspan.
  rewrite (valid_entry_sv48 _ _ _ Hsize).
  unfold witness_entry. cbv beta iota.
  split; [| split; [exact (image_brk_witness_valid segs H) | split]].
  - unfold valid_sp, sp_window_lo, sp_window_hi.
    rewrite Z_to_bv_unsigned, bv_wrap_small
      by (unfold bv_modulus; cbn; lia).
    lia.
  - unfold valid_mmap_base, mmap_base_min, mmap_base_max, sp_window_hi,
      page_size.
    rewrite Z_to_bv_unsigned, bv_wrap_small
      by (unfold bv_modulus; cbn; lia).
    lia.
  - unfold entry_stack_fits.
    rewrite Z_to_bv_unsigned, bv_wrap_small
      by (unfold bv_modulus, sp_window_lo; cbn; lia).
    unfold entry_stack_span_max in Hspan.
    unfold sp_window_lo, sp_window_hi. lia.
Qed.

(** [Equivalence.image_brk_satisfiable_entry] under the abort stance. *)
Lemma image_brk_satisfiable_entry_abort : forall img inp,
  valid_input_abort inp ->
  image_brk_satisfiable (img_segments img) = true ->
  exists en, valid_entry img en inp.
Proof.
  intros img inp Hv H.
  pose proof (valid_input_abort_va_size _ Hv) as Hsize.
  destruct Hv as (Hargv & Henvp & _).
  exists (witness_entry (img_segments img)).
  exact (witness_entry_valid img inp Hargv Henvp Hsize H).
Qed.

(** The input: argv ["prog"], no environment, an empty file system, an
    empty standard input, uid and gid 1000, no supplementary groups, the
    quiet network, the default descriptor limit, an empty blocked mask,
    the V-less capability word, the abort declaration as given, and
    Sv48. *)
Definition prog_arg : list byte :=
  [Z_to_bv 8 112; Z_to_bv 8 114; Z_to_bv 8 111; Z_to_bv 8 103].

Definition witness_input (abort : bool) : ProcInput :=
  mkProcInput [prog_arg] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1000) []
    net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc abort Sv48.

Lemma prog_arg_no_nul : ~ In (Z_to_bv 8 0) prog_arg.
Proof.
  unfold prog_arg. cbn [In].
  intros [H | [H | [H | [H | []]]]];
    apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate.
Qed.

Ltac witness_input_tac :=
  unfold witness_input, valid_argv, valid_envp;
  cbn [mkProcInput in_argv in_envp in_fs];
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try exact prog_arg_no_nul;
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | exact prog_arg_no_nul
                 | split | cbn; lia | reflexivity | intros [] ];
  try valid_urandom_default.

Lemma witness_input_valid : valid_input_hwcap_rv64gc (witness_input false).
Proof. unfold valid_input_hwcap_rv64gc. witness_input_tac. Qed.

Lemma witness_input_valid_abort :
  valid_input_abort_hwcap_rv64gc (witness_input true).
Proof. unfold valid_input_abort_hwcap_rv64gc. witness_input_tac. Qed.

(** The launch premises of a pair statement under [Run.valid_input] or
    [Run.valid_input_hwcap_rv64gc], all at once, for any two images that
    pass the check.  The two entries are independent; the input is
    shared. *)
Lemma pair_premises_inhabited : forall p s,
  image_brk_satisfiable (img_segments p) = true ->
  image_brk_satisfiable (img_segments s) = true ->
  valid_entry p (witness_entry (img_segments p)) (witness_input false)
  /\ valid_entry s (witness_entry (img_segments s)) (witness_input false)
  /\ valid_input (witness_input false)
  /\ valid_input_hwcap_rv64gc (witness_input false).
Proof.
  intros p s Hp Hs.
  pose proof witness_input_valid as Hv.
  pose proof (valid_input_of_valid_input_hwcap_rv64gc _ Hv) as Hv'.
  pose proof (valid_input_va_size _ Hv') as Hsize.
  destruct Hv' as (Hargv & Henvp & _).
  split; [exact (witness_entry_valid p _ Hargv Henvp Hsize Hp) |].
  split; [exact (witness_entry_valid s _ Hargv Henvp Hsize Hs) |].
  split; [exact (valid_input_of_valid_input_hwcap_rv64gc _ Hv) | exact Hv].
Qed.

(** The same under [Run.valid_input_abort] or
    [Run.valid_input_abort_hwcap_rv64gc]. *)
Lemma pair_premises_inhabited_abort : forall p s,
  image_brk_satisfiable (img_segments p) = true ->
  image_brk_satisfiable (img_segments s) = true ->
  valid_entry p (witness_entry (img_segments p)) (witness_input true)
  /\ valid_entry s (witness_entry (img_segments s)) (witness_input true)
  /\ valid_input_abort (witness_input true)
  /\ valid_input_abort_hwcap_rv64gc (witness_input true).
Proof.
  intros p s Hp Hs.
  pose proof witness_input_valid_abort as Hv.
  pose proof (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ Hv) as Hv'.
  pose proof (valid_input_abort_va_size _ Hv') as Hsize.
  destruct Hv' as (Hargv & Henvp & _).
  split; [exact (witness_entry_valid p _ Hargv Henvp Hsize Hp) |].
  split; [exact (witness_entry_valid s _ Hargv Henvp Hsize Hs) |].
  split; [exact (valid_input_abort_of_valid_input_abort_hwcap_rv64gc _ Hv)
         | exact Hv].
Qed.
