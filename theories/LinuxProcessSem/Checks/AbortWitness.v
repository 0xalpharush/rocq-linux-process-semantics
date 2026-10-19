(** * LinuxProcessSem.Checks.AbortWitness — an image that really aborts

    Not part of the trusted specification: this file is QA on the
    definitions, in the sense [Checks/Examples.v] describes, and it
    exists to close one specific gap in that file's abort-family
    statements.

    ** The gap

    [Equivalence.error_free_unkilled] is [Equivalence.error_free] plus
    "and it is not killed", and the abort-declared statement family is
    stated with it.  Two things suggest that the extra
    conjunct is doing work, and both stop short of a run:

    - [Equivalence.error_free_unkilled_bites] exhibits a [behavior] whose
      trace set contains a [State.KillEv].  That behavior is HAND-WRITTEN.
      It shows the two PREDICATES differ on something of the right type;
      it does not show that any IMAGE separates them, and a [Run.behavior]
      is a record of bare [Prop]s, so nothing stops one being written
      that no [Run.run] returns.
    - [Equivalence.strong_universal_error_free_T_abort_refuted_by_abort]
      takes [Equivalence.dies_by_signal (Run.run …)] as a HYPOTHESIS.
      Without an image that discharges it, the abort family's
      refutation is stated conditionally and never fires.  A conditional refutation whose condition is never met is
      indistinguishable, from inside the development, from one whose
      condition is unsatisfiable.

    This file supplies the missing half: a concrete six-instruction image
    whose run reaches [State.KillEv], and the two statements that fall
    out of it — [abrt_dies_by_signal], which discharges the hypothesis,
    and [abrt_refutes_error_free_abort], which is the refutation actually
    fired at a real image.  It is the abort-declared twin of
    [Checks.Examples.undecodable_image_refutes_error_free_equivalence],
    and it is deliberately built the way that one is: at a valid entry,
    on a valid input, so that a statement quantified over those is really
    reached.

    ** Why an image is needed rather than a longer argument

    [Equivalence.dies_by_signal] is read off [Run.behavior]'s trace set,
    and [Run.run]'s trace set is [Run.obs_trace] of the initial
    configuration — an existential over [Run.star].  So the only way to
    satisfy it is to walk a real execution, and walking one is what
    catches the things prose does not: that the tid the [tkill] names has
    to be the one the model CHOSE rather than a constant the image
    carries, that the choice is made by a syscall the program has to
    issue first, and that [Run.sstep_killed] rather than [Run.sstep_exit]
    is the rule that fires at the end.

    ** The program

    Six instructions at 0x100, the shortest that can abort under this
    model, written as the hex a loader would have produced:

    #<pre>
      addi a7, x0, 96     06000893   set_tid_address
      addi a0, x0, 0      00000513   tidptr = NULL
      ecall               00000073   -> a0 = the tid the model chose
      addi a7, x0, 130    08200893   tkill
      addi a1, x0, 6      00600593   SIGABRT
      ecall               00000073   -> killed
    #</pre>

    THE FIRST SYSCALL IS NOT CEREMONY.  [Kernel.Signal.tkill_self]
    declines with [Monad.unmodeled] while [State.m_tid] is [None], and
    declines again unless the [pid] it is handed EQUALS the recorded tid.
    [Kernel.Fork.set_tid_address_spec] is what pins it, and it pins it to
    a value drawn with [Monad.choose] from the whole
    [Kernel.Fork.PID_MAX_ENVELOPE] window — the model cannot predict it,
    exactly as it cannot predict getrandom's bytes.  So no image can
    carry the right [pid] as an immediate.  What makes this program work
    is that [Run.apply_effect] writes the syscall's return value into a0
    and neither instruction between the two [ecall]s touches a0, so the
    tid flows from the kernel's answer straight into [tkill]'s first
    argument.  That is musl's own arrangement read back one level:
    [__init_tp] seeds [__pthread_self()->tid] from [set_tid_address], and
    [raise] sends to it.

    The choice is why this file's [abrt_eff1] names 4242: any value in
    the window would do, this is one, and it is
    [Cases.Kernel.Signal.abort_tid] so that the fixture and the run agree.

    THE MASK IS THE OTHER PREMISE.  [abrt_input] launches with
    [State.in_sigmask] clear, so SIGABRT is not blocked and
    [Kernel.Signal.send_sigabrt] takes the [State.with_killed] branch
    rather than the [State.with_sigabrt_pending] one.  musl's real
    [raise] blocks first and dies on the mask restore two calls later;
    that longer path is deliberately NOT what this file
    walks — the shortest path to a [State.KillEv] is what a non-vacuity
    witness wants.

    ADMISSION REASON (the third at the top of [Checks/Examples.v]): what
    is pinned here is that a [Run.run]'s TRACE SET contains a
    [State.KillEv], which is a statement about the model's own execution
    relation, not about anything a real run reveals. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs Examples Omni.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   The image, the launch, and the two syscall answers
   ========================================================================= *)

Definition abrt_segment : Segment := {|
  seg_base := 0x100;
  seg_size := 24;
  seg_perms := "r-x"%string;
  seg_bytes := ["930800061305000073000000930820089305600073000000"%pstring]
|}.
Definition abrt_segments : list Segment := [abrt_segment].
Definition abrt_image : Image := mkImage abrt_segments 0x100 demo_phdrs.

(** The same launch [Checks.Examples] runs its images on — one empty
    argument, no environment, an empty file system, end of input — with
    the two fields this file needs pinned: [State.in_sigmask] clear, so
    SIGABRT is deliverable, and [State.in_abort_terminal] SET, which is
    what [Run.valid_input_abort] asks for and what
    [Kernel.Signal.tkill_spec] tests first. *)
Definition abrt_input : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap true Sv48.

Example abrt_input_declares_abort : in_abort_terminal abrt_input = true.
Proof. reflexivity. Qed.

(** [Run.valid_input_abort], proved the way
    [Checks.Examples.demo_input_valid] proves [Run.valid_input] — the same
    shared clauses, the same guarded arms, and the abort declaration this
    file is about rather than its negation. *)
Example abrt_input_valid : valid_input_abort abrt_input.
Proof.
  unfold valid_input_abort, abrt_input, valid_argv, valid_envp.
  cbn [mkProcInput in_argv in_envp in_fs].
  repeat split; cbn;
    try (unfold valid_nofile; apply Z.leb_le; vm_compute; reflexivity);
    try (unfold valid_sigmask; apply bv_eq; vm_compute; reflexivity);
    try (unfold valid_hwcap; left; reflexivity);
    try lia; try reflexivity;
    repeat first [ apply Forall_nil | apply Forall_cons | split
                 | cbn; lia | reflexivity | intros [] ].
  all: try valid_urandom_default.
Qed.

(** The entry is [Checks.Examples.demo_entry], and it is valid here for
    the reason it is valid there: this image's only segment sits in the
    first page, so the same break base serves, and the fourth conjunct
    is decided by [Run.entry_stack_span_bound] from the argv and envp
    clauses alone — which [Run.valid_input_abort] carries in the same
    two positions [Run.valid_input] does. *)
Example demo_entry_valid_abrt : forall inp,
  valid_input_abort inp -> valid_entry abrt_image demo_entry inp.
Proof.
  intros inp Hvalid.
  rewrite (valid_entry_sv48 _ _ _ (valid_input_abort_va_size _ Hvalid)).
  destruct Hvalid as (Hargv & Henvp & _).
  pose proof (entry_stack_span_bound _ _ Hargv Henvp).
  cbn [abrt_image demo_entry].
  unfold valid_sp, valid_brk, valid_mmap_base, entry_stack_fits.
  rewrite Z_to_bv_unsigned, bv_wrap_small
    by (unfold bv_modulus; cbn; lia).
  unfold entry_stack_span_max, sp_window_lo, sp_window_hi in *.
  repeat split; try lia; vm_compute; try reflexivity; try discriminate.
Qed.

(* =========================================================================
   Walking the run
   ========================================================================= *)

(** The states along the first leg, named by their step count, with the
    memory abstracted exactly as [Checks.Omni]'s [wloop_msk] family
    abstracts it: no instruction of this image writes memory, so every
    state on the way carries the initial one's. *)
Definition abrt_ms0 : machine_state :=
  init_machine_state abrt_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    demo_draw
    (in_argv abrt_input) (in_envp abrt_input) (in_uid abrt_input)
    (in_hwcap abrt_input).
Definition abrt_msk (k : nat) : machine_state :=
  match run_steps k abrt_segments abrt_ms0 with
  | Some ms => ms
  | None => abrt_ms0
  end.
Definition abrt_s (k : nat) : machine_state :=
  with_mem (abrt_msk k) (ms_mem abrt_ms0).

Definition abrt_model (lim : Z) : Model :=
  init_model (segments_reserved abrt_segments) (Z_to_bv 64 0x1000)
    (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000) lim abrt_input.
Definition abrt_c (lim : Z) : config := mkCfg (abrt_s 0) (abrt_model lim).

Lemma abrt_config : forall lim,
  init_config abrt_segments 0x100 demo_phdrs (Z_to_bv 64 0x7fff80000000)
    (Z_to_bv 64 0x1000) (Z_to_bv 64 mmap_base_max) demo_draw lim abrt_input
  = abrt_c lim.
Proof.
  intros lim. unfold init_config, abrt_c.
  f_equal; try exact (with_mem_eta abrt_ms0).
Qed.

Lemma abrt_step : forall k, (k < 3)%nat -> forall mem,
  RiscvSemantics.step abrt_segments (with_mem (abrt_msk k) mem)
  = MachineOk (with_mem (abrt_msk (S k)) mem).
Proof.
  intros k Hk mem.
  do 3 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
Qed.

Lemma abrt_instr_sstep : forall lim k, (k < 3)%nat ->
  sstep abrt_segments (mkCfg (abrt_s k) (abrt_model lim)) []
    (SNext (mkCfg (abrt_s (S k)) (abrt_model lim))).
Proof.
  intros lim k Hk. unfold abrt_s.
  apply sstep_instr; [reflexivity | |].
  - do 3 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
  - no_lazy. rewrite (abrt_step k Hk). reflexivity.
Qed.

(** Three instructions in -- the two [addi]s and the [ecall] itself, which
    is an ordinary instruction step that leaves the number pending -- the
    first syscall is at the door and its number is 96. *)
Lemma abrt_svc3 : ms_svc_pending (abrt_s 3) = Some (Z_to_bv 64 96).
Proof. vm_compute. first [reflexivity | f_equal; apply bv_eq; reflexivity]. Qed.

(** THE TID THE MODEL CHOOSES.  [Monad.choose] admits any value in the
    window, so this effect names one; [abrt_sc1] is the statement that
    the acceptor agrees it is admissible, and nothing below depends on
    which one it is. *)
Definition abrt_eff1 : SyscallEffect := mkEffect abort_tid [] [].

Lemma abrt_sc1 : forall lim,
  check_syscall (sys_input abrt_segments (abrt_s 3) (Z_to_bv 64 96)) abrt_eff1
    (abrt_model lim)
  = CheckOk (with_tid abort_tid (abrt_model lim)) [].
Proof. intros lim. vm_compute. reflexivity. Qed.

(** The state the first syscall leaves: a0 holds the tid, and the pc has
    moved past the [ecall].  This is where the second leg starts. *)
Definition abrt_t0 : machine_state :=
  advance_past_svc (apply_effect (abrt_s 3) abrt_eff1).
Definition abrt_tk (k : nat) : machine_state :=
  match run_steps k abrt_segments abrt_t0 with
  | Some ms => ms
  | None => abrt_t0
  end.
(** The second leg abstracts ITS OWN memory rather than [abrt_ms0]'s.
    The two are equal — [abrt_eff1] carries no writes, copies, zeros or
    unmaps, and [Run.apply_effect] touches memory only through those —
    but naming [abrt_t0]'s is what lets [abrt_t 0] be [abrt_t0] by
    [Checks.Omni.with_mem_eta] alone, with no rewriting under
    [State.with_mem]. *)
Definition abrt_t (k : nat) : machine_state :=
  with_mem (abrt_tk k) (ms_mem abrt_t0).

Lemma abrt_syscall1_sstep : forall lim,
  sstep abrt_segments (mkCfg (abrt_s 3) (abrt_model lim)) []
    (SNext (mkCfg (abrt_t 0) (with_tid abort_tid (abrt_model lim)))).
Proof.
  intros lim.
  replace (abrt_t 0) with (advance_past_svc (apply_effect (abrt_s 3) abrt_eff1))
    by (unfold abrt_t, abrt_tk, run_steps; fold abrt_t0;
        exact (eq_sym (with_mem_eta abrt_t0))).
  eapply sstep_syscall;
    [ reflexivity
    | exact abrt_svc3
    | apply check_syscall_ok_iff; exact (abrt_sc1 lim)
    | reflexivity
    | apply materialize_model_accesses_no_lazy; reflexivity ].
Qed.

Lemma abrt_step2 : forall k, (k < 3)%nat -> forall mem,
  RiscvSemantics.step abrt_segments (with_mem (abrt_tk k) mem)
  = MachineOk (with_mem (abrt_tk (S k)) mem).
Proof.
  intros k Hk mem.
  do 3 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
Qed.

Lemma abrt_instr2_sstep : forall lim k, (k < 3)%nat ->
  sstep abrt_segments
    (mkCfg (abrt_t k) (with_tid abort_tid (abrt_model lim))) []
    (SNext (mkCfg (abrt_t (S k)) (with_tid abort_tid (abrt_model lim)))).
Proof.
  intros lim k Hk. unfold abrt_t.
  apply sstep_instr; [reflexivity | |].
  - do 3 (destruct k as [| k]; [vm_compute; reflexivity |]). lia.
  - no_lazy. rewrite (abrt_step2 k Hk). reflexivity.
Qed.

(** Three more instructions, and the second [ecall] is pending at 130. *)
Lemma abrt_svc_tkill : ms_svc_pending (abrt_t 3) = Some (Z_to_bv 64 130).
Proof. vm_compute. first [reflexivity | f_equal; apply bv_eq; reflexivity]. Qed.

(** The kill itself.  a0 carries the tid the first syscall returned, a1
    carries 6, and the post-model is [State.with_killed] — the same
    answer [Cases.Kernel.Signal.tkill_sigabrt_unblocked_kills] pins at a
    hand-built model, here reached from a real machine state whose
    registers the program put there. *)
Definition abrt_killed_model (lim : Z) : Model :=
  with_killed (Z_to_bv 64 6) (with_tid abort_tid (abrt_model lim)).

Lemma abrt_sc2 : forall lim,
  check_syscall (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
    (mkEffect (Z_to_bv 64 0) [] []) (with_tid abort_tid (abrt_model lim))
  = CheckOk (abrt_killed_model lim) [].
Proof. intros lim. vm_compute. reflexivity. Qed.

(** The trace the run ends on. *)
Definition abrt_trace (lim : Z) : list event :=
  [KillEv (Z_to_bv 64 6) (m_fs (abrt_killed_model lim))].

Lemma abrt_kill_sstep : forall lim,
  sstep abrt_segments
    (mkCfg (abrt_t 3) (with_tid abort_tid (abrt_model lim)))
    (abrt_trace lim)
    (SNext (mkCfg (abrt_t 3) (abrt_killed_model lim))).
Proof.
  intros lim. unfold abrt_trace.
  change [KillEv (Z_to_bv 64 6) (m_fs (abrt_killed_model lim))]
    with ([] ++ [KillEv (Z_to_bv 64 6) (m_fs (abrt_killed_model lim))]).
  eapply sstep_killed;
    [ reflexivity
    | exact abrt_svc_tkill
    | apply check_syscall_ok_iff; exact (abrt_sc2 lim)
    | reflexivity ].
Qed.

(** The whole execution: two instructions, [set_tid_address], two more
    instructions, [tkill], and the process is dead. *)
Lemma abrt_star : forall lim,
  star abrt_segments (abrt_c lim) (abrt_trace lim)
    (mkCfg (abrt_t 3) (abrt_killed_model lim)).
Proof.
  intros lim.
  change (abrt_trace lim)
    with ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++ ([] ++
         (abrt_trace lim ++ [])))))))).
  unfold abrt_c.
  eapply star_step; [exact (abrt_instr_sstep lim 0 ltac:(lia)) |].
  eapply star_step; [exact (abrt_instr_sstep lim 1 ltac:(lia)) |].
  eapply star_step; [exact (abrt_instr_sstep lim 2 ltac:(lia)) |].
  eapply star_step; [exact (abrt_syscall1_sstep lim) |].
  eapply star_step; [exact (abrt_instr2_sstep lim 0 ltac:(lia)) |].
  eapply star_step; [exact (abrt_instr2_sstep lim 1 ltac:(lia)) |].
  eapply star_step; [exact (abrt_instr2_sstep lim 2 ltac:(lia)) |].
  eapply star_step; [exact (abrt_kill_sstep lim) |].
  apply star_refl.
Qed.

(* =========================================================================
   What it buys
   ========================================================================= *)

(** THE HYPOTHESIS, DISCHARGED.  This is the statement
    [Equivalence.strong_universal_error_free_T_abort_refuted_by_abort]
    takes as an assumption. *)
Theorem abrt_dies_by_signal : forall lim,
  dies_by_signal (run abrt_image lim demo_entry abrt_input).
Proof.
  intros lim.
  cbn [run bh_traces abrt_image demo_entry].
  rewrite abrt_config.
  exists (abrt_trace lim), (Z_to_bv 64 6), (m_fs (abrt_killed_model lim)).
  split.
  - exists (abrt_trace lim), (mkCfg (abrt_t 3) (abrt_killed_model lim)).
    split; [exact (abrt_star lim) | apply is_prefix_refl].
  - now left.
Qed.

(** ... and therefore the abort family's bite is FIRED rather than
    stated.  [Equivalence.error_free_unkilled]'s second conjunct is what
    fails here: this run reaches no [Run.sstep] error at all — the model
    follows it to the end — so [Equivalence.error_free] alone would be
    SATISFIED by it, which is exactly the weakening
    [Equivalence.error_free_unkilled] exists to prevent.  A reader who
    wants the difference in one line has it here: the same run, accepted
    by one predicate and refused by the other. *)
Theorem abrt_refutes_error_free_abort :
  ~ strong_universal_error_free_T_abort abrt_image abrt_image.
Proof.
  apply (strong_universal_error_free_T_abort_refuted_by_abort
           abrt_image abrt_image demo_entry demo_entry abrt_input
           (demo_entry_valid_abrt _ abrt_input_valid)
           (demo_entry_valid_abrt _ abrt_input_valid)
           abrt_input_valid).
  exact (abrt_dies_by_signal source_alloc_limit).
Qed.

(** THE CONTROL, and it is the half that says the refutation above is
    about the ABORT rather than about the image.  The identical program
    is NOT refuted this way with the declaration clear, because with it
    clear [Kernel.Signal.tkill_spec] declines and the run never reaches
    a [State.KillEv] to be refuted by — it leaves the modeled surface
    instead.  So the two stances really do differ on this image, which
    is what [Run.valid_input] pinning [false] is worth. *)
Definition abrt_input_undeclared : ProcInput :=
  mkProcInput [[]] [] [] IEof demo_uid demo_gid demo_groups net_silent
    default_nofile (Z_to_bv 64 0) demo_hwcap false Sv48.

Lemma abrt_tkill_declined_undeclared :
  check_syscall (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
    (mkEffect (Z_to_bv 64 0) [] [])
    (with_tid abort_tid
       (init_model (segments_reserved abrt_segments) (Z_to_bv 64 0x1000)
          (Z_to_bv 64 mmap_base_max) (Z_to_bv 64 0x7fff80000000)
          source_alloc_limit abrt_input_undeclared))
  = CheckUnmodeled.
Proof. vm_compute. reflexivity. Qed.

(** THE DATA FLOW, PINNED.  Everything above rests on one claim about the
    program that a reader cannot check by looking at the trace: that
    [tkill]'s first argument is the value the FIRST syscall returned,
    rather than a constant the image carries.  These three say it.

    First, the argument really is the chosen tid at the second [ecall].
    The image contains no 4242: a0 was last written by
    [Run.apply_effect]. *)
Lemma abrt_tkill_pid_is_the_returned_tid :
  in_arg (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130)) 0 = abort_tid.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(** Second, the value was a CHOICE and not a constant: the acceptor
    admits a different tid from the same state, so nothing in the model
    forced 4242.  If [Kernel.Fork.set_tid_address_spec] ever answered a
    fixed value, this would stop holding and the paragraph above would
    stop being true. *)
Lemma abrt_sc1_admits_another_tid : forall lim,
  check_syscall (sys_input abrt_segments (abrt_s 3) (Z_to_bv 64 96))
    (mkEffect (Z_to_bv 64 1234) [] []) (abrt_model lim)
  = CheckOk (with_tid (Z_to_bv 64 1234) (abrt_model lim)) [].
Proof. intros lim. vm_compute. reflexivity. Qed.

(** Third, the match is what the kill DEPENDED on.  The same call, the
    same registers, the same declaration -- and a model whose recorded
    tid is one greater -- is declined rather than fatal.  So the death
    above is not the arm firing at any declared state; it is the arm
    firing because the program sent the signal to ITSELF. *)
Lemma abrt_tkill_other_tid_declined : forall lim,
  check_syscall (sys_input abrt_segments (abrt_t 3) (Z_to_bv 64 130))
    (mkEffect (Z_to_bv 64 0) [] [])
    (with_tid (Z_to_bv 64 4243) (abrt_model lim))
  = CheckUnmodeled.
Proof. intros lim. vm_compute. reflexivity. Qed.

(* =========================================================================
   The same refutation, in the classifier statement shape
   ========================================================================= *)

(** WHY THIS IS HERE AND NOT ONLY IN THE BASELINE SHAPE.  A classifier
    task is stated over [Run.run_scfg] rather than [Run.run], and the
    abort declaration has a family there too
    ([Equivalence.strong_universal_error_free_T_scfg_abort]).  Its bite
    needs an instance too, for the reason this file
    exists one shape up: a conditional refutation nobody has
    shown fires says nothing about whether the clause it names can ever
    be the one that fails.

    THE TRANSFER IS THE WHOLE PROOF, and it is one behaviour
    equivalence.  At [Run.may_fail_cfg] the filtered run and the plain
    run admit the same traces ([Run.run_scfg_may_fail]), and
    [Equivalence.dies_by_signal] is read off [Run.bh_traces], so it
    transports — which is what
    [Equivalence.dies_by_signal_behavior_equiv] is for.

    WHY [may_fail_cfg] RATHER THAN AN ARBITRARY CONFIGURATION: the
    filter only ever REMOVES executions ([Run.run_scfg_sub_traces]), so
    at a configuration that forces some family the kill could in
    principle be filtered out along with the run that reaches it.  What
    settles whether it is, is whether THIS image issues a syscall that
    configuration can refuse -- a number with no arm in
    [Run.injected_table] has nothing to inject, so no configuration
    refuses it.  This image issues [set_tid_address] and [tkill] and
    nothing else, and neither number is in that table, so no execution
    of it can be filtered and the witness would generalise to any
    configuration.  [may_fail_cfg] is stated because it is what a task
    gets by saying nothing, not because the wider claim would fail. *)
Theorem abrt_dies_by_signal_scfg : forall lim,
  dies_by_signal (run_scfg may_fail_cfg abrt_image lim demo_entry abrt_input).
Proof.
  intros lim.
  apply (dies_by_signal_behavior_equiv _ _ (run_scfg_may_fail _ _ _ _)).
  exact (abrt_dies_by_signal lim).
Qed.

(** ... and the classifier-shape refutation, fired rather than stated.
    The image is refuted against ITSELF, so the only clause that can
    fail is the one [Equivalence.error_free_unkilled] adds over
    [Equivalence.error_free]: the two runs are the same run, their trace
    sets are equal, and neither takes an error transition -- a followed
    abort is not an error.  That is the weakening the conjunct exists to
    stop, exhibited in the shape a classifier task is actually stated
    in. *)
Theorem abrt_refutes_error_free_scfg_abort :
  ~ strong_universal_error_free_T_scfg_abort may_fail_cfg abrt_image abrt_image.
Proof.
  apply (strong_universal_error_free_T_scfg_abort_refuted_by_abort
           may_fail_cfg abrt_image abrt_image demo_entry demo_entry abrt_input
           (demo_entry_valid_abrt _ abrt_input_valid)
           (demo_entry_valid_abrt _ abrt_input_valid)
           abrt_input_valid).
  exact (abrt_dies_by_signal_scfg source_alloc_limit).
Qed.
