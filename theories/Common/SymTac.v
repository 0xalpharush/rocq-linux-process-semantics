(** * Common.SymTac — the per-block tactic wrapper around [Common.SymExec].

    EXPLORATION / PROTOTYPE.

    [Common/SymExec] proves the theorem; this file is what makes it
    cheap to USE.  Applying [sym_exec_sound] by hand costs ~30 lines of
    mechanical boilerplate per block (build the entry [sym_state], build
    [st_ok] from the goal's machine state, [Eval vm_compute] the exit
    state and the side-condition list, [destruct] the conclusion,
    re-attach the resulting [msteps] to whichever chain relation the
    goal is in, read the exit registers back through [regs_ok]).  At
    that price a straight line has to be ~40 instructions long before it
    pays for itself, which is only true of a crt entry sequence.

    [sym_block] does all of it in one tactic call.  What is left for the
    caller is exactly the mathematical content:

      sym_block segs fuel dirs reads pins pvals rvals R H.
      { (* the side conditions the block assumed, in order *) ... }
      { (* one goal per pinned register *) ... }

    and, when the block is pure ALU/control (the common case), both
    braces are empty and the whole block is ONE line.

    THE ARGUMENTS.

    - [segs]  — the image's segment list (the same one the fetch lemmas use).
    - [fuel]  — an upper bound on the number of instructions to run.  The
      executor stops on its own at the first thing it does not model, so
      over-estimating costs only [vm_compute] time.
    - [dirs]  — the branch script: one [bool] per [Branch] the run meets.
      Each one becomes an [SCBr] side condition, so nothing is assumed.
    - [reads] — the read script: an [expr] NAMING each value the block
      loads out of the base memory, in the order the executor meets
      them.  Empty (or exhausted) means "call it a fresh variable", the
      only option before; naming a reloaded return address [ELit 0x11020]
      is what lets the [ret] two instructions later resolve, which is
      the difference between stopping at every musl wrapper epilogue and
      running through it.  Either way the obligation is the same
      [SCReadBase].
    - [pins]  — [(register, expr)] pairs describing what the caller
      already knows about the entry register file.  The entry state is
      otherwise [sr_id] ("every register is its own variable"), which is
      already enough for sp-relative addressing: [EVar 2] IS a legal
      symbolic base.  A pin is needed when a register's value has to be
      a LITERAL for the run to continue — a [jalr] return address, a
      global pointer used as an absolute address.
    - [pvals] — the values of the [EVar 32], [EVar 33], … the pins
      mention, in index order.  Pinning [sp] to [EVar 32] with
      [pvals = [Z_to_bv 64 (bv_unsigned rsp - 32)]] is how a frame base
      enters the block as a symbolic-but-named quantity.
    - [rvals] — the values of the words the block READS out of the base
      memory, in the order the executor meets them (each one raises an
      [SCReadBase] obligation).  Their indices continue after [pvals]'.
    - [R], [H] — the names to bind the exit register file and its
      [regs_ok] fact to.  [H] is what [sym_regs] reads the block's
      results out of.

    THE VALUATION.  [E] is always [Eplus regs (pvals ++ rvals)]: below
    32 it is the ENTRY register file, at and above 32 it is the caller's
    list.  Nothing else is ever needed, and — this is the point — the
    valuation is a term the executor never sees.  Everything
    [vm_compute] touches ([sym_exec], [sr_pins], [sr_get]) is closed
    deep syntax: [Z] literals, register indices, the memory image.  No
    [bv] variable can reach it, which is the trap [Common/StepTac]'s
    [bveq] docstring describes.

    WHAT STOPS A BLOCK.  The executor hands the state back at the first
    instruction it does not model, and [sym_block] then leaves the goal
    at exactly that pc for the tactic layer.  In the example proofs the
    three reasons that actually fire are, in order of frequency:
    [ecall]; a [jalr] whose target register is not a literal (a [ret]
    at the top of a block, before anything has written [ra]); and the
    narrow accesses [sh] and the SIGN-EXTENDING [lb]/[lh].

    The narrow-access list is worth stating precisely, because the
    zero-extending loads and the wider stores DO go through, and a reader
    who assumes otherwise gives up on the reflective route for a block
    that would have run.  [sym_step]'s store arm takes [SZ1]/[SZ4]/[SZ8],
    so [sb]/[sw]/[sd] are all modelled and only [sh] ([SZ2]) is not.  Its
    load arm splits: a read that MISSES the store log takes [SZ8] signed,
    [SZ4]/[SZ2]/[SZ1] unsigned, and [SZ4] signed through [mkSext32] — so
    [ld]/[lwu]/[lhu]/[lbu]/[lw] all go through there and only the
    sign-extending [lb]/[lh] are missing — while a read that HITS the log
    is [SZ8] signed only, a slot being read back whole. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.Common Require Import
  ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim WallSim StreamSim
  DrainSim StoreOk Footprint SymExec StepTac ShapeAlg.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* ######################################################################### *)
(* 1. Pinning entry registers                                                *)
(* ######################################################################### *)

(** Apply a list of [(register, expr)] pins to a symbolic register file.
    Left to right, so a later pin of the same register wins. *)
Fixpoint sr_pins (ps : list (reg * expr)) (sr : list expr) : list expr :=
  match ps with
  | [] => sr
  | (r, e) :: rest => sr_pins rest (sr_upd sr (ridx r) e)
  end.

(** The caller's side of a pin list: each pinned register really does
    hold the value its [expr] denotes. *)
Definition pins_ok (E : env) (regs : bvmap 5 word) (ps : list (reg * expr))
  : Prop :=
  Forall (fun p => getr regs (fst p) = edenot E (snd p)) ps.

Lemma regs_ok_pins : forall E ps sr regs,
  regs_ok E sr regs -> pins_ok E regs ps -> regs_ok E (sr_pins ps sr) regs.
Proof.
  intros E ps. induction ps as [|[r e] rest IH]; intros sr regs Hr Hp;
    [exact Hr|].
  unfold pins_ok in Hp. inversion Hp as [|p ps' Hh Ht Heq]; subst.
  cbn [fst snd] in Hh. cbn [sr_pins].
  apply IH; [apply regs_ok_pin; [exact Hr | exact Hh] | exact Ht].
Qed.

(* ######################################################################### *)
(* 2. Value normalization for the post-state reader                          *)
(* ######################################################################### *)

(** A [mv rd,rs] is [addi rd,rs,0]; the smart constructor cannot fold it
    (the base is symbolic), so EVERY register copy in a compiled
    prologue denotes as [alu64 ADD x 0].  One lemma collapses all of
    them, which is why [sym_regs] can read a shuffled argument register
    back without a per-instruction script. *)
Lemma alu64_add_0 : forall x : word, alu64 ALU_ADD x (Z_to_bv 64 0) = x.
Proof.
  intro x. rewrite alu_add. change (v_add x (Z_to_bv 64 0)) with (v_addi x 0).
  apply v_addi_0.
Qed.

(** The corresponding 32-bit identity, for a [sext.w]/[addiw rd,rs,0]. *)
Lemma aluw_add_0 : forall x : word,
  sext 64 (alu32 ALU_ADD (low32 x) (low32 (Z_to_bv 64 0))) = v_lw x.
Proof.
  intro x. rewrite low32_lit.
  change (Z_to_bv 32 0) with (@Z_to_bv 32 0).
  rewrite alu32_add_0. apply b_lw_val.
Qed.

(** The word-op counterpart of [alu_add]/[alu_sub]/... .  The executor's
    [EAluw op a (ELit k)] denotes as
    [sext 64 (alu32 op (low32 a) (low32 (Z_to_bv 64 k)))], and NO library
    lemma is stated against that spelling: [PropExec.w_addiw] takes the
    immediate as a [bv 12] under a [sext 32], which is the shape the
    per-instruction step lemmas produce, not the one a reflective block
    leaves behind.  Without this rule every [addiw]/[sext.w] a block
    executes has to be re-derived at its use site — and [addiw] is how
    every 32-bit C expression compiles. *)
Lemma aluw_addi_lit : forall (a : word) (k : Z),
  sext 64 (alu32 ALU_ADD (low32 a) (low32 (Z_to_bv 64 k))) = v_addiw a k.
Proof.
  intros a k. apply bv_eq. unfold v_addiw.
  rewrite sext32_unsigned, !Z_to_bv_unsigned. f_equal.
  change (alu32 ALU_ADD (low32 a) (low32 (Z_to_bv 64 k)))
    with (low32 a + low32 (Z_to_bv 64 k)).
  rewrite bv_add_unsigned, !low32_unsigned, Z_to_bv_unsigned.
  rewrite bv_swrap_wrap', bv_swrap_add_idemp_l.
  rewrite (bv_wrap_bv_wrap 32 64 k) by lia.
  rewrite bv_swrap_add_idemp_r. reflexivity.
Qed.

(** The four denotation projections, as REWRITE rules.  [cbn]'s delta
    list cannot be used for these: [adenot]/[bdenot] unfold to a [v_addi]
    that is already in normal form, so [cbn] judges the step
    unproductive and leaves the projection folded — the resulting goal
    then mentions [adenot], which no library lemma is stated against. *)
Lemma bdenot_var : forall E n, bdenot E (SBVar n) = E n.
Proof. reflexivity. Qed.

Lemma bdenot_lit : forall E, bdenot E SBLit = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Lemma edenot_lit : forall E z, edenot E (ELit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.

Lemma edenot_var : forall E n, edenot E (EVar n) = E n.
Proof. reflexivity. Qed.

(** [v_addi] IS [Z_to_bv 64 (bv_unsigned x + i)] definitionally (that is
    how [SeqExec.v_addi_m] and [StepTac.v_addi_nneg_t] are proved by
    [reflexivity]); as a rewrite rule with the displacement a VARIABLE it
    normalizes any offset, where [StepTac.sp_norm] only knows the six
    negative constants it has named lemmas for.  A reflectively executed
    block produces whatever displacement the compiler chose. *)
Lemma v_addi_Z : forall (x : word) (i : Z),
  v_addi x i = Z_to_bv 64 (bv_unsigned x + i).
Proof. reflexivity. Qed.

Lemma adenot_var : forall E n k,
  adenot E (SA (SBVar n) k) = Z_to_bv 64 (bv_unsigned (E n) + k).
Proof. reflexivity. Qed.

Lemma adenot_lit : forall E k, adenot E (SA SBLit k) = Z_to_bv 64 k.
Proof.
  intros E k. unfold adenot. cbn [a_base a_off bdenot].
  rewrite v_addi_Z, u_Z_to_bv64_0; f_equal; lia.
Qed.

(** Reduce an [Eplus] application to the thing it actually is: an entry
    register read below 32, a caller-supplied value at or above it.
    The [Z_to_bv 5] the index roundtrip leaves behind is re-spelled as
    the numeral literal the rest of the library uses, so a caller's
    [reg_get regs 8 = …] hypothesis applies by [rewrite]. *)
End WithFP1.
Ltac sym_env_cbn :=
  cbn [Eplus Nat.ltb Nat.leb Nat.sub Nat.add Z.of_nat nth app fst snd
       a_base a_off e_addr e_width e_val].

Ltac sym_env_norm :=
  sym_env_cbn;
  rewrite ?adenot_var, ?adenot_lit, ?bdenot_var, ?bdenot_lit,
          ?edenot_lit, ?edenot_var, ?u_Z_to_bv64_0;
  sym_env_cbn;
  repeat match goal with
  | |- context [getr ?rs (Z_to_bv 5 ?z)] =>
      let u := eval vm_compute in z in
      let l := constr:(@BV 5 u ltac:(vm_compute; exact I)) in
      replace (Z_to_bv 5 z) with l by (apply bv_eq; vm_compute; reflexivity)
  end.

Section WithFP3.
Context {fx : FPState}.

(** Put every address the symbolic layer produced into the canonical
    [Z_to_bv 64 (bv_unsigned base + k)] spelling the example proofs
    state their frame slots in, and collapse the
    [bv_unsigned (Z_to_bv 64 _)] projections that leaves. *)
(** Fold the literal displacements a chain of [addi]s leaves behind.
    [sp] pushed twice and then indexed reads back as
    [bv_unsigned rsp - 32 + -8]; every example states its frame slots as
    [bv_unsigned rsp - 40], and the downstream read lemmas match
    syntactically, so the two spellings have to be reconciled here
    rather than at each use site.  Every step is closed [Z] arithmetic
    discharged by [lia]. *)
End WithFP3.
Ltac sym_z_lit k :=
  lazymatch k with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

Ltac sym_z_norm :=
  repeat match goal with
  (* An ABSOLUTE address arrives as [bv_unsigned (Z_to_bv 64 0) + k],
     i.e. [0 + k] once [u_norm] has run.  Left alone it defeats every
     downstream [imm_norm; lia] (the image's store/read lemmas want the
     bare literal), which is one [replace] per absolute access. *)
  | |- context [Z_to_bv 64 (0 + ?k)] =>
      sym_z_lit k; replace (0 + k)%Z with k by lia
  | |- context [Z_to_bv 64 (?a - ?k1 + ?k2)] =>
      sym_z_lit k1; sym_z_lit k2;
      let v := eval vm_compute in (k1 - k2)%Z in
      replace (a - k1 + k2)%Z with (a - v)%Z by lia
  | |- context [Z_to_bv 64 (?a + ?k1 + ?k2)] =>
      sym_z_lit k1; sym_z_lit k2;
      let v := eval vm_compute in (k1 + k2)%Z in
      replace (a + k1 + k2)%Z with (a + v)%Z by lia
  | |- context [Z_to_bv 64 (?a + Zneg ?p)] =>
      replace (a + Zneg p)%Z with (a - Zpos p)%Z by lia
  end.

Ltac sym_addr_norm :=
  imm_norm; rewrite ?v_addi_Z; sym_env_norm; u_norm; sym_z_norm.

Section WithFP6.
Context {fx : FPState}.

(** Re-spell a CLOSED stored word as the numeral literal the example
    proofs use.  A stored return address arrives from the executor as
    [Z_to_bv 64 69664] and has to read back as [0x11020 : word] for the
    tactic layer's [rdn_wbytes_hit8] to close by [reflexivity].

    Scoped to [word_to_le_bytes] arguments on purpose: the two spellings
    are propositionally but not definitionally equal, and re-spelling
    one that appears in an EXPORTED lemma statement (a [to_rd]'s buffer
    size, say) would change the statement. *)
End WithFP6.
Ltac sym_lit_norm :=
  repeat match goal with
  (* Same problem one level out: an ABSOLUTE store address in the log
     denotes as [Z_to_bv 64 77824], and every image read lemma
     ([rdn_wbytes_hit], the [rdn_wbytes_disjoint] chains) is stated
     against the numeral literal [0x13000] the caller wrote.  Without
     this the caller pays a [replace ... by bveq] per absolute store the
     block performed, which is the single most common line in a
     converted proof. *)
  | |- context [wbytes ?m (Z_to_bv 64 ?z) ?bs] =>
      lazymatch z with
      | Zpos _ =>
          let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
          replace (Z_to_bv 64 z) with l by bveq
      end
  | |- context [word_to_le_bytes ?n (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | Zpos _ =>
          let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
          replace (Z_to_bv 64 z) with l by bveq
      end
  end.

Section WithFP7.
Context {fx : FPState}.

(** Normalize a symbolic value into the [v_*] shapes the tactic library
    ([sp_norm], [bveq], [getr_resolve]) expects.  Extends
    [SymExec.sym_val_norm] with the [mv] identities and the valuation. *)
End WithFP7.
Ltac sym_norm :=
  cbn [edenot sr_get nth ridx s_regs s_pc s_log s_next branch_taken];
  rewrite ?alu64_add_0, ?aluw_add_0;
  rewrite ?aluw_addi_lit;
  rewrite ?alu_add, ?alu_sub, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slt, ?alu_sltu, ?alu_sll, ?alu_srl, ?alu_sra;
  rewrite ?v_add_lit, ?v_sub_lit;
  sym_addr_norm.

Section WithFP8.
Context {fx : FPState}.

(** Unfold the store log's denotation into the [wbytes] chain the tactic
    layer's read lemmas ([rdn_wbytes_hit8], [rdn_wbytes_disjoint],
    [rdn_wbytes_below]) are stated against, with the addresses in
    canonical form and the stored constants in literal form. *)
End WithFP8.
Ltac sym_mem_norm :=
  cbn [mem_denot e_addr e_width e_val];
  sym_norm; sym_lit_norm.

Section WithFP9.
Context {fx : FPState}.

(* ######################################################################### *)
(* 3. Attaching an [msteps] to whichever chain relation the goal is in       *)
(* ######################################################################### *)

(** The two chain relations that had no [msteps]-prepending lemma yet.
    Both are the same two-line induction as [CatSim.msteps_to_wexit]. *)
Lemma msteps_to_exit : forall segs code ms ms',
  msteps segs ms ms' -> to_exit segs code ms' -> to_exit segs code ms.
Proof.
  intros segs code ms ms' H; induction H as [|ms ms1 ms2 Hp Hs Hms IH]; [auto|].
  intro He. eapply te_step; eauto.
Qed.

Lemma msteps_to_wr : forall segs LH bs ms ms',
  msteps segs ms ms' ->
  StreamSim.to_wr segs LH bs ms' -> StreamSim.to_wr segs LH bs ms.
Proof.
  intros segs LH bs ms ms' H; induction H as [|ms ms1 ms2 Hp Hs Hms IH];
    [auto|].
  intro Hw. eapply StreamSim.twr_step; eauto.
Qed.

(** The loop-body goal of [StreamSim]: "this state runs to SOME loop
    head".  Prepending an [msteps] to it is what lets a block run all
    the way to the loop head and then close by [mst_refl], instead of
    guessing the target state into an [eexists] before the block has
    produced its register file. *)
Lemma msteps_lh_next : forall segs LH ms ms',
  msteps segs ms ms' ->
  StreamSim.lh_next segs LH ms' -> StreamSim.lh_next segs LH ms.
Proof.
  intros segs LH ms ms' H (m & Hm & HL). exists m. split; [|exact HL].
  eapply msteps_trans; eauto.
Qed.

(** The model side conditions carried by [ShapeAlg.rz_msteps] but not the other
    chain relations do not: a silent machine step is only admissible
    from a NON-halted model with no lazy mappings.  In a [realizes]
    derivation these are always either hypotheses in context or literals,
    and the model is often wrapped in the allocator's model transformers —
    which preserve both fields. *)
End WithFP9.
Ltac sym_halted :=
  solve [ reflexivity
        | eassumption
        | (rewrite ?MmapSim.mmap_model_halted, ?MmapSim.munmap_model_halted;
           solve [ reflexivity | eassumption ])
        | (cbn [cfg_model m_halted]; autorewrite with model; solve [ reflexivity | eassumption ]) ].

Ltac sym_no_lazy :=
  cbn [cfg_model];
  repeat first
    [ rewrite MmapSim.mmap_model_lazy
    | apply MmapSim.munmap_model_no_lazy ];
  solve [ reflexivity | eassumption ].

Section WithFP10.
Context {fx : FPState}.

(** Prepend a run of ordinary instruction steps to the current chain
    goal.  Mirrors [StepTac.chain_step] one level up: same set of
    relations, [msteps] instead of a single [step].

    The [ShapeAlg.realizes] case is what lets a [sym_block] run
    directly inside a shape-algebra derivation instead of inside one of
    the bespoke [to_*] relations.  It is [ShapeAlg.rz_msteps] with its
    model premises pre-discharged by [sym_halted] and [sym_no_lazy], so
    that this alternative leaves the SAME two goals as every other one
    ([msteps], then the advanced chain goal) and [chain_mst; [exact
    Hms|]] keeps working verbatim. *)
End WithFP10.
Ltac chain_mst :=
  first [ eapply CatSim.msteps_to_wexit
        | eapply MmapSim.msteps_twm
        | eapply MmapSim.msteps_twm_tail
        | eapply MmapSim.msteps_tmw
        | eapply StreamSim.msteps_to_rd
        | eapply msteps_to_wr
        | eapply WallSim.msteps_to_wall_tail
        | eapply WallSim.msteps_to_wallexit
        | eapply DrainSim.msteps_to_rd
        | eapply DrainSim.msteps_to_out
        | eapply msteps_to_exit
        | eapply msteps_lh_next
        | (eapply ShapeAlg.rz_msteps; [ sym_halted | sym_no_lazy | | ])
        | eapply msteps_trans ].

Section WithFP11.
Context {fx : FPState}.

(** Regression: the [realizes] alternative really does leave the two
    goals [chain_mst]'s callers expect, in that order. *)
Lemma chain_mst_realizes : forall segs ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ShapeAlg.realizes segs (mkCfg ms' model) T ->
  ShapeAlg.realizes segs (mkCfg ms model) T.
Proof.
  intros segs ms ms' model T Hh Hlazy Hms Hr.
  chain_mst; [exact Hms | exact Hr].
Qed.

(** ... and through an allocator's model transformer, which is the
    shape [DrainAlg.rz_mmap_drain]'s success continuation hands the
    per-binary layer. *)
Lemma chain_mst_realizes_mmap : forall segs ms ms' model a n T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  ShapeAlg.realizes segs (mkCfg ms' (MmapSim.mmap_model a n model)) T ->
  ShapeAlg.realizes segs (mkCfg ms (MmapSim.mmap_model a n model)) T.
Proof.
  intros segs ms ms' model a n T Hh Hlazy Hms Hr.
  chain_mst; [exact Hms | exact Hr].
Qed.

(* ######################################################################### *)
(* 4. Reading a block's post-state back                                      *)
(* ######################################################################### *)

(** Resolve every [getr R r] in the current goal through the exit
    [regs_ok] fact [H], reduce the symbolic register file by
    [vm_compute] (closed deep syntax only — the valuation is not part of
    it) and normalize the result.

    This is the counterpart of [SeqExec.getr_resolve]: after a
    [sym_block] the register file is an opaque [R], and this is how a
    fact about it is read out. *)
(** Close a goal that [sym_regs] has reduced.  Four spellings occur:
    already syntactically equal; two [Z_to_bv 64] terms whose arguments
    differ by [Z] arithmetic; the same over an OPEN [sp] window; and a
    closed [bv] equation between two literal forms.  Note the order:
    [bveq] is LAST, because it is the only alternative that reaches
    [vm_compute], and an open [bv] goal does not make [vm_compute] fail
    — it makes it allocate until the machine dies (its own docstring's
    warning).  Everything an open goal can be closed by is tried first,
    and [bveq]'s timeout is the backstop. *)
End WithFP11.
Ltac sym_close :=
  first [ reflexivity
        | (f_equal; lia)
        | (apply bv_eq; u_norm; lia)
        | bveq ].

Ltac sym_regs H :=
  getr_resolve; regupd_resolve;
  rewrite <- ?getr_nz by reg_neq_tac;
  rewrite ?(H _);
  repeat match goal with
  | |- context [sr_get ?a ?b] =>
      let v := eval vm_compute in (sr_get a b) in change (sr_get a b) with v
  end;
  sym_norm.

Section WithFP13.
Context {fx : FPState}.

(** Same, for a single register, stating the value.  Produces
    [getr R r = v] as a hypothesis, leaving the caller's [tac] to close
    whatever arithmetic is left. *)
End WithFP13.
Ltac sym_reg H R r v tac :=
  assert (getr R r = v) by (sym_regs H; tac).

Section WithFP14.
Context {fx : FPState}.

(* ######################################################################### *)
(* 5. [sym_block]                                                            *)
(* ######################################################################### *)

(** Syntactic length of a list literal.  Deliberately NOT [eval
    vm_compute in (length l)]: [pvals]/[rvals] hold OPEN [bv] terms, and
    [vm_compute] on one of those does not fail, it allocates until the
    machine dies (see [StepTac.bveq]'s docstring).  This walks the
    constr instead and never reduces anything. *)
End WithFP14.
Ltac list_len l :=
  lazymatch l with
  | nil => constr:(0%nat)
  | @cons _ _ ?t => let n := list_len t in constr:(S n)
  end.

Section WithFP15.
Context {fx : FPState}.

(** Put the chain goal's pc into the [Z_to_bv 64 z] spelling [st_ok]
    wants.  The numeral-literal form the tactic layer leaves behind is
    NOT convertible to it (different well-formedness proofs), so this is
    a propositional rewrite. *)
End WithFP15.
Ltac sym_pc_Z :=
  lazymatch goal with
  | |- context [ mkst ?r ?p ?m ?ro ] =>
      lazymatch p with
      | Z_to_bv 64 _ => idtac
      | _ => check_closed_term p;
             let u := vm_eval (bv_unsigned p) in
             replace p with (Z_to_bv 64 u) by bveq
      end
  end.

Section WithFP16.
Context {fx : FPState}.

(** Re-spell the chain state's pc as a numeral literal.  [StepTac]'s
    [norm_pc] does this for the chain-goal heads it enumerates; a block
    can also land on one it does not know (StreamSim's [lh_next], the
    loop-body goal), and the pc has to be a literal for the next fetch
    lemma to apply. *)
End WithFP16.
Ltac sym_pc_lit :=
  try lazymatch goal with
  | |- context [ mkst ?r ?p ?m ?ro ] => wlit p
  end.

Section WithFP17.
Context {fx : FPState}.

(** The side conditions a block emits that need no per-binary input.
    Every [SCFlat] is "this address is inside the window the caller
    already has bounds for", which is one [lia]; every [SCBr] whose
    operands the pins made literal is closed.  Between them that is
    two thirds of the obligations of a typical block, and discharging
    them here is the difference between a per-block cost that scales
    with the number of memory accesses and one that scales with the
    number of INTERESTING memory accesses.

    Deliberately no [vm_compute]: an [SCFlat] mentions the caller's
    symbolic [sp], and [vm_compute] on an open [bv] term does not fail,
    it allocates until the machine dies. *)
End WithFP17.
Ltac sym_sc_auto :=
  first [ reflexivity | (repeat split; lia) ].

Section WithFP18.
Context {fx : FPState}.

(** A pin that the PREVIOUS block already established.  Blocks chain:
    the register a block pins is almost always one an earlier
    [sym_block] left a [regs_ok] fact about, so the obligation is
    discharged by reading it back out — which hypothesis to read it out
    of is found by backtracking over the [regs_ok] facts in context.
    Deliberately closed with the [vm_compute]-free closers only: a wrong
    guess must fail FAST, and the goal is open ([sp] is symbolic). *)
End WithFP18.
Ltac sym_pin_auto :=
  first
  [ reflexivity
  | multimatch goal with
    | H : regs_ok _ _ _ |- _ =>
        sym_regs H; first [ reflexivity | (f_equal; lia) | (apply bv_eq; u_norm; lia) ]
    end ].

Section WithFP19.
Context {fx : FPState}.

(** Execute a straight line reflectively.

    Leaves, in order: the block's side conditions (one goal, an
    already-[Forall_cons]-peeled conjunction — empty and auto-closed for
    a pure ALU block), one goal per pin, and then the original chain
    goal advanced to the state the executor stopped at. *)
End WithFP19.
Ltac sym_block segs fuel dirs rds ps pvals rvals R H :=
  sym_pc_Z;
  lazymatch goal with
  | |- context [ mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom ] =>
    let k := list_len pvals in
    let ss0 := constr:(SS pc (sr_pins ps sr_id) (@nil sentry) (32 + k)%nat) in
    let EE := constr:(Eplus regs (pvals ++ rvals)) in
    let ss1 := eval vm_compute in (fst (sym_exec segs fuel dirs rds ss0 [])) in
    let scs := eval vm_compute in (snd (sym_exec segs fuel dirs rds ss0 [])) in
    let Hsc := fresh "Hsc" in
    let Hst := fresh "Hst" in
    let Hms := fresh "Hms" in
    let Heq := fresh "Heq" in
    let Hlf := fresh "Hlf" in
    let msx := fresh "msx" in
    assert (Hsc : scs_denot segs mem EE scs);
    [ unfold scs_denot;
      repeat first [ apply Forall_nil | apply Forall_cons ];
      cbv beta iota delta [sc_denot sc_flat adenot bdenot a_base a_off];
      try sym_norm; try sym_sc_auto
    | assert (Hst : st_ok EE mem rom ss0 (mkst regs (Z_to_bv 64 pc) mem rom));
      [ exists regs; split;
        [ reflexivity
        | split; [ apply regs_ok_pins; [ apply regs_ok_Eplus | ] | exact I ] ];
        unfold pins_ok;
        repeat first [ apply Forall_nil | apply Forall_cons ];
        cbn [fst snd edenot]; sym_env_norm; try sym_pin_auto
      | destruct (sym_exec_sound segs fuel dirs rds ss0 [] ss1 scs EE mem rom _
                    ltac:(vm_compute; reflexivity) Hsc Hst)
          as (msx & Hms & (R & Heq & H & Hlf));
        clear Hsc Hst;
        chain_mst; [ exact Hms | ];
        rewrite Heq; clear Heq Hms msx;
        cbn [s_pc s_log]; try sym_mem_norm;
        norm_pc; sym_pc_lit ] ]
  end.

Section WithFP20.
Context {fx : FPState}.

(* ######################################################################### *)
(* 6. [sym_block_ex] — the FACTORABLE variant                                *)
(* ######################################################################### *)

(** [sym_block] ends by [destruct]ing the executor's conclusion INTO THE
    GOAL IT IS STANDING IN: the exit register file becomes a goal-local
    variable and the block's [msteps] is immediately spent by
    [chain_mst].  That is right for a straight line kept in one goal,
    and wrong for anything one wants to prove ONCE and reuse — a
    per-iteration loop-body lemma

      Lemma body : <pre> ->
        exists R, <facts about R> /\ msteps segs ms (mkst R pc' mem' rom)

    cannot be closed with [sym_block] at all, because instantiating the
    existential with the tactic's local [R] takes it out of scope.
    ([DrainAlg]'s [Hread] hypothesis and a Hoare loop rule both ask for
    exactly that statement; the pre-[sym_block] [stepiv] style could
    express it only because its exit register file was a concrete
    [regupd] chain — see [mmap_upper_ns_source.source_to_mmap].)

    [sym_block_ex] moves the [destruct] OUT of the tactic: it runs the
    same executor over the same block and leaves

      R   : bvmap 5 word              the exit register file
      H   : regs_ok E sr_exit R       every exit register, symbolically
      Hms : msteps segs ms (mkst R (Z_to_bv 64 pc') mem' rom)

    in the CONTEXT, and does not touch the goal.  The caller then
    supplies [R] as their own existential's witness and reads whatever
    facts their statement promises out of [H] with [sym_regs] — the
    same reader [sym_block]'s callers already use.  Both routes go
    through the same [sym_exec_sound]; only the packaging differs.

    ARGUMENTS.  As [sym_block], plus:

    - [ms]  — the block's ENTRY machine state, given EXPLICITLY rather
      than found in the goal (there is no chain goal to find it in, and
      in a factored statement the exit state also matches the [mkst]
      pattern).  It must be spelled [mkst regs (Z_to_bv 64 pc) mem rom];
      that is the spelling [sym_pc_Z] produces at a call site and the
      one to write in a factored lemma's statement.
    - [Hms] — the name to bind the block's [msteps] to.

    THE EXIT MEMORY.  [Hms]'s target memory is the log's denotation,
    reduced by [cbn]: for a block with no stores (the common case for a
    loop body that only computes) that is literally the entry [mem],
    and for a block with stores it is the [wbytes] chain the log
    denotes, which is what the factored statement should say.  Unlike
    [sym_block] this is NOT put through [sym_mem_norm] — normalizing a
    hypothesis and normalizing a goal are different tactics, and the
    caller's own statement fixes the spelling anyway. *)
End WithFP20.
Ltac sym_block_ex segs ms fuel dirs rds ps pvals rvals R H Hms :=
  lazymatch ms with
  | mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom =>
    let k := list_len pvals in
    let ss0 := constr:(SS pc (sr_pins ps sr_id) (@nil sentry) (32 + k)%nat) in
    let EE := constr:(Eplus regs (pvals ++ rvals)) in
    let ss1 := eval vm_compute in (fst (sym_exec segs fuel dirs rds ss0 [])) in
    let scs := eval vm_compute in (snd (sym_exec segs fuel dirs rds ss0 [])) in
    let Hsc := fresh "Hsc" in
    let Hst := fresh "Hst" in
    assert (Hsc : scs_denot segs mem EE scs);
    [ unfold scs_denot;
      repeat first [ apply Forall_nil | apply Forall_cons ];
      cbv beta iota delta [sc_denot sc_flat adenot bdenot a_base a_off];
      try sym_norm; try sym_sc_auto
    | assert (Hst : st_ok EE mem rom ss0 ms);
      [ exists regs; split;
        [ reflexivity
        | split; [ apply regs_ok_pins; [ apply regs_ok_Eplus | ] | exact I ] ];
        unfold pins_ok;
        repeat first [ apply Forall_nil | apply Forall_cons ];
        cbn [fst snd edenot]; sym_env_norm; try sym_pin_auto
      | destruct (sym_exec_ex segs fuel dirs rds ss0 [] ss1 scs EE mem rom _
                    ltac:(vm_compute; reflexivity) Hsc Hst)
          as (R & H & Hms);
        clear Hsc Hst;
        cbn [s_pc s_regs s_log mem_denot] in Hms ] ]
  end.

Section WithFP21.
Context {fx : FPState}.

(* ######################################################################### *)
(* 7. Consuming a factored block                                             *)
(* ######################################################################### *)

(** Attach a factored block's [msteps] to the chain goal at the call
    site.  This is the other half of moving the [destruct] outwards:
    [sym_block] did [chain_mst; [exact Hms|]; norm_pc] itself, and a
    caller who got their [msteps] from a LEMMA instead does it here.

    [sym_pc_Z] first because the chain goal's pc is a numeral literal
    and a factored statement's is [Z_to_bv 64 _] (they are
    propositionally but not definitionally equal), then [norm_pc] /
    [sym_pc_lit] to put the pc back into the literal form the next
    fetch lemma wants.

    So the whole call is two lines:

      destruct (block_lemma …) as (R & Hfacts & Hms). sym_chain Hms.

    and the block's results are read out of [Hfacts] — directly if the
    factored statement promised [getr R r = v] facts (the usual
    choice), or with [sym_regs Hfacts] if it exported the whole
    [regs_ok] against a [vm_compute]d [s_regs] literal, which is the
    same reader a [sym_block] call site uses. *)
End WithFP21.
Ltac sym_chain Hms :=
  sym_pc_Z; chain_mst; [ exact Hms | ]; norm_pc; sym_pc_lit.
