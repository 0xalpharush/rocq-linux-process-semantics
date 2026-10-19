(* Written by the OSS-Fuzz proof collaborators. *)
(** * WalkTac — thin helpers on top of [StepTac] for walking concrete code
      with the generated [*_code.v] fetch/decode facts.

    - [gres]        peel [getr] through a [regupd] chain (SeqExec.getr_resolve
                    minus its final [getr_nz] respelling).  = MuslCall.gres.
    - [vals_lit]    fold every CLOSED register value in the goal's [regupd]
                    chain(s) to its [Z_to_bv 64 z] literal (vm-computed,
                    closedness-guarded, skips values already literal).
    - [vnorm]       the after-step normalizer: [gres; imm_norm;
                    rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; vals_lit].  Keeps the symbolic state
                    SMALL — without it every register read re-embeds the
                    earlier [regupd] chain and the state doubles per step.
    - [stepn F D]   one ALU instruction ([stepi]) or [jal] ([stepj]) + [vnorm].
    - [stepb_tk F D tac] / [stepb_ft F D tac]
                    one conditional branch, taken / not taken; [tac] closes
                    the condition fact ([c_eq ..]/[c_lts ..]/[c_ltu ..] =
                    true/false) AFTER [gres] has resolved its registers.
    - [stepret F D k tac]
                    [ret]/[jr] through [stepjr] to target [k]; [tac] proves
                    [getr regs rs1 = k] after [gres].  If [k] is a literal
                    the pc is re-literalized; if [k] is a variable with
                    [Hk : ret_ok k] in context, the pc becomes [k]. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare.
Import ListNotations.
Open Scope bv_scope.

Ltac gres :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero.

(** [add rd, rs, x] with a zero operand (e.g. [add a2,s4,a2] after
    [mv a2,zero-valued s0]). *)
Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
  intro x. unfold v_add. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  rewrite Z.add_0_l. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(** Is [z] a Z numeral (Z0 / Zpos p / Zneg p with p built from xI/xO/xH)? *)
Ltac is_pos_lit p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => is_pos_lit q
  | xI ?q => is_pos_lit q
  end.
Ltac is_Z_lit z :=
  lazymatch z with
  | Z0 => idtac
  | Zpos ?p => is_pos_lit p
  | Zneg ?p => is_pos_lit p
  end.

(** Fold one closed, not-yet-literal word term to [Z_to_bv 64 z]. *)
Ltac val_lit v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
  | @BV _ _ _ => fail
  | _ => wlit_closed v
  end.

(** Fold every closed register value sitting in a [regupd] chain. *)
Ltac vals_lit :=
  repeat match goal with
         | |- context [regupd _ _ ?v] => val_lit v
         end.

Ltac vnorm := gres; imm_norm; rewrite ?v_addi_0, ?v_add_0_r, ?v_add_0_l; vals_lit.

(** ALU step or jump, then normalize. *)
Ltac stepn F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.

(** ALU step with the written value stated by the caller (StepTac.stepiv)
    and the standard value closer. *)
Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.

(** Conditional branches. *)
Ltac stepb_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

Ltac stepb_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

(** Close a CLOSED boolean condition ([c_xx lit lit = b]) by computation.
    (The leading [idtac;] matters: it makes the body a sequence, so that
    passing [ltac:(cond_compute)] as a tactic argument does not evaluate
    the [lazymatch] eagerly at the call site -- the classic Ltac trap.) *)
Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.

(** Branch on two CLOSED (literal) register values: the condition
    computes, and so does the direction. *)
Ltac stepb F D :=
  first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

(** [ret] / [jr rs]: jump through a register to [k]. *)
Ltac stepret F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).

(** Store-double with SYMBOLIC operands.  Unlike StepTac's [stepw], the
    address/value side goals are normalized with [gres] (not
    [getr_resolve], whose final [getr_nz] respells [getr regs r] as
    [reg_get regs r] and so disconnects the goal from the walker's
    [getr regs r = v] hypotheses); they are then closed by reflexivity /
    assumption / [f_equal; lia] / [bveq].  [aa]/[vv]: the intended address
    and value; [oktac] closes [store_ok]. *)
Ltac stepsd F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac ]
  | step_simpl ].

(** Load-double of a value [vv] whose 8 bytes [word_to_le_bytes 8 vv] the
    tactic [rtac] reads back ([rtac] proves [rdn segs mem ADDR 8 = Some
    (word_to_le_bytes 8 vv)] after the address has been normalized). *)
Ltac stepld F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm ].
