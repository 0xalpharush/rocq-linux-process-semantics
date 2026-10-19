(** * Instr: the RV64GC base instruction AST.

    Design rules:
    - Immediates are kept at their *encoded* width with the sign bit
      included (I/S: 12 bits, B: 13, U: 20, J: 21); interpretation
      (sign-extension, shifting) is deferred to the semantics.
    - Compressed instructions have their own AST in [DecodeC] and are
      expanded into this AST, so the execution semantics is written once. *)

From LinuxProcessSemantics.Riscv Require Import Prelude.

(** Integer register-register ops (OP / OP-32 major opcodes). *)
Inductive aluop : Type :=
| ALU_ADD | ALU_SUB | ALU_SLL | ALU_SLT | ALU_SLTU
| ALU_XOR | ALU_SRL | ALU_SRA | ALU_OR | ALU_AND.

(** M extension ops. *)
Inductive mulop : Type :=
| M_MUL | M_MULH | M_MULHSU | M_MULHU
| M_DIV | M_DIVU | M_REM | M_REMU.

Inductive branch_cond : Type :=
| BC_EQ | BC_NE | BC_LT | BC_GE | BC_LTU | BC_GEU.

(** Memory access sizes, in bytes. *)
Inductive msize : Type := SZ1 | SZ2 | SZ4 | SZ8.

(** A extension. *)
Inductive amoop : Type :=
| AMO_SWAP | AMO_ADD | AMO_XOR | AMO_AND | AMO_OR
| AMO_MIN | AMO_MAX | AMO_MINU | AMO_MAXU.

Inductive awidth : Type := AW | AD.  (** .w / .d *)

(** Zicsr. *)
Inductive csrop : Type := CSR_RW | CSR_RS | CSR_RC.

(** F/D formats and op groups. *)
Inductive ffmt : Type := FMT_S | FMT_D.

Inductive fariop : Type := F_ADD | F_SUB | F_MUL | F_DIV.
Inductive fmaop : Type := F_MADD | F_MSUB | F_NMSUB | F_NMADD.
Inductive fsgnop : Type := F_SGNJ | F_SGNJN | F_SGNJX.
Inductive fminmaxop : Type := F_MIN | F_MAX.
Inductive fcmpop : Type := F_EQ | F_LT | F_LE.

(** Operand kind of an [Fcvt]: integer (32/64, signed/unsigned) or FP
    format.  Decoding only produces the architecturally valid pairs. *)
Inductive fcvt_ty : Type :=
| FC_W | FC_WU | FC_L | FC_LU  (** integer targets/sources *)
| FC_S | FC_D.                 (** FP formats *)

(** fmv.x.w / fmv.w.x / fmv.x.d / fmv.d.x: direction of the raw move. *)
Inductive fmvdir : Type := FMV_X_F | FMV_F_X.

Inductive instr : Type :=
(* RV32I / RV64I *)
| Lui (rd : reg) (imm : bv 20)
| Auipc (rd : reg) (imm : bv 20)
| Jal (rd : reg) (imm : bv 21)               (* bit 0 of imm is always 0 *)
| Jalr (rd rs1 : reg) (imm : bv 12)
| Branch (c : branch_cond) (rs1 rs2 : reg) (imm : bv 13)  (* bit 0 always 0 *)
| Load (sz : msize) (signed : bool) (rd rs1 : reg) (imm : bv 12)
| Store (sz : msize) (rs1 rs2 : reg) (imm : bv 12)  (* mem[rs1+imm] <- rs2 *)
| OpImm (op : aluop) (rd rs1 : reg) (imm : bv 12)
    (* addi/slti/sltiu/xori/ori/andi; never SUB/shift *)
| ShiftImm (op : aluop) (rd rs1 : reg) (shamt : bv 6)   (* slli/srli/srai *)
| Op (op : aluop) (rd rs1 rs2 : reg)
| OpImm32 (rd rs1 : reg) (imm : bv 12)                  (* addiw *)
| ShiftImm32 (op : aluop) (rd rs1 : reg) (shamt : bv 5) (* slliw/srliw/sraiw *)
| Op32 (op : aluop) (rd rs1 rs2 : reg)  (* addw/subw/sllw/srlw/sraw *)
| Fence (fm : bv 4) (pred succ : bv 4) (rd rs1 : reg)
| FenceI (rd rs1 : reg) (imm : bv 12)
| Ecall
| Ebreak
(* M *)
| Mul (op : mulop) (rd rs1 rs2 : reg)
| Mul32 (op : mulop) (rd rs1 rs2 : reg)  (* mulw/divw/divuw/remw/remuw *)
(* A *)
| Lr (w : awidth) (aq rl : bool) (rd rs1 : reg)
| Sc (w : awidth) (aq rl : bool) (rd rs1 rs2 : reg)
| Amo (op : amoop) (w : awidth) (aq rl : bool) (rd rs1 rs2 : reg)
(* Zicsr *)
| Csr (op : csrop) (rd rs1 : reg) (csr : bv 12)
| CsrI (op : csrop) (rd : reg) (uimm : bv 5) (csr : bv 12)
(* F/D loads/stores (rd/rs2 name FP registers) *)
| FLoad (fmt : ffmt) (rd rs1 : reg) (imm : bv 12)
| FStore (fmt : ffmt) (rs1 rs2 : reg) (imm : bv 12)
(* F/D computation *)
| Fma (op : fmaop) (fmt : ffmt) (rd rs1 rs2 rs3 : reg) (rm : bv 3)
| Fari (op : fariop) (fmt : ffmt) (rd rs1 rs2 : reg) (rm : bv 3)
| Fsqrt (fmt : ffmt) (rd rs1 : reg) (rm : bv 3)
| Fsgnj (op : fsgnop) (fmt : ffmt) (rd rs1 rs2 : reg)
| Fminmax (op : fminmaxop) (fmt : ffmt) (rd rs1 rs2 : reg)
| Fcmp (op : fcmpop) (fmt : ffmt) (rd rs1 rs2 : reg)
| Fcvt (dst src : fcvt_ty) (rd rs1 : reg) (rm : bv 3)
| Fmv (dir : fmvdir) (fmt : ffmt) (rd rs1 : reg)
| Fclass (fmt : ffmt) (rd rs1 : reg).

#[global] Instance aluop_eq_dec : EqDecision aluop.
Proof. solve_decision. Defined.
#[global] Instance mulop_eq_dec : EqDecision mulop.
Proof. solve_decision. Defined.
#[global] Instance branch_cond_eq_dec : EqDecision branch_cond.
Proof. solve_decision. Defined.
#[global] Instance msize_eq_dec : EqDecision msize.
Proof. solve_decision. Defined.
#[global] Instance amoop_eq_dec : EqDecision amoop.
Proof. solve_decision. Defined.
#[global] Instance awidth_eq_dec : EqDecision awidth.
Proof. solve_decision. Defined.
#[global] Instance csrop_eq_dec : EqDecision csrop.
Proof. solve_decision. Defined.
#[global] Instance ffmt_eq_dec : EqDecision ffmt.
Proof. solve_decision. Defined.
#[global] Instance fariop_eq_dec : EqDecision fariop.
Proof. solve_decision. Defined.
#[global] Instance fmaop_eq_dec : EqDecision fmaop.
Proof. solve_decision. Defined.
#[global] Instance fsgnop_eq_dec : EqDecision fsgnop.
Proof. solve_decision. Defined.
#[global] Instance fminmaxop_eq_dec : EqDecision fminmaxop.
Proof. solve_decision. Defined.
#[global] Instance fcmpop_eq_dec : EqDecision fcmpop.
Proof. solve_decision. Defined.
#[global] Instance fcvt_ty_eq_dec : EqDecision fcvt_ty.
Proof. solve_decision. Defined.
#[global] Instance fmvdir_eq_dec : EqDecision fmvdir.
Proof. solve_decision. Defined.
#[global] Instance instr_eq_dec : EqDecision instr.
Proof. solve_decision. Defined.

Definition msize_bytes (sz : msize) : Z :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.
