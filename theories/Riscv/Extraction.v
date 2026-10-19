(** * Riscv.Extraction — extract the RV64GC ISA model to OCaml

    Produces [riscv_model.ml] (+ [.mli]), for a differential tester
    that checks this model against independent reference
    implementations of the ISA (a disassembler for the decoder; the
    Sail RISC-V model for execution).

    Not part of the batch build, because compiling it writes a .ml file
    as a side effect: theories/dune names it explicitly in
    [(modules :standard \ Riscv.Extraction LinuxProcessSem.Checks.Extraction)],
    so that list is what must be updated if this file is moved or
    renamed.

    Representation notes for the OCaml side:

    - [N]/[Z]/[positive] are realized with zarith's [Big_int_Z], so the
      OCaml caller can build operands from parsed integers cheaply.
    - [bv n] is a record whose only computational field is the unsigned
      [Z] (the [BvWf] proof is erased), so a bitvector extracts to a
      bare [Big_int_Z.big_int] and the WIDTH IS ERASED.  The OCaml
      caller must therefore mask values itself when constructing inputs, and
      must recover each immediate's width from the [instr] constructor
      rather than from the runtime value.  Widths the model carries
      explicitly ([ELoad]/[EStore]'s [n], [exec]'s size argument, the
      [Z] in [decode_any]'s result) survive extraction and are readable.
    - [eff]'s [ELoad] continuation extracts to an OCaml closure, so the
      OCaml caller answers loads on demand out of its own memory. *)

From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlZBigInt.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.

Require Extraction.

(* Roots: the two decoders and the compressed expander, plus the
   execution semantics and its core-state plumbing. *)
Extraction "riscv_model.ml"
  decode
  decode16
  expand_c
  decode_any
  is_defined_illegal
  exec
  step
  msize_bytes.
