(** * LinuxProcessSem.Checks.Extraction — extract the verified checker to OCaml

    The page-rounding / grant-top roots are the [Z]-side
    helpers of the bitvector model
    ([page_round_up_Z]/[page_round_down_Z]; [two_pow_64],
    [sp_window_lo] and [mmap_base_max] are [Z] constants).  [bv]
    extracts to its unsigned
    [Z] value (the [BvWf] proof is erased).

    Not part of the batch build (it writes a .ml file as a side effect):
    theories/dune excludes it by name in
    [(modules :standard \ Riscv.Extraction LinuxProcessSem.Checks.Extraction)],
    so that list is what must be updated if this file is moved or renamed.
    Compile it by hand to write syscall_model.ml.

    The extracted artifact is [ExecutableSpecs.check_syscall_for_run].
    Its raw syscall acceptor is verified against the relational specs, then
    its successful post-model is charged for the effect's copy-in/copy-out
    ranges exactly as [Run.sstep_syscall] charges them.  A caller
    assembles a [SyscallInput] (registers plus captured pre-syscall
    memory as a lookup closure) and a [SyscallEffect] (observed return value
    plus the captured output buffers) for each real syscall and folds this
    accounted checker over the run.

    [N]/[Z]/[positive] are realized with zarith's [Big_int_Z] so OCaml
    can build argument/return values from parsed integers cheaply. *)

From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlZBigInt.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.

Require Extraction.

(* Roots: the checker, the initial state, input/effect constructors, the
   fd-table lookup (a caller needs it on the write, readv and writev
   paths, to decide which user memory a transfer touched; read's own
   capture is fd-blind and never asks the kind), error-encoding helpers, the iovec layout decoder that
   picks which guest ranges to capture (no spec reaches it,
   so it is not extracted transitively; see [State.read_iovecs] for why
   it is the validation-free one), the mmap argument-shape
   predicates and the mremap flag word,
   the futex predicate deciding whether a call read its word
   (a root rather than a transitively reached name, because the checker
   states that gate in its own order and never reaches this spelling; and
   a shared definition rather than a second copy in OCaml, with
   [Checks.Sys.Kernel.Futex.Syscalls.futex_copyins_exact] proving it
   describes the ledger every answered call carries), the effect components a caller would otherwise re-derive
   in OCaml ([brk_zeros], [brk_unmaps]) together with the two whole mremap
   effect records that hold all three mremap ledgers
   ([mremap_inplace_effect], [mremap_move_effect] -- [mremap_tail] itself is
   reached only through them, so it is not a root), the model
   projections, and [State.net_silent], the quiet [State.NetQueue]. *)
Extraction "syscall_model.ml"
  check_syscall_for_run
  init_model
  net_silent
  mkInput
  mkEffectU
  mkCopy
  fd_lookup
  fs_lookup
  addr_is_error_b
  errno_ret
  read_iovecs
  two_pow_64
  page_round_up_Z
  page_round_down_Z
  map_has
  mmap_modeled_b
  mmap_noaccess_b
  mmap_fixed_noaccess_b
  mmap_fixed_rw_b
  mmap_noreplace_noaccess_b
  mmap_noreplace_rw_b
  madvise_dontneed_b
  madvise_dontneed_ok
  int32
  futex_wait_reads_b
  FUTEX_WORD_SIZE
  MREMAP_MAYMOVE
  sp_window_lo
  mmap_base_min
  State.TASK_SIZE
  mmap_base_max
  brk_zeros
  brk_unmaps
  mremap_inplace_effect
  mremap_move_effect
  brk_aslr_max
  reserved_top
  m_fds
  m_halted
  m_killed
  m_vmmaps
  m_fs
  vm_brk
  vm_maps
  vm_noaccess
  vm_reserved.
