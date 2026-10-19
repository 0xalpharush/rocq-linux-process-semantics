(** * LinuxProcessSem.Sys.Fs.EventFd — eventfd2 (19)

    This file answers to Linux [fs/eventfd.c]: it holds what the kernel
    defines there, and nothing else.  Which file a spec belongs in is
    therefore not a judgement call — look up where the kernel defines
    the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(** WHICH KERNEL THIS IS A MODEL OF.

    Cited by function name.  Every body quoted below was read from the
    pinned tree itself — stable v6.18.46, commit
    1f99e9ab748fc5c32120de9c4eca31abfe54a4d5, this repository's kernel
    of record.  The tags named in the windows WERE fetched, and only to
    bound them: every text that is CITED is the pinned commit's.

      fs/eventfd.c                [do_eventfd],
                                  [SYSCALL_DEFINE2(eventfd2, ...)],
                                  [SYSCALL_DEFINE1(eventfd, ...)],
                                  [eventfd_fops]
      include/linux/eventfd.h     [EFD_SHARED_FCNTL_FLAGS],
                                  [EFD_FLAGS_SET]
      include/uapi/linux/eventfd.h
                                  [EFD_SEMAPHORE], [EFD_CLOEXEC],
                                  [EFD_NONBLOCK]
      fs/file.c                   [get_unused_fd_flags],
                                  [__get_unused_fd_flags], [alloc_fd],
                                  [expand_files]
      fs/anon_inodes.c            [anon_inode_getfile_fmode],
                                  [__anon_inode_getfile]
      init/Kconfig                [config EVENTFD]
      kernel/sys_ni.c             [COND_SYSCALL(eventfd2)]
      include/uapi/asm-generic/unistd.h
                                  [__NR_eventfd2]

    WINDOWS, per function, ending at the pinned commit.  Each was read
    by fetching the file at the tag and comparing the function's own
    text; the bound given is the earliest tag that matches AND whose
    successors all match, so a later regression cannot hide inside one.

      v6.15 - v6.18.46      [do_eventfd], byte-for-byte.  v6.12 differs,
                            and only past the gate this file models:
                            it calls [anon_inode_getfile] and then sets
                            [FMODE_NOWAIT] by hand where the pinned text
                            calls [anon_inode_getfile_fmode].  Both of
                            those sit below the [return -EINVAL], so the
                            difference is invisible to every answer here
                            — but the TEXT is not identical, and this
                            repository pins text.
      at least v5.10        [SYSCALL_DEFINE2(eventfd2, ...)] and
                            [SYSCALL_DEFINE1(eventfd, ...)], and the
                            gate itself: [if (flags & ~EFD_FLAGS_SET)
                            return -EINVAL;] is the same statement in
                            the same place in every tag fetched down to
                            v5.10.
      at least v5.10        [EFD_SHARED_FCNTL_FLAGS] and
                            [EFD_FLAGS_SET] in include/linux/eventfd.h,
                            and [EFD_SEMAPHORE] at [(1 << 0)] — the
                            latter in include/linux/eventfd.h through
                            v6.1 and in include/uapi/linux/eventfd.h
                            from at least v6.6.  Same value either side
                            of that move; see [Uapi.EFD_SEMAPHORE].

    "AT LEAST" IS NOT "UNCHANGED SINCE".  v5.10 is the floor of the
    probe set, not an established boundary: the texts are identical at
    every tag fetched down to it and may well go back further; nobody
    looked.  A reader who needs a real lower bound has to fetch it, and
    this sentence is what tells them the number here will not answer the
    question.

    ON riscv64 THERE IS NO [eventfd], ONLY [eventfd2].  The generic
    64-bit syscall table carries [__NR_eventfd2 19] and no [__NR_eventfd]
    at all (include/uapi/asm-generic/unistd.h), so
    [SYSCALL_DEFINE1(eventfd, unsigned int, count)] — which is
    [do_eventfd(count, 0)] — is unreachable here.  It is named in the
    citation list anyway because it is the OTHER caller of the function
    this file models, and a reader checking that [do_eventfd]'s gate is
    the whole of the argument rejection needs to see both callers to
    know that neither adds a check of its own.  Neither does: each is a
    one-line forward.

    THIS ARM MODELS THE ARGUMENT REJECTION AND NOTHING ELSE, exactly as
    [Fs.Timerfd] does, and for the same reason: every input that
    survives the gate CREATES A FILE DESCRIPTOR, and this model has no
    descriptor kind to put an eventfd counter behind — none of
    [State.FdEntry]'s constructors is an eventfd.  Adding one is not a
    local change: every [FdEntry] match in the tree is exhaustive on
    purpose, so the read, write, stat, sync, ioctl, select, epoll and
    socket specs, their acceptors, their witnesses and the example
    proofs would each have to decide the new case.

    WHAT THAT COSTS is priority 3 and nothing else: a program that
    successfully creates an eventfd leaves the modeled surface at the
    [eventfd2] itself, so [Equivalence.strong_universal] is vacuous over
    it rather than wrong about it.  Source and target are judged against
    the same model, so no pair of programs is separated by this.  The
    condition that would let this arm grow a success is a single one,
    and it is worth writing down because it is one step to check rather
    than an argument to re-derive: a descriptor kind in [State.FdEntry]
    carrying the 64-bit counter and the [EFD_SEMAPHORE] bit, which is
    also what a [read] or a [write] on an eventfd needs, and what
    [Fs.EventPoll] would need before [epoll_ctl] could record interest
    in one.

    THE GATE IS ONE [if], AND IT IS THE FIRST THING [do_eventfd] DOES
    that can fail.  Linux writes

      static int do_eventfd(unsigned int count, int flags)
      {
              ...
              /* Check the EFD_* constants for consistency.  */
              BUILD_BUG_ON(EFD_CLOEXEC != O_CLOEXEC);
              BUILD_BUG_ON(EFD_NONBLOCK != O_NONBLOCK);
              BUILD_BUG_ON(EFD_SEMAPHORE != (1 << 0));

              if (flags & ~EFD_FLAGS_SET)
                      return -EINVAL;

              ctx = kmalloc(sizeof( *ctx ), GFP_KERNEL);

    (the quoted [sizeof] is written with a space after its parenthesis
    because [(] followed by [*] opens a nested Rocq comment; the kernel
    text has no space there).

    (Linux v6.18.46, fs/eventfd.c, [do_eventfd]).  The three
    [BUILD_BUG_ON]s are compile-time assertions and cost the call
    nothing at run time, so the [if] is the first statement with a
    verdict.  ORDER IS BEHAVIOR here in the strongest possible sense:
    the flag word is judged BEFORE the [kmalloc] and before any
    descriptor is reserved, so a rejected [eventfd2] allocates nothing,
    consumes no fd number, and cannot answer -ENOMEM or -EMFILE — those
    two are unreachable on this path rather than merely unmodeled.

    [count] IS NOT READ BY ANY MODELED PATH.  It is the initial value of
    the counter and is stored by [ctx->count = count], which sits below
    the gate; nothing above the gate looks at it.  So no arm below takes
    it as an argument, and [eventfd2(count, flags)] answers -EINVAL for
    EVERY [count] when [flags] is refused — including counts a reader
    might expect to be rejected, such as [(unsigned int)-1].  There is
    no [count] the kernel refuses: the type is [unsigned int], so the
    64-bit register's high half is discarded and every remaining value
    is a legal initial counter.

    THE FLAG WORD ARRIVES ALREADY TRUNCATED TO 32 BITS, and that is
    load-bearing rather than incidental.  [flags] is declared [int] in
    [SYSCALL_DEFINE2(eventfd2, unsigned int, count, int, flags)], and
    riscv64's wrapper narrows it at the boundary: [__SYSCALL_DEFINEx]
    calls [__do_sys##name] through [__SC_CAST], which is [(__force t) a]
    (Linux v6.18.46, arch/riscv/include/asm/syscall_wrapper.h and
    include/linux/syscalls.h), while [SC_RISCV_REGS_TO_ARGS] hands over
    the registers full-width.  So the high half of the register is
    DISCARDED before the mask is applied, and [eventfd2(0, 2^32)] is
    [eventfd2(0, 0)] — which Linux answers with a descriptor, not with
    the -EINVAL a full-register test would give.  [Sys.SyscallTable]
    applies [flag32] at the arm, which is where the kernel does it and
    where [timerfd_create]'s and [epoll_create1]'s flag words are
    already narrowed; this spec receives the word narrowed and must not
    narrow it again.

    THE TEST IS A TRUTHINESS TEST, not a sign test, and that is what
    makes [Z.ldiff] the faithful spelling.  [flags & ~EFD_FLAGS_SET] is
    used directly as the [if] condition, so a residue of 0x80000000 —
    negative as an [int] — takes the -EINVAL just as 1 does.  An
    implementation that compared the residue against 0 with [>] rather
    than [<>] would admit [flags = 1 << 31]; this one does not.
    [Fs.Timerfd] carries the identical argument for the identical
    reason.

    WHAT THE DECLINE COVERS, walked from the source so the gap is a
    named list rather than "the rest": -ENOMEM from the [kmalloc] of the
    [eventfd_ctx]; -EMFILE from [get_unused_fd_flags]; -ENOENT or
    -ENODEV from [anon_inode_getfile_fmode]; and the success, which is
    the descriptor number.

    NO -EINVAL IS REACHABLE ON ANY OF THEM, which is what makes this a
    decline that loses coverage WITHOUT losing precision: the errno the
    arm commits to is exactly the errno Linux commits to, and there is
    no input where the model answers -EINVAL and Linux answers something
    else.  The claim is checkable rather than rhetorical — these are the
    returns of the functions [do_eventfd] reaches after the gate, each
    read at v6.18.46:

    - [do_eventfd] itself (fs/eventfd.c) has exactly one
      [return -EINVAL] in its body, the gate's;
    - [get_unused_fd_flags] (fs/file.c) forwards
      [__get_unused_fd_flags] to [alloc_fd], whose only errno is
      -EMFILE, and [expand_files] beneath it carries -EMFILE too;
    - [__anon_inode_getfile] (fs/anon_inodes.c), under
      [anon_inode_getfile_fmode], yields -ENOENT when the fops' module
      cannot be pinned and -ENODEV when the shared anon inode is an
      error pointer, and otherwise forwards [alloc_file_pseudo], which
      is an allocation failure;
    - [ida_alloc] cannot contribute one, because [do_eventfd] does not
      TEST its result: it writes [ctx->id = ida_alloc(...)] and reads on.

    That is the walk, not a claim about the whole tree: a caller
    reaching [do_eventfd] through some path not enumerated here is
    outside what was checked.

    CONFIG_EVENTFD IS ASSUMED ON.  fs/Makefile builds eventfd.c under
    [obj-$(CONFIG_EVENTFD)] and kernel/sys_ni.c carries
    [COND_SYSCALL(eventfd2)], so a kernel built without it answers
    -ENOSYS to every input this arm calls -EINVAL.  init/Kconfig gives
    [config EVENTFD] a [default y] and hides its prompt behind EXPERT.
    It is the same class of assumption every arm whose syscall carries a
    [COND_SYSCALL] makes — kernel/sys_ni.c has one for [timerfd_create]
    and one for [socket] too — and it is stated here rather than tested
    because no syscall argument distinguishes the two builds.  It is the
    ONE premise outside this call's own arguments that the -EINVAL rests
    on. *)

(** The flag mask [eventfd2] admits, written out of the kernel's own
    [if].  RESTATED rather than shared with the acceptor and the
    witness, and deliberately so: this predicate decides WHICH ARM RUNS,
    and a gate the three layers imported from one definition would agree
    with itself however wrong it was.  The soundness and completeness
    lemmas are what force the three statements to coincide, which is the
    same reason [Fs.Timerfd] and [Kernel.Time.PosixTimers] restate their
    envelope bounds in each layer instead of sharing them. *)
Definition eventfd2_einval_b (flags : word) : bool :=
  negb (Z.eqb (Z.ldiff (bv_unsigned flags) EFD_FLAGS_SET) 0).

(** [eventfd2 count flags]: create a descriptor holding a 64-bit counter.

    No [get_model] and no [count]: the answer is a function of the flag
    word alone.  The -EINVAL arm touches no memory, emits no event and
    changes no state, which is what the kernel does on that path too —
    it returns before the [kmalloc]. *)
Definition eventfd2_spec (flags : word) : Sys SyscallEffect :=
  if eventfd2_einval_b flags
  then err_ret EINVAL      (* real -EINVAL, decided before anything is allocated *)
  else unmodeled.          (* ENOMEM / EMFILE / ENOENT / ENODEV / the descriptor: fail closed *)
