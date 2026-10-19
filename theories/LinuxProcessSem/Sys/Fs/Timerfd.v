(** * LinuxProcessSem.Sys.Fs.Timerfd — timerfd_create (85)

    This file answers to Linux [fs/timerfd.c]: it holds what the kernel
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

(** THIS ARM MODELS THE ARGUMENT REJECTION AND NOTHING ELSE.  Every
    input that survives it is declined.  The reason is that a surviving
    input CREATES A FILE DESCRIPTOR, and this model has no descriptor
    kind to put a timer behind: none of [State.FdEntry]'s constructors
    is a timerfd.  Adding one is not a local change —
    every [FdEntry] match in the tree is exhaustive on purpose, so the
    read, write, stat, sync, ioctl, select and socket specs, their
    acceptors, their witnesses and the example proofs would each have to
    decide the new case.

    What that costs is priority 3 and nothing else: a program that
    successfully creates a timerfd leaves the modeled surface at the
    [timerfd_create] itself, so [Equivalence.strong_universal] is
    vacuous over it rather than wrong about it.  The condition that
    would let this arm grow a success is a single one, and it is worth
    writing down because it is one step to check rather than an argument
    to re-derive: a descriptor kind for a timer in [State.FdEntry],
    which is what [timerfd_settime] (86) and [timerfd_gettime] (87) also
    wait on.

    So what is here is exact rather than approximate: the -EINVAL the
    kernel returns before it allocates anything, and a fail-closed
    decline for everything after.  The bound is named in place, the way
    [Open.openat_spec] names the -EMFILE it stops short of.

    THE GATE IS ONE [if], AND THAT IS BEHAVIOR.  Linux writes

      if ((flags & ~TFD_CREATE_FLAGS) ||
          (clockid != CLOCK_MONOTONIC && clockid != CLOCK_REALTIME &&
           clockid != CLOCK_REALTIME_ALARM && clockid != CLOCK_BOOTTIME &&
           clockid != CLOCK_BOOTTIME_ALARM))
        return -EINVAL;

    (Linux v6.18.46, fs/timerfd.c, [SYSCALL_DEFINE2(timerfd_create)]).
    The two halves are DISJUNCTS OF ONE CONDITION, not two sequential
    tests, so there is no ordering question between them and no
    "which errno wins" between them either — they win together.  Where
    the ordering does matter is against the NEXT test: the capability
    check for the alarm clocks sits in a separate [if] BELOW this one,
    so an unknown flag bit together with [CLOCK_REALTIME_ALARM] is
    -EINVAL and never -EPERM.  That is the one precedence fact this arm
    encodes.

    WHY THE ALARM CLOCKS ARE IN THE ADMITTED SET even though the model
    can never answer for them.  Dropping [CLOCK_REALTIME_ALARM] and
    [CLOCK_BOOTTIME_ALARM] from the membership test would be the
    tempting simplification — they need CAP_WAKE_ALARM, which this model
    has no notion of, so they are declined either way.  It would also be
    WRONG, and wrong in the direction that matters: [timerfd_create
    (CLOCK_REALTIME_ALARM, 0)] would then answer -EINVAL, an errno Linux
    does not produce for it.  Linux answers -EPERM without the
    capability and a descriptor with it, and both are outside the
    modeled surface.  A declined input costs coverage; a confidently
    wrong errno costs soundness, so the two ids are admitted here and
    declined below.

    WHAT THE DECLINE COVERS, walked from the source so the gap is a
    named list rather than "the rest": -EPERM from
    [capable(CAP_WAKE_ALARM)] on the two alarm ids; -ENOMEM from the
    [kzalloc] of the [timerfd_ctx]; -EMFILE from [get_unused_fd_flags];
    -ENOENT or -ENODEV from [anon_inode_getfile_fmode]; and the success,
    which is the descriptor number.

    NO -EINVAL IS REACHABLE ON ANY OF THEM, which is what makes this a
    decline that loses coverage WITHOUT losing precision: the errno the
    arm commits to is exactly the errno Linux commits to, and there is no
    input where the model answers -EINVAL and Linux answers something
    else.  The claim is worth its own paragraph because it is the one
    that justifies the arm's shape, and it is checkable rather than
    rhetorical — these are the returns of the functions [timerfd_create]
    reaches after the gate, each read at v6.18.46:

    - [timerfd_create] itself (fs/timerfd.c) has exactly one
      [return -EINVAL] in its body, the gate's;
    - [alloc_fd] (fs/file.c), under [get_unused_fd_flags], carries
      -EMFILE as its only errno, and [expand_files] beneath it the same;
    - [__anon_inode_getfile] (fs/anon_inodes.c) yields -ENOENT or
      -ENODEV, and [alloc_file_pseudo] (fs/file_table.c) forwards
      [alloc_path_pseudo] and [alloc_file], which are allocation
      failures.

    That is the walk, not a claim about the whole tree: a caller reaching
    [timerfd_create] through some path not enumerated here is outside
    what was checked.

    THE ARGUMENTS ARRIVE ALREADY TRUNCATED TO 32 BITS, and that is
    load-bearing rather than incidental.  Both parameters are declared
    [int] in the [SYSCALL_DEFINE2], and riscv64's wrapper narrows each
    at the boundary: [__SYSCALL_DEFINEx] calls [__do_sys##name] through
    [__SC_CAST], which is [(__force t) a] (Linux v6.18.46,
    arch/riscv/include/asm/syscall_wrapper.h and include/linux/syscalls.h),
    while [SC_RISCV_REGS_TO_ARGS] hands over the registers full-width.
    So the high half of either register is DISCARDED before any test
    runs, and [timerfd_create(2^32 + 1, 0)] is [timerfd_create(1, 0)] —
    which Linux answers with a descriptor, not with the -EINVAL a
    full-register comparison would give.  [Sys.SyscallTable] applies
    [clockid32] and [flag32] at the arm, which is where the kernel does
    it and where [clock_gettime]'s id is already narrowed; this spec
    receives both words narrowed and must not narrow them again.

    THE MEMBERSHIP TEST IS STATED OVER THE UNSIGNED LOW HALF while
    Linux compares a signed [int].  The two agree on every input, and
    the argument is not "small constants" hand-waving: each of the five
    targets is below 2^31, and for such a constant [c], a 32-bit pattern
    equals [c] as a signed [int] exactly when it equals [c] as an
    unsigned one.  Equality against a non-negative constant cannot
    separate the two readings.  (The sign question is real elsewhere —
    [clockid32]'s own comment records that the NEGATIVE id space reaches
    a live CPU-clock family [clock_gettime] partly succeeds on.  It does
    not arise here because this test is equality, not ordering, and
    because every negative id lands outside the admitted set and takes
    the -EINVAL Linux gives it.)

    THE FLAG TEST IS A TRUTHINESS TEST, not a sign test, and that is
    what makes [Z.ldiff] the faithful spelling.  [flags & ~TFD_CREATE_FLAGS]
    is used directly as the [if] condition, so a result of 0x80000000 —
    which is negative as an [int] — is nonzero and takes the -EINVAL
    just as 1 does.  An implementation that compared the residue against
    0 with [>] rather than [<>] would admit [flags = 1 << 31]; this one
    does not.

    CONFIG_TIMERFD IS ASSUMED ON.  fs/Makefile builds timerfd.c under
    [obj-$(CONFIG_TIMERFD)] and kernel/sys_ni.c carries
    [COND_SYSCALL(timerfd_create)], so a kernel built without it answers
    -ENOSYS to every input this arm calls -EINVAL.  init/Kconfig defaults
    it to y and hides the switch behind EXPERT.  It is the same class of
    assumption every arm whose syscall carries a [COND_SYSCALL] makes —
    kernel/sys_ni.c has one for [socket] too — and it is stated here
    rather than tested because no syscall argument distinguishes the two
    builds.  It is the ONE premise outside this call's own arguments that
    the -EINVAL rests on. *)

(** The five clock ids [timerfd_create] admits, written out of the
    kernel's own five-way comparison.  RESTATED rather than shared with
    the acceptor and the witness, and deliberately so: this predicate
    decides WHICH ARM RUNS, and a gate the three layers imported from
    one definition would agree with itself however wrong it was.  The
    soundness and completeness lemmas are what force the three
    statements to coincide, which is the same reason
    [Kernel.Time.PosixTimers] restates its envelope bound in each layer
    instead of sharing it. *)
Definition timerfd_create_einval_b (clkid flags : word) : bool :=
  orb (negb (Z.eqb (Z.ldiff (bv_unsigned flags) TFD_CREATE_FLAGS) 0))
      (negb (orb (Z.eqb (bv_unsigned clkid) CLOCK_REALTIME)
             (orb (Z.eqb (bv_unsigned clkid) CLOCK_MONOTONIC)
              (orb (Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME)
               (orb (Z.eqb (bv_unsigned clkid) CLOCK_REALTIME_ALARM)
                    (Z.eqb (bv_unsigned clkid) CLOCK_BOOTTIME_ALARM)))))).

(** [timerfd_create clockid flags]: create a descriptor bound to a clock.

    No [get_model]: the answer is a function of the two arguments alone.
    The -EINVAL arm touches no memory, emits no event and changes no
    state, which is what the kernel does on that path too — it returns
    before the [kzalloc]. *)
Definition timerfd_create_spec (clkid flags : word) : Sys SyscallEffect :=
  if timerfd_create_einval_b clkid flags
  then err_ret EINVAL      (* real -EINVAL, decided before anything is allocated *)
  else unmodeled.          (* EPERM / ENOMEM / EMFILE / the descriptor: fail closed *)
