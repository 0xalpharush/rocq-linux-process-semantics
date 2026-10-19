# Scope, assumptions and known gaps

Read this document before you use a proof as evidence about a real program.
It tells you which systems the model describes, where the model is narrower
than those systems, which assumptions it does not check, and where it is
less precise than those systems. The design priorities in
[README.md](README.md#design-priorities) refer to this document.

## Supported systems

- Stable Linux v6.18.46 (commit `1f99e9ab748fc5c32120de9c4eca31abfe54a4d5`),
  on riscv64.
- QEMU user mode for riscv64.
- For instructions: the RISC-V specification (RV64GC).

Bugs in Linux or QEMU do not count.

Other stable kernels (v4.17 and later) are a goal. They are not supported
now. The model does not check claims about them.

## Where the model is narrower

The statements restrict these cases, or the model says `unmodeled` for
them. A proof says nothing about a program in such a case.

| Area | Limit |
| --- | --- |
| Threads | The model has one thread. It has no scheduler and no shared-memory interleaving. For `fork`-like calls, the model describes the parent only. It does not run the child. |
| Signals | The model does not run signal handlers. |
| Address-space size | The system call specifications use Sv48. Thus you cannot prove the Sv39 and Sv57 statements for an image that can run. |
| Stack limit | The stack limit is 8 MiB. A larger or unlimited `RLIMIT_STACK`, which selects the legacy mmap layout, is outside the model. |
| Arguments | `Run.valid_input` requires that the arguments after `argv[0]` do not contain `/` and are not `..`. Thus a proof about `cp src dst` does not apply to `cp /tmp/src dst`. |
| Network | The list of connections is never empty. Thus the model does not include an environment where no peer ever connects. |
| Memory budgets | The source can allocate 16 GiB and the target 512 GiB (`State.source_alloc_limit`, `State.target_alloc_limit`). The `*_budgets` statements change this premise. |
| Files | The file model has no full directory tree, no symbolic links, no device files except `/dev/null` and `/dev/urandom`, and no permissions. |

## Assumptions that the model does not check

If one of these assumptions is false, a proof can be correct but it does
not apply.

- No other process, also not a child of the program, changes the modeled
  files or holds locks on them.
- `/dev/null` is the null device (major 1, minor 3). `/dev/urandom` is the
  random device (major 1, minor 9).
- No tracer (`ptrace`) or other outside agent changes the process.
- The binary is a static executable (`ET_EXEC`). `elf-snapshot` does not
  check this. For a static PIE, the model can give a wrong initial program
  break.

## Known gaps in precision

Design priority 2 asks that the model include no behavior that no supported
system gives. The model does not meet it in these cases. In each case, a
statement that compares sets of behaviors (for example, equivalence) can be
true of the model and false of the real systems.

- **No parameter for the system.** The model does not choose between Linux
  and QEMU user mode, or between Linux configurations (for example, the two
  mmap layouts). Where they differ, the model lets each system call choose
  again. A real system makes the choice the same way each time. Also, the
  source and the target can make different choices, as if they ran on
  different systems.
- **mmap placement.** A mapping without an address hint can go to any free,
  page-aligned address below `State.alloc_top`. This is wider than the
  placement policy of each supported system.
- **Random bytes.** The bytes of `/dev/urandom` are an input
  (`State.ProcInput.in_urandom`): the source and the target see the same
  stream. The bytes of `getrandom` are a free choice at each call: the source
  and the target choose them independently. Thus "equivalent" means a
  different thing for each API. Two programs that print the same random
  bytes in a different order are equivalent if both use `getrandom`, but not
  if both use `/dev/urandom`. A program that uses `/dev/urandom` and one
  that uses `getrandom` for the same work cannot be proved equivalent.

## What the proofs do not check

- The executable checker of each system call is proved to agree with its
  specification. This does not show that the specification agrees with
  Linux. An error in both gives a correct proof of the wrong thing.
- Comments that state kernel behavior name the file and the function in
  Linux v6.18.46. No tool checks that these comments are correct.
