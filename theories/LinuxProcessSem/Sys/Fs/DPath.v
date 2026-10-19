(** * LinuxProcessSem.Sys.Fs.DPath — getcwd (17)

    This file answers to Linux [fs/d_path.c]: it holds what the kernel
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

(** getcwd's injectable failures: the three answers that depend on
    kernel or file-system state this model does not carry, all of them
    decided BEFORE the size comparison and therefore live on every arm
    below.

    - ENOMEM — [__getname()], the very first statement, is a
      [GFP_KERNEL] allocation out of [names_cachep] and can fail.  It
      is the only error that returns without the RCU section running
      at all.
    - ENOENT — [d_unlinked(pwd.dentry)]: the caller's working directory
      has been removed from the dcache hash and is not its own root.
      Another process rmdir'ing the directory this one sits in produces
      it.  Note it is NOT the unreachable case: a working directory
      outside the caller's root is a SUCCESS returning a string prefixed
      "(unreachable)".
    - ENAMETOOLONG — the assembled path did not fit [PATH_MAX], which
      [prepend]/[prepend_char] signal by driving the buffer's [len] to
      -1.  Reachable by nesting directories with relative [mkdir]s until
      the absolute path exceeds 4096 bytes.

    (Linux v6.18.46, commit 1f99e9ab748f, fs/d_path.c,
    [SYSCALL_DEFINE2(getcwd)].)

    EFAULT is deliberately absent: it can only be reached AFTER the size
    comparison, which the modeled band below never gets past. *)
Definition getcwd_errnos : list Z := [ENOMEM; ENOENT; ENAMETOOLONG].

(** [getcwd buf size]: copy the caller's working directory out, and
    return its length INCLUDING the terminating NUL (not 0 — the comment
    above [SYSCALL_DEFINE2(getcwd)] states the convention, and line
    [error = len;] is where it happens).

    THERE IS NO WORKING DIRECTORY IN THIS MODEL, and that is a fact
    about the representation rather than a gap in the bookkeeping.
    [State.Model] has no pwd field; [Fs.Fs] is a flat association list
    from an UNINTERPRETED byte-string path to that file's bytes, with no
    root, no directories and no resolution; and every modeled path-taking
    syscall ([Fs.Open.openat_spec], [Fs.Stat.newfstatat_spec],
    [Fs.Namei.unlinkat_spec]) declines any dirfd but AT_FDCWD and then
    looks the name up in that map directly.  So the working directory is
    not an untracked value that could be threaded through later — there
    is no term in the model a directory could be, and the string getcwd
    would return is not a function of any modeled state.  Every outcome
    that would carry that string is therefore [unmodeled], fail closed.
    (This paragraph stops being true the moment [Fs] grows directories
    and [State.Model] a pwd field: at that point the success arm and the
    -EFAULT arm below it become derivable and the decline should go.)

    WHAT IS LEFT IS THE BAND WHERE THE WORKING DIRECTORY CANNOT MATTER.
    Call [len] the quantity the kernel compares against [size] and
    returns on success.  For [size <= 1], [len > size] holds for EVERY
    possible working directory, so no success and no -EFAULT is
    reachable and the answer is -ERANGE or one of the three injectable
    errnos above.  The argument, in the kernel's own order, reading
    [SYSCALL_DEFINE2(getcwd)], [prepend_path], [__prepend_path],
    [prepend], [prepend_char] and [prepend_name] in Linux v6.18.46,
    commit 1f99e9ab748f, fs/d_path.c:

    - [DECLARE_BUFFER(b, page, PATH_MAX)] starts [b.len] at PATH_MAX.
    - [prepend_char(&b, 0)] writes the terminating NUL first, taking
      [b.len] to PATH_MAX - 1.
    - [prepend_path] either OVERFLOWS — [prepend]/[prepend_char] set
      [b.len] to -1 — or returns having consumed at least one more byte:
      its tail is [if (b.len == p->len) prepend_char(&b, '/');], so a
      working directory equal to the root still costs the "/".  Hence
      [b.len <= PATH_MAX - 2] on every non-overflow path.  That step
      needs [b.len] never to RISE, since the "/" fires only on
      equality.  For a non-negative [namelen], [prepend] and
      [prepend_char] only ever lower it or set it to -1, and
      [prepend_path]'s own two writes — [b = *p] at [restart:], and the
      same assignment again when [__prepend_path] answered 3 — restore
      it to exactly [p->len] rather than above it.
      So the only input that could raise it is a NEGATIVE [namelen]:
      [prepend_name] reads a [u32 dlen] out of [d_name.len] and passes
      it into [prepend]'s [int], so a length at or above 2^31 would
      make [p->len -= namelen] increase [p->len] instead.  [struct
      qstr] carries no bound of its own, and neither does the path walk
      — fs/namei.c has no NAME_MAX check at all, which [Uapi.NAME_MAX]
      already records and [Namei.unlinkat_spec] already leans on.  The
      bound that does hold is the ALLOCATION's, and it covers every
      dentry however the name was built: [__d_alloc] (fs/dcache.c)
      stores it inline or through a [kmalloc] sized from [name->len],
      and KMALLOC_MAX_SIZE is 4 MiB on riscv64 (MAX_PAGE_ORDER 10,
      PAGE_SHIFT 12), so a 2^31-byte name fails the allocation instead
      of reaching a dentry.  The one name written outside [__d_alloc] —
      [d_mark_tmpfile]'s [sprintf] of an inode number into the inline
      buffer — is bounded by its own format.  A merely LARGE [dlen] is
      harmless in any case: [prepend] takes its overflow branch,
      [b.len] becomes -1, and the [len > PATH_MAX] guard below catches
      it.  Only a [dlen] at or above 2^31 would put [len] below 2
      without tripping that guard, and no dentry can hold one.
    - [len = PATH_MAX - b.len], so [len >= 2] when the buffer held, and
      [len = PATH_MAX + 1] when it did not.
    - the overflow is caught FIRST, by [if (len > PATH_MAX) error =
      -ENAMETOOLONG;], so [len > size] is only ever evaluated with
      [len] in [2, PATH_MAX].

    So [size] of 0 or 1 is -ERANGE, whatever the working directory is.
    A working directory outside the caller's root does not weaken this.
    [__prepend_path] answers 1 (absolute root), 2 (detached) or 3
    (escaped mid-walk); getcwd keys on [> 0] rather than on any one of
    them and prepends the 13-byte literal "(unreachable)" for all
    three.  On the 3, [prepend_path] additionally resets the buffer
    ([if (unlikely(error == 3)) b = *p;]) before the "/" test — so
    [len] is exactly 15 there, and at least 15 on the other two.

    ORDER, AND WHAT IT MEANS FOR [buf].  The kernel's sequence is
    ENOMEM, then ENOENT, then the whole path is built into a KERNEL
    page, then ENAMETOOLONG, then ERANGE, and only then a single
    [copy_to_user].  There is no [access_ok] and no probe of [buf]
    anywhere earlier.  So [buf] is not an argument of this spec at all
    — a spec that consulted [in_wmem] here would answer -EFAULT where
    Linux answers -ERANGE, and [getcwd(NULL, 0)] really is -ERANGE.
    The -EINVAL that POSIX documents for a zero size is glibc's own and
    never reaches the kernel: [sysdeps/unix/sysv/linux/getcwd.c]
    answers a zero [size] with a non-null [buf] before issuing the
    call, and substitutes PATH_MAX when [buf] is null.  That half is
    not pinned to a glibc version because nothing here rests on it;
    what does is that the syscall body has no -EINVAL arm at all,
    which is read from the fs/d_path.c above.

    Nothing is written on any admitted arm, so the effect is a bare
    return with five empty ledgers.

    -ERANGE and the three injectable errnos are offered as an [alt]
    rather than ranked, because they are not a priority ordering over
    one state: in any single run exactly one of them applies, and which
    one is decided by allocator, dcache and directory-depth conditions
    the model does not carry. *)
Definition getcwd_spec (size : word) : Sys SyscallEffect :=
  if (1 <? bv_unsigned size)%Z then unmodeled   (* the cwd would decide it: fail closed *)
  else alt (e <- errno_from getcwd_errnos ;; err_ret e) (err_ret ERANGE).
