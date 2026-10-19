(** * LinuxProcessSem.Sys.Kernel.Groups — getgroups (158) and setgroups (159)

    This file answers to Linux [kernel/groups.c]: it holds what the
    kernel defines there, and nothing else.  Which file a spec belongs
    in is therefore not a judgement call — look up where the kernel
    defines the syscall.  [Specs.v] carries the whole map.

    TRUST BOUNDARY: this file is part of the trusted specification.
    [Specs.v] holds the dispatcher and re-exports this module; see that
    file's header for the representation and fail-closed conventions
    every spec here follows. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Export
  Syscall Uapi Uaccess.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* ---- getgroups (158) ---------------------------------------------------- *)

(** [getgroups gidsetsize grouplist] (158): how many supplementary
    groups the process has, and — on a path this spec DECLINES — the
    groups themselves.

    THE WHOLE KERNEL FUNCTION, in its own order (Linux, kernel/groups.c,
    [SYSCALL_DEFINE2(getgroups)] and the one helper it calls,
    [groups_to_user]):

      if (gidsetsize < 0)            return -EINVAL;
      i = cred->group_info->ngroups;
      if (gidsetsize) {
        if (i > gidsetsize)          { i = -EINVAL; goto out; }
        if (groups_to_user(grouplist, cred->group_info))
                                     { i = -EFAULT; goto out; }
      }
      out: return i;

    Both functions are byte-identical from v4.9 through v6.18.
    [groups_to_user] last changed at commit 81243eacfa40 ("cred:
    simpler, 1D supplementary groups", first released in v4.9), a
    [GROUP_AT(group_info, i)] to [group_info->gid[i]] refactor with no
    behavioral change; the [getgroups] body has not changed since
    commit 30639b6af85a moved it into kernel/groups.c for v2.6.31.  The
    claim is over the WHOLE INTERVAL rather than its endpoints, which is
    the only form worth stating: the file's commit history since
    v2.6.31 contains no change to a line inside either function, and no
    stable branch backports one.  Tags read: v4.9, v5.4, v5.10, v5.15,
    v6.1, v6.6, v6.12, v6.16 and mainline master; stable branches read:
    linux-4.19.y, 5.4.y, 5.10.y, 5.15.y, 6.1.y, 6.6.y, 6.12.y.

    ORDER IS THE POINT HERE, three times over.

    - The NEGATIVE SIZE is refused before [current_cred()->group_info]
      is even read, so a negative [gidsetsize] with a garbage
      [grouplist] is -EINVAL and never -EFAULT.
    - A SIZE OF ZERO skips the whole [if (gidsetsize)] block, so the
      pointer is not touched at any width: [getgroups(0, <anything>)]
      answers the count.  That is the form musl's [getgroups] wrapper
      passes through unchanged (musl 1.2.5, src/unistd/getgroups.c) and
      the form dropbear's non-multiuser sanity check uses.
    - A SIZE TOO SMALL is -EINVAL BEFORE any store, so [getgroups(1,
      <garbage>)] on a process with five groups is -EINVAL rather than
      -EFAULT.

    [gidsetsize] is an [int], so only the low half of a0 reaches these
    comparisons and it is read as two's complement: a0 = 2^32 is
    [gidsetsize = 0], not a huge positive ([__SC_CAST] in
    include/linux/syscalls.h, applied by [__SYSCALL_DEFINEx] out of
    arch/riscv/include/asm/syscall_wrapper.h).  [Syscall.sint32] is that
    reading.  [grouplist] is a full 64-bit pointer and is NOT an
    argument of this spec at all, which is the sharpest way to state
    what the arms below share: no modeled path reads it.

    THERE IS NO UPPER BOUND ON [gidsetsize].  [setgroups] rejects a size
    above [Uapi.NGROUPS_MAX]; [getgroups] does not test it at all, so
    [getgroups(70000, buf)] is the count on a process whose list fits
    and would be the write on one whose list does not.  Nothing below
    compares [n] against [NGROUPS_MAX] for that reason — the guard
    further down is on the STORED LIST's length, not on the argument.

    THE ZERO-LENGTH LIST IS THE SUBTLE ARM.  With [gidsetsize > 0] and
    no supplementary groups, control does enter the block, but
    [groups_to_user]'s loop runs [ngroups] times — zero — and returns 0
    without a single [put_user].  There is no up-front [access_ok] over
    the array; validation is per element, inside the loop.  So
    [getgroups(64, <a garbage pointer>)] returns 0, not -EFAULT, for a
    process with no supplementary groups, and this spec says so.

    DECLINED: [gidsetsize >= ngroups > 0], the path that WRITES.  It
    stores [ngroups] 4-byte [gid_t]s ascending from [grouplist], each
    through its own [put_user], and a fault at element k leaves elements
    0..k-1 written — the kernel does not roll back.  Modeling that
    exactly means either proving the whole array writable or proving the
    FIRST element's range refused by [access_ok], the way
    [Net.Socket.socketpair_spec] reasons about its two stores; the band
    between those is [unmodeled] either way, and unlike socketpair the
    array's length is not fixed.  Cost of the decline, stated plainly: a
    program that reads its own group list — [initgroups], [id], anything
    that calls [getgroups(n, buf)] with [n] large enough — leaves the
    modeled surface on that call.  A program that only asks HOW MANY
    does not.

    NOT MODELED EITHER, and not the same kind of gap:
    [from_kgid_munged] answers an unmappable gid with [overflowgid]
    rather than an errno, so the ELEMENT VALUES this spec does not hand
    out would depend on the caller's user namespace.  The model already
    assumes the init namespace with an identity map (see
    [State.creds_privileged] for the standing assumptions), where the
    munge is the identity.

    THE [NGROUPS_MAX] GUARD is a fail-closed answer to a state Linux
    cannot build.  [Uapi.NGROUPS_MAX] bounds every [struct group_info]
    the kernel will allocate, so a longer [State.cr_groups] describes no
    process; the count such a state would report might not even fit the
    [int] this syscall returns.  Rather than answer for it, the spec
    declines — after the negative-size check, because that check comes
    first in the kernel and an impossible state must not reorder a
    behavior. *)
Definition getgroups_spec (gidsetsize : word) : Sys SyscallEffect :=
  let n := sint32 gidsetsize in
  if (n <? 0)%Z then err_ret EINVAL
  else
    m <- get_model ;;
    let ng := Z.of_nat (length (cr_groups (m_creds m))) in
    if (NGROUPS_MAX <? ng)%Z then unmodeled
    else if (n =? 0)%Z then ret_only (Z_to_bv 64 ng)
    else if (n <? ng)%Z then err_ret EINVAL
    else if (ng =? 0)%Z then ret_only (Z_to_bv 64 0)
    else unmodeled.

(* ---- setgroups (159) ---------------------------------------------------- *)

(** [setgroups gidsetsize grouplist] (159): -EPERM for an unprivileged
    caller, and FAIL CLOSED for a privileged one.  (Linux v6.18.46,
    commit 1f99e9ab748f, kernel/groups.c, [SYSCALL_DEFINE2(setgroups)] /
    [may_setgroups] / [groups_from_user]; the whole file is
    byte-identical there and at every mainline release tag from v6.10
    through v6.18.)  [State.creds_privileged] carries the standing
    assumptions that let an effective uid answer the capability question
    [may_setgroups] really asks.

    The -EPERM half is exact, and it is exact for a reason worth naming:
    [may_setgroups()] is the FIRST thing the syscall does, before the
    [gidsetsize] bound and before the pointer is touched.  So an
    unprivileged caller gets -EPERM whatever it passes — a negative size,
    a size past NGROUPS_MAX, an unmapped list — and the spec needs
    neither argument.  A model that checked the arguments first would
    answer -EINVAL or -EFAULT where the kernel answers -EPERM.

    The successful half is DECLINED rather than faked.  It writes the
    supplementary group list — [State.cr_groups], the list [getgroups]
    (158) above reports the length of — so accepting the call while
    discarding what it wrote would make the next [getgroups] answer for
    a list nobody set.  The model carries the list;
    what is missing is a per-element import from user memory with the
    kernel's index-ordered -EFAULT-before-EINVAL precedence, and
    [groups_sort]'s ascending reorder, which is observable because
    [getgroups] hands back the STORED order and not the written one.

    Cost of the decline, stated plainly: a source binary that drops
    privilege the way dropbear does — [setgroups] via [initgroups],
    then [setgid], then [setuid] — leaves the modeled surface at the
    first of those three, so it cannot be certified.  The
    [rt_sigprocmask] (135) pair
    musl wraps around every credential syscall (musl 1.2.5,
    src/thread/synccall.c) is answered, so it does not leave earlier. *)
Definition setgroups_spec : Sys SyscallEffect :=
  m <- get_model ;;
  if creds_privileged (m_creds m) then unmodeled else err_ret EPERM.
