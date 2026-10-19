(** * LinuxProcessSem.Checks.Sys.Mm.Madvise — the madvise (233) checker, and its proofs

    Mirrors [Sys/Mm/Madvise.v], which answers to Linux [mm/madvise.c]:
    this file holds the checker for the syscall defined there, and no
    other.

    [Checks/ExecutableSpecs.v] keeps the dispatcher
    and the four top-level theorems and re-exports this module. The
    checker here is executable, and its proofs relate it to the
    relational spec in the matching [Sys] module. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Export
  Prelude Fs.ReadWrite.

(** Gate for gate the spec's order: alignment, then the advice, then the
    zero length, then the wrapping range, then the ledger.  On the
    answered shape the effect must be exactly the zero-fill of the
    page-rounded range with a zero return, and the post-model is the
    spec's [madvise_dontneed_next]. *)
Definition check_madvise (addr len advice : word) (eff : SyscallEffect)
    (m : Model) : check_result :=
  if negb (Z.eqb (bv_unsigned addr mod page_size) 0)
  then check_ret_only eff (errno_ret EINVAL) m []
  else if negb (madvise_dontneed_b advice) then CheckUnmodeled
  else if w_is0 len then check_ret_only eff (Z_to_bv 64 0) m []
  else if (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z
  then check_ret_only eff (errno_ret EINVAL) m []
  else
    let nZ := page_round_up_Z (bv_unsigned len) in
    let n := Z_to_bv 64 nZ in
    if madvise_dontneed_ok (m_vmmaps m) addr n then
      match eff with
      | mkEffectU r [] zs [] [] [] =>
          if w_is0 r && listNN_eqb zs [(addr, n)]
          then CheckOk (madvise_dontneed_next m addr n) []
          else CheckReject
      | _ => CheckReject
      end
    else CheckUnmodeled.

Lemma check_madvise_sound_ok : forall addr len advice eff m m' evs i,
  check_madvise addr len advice eff m = CheckOk m' evs ->
  madvise_spec addr len advice i m (Ok eff m' evs).
Proof.
  intros addr len advice eff m m' evs i H.
  unfold check_madvise in H. unfold madvise_spec.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct (negb (madvise_dontneed_b advice)) eqn:Hadv; [discriminate|].
  destruct (w_is0 len) eqn:Hlen.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { apply check_ret_only_ok_iff in H. destruct H as (-> & -> & ->).
    apply pure_ok. }
  cbv zeta in H.
  destruct (madvise_dontneed_ok (m_vmmaps m) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok;
    [|discriminate].
  destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
    [destruct us as [|? ?];
      [destruct cs as [|? ?]; [destruct copyins as [|? ?]|]|]|];
    try discriminate.
  destruct (w_is0 r
            && listNN_eqb zs
                 [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))])
    eqn:HC; [|discriminate].
  inversion H; clear H; subst.
  apply andb_true_iff in HC as [Hr Hzs].
  unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
  apply listNN_eqb_eq in Hzs; subst zs.
  eapply bind_ok0; [apply get_model_ok|]. cbv beta zeta.
  rewrite Hok.
  eapply bind_ok0; [apply modify_ok|]. apply pure_ok.
Qed.

Lemma check_madvise_sound_unmodeled : forall addr len advice eff m i,
  check_madvise addr len advice eff m = CheckUnmodeled ->
  madvise_spec addr len advice i m Unmodeled.
Proof.
  intros addr len advice [r ws zs us cs copyins] m i H.
  unfold check_madvise in H. unfold madvise_spec.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct (negb (madvise_dontneed_b advice)) eqn:Hadv;
    [apply unmodeled_intro|].
  destruct (w_is0 len) eqn:Hlen.
  { now apply check_ret_only_no_unmodeled in H. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { now apply check_ret_only_no_unmodeled in H. }
  cbv zeta in H.
  destruct (madvise_dontneed_ok (m_vmmaps m) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  { exfalso. destruct ws;
      [destruct us; [destruct cs; [destruct copyins|]|]|]; try discriminate.
    destruct (w_is0 r
              && listNN_eqb zs
                   [(addr, Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))]);
      discriminate. }
  eapply bind_unmodeled2; [apply get_model_ok|]. cbv beta iota zeta.
  rewrite Hok. apply unmodeled_intro.
Qed.

Lemma check_madvise_complete_ok : forall addr len advice eff m m' evs i,
  madvise_spec addr len advice i m (Ok eff m' evs) ->
  check_madvise addr len advice eff m = CheckOk m' evs.
Proof.
  intros addr len advice eff m m' evs i H.
  unfold madvise_spec in H. unfold check_madvise.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct (negb (madvise_dontneed_b advice)) eqn:Hadv.
  { unfold unmodeled in H. discriminate. }
  destruct (w_is0 len) eqn:Hlen.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { sys_unfold. inv_ok. cbn; try rewrite bv_eqb_refl; reflexivity. }
  cbv zeta.
  destruct (madvise_dontneed_ok (m_vmmaps m) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: { sys_unfold. cbv iota in H. inv_ok. rewrite Hok in *. inv_ok. }
  sys_unfold. cbv iota in H. inv_ok. rewrite Hok in *. inv_ok.
  cbv iota. unfold w_is0. rewrite bv_eqb_refl.
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma check_madvise_complete_unmodeled : forall addr len advice m i eff,
  madvise_spec addr len advice i m Unmodeled ->
  check_madvise addr len advice eff m = CheckUnmodeled.
Proof.
  intros addr len advice m i eff H.
  unfold madvise_spec in H. unfold check_madvise.
  destruct (negb (Z.eqb (bv_unsigned addr mod page_size) 0)) eqn:Halign.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  destruct (negb (madvise_dontneed_b advice)) eqn:Hadv; [reflexivity|].
  destruct (w_is0 len) eqn:Hlen.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  destruct ((two_pow_64
             <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z)
    eqn:Hbig.
  { sys_unfold. cbv iota in H. inv_ok; discriminate. }
  cbv zeta.
  destruct (madvise_dontneed_ok (m_vmmaps m) addr
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))) eqn:Hok.
  2: reflexivity.
  sys_unfold. cbv iota in H. inv_ok. rewrite Hok in *. inv_ok.
Qed.
