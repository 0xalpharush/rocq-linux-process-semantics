(** The exit bridge relates two local denotations to shared syntax, not to
    Linux. These accepting and rejecting witnesses pin the semantic mistakes
    a common artifact or its interpreter could otherwise hide. *)

From Stdlib Require Import ZArith List Bool PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Bridge Require Import Exit.
Import ListNotations.
Open Scope bv_scope.

Definition input255 : SyscallInput :=
  mkInput (Z_to_bv 64 93) [Z_to_bv 64 255; Z_to_bv 64 7]
    (fun _ => None) (fun _ => None).

Lemma input255_exit : exit_number (in_sysno input255).
Proof. left. reflexivity. Qed.

Theorem correct_answer_accepted : forall m,
  syscall_spec input255 m (evaluate exit_clause input255 m).
Proof.
  intros m. apply (proj2 (exit_dispatch_normal_form _ _ _ input255_exit)). reflexivity.
Qed.

Definition group_input255 : SyscallInput :=
  mkInput (Z_to_bv 64 94) [Z_to_bv 64 255; Z_to_bv 64 7]
    (fun _ => None) (fun _ => None).

Lemma group_input255_exit : exit_number (in_sysno group_input255).
Proof. right. reflexivity. Qed.

Theorem group_answer_accepted : forall m,
  syscall_spec group_input255 m (evaluate exit_clause group_input255 m).
Proof.
  intros m. apply (proj2 (exit_dispatch_normal_form _ _ _ group_input255_exit)).
  reflexivity.
Qed.

Definition halted (o : outcome SyscallEffect) : option word :=
  match o with Ok _ m _ => m_halted m | Unmodeled => None end.

Definition returned (o : outcome SyscallEffect) : option word :=
  match o with Ok eff _ _ => Some (eff_ret eff) | Unmodeled => None end.

Definition wide_input : SyscallInput :=
  mkInput (Z_to_bv 64 93) [Z_to_bv 64 0x1ff] (fun _ => None) (fun _ => None).

Lemma wide_input_exit : exit_number (in_sysno wide_input).
Proof. left. reflexivity. Qed.

Theorem wide_status_accepted : forall m,
  syscall_spec wide_input m
    (Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (Z_to_bv 64 255) m) []).
Proof.
  intros m. apply (proj2 (exit_dispatch_normal_form _ _ _ wide_input_exit)).
  unfold evaluate, exit_clause.
  change (Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (Z_to_bv 64 255) m) [] =
    Ok (mkEffect (Z_to_bv 64 0) [] [])
      (with_halted (bv_and (Z_to_bv 64 0x1ff) (Z_to_bv 64 255)) m) []).
  assert (Hmask : bv_and (Z_to_bv 64 0x1ff) (Z_to_bv 64 255) = Z_to_bv 64 255).
  { apply bv_eq. reflexivity. }
  now rewrite Hmask.
Qed.

Theorem unmasked_wide_status_rejected : forall m,
  ~ syscall_spec wide_input m
    (Ok (mkEffect (Z_to_bv 64 0) [] []) (with_halted (Z_to_bv 64 0x1ff) m) []).
Proof.
  intros m H. apply (proj1 (exit_dispatch_normal_form _ _ _ wide_input_exit)) in H.
  apply (f_equal halted) in H.
  apply (f_equal (fun x : option word => option_map bv_unsigned x)) in H.
  vm_compute in H. discriminate.
Qed.

Theorem wrong_mask_rejected : forall m,
  ~ syscall_spec input255 m
    (evaluate (halt (Z_to_bv 8 0) (Z_to_bv 8 127) (Z_to_bv 8 0)) input255 m).
Proof.
  intros m H. apply (proj1 (exit_dispatch_normal_form _ _ _ input255_exit)) in H.
  apply (f_equal halted) in H.
  apply (f_equal (fun x : option word => option_map bv_unsigned x)) in H.
  vm_compute in H. discriminate.
Qed.

Theorem wrong_argument_rejected : forall m,
  ~ syscall_spec input255 m
    (evaluate (halt (Z_to_bv 8 1) (Z_to_bv 8 255) (Z_to_bv 8 0)) input255 m).
Proof.
  intros m H. apply (proj1 (exit_dispatch_normal_form _ _ _ input255_exit)) in H.
  apply (f_equal halted) in H.
  apply (f_equal (fun x : option word => option_map bv_unsigned x)) in H.
  vm_compute in H. discriminate.
Qed.

Theorem wrong_return_rejected : forall m,
  ~ syscall_spec input255 m
    (evaluate (halt (Z_to_bv 8 0) (Z_to_bv 8 255) (Z_to_bv 8 1)) input255 m).
Proof.
  intros m H. apply (proj1 (exit_dispatch_normal_form _ _ _ input255_exit)) in H.
  apply (f_equal returned) in H.
  apply (f_equal (fun x : option word => option_map bv_unsigned x)) in H.
  vm_compute in H. discriminate.
Qed.

Theorem unmodeled_rejected : forall m, ~ syscall_spec input255 m Unmodeled.
Proof.
  intros m H. apply (proj1 (exit_dispatch_normal_form _ _ _ input255_exit)) in H.
  discriminate.
Qed.

Theorem decline_unmodeled_accepted : forall i m, denote decline i m Unmodeled.
Proof. reflexivity. Qed.

Theorem decline_success_rejected : forall i m,
  ~ denote decline i m (evaluate exit_clause i m).
Proof. intros i m H. discriminate. Qed.

Theorem wrong_mask_has_different_serialization :
  serialize (halt (Z_to_bv 8 0) (Z_to_bv 8 127) (Z_to_bv 8 0)) <>
  serialize exit_clause.
Proof. vm_compute. discriminate. Qed.

Local Open Scope pstring_scope.
Theorem decline_decoded : read_artifact "01" = Some decline.
Proof. vm_compute. reflexivity. Qed.
Theorem unknown_tag_rejected : read_artifact "02" = None.
Proof. vm_compute. reflexivity. Qed.
Theorem wrong_arity_rejected : read_artifact "00" = None.
Proof. vm_compute. reflexivity. Qed.
Theorem odd_length_rejected : read_artifact "0000ff0" = None.
Proof. vm_compute. reflexivity. Qed.
Theorem trailing_byte_rejected : read_artifact "0000ff0000" = None.
Proof. vm_compute. reflexivity. Qed.
Theorem invalid_hex_rejected : read_artifact "0000gg00" = None.
Proof. vm_compute. reflexivity. Qed.

Theorem high_status_normalized :
  bv_unsigned (bv_and (Z_to_bv 64 0x1000001ff) (Z_to_bv 64 255)) = 255%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem full_status_rejected :
  bv_unsigned (bv_and (Z_to_bv 64 0x1000001ff) (Z_to_bv 64 255)) <> 0x1000001ff%Z.
Proof. vm_compute. discriminate. Qed.

Theorem seven_bit_remainder_rejected :
  bv_unsigned (bv_and (Z_to_bv 64 255) (Z_to_bv 64 255)) <>
    (bv_unsigned (Z_to_bv 64 255) mod 128)%Z.
Proof. vm_compute. discriminate. Qed.
