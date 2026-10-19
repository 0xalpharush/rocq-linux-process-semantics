(* Written by the OSS-Fuzz proof collaborators. *)
(** * Common.TargetCover — interval-cover dispatch for a per-payload-length-class proof.

    A phase proved per PAYLOAD-LENGTH CLASS [lo <= n <= hi]: a class theorem has
    the form [TPgen Q lo hi] = [forall n, lo <= n <= hi -> Q n] for the image's
    class predicate [Q] (e.g. "every target_pre configuration whose payload
    length is n realizes t_target").  [tp_dispatch]: a list of proved classes
    whose intervals cover [lo, hi] (reflective check [tp_covers], by
    [vm_compute]) proves [TPgen Q lo hi].  Stdlib only; [Q] is abstract. *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.

Definition TPgen (Q : Z -> Prop) (lo hi : Z) : Prop := forall n, lo <= n <= hi -> Q n.

(** A proved class. *)
Record tpc (Q : Z -> Prop) : Type := TPC { c_lo : Z; c_hi : Z; c_ok : TPgen Q c_lo c_hi }.
Arguments TPC {Q} _ _ _.
Arguments c_lo {Q} _.
Arguments c_hi {Q} _.
Arguments c_ok {Q} _.

(** [tp_covers ivs lo hi]: the intervals (sorted by lower end) cover [lo, hi]. *)
Fixpoint tp_covers (ivs : list (Z * Z)) (lo hi : Z) : bool :=
  match ivs with
  | [] => Z.ltb hi lo
  | (a, b) :: rest => (Z.ltb hi lo) || (Z.leb a lo && tp_covers rest (Z.max lo (b + 1)) hi)
  end.

Lemma tp_covers_sound : forall ivs lo hi x,
  tp_covers ivs lo hi = true -> lo <= x <= hi -> exists ab, In ab ivs /\ fst ab <= x <= snd ab.
Proof.
  induction ivs as [|[a b] rest IH]; intros lo hi x Hc Hx; cbn [tp_covers] in Hc.
  - apply Z.ltb_lt in Hc. lia.
  - apply orb_prop in Hc. destruct Hc as [Hc|Hc]; [apply Z.ltb_lt in Hc; lia|].
    apply andb_prop in Hc as [Ha Hr]. apply Z.leb_le in Ha.
    destruct (Z.le_gt_cases x b) as [Hle|Hgt].
    + exists (a, b). split; [left; reflexivity | cbn; lia].
    + destruct (IH (Z.max lo (b + 1)) hi x Hr ltac:(lia)) as (ab & Hin & Hab).
      exists ab. split; [right; exact Hin | exact Hab].
Qed.

Definition ivs {Q : Z -> Prop} (cls : list (tpc Q)) : list (Z * Z) := map (fun c => (c_lo c, c_hi c)) cls.

Theorem tp_dispatch : forall (Q : Z -> Prop) (cls : list (tpc Q)) (lo hi : Z),
  tp_covers (ivs cls) lo hi = true -> TPgen Q lo hi.
Proof.
  intros Q cls lo hi Hc n Hn.
  destruct (tp_covers_sound (ivs cls) lo hi n Hc Hn) as (ab & Hin & Hab).
  unfold ivs in Hin. apply in_map_iff in Hin as (c & <- & Hin). cbn [fst snd] in Hab.
  exact (c_ok c n Hab).
Qed.

(** single class as a [TPgen] from a plain interval-quantified statement *)
Lemma tpgen_intro : forall (Q : Z -> Prop) lo hi, (forall n, lo <= n <= hi -> Q n) -> TPgen Q lo hi.
Proof. intros Q lo hi H. exact H. Qed.

Lemma k_cases : forall k : Z, 1 <= k <= 10 ->
  k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10.
Proof. intros k Hk. lia. Qed.
