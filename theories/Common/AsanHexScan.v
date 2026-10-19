(* Written by the OSS-Fuzz proof collaborators. *)
(* HexScan — AXIOM-FREE check that every byte offset below a
   given count of a segment hex chunk decodes ([hex_byte_at s off <> None]).
   A scan of the PrimString with an int63 cursor would need the Uint63Axioms (of_to_Z, add_spec, leb_spec, ...)
   to relate the cursor to the spec's [hex_byte_at], and those axioms would show up in `Print Assumptions`.
   This scan simply EVALUATES the trusted spec's own [hex_byte_at s off] at every offset (binary-split recursion on the
   byte count, so no big unary numbers), hence its soundness lemma is purely structural: no int63 reasoning,
   no axiom.  Cost: ≈ 5.4 M evaluations of [hex_byte_at] for the asan .bss chunk (seconds under vm/native_compute). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Import ListNotations.

Definition byte_ok (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some _ => true | None => false end.

(** [scanN s fuel base n] checks offsets [base, base+n) by binary splitting of [n]. *)
Fixpoint scanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_ok s base
      else let h := N.div2 n in (scanN s f base h && scanN s f (base + h) (n - h))%bool
  end.

Lemma scanN_sound : forall s fuel base n,
  scanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None.
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [scanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_ok in H.
      destruct (hex_byte_at s base); [discriminate|discriminate].
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(** consequence for a one-chunk segment byte list: [chunk_bytes] is the spec's own length expression, which the
    image files evaluate once by [vm_compute] (pure computation, no axiom). *)
Lemma segment_byte_at_some1 : forall s (n : N) (off : N),
  scanN s 64 0 n = true ->
  (n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
  (Z.of_N off < Z.of_N n)%Z ->
  segment_byte_at [s] off <> None.
Proof.
  intros s n off Hs Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true
    by (symmetry; apply N.ltb_lt; lia).
  exact (scanN_sound s 64 0 n Hs off ltac:(lia)).
Qed.
