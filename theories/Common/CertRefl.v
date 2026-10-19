(* Written by the OSS-Fuzz proof collaborators. *)
(** * Common.CertRefl — the single-evaluation reflective certificate tactic.

    With it, a certificate file is one [Require] and one line per lemma.

    A reflective certificate has the shape

      Lemma leaf_ok : check ARGS plan = COk shape.
      Proof. cert_refl constr:(COk shape). Qed.

    where [check] is a plan checker of the ASan reflective automation
    ([AsanPlan.AP.check], or an image's [seg_check]/[pay_check] wrappers) and the
    right-hand side [shape] was obtained beforehand by running the same [check]
    (the "itinerary": [Eval native_compute in check ARGS plan]).  [reflexivity]
    would evaluate the checker TWICE — once in the tactic, once again when the
    kernel re-checks the proof term at [Qed].  [cert_refl rhs] instead builds the
    proof term [@eq_refl cres rhs <<: goal] as a RAW kernel term — a native-cast
    node around [eq_refl], with no pretyping of the cast — and hands it to the
    kernel with [exact_no_check], so the conversion runs ONCE, at [Qed], by
    [native_compute].  ([cres] is the checker's result type, [COk _ | CErr _];
    any inductive with a decidable equality works the same way — change the
    annotation.)

    Which tactic.  Use [cert_refl_vm] in a certificate file.  [cert_refl]'s
    native cast makes the native compiler compile the file's whole [Require]
    closure, so it needs .coq-native objects for every Required module;
    [cert_refl_vm] needs none.  A certificate file necessarily [Require]s its
    per-binary memory-image module, so if that module has no .coq-native
    object, then under a native-compiling toolchain
    ([-native-compiler ondemand] or [yes]) [cert_refl] dies at the
    native compiler ("Unbound module N<image module>", "Native compiler exited
    with status 2").  Under [-native-compiler no] the native cast runs
    as the VM conversion anyway, after a [native-compiler-disabled] warning, so
    [cert_refl] and [cert_refl_vm] prove the same certificates at the same cost
    there — but only [cert_refl_vm] also works under a toolchain that does
    compile native code.

    Cost note.  Under a toolchain with native compilation disabled
    ([-native-compiler no])
    the native cast degrades to the VM conversion; the certificate
    stays valid, only slower (3-5x on the ASan plan checks).
    Nothing else in the reflective library needs native code. *)

From Ltac2 Require Import Ltac2 Constr Std Control.

(** [cert_refl rhs]: close a goal [lhs = rhs] whose two sides are convertible by
    computation, with one native-compute conversion at [Qed]. *)
Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.native g)).

(** the same with the VM conversion instead of native code — the one to use in
    a certificate file (see the header: it needs no native objects); under
    [-native-compiler no] every native cast turns into
    this anyway *)
Ltac2 cert_refl_vm (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl _ $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).
