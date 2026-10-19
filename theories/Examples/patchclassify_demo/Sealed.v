(** * Examples.patchclassify_demo.Sealed — the demo ascribed to the
      submission surface

    DEMO FILE (not part of the trusted specification), and the only file
    in this directory whose content is its TYPE.  Nothing is proved
    here: every definition below is a bare alias for a theorem [Images]
    or [Obligations] already proved, and the file's whole job is to make
    the Rocq kernel check that those theorems are the ones
    [EquivalenceDefinition.PatchClassifySpec.SPEC_PATCH_CLASSIFY] asks
    for.

    ** Why an ascription, rather than a list of theorem names

    [PatchClassifySpec]'s header gives the reason and it is worth
    restating at the point where it bites: a submission's proofs are
    ASCRIBED to the module type, so a proof of a different statement —
    about a different image, under a weakened predicate, with a bound
    about some other classifier — fails to typecheck here rather than
    passing quietly.  A directory of theorems with the right names
    establishes nothing; the same directory accepted by
    [Module DemoSealed <: SPEC_PATCH_CLASSIFY ...] establishes that the
    six images really do satisfy the surface.

    That is the difference this file makes to the demo, and it is the
    reason the aliases below are bare.  If any of them had to be
    restated — an adapter, a [Proof] block, an [apply] that reshuffled
    quantifiers — the restatement would be the thing to audit, and the
    theorems in [Obligations] would no longer be the theorems the
    surface demands.  They are not restated.  Each [Definition] is one
    identifier, and the ascription is what checks it.

    ** [Equivalence.IMAGE_WF] for all six, first

    The six well-formedness ascriptions come first because without them
    the five obligations are consistent with the demo having proved
    nothing at all.  Every obligation quantifies over valid
    [Run.ExecEntry]s, and an image with none satisfies all of them
    vacuously: [Classifier.decides_vacuous_no_entries] says such an
    image DECIDES EVERY property, contradictory ones included, and
    [Classifier.accepts_vacuous_no_entries] says it accepts every input,
    which empties [Classifier.rejects] and makes
    [Measure.weight_bound_T] hold at every multiplier for every weight.
    A file that pinned the five statements and the two numbers while
    skipping the well-formedness would have pinned exactly that: five
    theorems and two numerals, all seven free.

    [PatchClassifySpec]'s header names the two CLASSIFIER images as the
    pair easiest to forget and worst to omit, since they are the ones
    the vacuity lemmas above are about; [C1wf] and [C2wf] are therefore
    not optional decoration on the four an equivalence checker would
    already ascribe.  The eighteen lemmas they are built from are proved
    in [Images], beside the segments they are about, so that an edit
    breaking one fails in the file the edit is in.

    ** What the ascription does NOT establish

    It does not make the demo interesting; it makes it CHECKED.  Both
    classifiers fire on every valid finite input and both bounds are the
    trivial multiplier — the honest answers for this pair of originals,
    argued in [Obligations]' header and in the demo's README, which also
    names the refinement that would make the numbers say more.  The
    ascription is indifferent to that: it would accept a sharper
    instance and it accepts this one, and a reader who wants to know how
    much the demo says should read the bites at the end of [Obligations]
    rather than this file.

    In particular, [b1] and [b2] below being [1] is not a claim that [1]
    is the least provable multiplier.  [Obligations]' [demo_b_zero_refutable]
    and [demo_b_half_refutable] show two smaller values are refutable,
    which is what makes the multiplier load-bearing rather than
    decorative, and they leave every [b] strictly between [144495 # 262144]
    and [1] open. *)

From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence Measure PatchClassifySpec.
From LinuxProcessSemantics.Examples.patchclassify_demo Require Import
  Images Distribution Obligations.

(* =========================================================================
   [Equivalence.IMAGE_WF] for all six images
   ========================================================================= *)

(** Three aliases each, in the order [Equivalence.IMAGE_WF] declares
    them.  [brk_satisfiable] is the one whose failure would sink the
    example silently — it is what inhabits the entry space, and hence
    what makes [Run.valid_entry] satisfiable at all — and the other two
    close the vacuity routes that run through the error escape. *)

Module O1wf <: IMAGE_WF O1m.
  Definition entry_fetchable := O1_entry_fetchable.
  Definition phdrs_readable := O1_phdrs_readable.
  Definition brk_satisfiable := O1_brk_satisfiable.
End O1wf.

Module O2wf <: IMAGE_WF O2m.
  Definition entry_fetchable := O2_entry_fetchable.
  Definition phdrs_readable := O2_phdrs_readable.
  Definition brk_satisfiable := O2_brk_satisfiable.
End O2wf.

Module P1wf <: IMAGE_WF P1m.
  Definition entry_fetchable := P1_entry_fetchable.
  Definition phdrs_readable := P1_phdrs_readable.
  Definition brk_satisfiable := P1_brk_satisfiable.
End P1wf.

Module P2wf <: IMAGE_WF P2m.
  Definition entry_fetchable := P2_entry_fetchable.
  Definition phdrs_readable := P2_phdrs_readable.
  Definition brk_satisfiable := P2_brk_satisfiable.
End P2wf.

(** The two the header says are easiest to forget. *)
Module C1wf <: IMAGE_WF C1m.
  Definition entry_fetchable := C1_entry_fetchable.
  Definition phdrs_readable := C1_phdrs_readable.
  Definition brk_satisfiable := C1_brk_satisfiable.
End C1wf.

Module C2wf <: IMAGE_WF C2m.
  Definition entry_fetchable := C2_entry_fetchable.
  Definition phdrs_readable := C2_phdrs_readable.
  Definition brk_satisfiable := C2_brk_satisfiable.
End C2wf.

(* =========================================================================
   The submission surface, sealed
   ========================================================================= *)

(** The five obligations and the two bounds, at the argument order
    [PatchClassifySpec.SPEC_PATCH_CLASSIFY] declares — [O1m P1m O2m P2m
    C1m C2m], the two originals interleaved with their patches, then the
    two classifiers, then the distribution.

    [DemoDist] enters as trusted metadata and not as a claim: its two
    obligations are about the weight function (nonnegativity, and
    [Measure.DISTRIBUTION]'s [w_core_blind]), both discharged in
    [Distribution] from [MeasureLib]'s lifting lemmas, and neither is
    something a submission would have to establish. *)
Module DemoSealed <: SPEC_PATCH_CLASSIFY O1m P1m O2m P2m C1m C2m DemoDist.
  Definition strong_universal := P1_P2_strong_universal.
  Definition classifies_diff := C1_classifies_patch_diff.
  Definition classifies_good := C2_classifies_good_inputs.
  Definition b1 : Q := 1%Q.
  Definition b2 : Q := 1%Q.
  Definition bound_diff := C1_weight_bound.
  Definition bound_good := C2_weight_bound.
End DemoSealed.

(* =========================================================================
   The error-free flavor, which the demo also satisfies
   ========================================================================= *)

(** [PatchClassifySpec.SPEC_PATCH_CLASSIFY_ERROR_FREE] is the surface a
    task OPTS IN to: it replaces the patch obligation with
    [Equivalence.strong_universal_error_free_T], which additionally
    demands that neither patched binary ever reaches the error
    transition.  Its header explains why that is a separate module type
    rather than an extension — the stronger reading is unprovable for
    any binary that can legitimately crash, so no task should get it by
    default.

    These two patches cannot crash: they execute three instructions and
    exit, at every valid entry on every input, which is what
    [Obligations]' [P1_P2_strong_universal_error_free] says.  So the
    demo satisfies the stronger surface too, and the ascription below is
    the evidence.  The other five declarations are the same identifiers
    as above, deliberately: the classifiers are asked the same
    questions in both flavors and the measure layer never sees the
    difference.

    Nothing downstream needs both.  [DemoSealedErrorFree] is here
    because a demo of a surface that has two flavors should show that
    the instance it built lands in the sharper one, and because
    [Equivalence.strong_universal_error_free_implies] — which is how
    [Obligations] derives [P1_P2_strong_universal] in the first place —
    is easier to trust when both endpoints are exhibited. *)
Module DemoSealedErrorFree <:
    SPEC_PATCH_CLASSIFY_ERROR_FREE O1m P1m O2m P2m C1m C2m DemoDist.
  Definition strong_universal_error_free := P1_P2_strong_universal_error_free.
  Definition classifies_diff := C1_classifies_patch_diff.
  Definition classifies_good := C2_classifies_good_inputs.
  Definition b1 : Q := 1%Q.
  Definition b2 : Q := 1%Q.
  Definition bound_diff := C1_weight_bound.
  Definition bound_good := C2_weight_bound.
End DemoSealedErrorFree.

(* =========================================================================
   Reading the two bounds
   ========================================================================= *)

(** [PatchClassifySpec]'s header is explicit that a consuming checker
    PRINTS [b1] and [b2] and does not compare them against an expected
    value, because [Q]'s propositional equality is [Qeq] and not
    Leibniz [eq]: [1] and [2 # 2] are the same bound written two ways,
    and a [vm_compute; reflexivity] check against a literal would accept
    one and reject the other while both name the same fact.

    So the two statements below are written in [Qeq], which is the form
    that transports — [Measure.weight_bound_qeq] carries the bound along
    it in both the mass and the multiplier.  They are a demonstration of
    the reading discipline and not a check the demo needs: a reader
    wanting the number reads [b1] itself. *)

Example demo_b1_reads_as_one : (DemoSealed.b1 == 1)%Q.
Proof. reflexivity. Qed.

Example demo_b2_reads_as_one : (DemoSealed.b2 == 1)%Q.
Proof. reflexivity. Qed.

(** And the printed bound is an UPPER bound rather than a measurement,
    which is [Measure.weight_bound_mono]: a proof at [b] is a proof at
    every larger [b'].  Instantiated here so that the honest reading of
    the demo's numbers — "the fire set weighs at most this much" — is
    exhibited rather than asserted. *)
Example demo_bound_diff_at_two :
  weight_bound_T C1_image DemoDist.w DemoDist.M 2.
Proof.
  apply (weight_bound_mono _ _ _ DemoSealed.b1).
  - rewrite demo_M_is_one. apply Qlt_le_weak. reflexivity.
  - unfold DemoSealed.b1. apply Qlt_le_weak. reflexivity.
  - exact DemoSealed.bound_diff.
Qed.

(* =========================================================================
   The audit
   ========================================================================= *)

(** What [theories/Examples]' generated [Checker.v] does for the
    baseline check, done by hand for the six-image surface: print the
    assumptions of each sealed obligation, so that the ascription above
    is auditable and not merely accepted.  Every one of them reports the
    [PrimInt63]/[PrimString] primitives that this development's
    machine-word and string layers rest on, and nothing else — in
    particular no [functional_extensionality_dep], which the compiled
    examples do use and this one has no occasion to.

    The generated file wraps its one print in a fixed [Set Printing]
    preamble and [idtac] markers, so that a consumer can parse the
    assumption set out of a build log.  These are plain, because nothing
    parses this directory: a reader is the audience, and the six lines
    below are for them. *)

Print Assumptions DemoSealed.strong_universal.
Print Assumptions DemoSealed.classifies_diff.
Print Assumptions DemoSealed.classifies_good.
Print Assumptions DemoSealed.bound_diff.
Print Assumptions DemoSealed.bound_good.
Print Assumptions DemoSealedErrorFree.strong_universal_error_free.
