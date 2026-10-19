(** * EquivalenceDefinition.PatchClassifySpec — the sealing surface for a patch-plus-classifier submission

    TRUST BOUNDARY: this file is part of the trusted specification.
    Proof files never edit it.  A top-level check that ascribes against
    the module types below depends on the definitions here — and on
    everything they name — remaining fixed, exactly as the baseline
    check depends on [Equivalence].

    [Equivalence.SPEC] seals a submission that answers ONE question
    about TWO binaries: are they observably equivalent.  This file seals
    a submission that answers three questions about SIX, and it is
    nothing but the packaging: every obligation it declares is stated in
    the file that defines it, and this one adds no definition of its
    own.  A module type is the right shape for that job for the reason
    [Equivalence.SPEC]'s header gives — the submission's proofs are
    ascribed to it, so a proof of a DIFFERENT statement (a different
    image, a weakened predicate, a bound about some other classifier)
    fails the ascription rather than silently passing.

    ** The six images and what each is asked

    Two originals [O1m], [O2m] are given to the submission; the other
    four are produced by it.

    - [P1m], [P2m] are patched builds of the two originals, and the
      equivalence obligation is stated BETWEEN THE PATCHES, not between
      a patch and its own original: [Equivalence.strong_universal_T] on
      [P1] and [P2].  Which is the whole point of the exercise — the
      originals are not equivalent to each other (that is the defect),
      and the submission must repair BOTH so that they become so, at
      the two roles' respective allocation budgets
      ([State.source_alloc_limit] for the first, [State.target_alloc_limit]
      for the second, as [Equivalence.strong_equiv] pins them).
    - [C1m] is the PATCH-DIFFERENCE classifier: on a finite input it
      exits 0 exactly when both patches preserved behavior, and 1 when
      either changed it ([Classifier.classifies_patch_diff_T], whose
      [Classifier.agree] conjunction is a union scope — the classifier
      fires if EITHER pair differs).
    - [C2m] is the GOOD-INPUT classifier: on a finite input it exits 0
      exactly when the two ORIGINALS were already error-free equivalent
      there ([Classifier.classifies_good_inputs_T], over
      [Classifier.good_input], which is [Equivalence.strong_equiv_error_free]
      at all entry pairs).

    The two classifier obligations are TOTAL DECISION statements, not
    acceptance statements: [Classifier.decides] demands a verdict — all
    executions exit 0, or all exit 1 — on every valid finite input at
    every valid entry.  [Classifier]'s header argues each of the three
    restrictions in that sentence (finite inputs, per-entry, total); none
    of them is weakened here.

    ** [b1] and [b2] are chosen by the submission and READ, never compared

    The two bounds are [Parameter]s of the module type, so the submission
    supplies them along with their proofs; nothing here or downstream
    dictates a value.  A consuming checker that wants to show a reader
    what was proved PRINTS them — [Print] or [Eval vm_compute] on the
    ascribed module's [b1] — and does not compare them against an
    expected value.  That is not a stylistic preference; it is
    [Measure]'s header restated at the surface where it bites.  [Q]'s
    propositional equality is [Qeq], not Leibniz [eq], so [1#2] and
    [2#4] are the same bound written two ways, and a
    [vm_compute; reflexivity] check against a literal would accept one
    and reject the other while both name the same fact.

    Two lemmas make a printed bound readable without any such
    comparison.  [Measure.weight_bound_mono] says a proof at [b] is a
    proof at every larger [b'], so a printed [b] is an UPPER BOUND
    claim — the honest reading of "the classifier's fire set weighs at
    most this much" — rather than an exact measurement.
    [Measure.weight_bound_qeq] says the claim transports along [Qeq] in
    both [M] and [b], so a reader comparing a submission's [b1] with a
    threshold of their own may do it in whichever representation they
    like.

    ** [Equivalence.IMAGE_WF] for ALL SIX images is the checker's job

    Every obligation below is a [forall] over valid execution entries, and
    an image for which no [Run.valid_entry] exists satisfies all of them
    with nothing established about anything.  The baseline check already
    ascribes [Equivalence.IMAGE_WF] per image for that reason; here the
    same ascription is needed SIX times, and the two extra ones — for the
    classifiers — are the ones easiest to forget and worst to omit.

    Two lemmas mechanize why.  [Classifier.decides_vacuous_no_entries]:
    an image with no valid entry DECIDES EVERY property, including
    contradictory ones, so [classifies_diff] and [classifies_good] would
    both hold of a classifier that is not a program.
    [Classifier.accepts_vacuous_no_entries]: the same image ACCEPTS EVERY
    INPUT, which empties [Classifier.rejects] and makes
    [Measure.weight_bound_T] hold at [b = 0] — and so, by
    [Measure.weight_bound_mono], at every [b] — for ANY weight function
    and any declared total.  A checker that pinned the classifier
    statements and the bounds but skipped the classifier images'
    well-formedness would have pinned exactly that: two theorems and two
    numbers, all four free.

    [Equivalence.image_brk_satisfiable] is the check in that group which
    inhabits the entry space; the other two close the vacuity routes that
    run through the error escape.  None of this can live in the module
    types below, because a functor body is type-checked once with the
    images abstract while these checks hold by [vm_compute] on each
    concrete image — the same division [Equivalence.IMAGE_WF]'s header
    describes.

    ** [W] is trusted metadata, not an obligation

    The distribution module [W : Measure.DISTRIBUTION] carries the weight
    function and the declared total mass.  Both are per-problem trusted
    metadata — supplied with the task, never proved by the submission —
    and the two proof obligations inside [Measure.DISTRIBUTION] are both
    about the weight function rather than about any submission:
    nonnegativity, and [Measure.DISTRIBUTION]'s [w_core_blind], which
    says the weight does not depend on the launch environment and so
    makes the per-core charge in [Measure.weight_bound_T] well defined.
    Neither is a claim the submission has to establish.  The bounds
    below are claims about the submission's classifiers RELATIVE to that
    declared pair; they say nothing about whether [W.M] is really the
    total mass of anything, and [Measure]'s header is explicit that no
    normalization obligation ties it to 1.

    ** What "fire set" denotes here

    A set of CORES, not of records.  [Measure.weight_bound_T] is indexed
    by [FinInput.fin_core] — argv, envp, the file system and standard
    input — so a core counts once however many launch environments
    ([FinInput.fin_uid], [fin_gid], [fin_groups], [fin_net]) it is
    offered under, and it counts as soon as ANY of them is rejected.
    A task author sizing a distribution should therefore weigh cores;
    [Measure.DISTRIBUTION]'s [w_core_blind] is the obligation that keeps
    a weight from disagreeing with that reading.  [Measure]'s header
    argues why the record-indexed alternative is not merely stricter but
    unprovable. *)

From Stdlib Require Import ZArith NArith List QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import
  Equivalence MustExit FinInput Classifier Measure.
Import ListNotations.
Open Scope bv_scope.

(* =========================================================================
   SPEC_PATCH_CLASSIFY — the baseline flavor
   ========================================================================= *)

(** The whole submission surface, in six declarations.  Each image module
    is turned into an [MemImageType.Image] exactly as [Equivalence.SPEC]
    does it — [mkImage] on the module's three fields — so that the
    statements here are literally the statements those files define, with
    no adapter in between.

    [strong_universal] is the patch obligation and is quantified over ALL
    valid inputs, infinite ones included; only the two classifier
    obligations restrict to finite inputs, and [Classifier]'s header
    argues why that restriction is forced rather than convenient.

    ** What would make the well-formedness requirement a MECHANISM

    Open question, named here because this is where acting on it would
    change something, and left unbuilt on purpose.

    Every obligation below is vacuously satisfiable by an image that
    fails to load: [Classifier]'s header gives the route in full, and
    [Classifier.decides]' own comment records that nothing well-formed
    has been proved to satisfy any of them.  What holds the route shut
    today is that a consuming checker is expected to ascribe
    [Equivalence.IMAGE_WF] for every image it names.  That is a
    CONVENTION.  Nothing in this file requires it, and this module type
    is exactly where the omission is invisible: it takes the six images
    as bare [MemImage] parameters, so a module can ascribe to it having
    proved that none of them loads, and collect [strong_universal]
    (whose [Equivalence.strong_universal_T] quantifies under
    [Run.valid_entry], so an empty entry space satisfies it),
    [classifies_diff], [classifies_good], and both bounds — an entry-less
    classifier accepts everything, which empties the reject set
    [Measure.weight_bound_T] sums over.  [b1] and [b2] are chosen
    values rather than obligations and are free either way.
    [SPEC_PATCH_CLASSIFY_ERROR_FREE] below takes the same six bare
    images and has the same hole; everything here applies to it
    unchanged.

    The mechanism is to take the well-formedness the same way the
    images are taken — as module parameters,
    [(O1wf : Equivalence.IMAGE_WF O1m) .. (C2wf : IMAGE_WF C2m)] — so
    that ascribing either module type is impossible without supplying
    them and the checker has no discipline left to skip.  What that
    costs, and why it is named rather than done: the six proofs have to
    exist before anything can ascribe at all, which is a real obligation
    on a task author and not only on a submission, and it changes both
    module types' arity, which every ascription (for example
    [Examples.patchclassify_demo.Sealed]) has to follow.  Whether the
    trade is right is the open
    question; that the guard is currently a convention is not. *)
Module Type SPEC_PATCH_CLASSIFY
    (O1m P1m O2m P2m C1m C2m : MemImage) (W : DISTRIBUTION).

  (** The two patched binaries are observably equivalent, at every valid
      entry pair and on every valid input. *)
  Parameter strong_universal :
    strong_universal_T
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs).

  (** [C1] decides, on finite inputs, whether BOTH patches preserved
      their original's behavior. *)
  Parameter classifies_diff :
    classifies_patch_diff_T
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs)
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs).

  (** [C2] decides, on finite inputs, whether the two ORIGINALS were
      already error-free equivalent. *)
  Parameter classifies_good :
    classifies_good_inputs_T
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs).

  (** The two bounds, chosen by the submission and read by printing —
      see this file's header. *)
  Parameter b1 b2 : Q.

  (** Neither classifier's fire set weighs more than its stated multiple
      of the declared total, measured by [W] — the fire set being a set
      of CORES, charged once each, per this file's header and
      [Measure.weight_bound_T]. *)
  Parameter bound_diff :
    weight_bound_T
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs) W.w W.M b1.
  Parameter bound_good :
    weight_bound_T
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs) W.w W.M b2.

End SPEC_PATCH_CLASSIFY.

(* =========================================================================
   SPEC_PATCH_CLASSIFY_ERROR_FREE — the error-free flavor
   ========================================================================= *)

(** The same submission surface with the patch obligation replaced by
    [Equivalence.strong_universal_error_free_T]: the two patched binaries
    must additionally never reach the error transition, on any input, at
    any valid entry.

    A SEPARATE module type rather than an extension, for the reason
    [Equivalence.SPEC_ERROR_FREE]'s header gives: the stronger reading is
    unprovable for any binary that can legitimately crash, so a task
    must OPT IN to it.  What a task gets by opting in is not only the
    stronger patch statement but a sharper classifier question — with
    both patches error-free, an input on which [Classifier.agree] fails
    can no longer fail because both sides crashed the same way.  Nothing
    is lost by the substitution:
    [Equivalence.strong_universal_error_free_implies] discharges the
    baseline obligation from this one, so a submission sealed here also
    satisfies [SPEC_PATCH_CLASSIFY] on the same six images.

    The other five declarations are unchanged, deliberately.  The
    classifiers are asked the same questions — [Classifier.good_input] is
    already the error-free comparison of the two originals, whichever
    flavor the patch obligation takes — and the measure layer never sees
    the difference. *)
Module Type SPEC_PATCH_CLASSIFY_ERROR_FREE
    (O1m P1m O2m P2m C1m C2m : MemImage) (W : DISTRIBUTION).

  (** The two patched binaries are error-free AND observably equivalent. *)
  Parameter strong_universal_error_free :
    strong_universal_error_free_T
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs).

  Parameter classifies_diff :
    classifies_patch_diff_T
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs)
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs).

  Parameter classifies_good :
    classifies_good_inputs_T
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs).

  Parameter b1 b2 : Q.

  Parameter bound_diff :
    weight_bound_T
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs) W.w W.M b1.
  Parameter bound_good :
    weight_bound_T
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs) W.w W.M b2.

End SPEC_PATCH_CLASSIFY_ERROR_FREE.

(* =========================================================================
   SPEC_PATCH_CLASSIFY_SCFG — the same surface under a spurious-failure
   configuration
   ========================================================================= *)

(** The six-image surface with the task's configuration
    [Cfg : Equivalence.SPURIOUS_CFG] as a functor argument, exactly as
    [Equivalence.SPEC_SCFG] takes it, and with the two readings the
    classifier layer keeps apart ([Classifier]'s spurious-failure
    section):

    - the patch obligation and the classified properties are under the
      TASK'S configuration ([Equivalence.strong_universal_T_scfg Cfg.cfg],
      [Classifier.classifies_patch_diff_T_s Cfg.cfg],
      [Classifier.classifies_good_inputs_T_s Cfg.cfg]);
    - the two classifiers' OWN runs are pinned to forced-only, for every
      family, whatever [Cfg.cfg] says — the [_fo] inside those two
      definitions, and [Measure.weight_bound_T_fo] for the bounds.

    At [Run.may_fail_cfg] the patch obligation and the classified
    properties are the ones [SPEC_PATCH_CLASSIFY] states
    ([Equivalence.strong_universal_T_scfg_may_fail],
    [Classifier.agree_s_may_fail], [Classifier.good_input_s_may_fail]);
    the classifier pin is what differs, and it is a weakening of the
    verdict obligation ([Classifier.decides_fo_of_decides]).  Everything
    this file's header says — the bounds are read and never compared,
    [Equivalence.IMAGE_WF] for all six images is the checker's job, [W]
    is trusted metadata, the fire set is a set of cores — applies
    unchanged. *)
Module Type SPEC_PATCH_CLASSIFY_SCFG
    (Cfg : SPURIOUS_CFG) (O1m P1m O2m P2m C1m C2m : MemImage) (W : DISTRIBUTION).

  Parameter strong_universal :
    strong_universal_T_scfg Cfg.cfg
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs).

  Parameter classifies_diff :
    classifies_patch_diff_T_s Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs)
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs).

  Parameter classifies_good :
    classifies_good_inputs_T_s Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs).

  Parameter b1 b2 : Q.

  Parameter bound_diff :
    weight_bound_T_fo
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs) W.w W.M b1.
  Parameter bound_good :
    weight_bound_T_fo
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs) W.w W.M b2.

End SPEC_PATCH_CLASSIFY_SCFG.

(** The error-free flavor, with the same substitution
    [SPEC_PATCH_CLASSIFY_ERROR_FREE] makes and the same classifier pin. *)
Module Type SPEC_PATCH_CLASSIFY_SCFG_ERROR_FREE
    (Cfg : SPURIOUS_CFG) (O1m P1m O2m P2m C1m C2m : MemImage) (W : DISTRIBUTION).

  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg Cfg.cfg
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs).

  Parameter classifies_diff :
    classifies_patch_diff_T_s Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs)
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs).

  Parameter classifies_good :
    classifies_good_inputs_T_s Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs).

  Parameter b1 b2 : Q.

  Parameter bound_diff :
    weight_bound_T_fo
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs) W.w W.M b1.
  Parameter bound_good :
    weight_bound_T_fo
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs) W.w W.M b2.

End SPEC_PATCH_CLASSIFY_SCFG_ERROR_FREE.

(* =========================================================================
   The same two surfaces with the CLASSIFIERS' AT_HWCAP word declared
   ========================================================================= *)

(** The classifier binaries take the same vector probe as the binaries
    they classify.  A classifier that reads [vlenb] to learn whether it
    has a vector unit executes, under an advertised V, a word the model
    declines, so its run is [Run.MachineUnmodeled], no
    [MustExit.must_exit_with_scfg] holds of it, and
    [Classifier.decides_fo] is FALSE for it — on every input, whatever
    the classifier would otherwise answer.  The surfaces below are how
    a task with such a classifier states what it can prove: the verdict
    obligations are the declared ones
    ([Classifier.classifies_patch_diff_T_s_hwcap_rv64gc] and its
    siblings), and
    [Classifier.classifies_patch_diff_T_s_hwcap_splits] says the
    undeclared surfaces above are the conjunction of each pair.

    WHAT IS NOT DECLARED HERE, deliberately.  The PATCH obligation
    ([Equivalence.strong_universal_T_scfg]) and the weight bounds are the
    undeclared ones, unchanged: the declaration in these surfaces is
    about the CLASSIFIER'S hart, which is the binary whose probe is at
    issue.  A task whose PATCH pair also probes states that separately,
    through the equivalence layer's own declared cells
    ([Equivalence.SPEC_HWCAP_RV64GC] and the configured abort cell), and
    the day a surface needs both halves declared at once it is written
    the way these are. *)

Module Type SPEC_PATCH_CLASSIFY_SCFG_HWCAP_RV64GC
    (Cfg : SPURIOUS_CFG) (O1m P1m O2m P2m C1m C2m : MemImage) (W : DISTRIBUTION).

  Parameter strong_universal :
    strong_universal_T_scfg Cfg.cfg
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs).

  Parameter classifies_diff :
    classifies_patch_diff_T_s_hwcap_rv64gc Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs)
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs).

  Parameter classifies_good :
    classifies_good_inputs_T_s_hwcap_rv64gc Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs).

  Parameter b1 b2 : Q.

  Parameter bound_diff :
    weight_bound_T_fo
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs) W.w W.M b1.
  Parameter bound_good :
    weight_bound_T_fo
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs) W.w W.M b2.

End SPEC_PATCH_CLASSIFY_SCFG_HWCAP_RV64GC.

Module Type SPEC_PATCH_CLASSIFY_SCFG_HWCAP_RV64GCV
    (Cfg : SPURIOUS_CFG) (O1m P1m O2m P2m C1m C2m : MemImage) (W : DISTRIBUTION).

  Parameter strong_universal :
    strong_universal_T_scfg Cfg.cfg
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs).

  Parameter classifies_diff :
    classifies_patch_diff_T_s_hwcap_rv64gcv Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs)
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs).

  Parameter classifies_good :
    classifies_good_inputs_T_s_hwcap_rv64gcv Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs).

  Parameter b1 b2 : Q.

  Parameter bound_diff :
    weight_bound_T_fo
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs) W.w W.M b1.
  Parameter bound_good :
    weight_bound_T_fo
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs) W.w W.M b2.

End SPEC_PATCH_CLASSIFY_SCFG_HWCAP_RV64GCV.

(** The error-free flavors, the same substitution again. *)
Module Type SPEC_PATCH_CLASSIFY_SCFG_ERROR_FREE_HWCAP_RV64GC
    (Cfg : SPURIOUS_CFG) (O1m P1m O2m P2m C1m C2m : MemImage) (W : DISTRIBUTION).

  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg Cfg.cfg
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs).

  Parameter classifies_diff :
    classifies_patch_diff_T_s_hwcap_rv64gc Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs)
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs).

  Parameter classifies_good :
    classifies_good_inputs_T_s_hwcap_rv64gc Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs).

  Parameter b1 b2 : Q.

  Parameter bound_diff :
    weight_bound_T_fo
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs) W.w W.M b1.
  Parameter bound_good :
    weight_bound_T_fo
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs) W.w W.M b2.

End SPEC_PATCH_CLASSIFY_SCFG_ERROR_FREE_HWCAP_RV64GC.

Module Type SPEC_PATCH_CLASSIFY_SCFG_ERROR_FREE_HWCAP_RV64GCV
    (Cfg : SPURIOUS_CFG) (O1m P1m O2m P2m C1m C2m : MemImage) (W : DISTRIBUTION).

  Parameter strong_universal_error_free :
    strong_universal_error_free_T_scfg Cfg.cfg
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs).

  Parameter classifies_diff :
    classifies_patch_diff_T_s_hwcap_rv64gcv Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage P1m.loaded_segments P1m.init_pc P1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage P2m.loaded_segments P2m.init_pc P2m.phdrs)
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs).

  Parameter classifies_good :
    classifies_good_inputs_T_s_hwcap_rv64gcv Cfg.cfg
      (mkImage O1m.loaded_segments O1m.init_pc O1m.phdrs)
      (mkImage O2m.loaded_segments O2m.init_pc O2m.phdrs)
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs).

  Parameter b1 b2 : Q.

  Parameter bound_diff :
    weight_bound_T_fo
      (mkImage C1m.loaded_segments C1m.init_pc C1m.phdrs) W.w W.M b1.
  Parameter bound_good :
    weight_bound_T_fo
      (mkImage C2m.loaded_segments C2m.init_pc C2m.phdrs) W.w W.M b2.

End SPEC_PATCH_CLASSIFY_SCFG_ERROR_FREE_HWCAP_RV64GCV.
