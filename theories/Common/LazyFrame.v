(** * Common.LazyFrame — silent steps through a NON-EMPTY lazy ledger

    TRUST BOUNDARY: image-INDEPENDENT proof library (like
    [Common.DivergeSim], which this file extends).

    WHY THIS EXISTS.  Every silent-step idiom in the simulation library
    ([ShapeAlg.node_instr], [DivergeSim.ts_spin_no_lazy], the [msteps]
    combinators) carries the hypothesis [m_vm_lazy model = []]: with an
    empty lazy ledger the accounting layer erases and a raw
    [RiscvSemantics.step] equality is all a proof needs.  An ASan-style
    binary leaves that regime PERMANENTLY at its first successful
    MAP_NORESERVE reservation, and this file supplies the replacement:
    an instruction whose access report is DISJOINT from every lazy range
    materializes nothing, so the accounted step still preserves the
    model exactly ([materialize_model_accesses_disjoint], the common
    generalization of [State.materialize_model_accesses_no_lazy] and
    [DivergeSim.materialize_model_accesses_nil] — both are its vacuous
    instances), and the [to_spin] smart-constructor family gains the
    disjoint spellings ([ts_spin_disjoint] /
    [ts_step_disjoint]).

    DOES AN ASAN-STYLE MAP_NORESERVE RESERVATION FORCE A NON-EMPTY
    [m_vm_lazy] UNDER THIS SPEC?  YES — with file/line evidence:

    - [Sys/Mm/Mmap.v:323] defines [MAP_NORESERVE = 16384 (0x4000)];
      [Mmap.v:335-336] ([mmap_flags_core]) masks exactly that bit out
      before the anonymous shape is matched, so the ASan reservation
      shape (PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS|
      MAP_NORESERVE, fd -1, off 0) IS the modeled shape
      ([mmap_modeled_b], Mmap.v:796-799), and [Mmap.v:338-339]
      ([mmap_noreserve_b]) reads the bit back at the one place it
      changes an answer.
    - The modeled grant applies [with_mmap_backing flags a n]
      ([Mmap.v:944] in [mmap_spec]'s rw branch; [Mmap.v:963-964] in the
      PROT_NONE branch; [Mmap.v:1138]/[Mmap.v:1288-1289] in the two
      MAP_FIXED branches), and [with_mmap_backing] ([Mmap.v:341-342])
      is [vm_add_lazy a n] whenever the bit is set.
    - [vm_add_lazy] ([State.v:2316-2317]) prepends
      [lazy_interior a n] to [m_vm_lazy]; [lazy_interior]
      ([State.v:2307-2314]) is the page-aligned interior, and a modeled
      grant is page-aligned with a page-rounded nonzero length
      ([Mmap.v:936-942]: [a mod page_size = 0], [0 < a],
      [nZ = page_round_up_Z len] with [len <> 0]), so
      [lazy_interior a n = [(a, n)]] — NON-EMPTY.
    - The entry persists until the range is unmapped or replaced
      ([vm_forget_range], [State.v:2237-2240]); an ordinary
      instruction step frames it ([Run.mi_account_step_model_frame],
      [Run.v:308-316]).
    - The reservation is also granted REGARDLESS of the remaining
      backed-memory budget ([mmap_noreserve_backed_ok],
      [Mmap.v:873-876], is unconditionally [true] for a NORESERVE
      call): the budget is charged per page on first touch, by
      [materialize_model_accesses] inside [mi_account_step]
      ([Run.v:277-287]).

    CONSEQUENCE FOR PROOFS.  After the shadow reservation succeeds, the
    no-lazy idiom is unavailable for the REST OF THE RUN on the grant
    path.  The constructor real proofs need there is the DISJOINT one:
    ASan's spin loop itself is access-free ([ts_spin_no_access] covers
    it with no hypothesis), but the straight line INTO the spin — and
    every ordinary load/store between the reservation and the program's
    other syscalls — needs [ts_step_disjoint] (its accesses land in the
    binary's data/stack segments, disjoint from the shadow reservation
    by the placement gate [grant_ok]'s region-freeness).  On the
    REFUSAL path of the reservation itself the ledger is still empty
    ([m_vm_lazy = []] before the first NORESERVE grant), so the
    no-lazy spellings — and [SpinAlg.srz_mmap_spin]'s hypotheses —
    apply as-is.

    The hypothesis shape: per access/range pair, the access does not
    wrap 2^64 (its page cursor is computed in [Z], [State.v:2110-2116])
    and its byte range is disjoint from the lazy range's byte range —
    the same [Z]-over-[bv_unsigned] discipline as every other bound in
    the spec ([BvBase]'s second rule).  When either list is empty the
    hypothesis is vacuous, which is exactly how the two existing lemmas
    fall out as instances. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import DivergeSim.
Import ListNotations.
Open Scope bv_scope.

(* ================================================================= *)
(* The disjointness hypothesis                                        *)
(* ================================================================= *)

(** Access [a, a + n) does not wrap and is disjoint from the byte range
    [lo, lo + sz).  The no-wrap conjunct is what ties the page cursor's
    unwrapped [Z] arithmetic back to the page's [word] base; every real
    access report satisfies it trivially (reported lengths are a few
    bytes and [alloc_ceiling] sits far below 2^64). *)
Definition access_outside_range (a : word) (n : nat) (lo sz : word) : Prop :=
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z /\
  (bv_unsigned a + Z.of_nat n <= bv_unsigned lo
   \/ bv_unsigned lo + bv_unsigned sz <= bv_unsigned a)%Z.

(** Every reported access is outside every lazy range.  Vacuously true
    when either list is empty. *)
Definition accesses_outside_lazy
    (accs : list (word * nat)) (lazy : list (word * word)) : Prop :=
  forall a n lo sz, In (a, n) accs -> In (lo, sz) lazy ->
    access_outside_range a n lo sz.

(* ================================================================= *)
(* Plumbing                                                           *)
(* ================================================================= *)

Lemma filter_all_false {A} : forall (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) -> List.filter f l = [].
Proof.
  intros f l H; induction l as [|x l IH]; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)).
  apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(** Rebuilding a model from its own backing ledgers is the identity. *)
Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim tm]. reflexivity.
Qed.

Lemma materialize_accesses_no_new : forall lazy materialized used limit accs,
  newly_materialized_pages lazy materialized accs = [] ->
  materialize_accesses lazy materialized used limit accs = Some materialized.
Proof.
  intros lazy materialized used limit accs Hnew.
  unfold materialize_accesses. rewrite Hnew. reflexivity.
Qed.

(* ================================================================= *)
(* Which pages an access report can name                              *)
(* ================================================================= *)

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.

(** Every page the cursor inserts is the page of some byte offset
    [k < n] past [base] (in unwrapped [Z], matching the cursor). *)
Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages];
    intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin)
        as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k.
        split; [left; reflexivity | split; assumption].
    + right. exists a', n', k.
      split; [right; exact Hin | split; assumption].
Qed.

(** The page of a byte inside a disjoint, non-wrapping access is not
    wholly contained in any of the lazy ranges. *)
Lemma page_in_ranges_outside : forall lazy (a : word) (n k : nat),
  (k < n)%nat ->
  (forall lo sz, In (lo, sz) lazy -> access_outside_range a n lo sz) ->
  page_in_ranges (page_base_of (bv_unsigned a + Z.of_nat k)) lazy = false.
Proof.
  intros lazy a n k Hk Hout.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  apply Bool.not_true_is_false. intro Htrue.
  unfold page_in_ranges in Htrue.
  apply existsb_exists in Htrue.
  destruct Htrue as ([lo sz] & Hin & Htest).
  cbn [fst snd] in Htest.
  apply andb_true_iff in Htest. destruct Htest as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct (Hout lo sz Hin) as [Hnw Hdisj].
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  pose proof (bv_unsigned_in_range 64 lo) as Hlo_rg.
  pose proof (bv_unsigned_in_range 64 sz) as Hsz_rg.
  assert (Hz0 : (0 <= z)%Z) by (unfold z; lia).
  (* the page base, unwrapped *)
  assert (Hq0 : (0 <= z / page_size)%Z)
    by (apply Z.div_pos; [exact Hz0 | unfold page_size; lia]).
  pose proof (Z.div_mod z page_size
                ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound z page_size
                ltac:(unfold page_size; lia)) as Hmb.
  assert (Hpb : bv_unsigned (page_base_of z)
                = ((z / page_size) * page_size)%Z).
  { unfold page_base_of. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64)%Z.
    unfold page_size in *. unfold z in *. lia. }
  rewrite Hpb in Hlo, Hhi.
  (* [z] sits inside its own page, and inside the access *)
  unfold page_size in *. unfold z in *. lia.
Qed.

(* ================================================================= *)
(* The idempotence theorem and its accounted-step corollaries         *)
(* ================================================================= *)

(** Accesses disjoint from every lazy range materialize nothing: the
    accounting layer is the identity on the model.  The common
    generalization of [State.materialize_model_accesses_no_lazy]
    (take [m_vm_lazy m = []]: the hypothesis is vacuous) and of
    [DivergeSim.materialize_model_accesses_nil] (take [accs = []]:
    ditto). *)
Theorem materialize_model_accesses_disjoint : forall m accs,
  accesses_outside_lazy accs (m_vm_lazy m) ->
  materialize_model_accesses m accs = Some m.
Proof.
  intros m accs Hout.
  assert (Hnew : newly_materialized_pages
                   (m_vm_lazy m) (m_vm_materialized m) accs = []).
  { unfold newly_materialized_pages. apply filter_all_false.
    intros p Hp.
    destruct (accesses_pages_in accs [] p Hp)
      as [[] | (a & n & k & Hin & Hk & ->)].
    rewrite (page_in_ranges_outside (m_vm_lazy m) a n k Hk).
    - reflexivity.
    - intros lo sz Hlz. exact (Hout a n lo sz Hin Hlz). }
  unfold materialize_model_accesses.
  rewrite (materialize_accesses_no_new (m_vm_lazy m) (m_vm_materialized m)
             (vm_backing_used m) (vm_limit (m_vmmaps m)) accs Hnew).
  cbv iota beta.
  rewrite with_vm_backing_id. reflexivity.
Qed.

(** An instruction whose access report is disjoint from every lazy
    range steps the machine and leaves the model alone — whatever the
    ledger holds. *)
Lemma mi_account_step_disjoint : forall segs ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros segs ms model ms' ranges Hstep Hout.
  rewrite (mi_account_step_of_accesses segs ms model ms' ranges Hstep).
  rewrite (materialize_model_accesses_disjoint model ranges Hout).
  reflexivity.
Qed.

(* ================================================================= *)
(* The disjoint smart constructors for DivergeSim's Layer 2           *)
(* ================================================================= *)

(** The one-step fixpoint, entered on an instruction with a disjoint
    (rather than empty) access report. *)
Lemma ts_spin_disjoint : forall segs ms model ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  to_spin segs ms model.
Proof.
  intros segs ms model ranges Hsvc Hstep Hout.
  apply ts_spin; [exact Hsvc|].
  exact (mi_account_step_disjoint segs ms model ms ranges Hstep Hout).
Qed.

(** A straight-line step INTO a spin, through a load/store whose
    accesses avoid the lazy ledger — the constructor the ASan grant
    path needs, where [m_vm_lazy] is permanently non-empty and
    [ts_step_no_lazy] is unavailable. *)
Lemma ts_step_disjoint : forall segs ms model ms' ranges,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  to_spin segs ms' model ->
  to_spin segs ms model.
Proof.
  intros segs ms model ms' ranges Hsvc Hstep Hout Hspin.
  exact (ts_step segs ms model ms' model Hsvc
           (mi_account_step_disjoint segs ms model ms' ranges Hstep Hout)
           Hspin).
Qed.
