(* Written by the OSS-Fuzz proof collaborators. *)
(** * Common.LiaFast — build-time hygiene for [lia]/[nia] in large proof contexts.

    WHY.  A symbolic-execution proof context holds hundreds of memory facts
    ([rdn .. = Some ..], [cell], register equations, [Forall] over images)
    that arithmetic can never use, and stdpp's [bitvector.tactics] (loaded
    through the process model) turns on
    [Zify.zify_convert_to_euclidean_division_equations_flag], so every [lia]
    also abstracts every [/] and [mod] it can see anywhere in the context.
    This preprocessing can take most of a file's compile time.

    WHAT (all OPT-IN; nothing here changes the meaning of [lia] for a file
    that merely [Require]s this module):

    - [lia_mod] / [nia_mod]: [lia]/[nia] with the euclidean-division
      preprocessing forced on ([Z.to_euclidean_division_equations] first) —
      for the few goals that need a division fact in a file that switched the
      flag off.
    - [prune_arith_ctx]: ONE Ltac2 [Std.keep] of the hypotheses whose
      statement is built from [/\ \/ ~ <-> ->] over arithmetic atoms
      ([=] at Z/nat/N/positive/bool, orders on Z/nat/N, [Z.divide], [True],
      [False]) plus let-bound definitions; everything else goes, together with
      the variables only it mentioned.  [alia] := prune, then [lia];
      [ania] := prune, then [nia].  Use them only where the arithmetic call is
      TERMINAL for the goal.
    - [flia_prune1]: a single-pass pruner (visits every hypothesis
      once, [clear]s the non-arithmetic ones, never touches a kept one, so the
      proof term references exactly what [lia] would reference — see the
      capture note below); [flia_lin]: for goals WITHOUT div/mod, also drops
      every hypothesis mentioning them and skips the euclidean pass entirely;
      [flia_full1]: full [lia] in the pruned context; [flia2] := linear
      attempt first, then full — proves everything std [lia] proves from the
      kept hypotheses, usually much cheaper; [flia1]: the two-stage variant
      that drops [_ mod _ = 0] facts unless the goal mentions mod/div.
    - [clia]: the closed-goal shortcut — a goal that mentions no variable is
      first tried in the EMPTY context (no hypothesis preprocessing at all),
      then as plain [lia]; a goal with a variable takes the plain path
      directly.  [zlit]: closed literal (in)equalities decided by
      [vm_compute], never by zify.  [plia] := [zlit] else [alia].
    - [solve_BvWf_fast]: the well-formedness side goal [BvWf n z] of a
      bit-vector literal ([(10 : reg)], [3%bv]) decided by [vm_compute]
      directly when both arguments are closed, in place of stdpp's
      [solve_BvWf] whose [is_closed_term] clears the whole context one
      hypothesis at a time (0.1-0.5 s per literal in a big-context walk).
      Same proof term.  Registered with [#[export]] at cost 9 (stdpp's is 10),
      so it is active exactly in the files that [Import] this module.

    HOW TO OPT IN (per file, after its last [Require].  A NON-[Local]
    [Ltac x ::= ...] takes effect in every file that merely [Require]s the
    module, and lia variants are NOT capture-neutral inside Sections — the
    hypotheses a lemma ends up depending on are the ones the certificate
    used — so any rebinding MUST be [Local]):

        From LinuxProcessSemantics.Common Require Import LiaFast.
        Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
        Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        (* and, if a file's div/mod goals are only over literal divisors: *)
        Local Ltac Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup ::= idtac.

    After converting a file, recompile its importers: a lemma proved with a
    pruning variant may reference a different set of Section hypotheses than
    before.  If a file's lemmas are applied with explicit argument lists
    elsewhere, leave that file alone or fix the importers.

    Depends on Stdlib + Ltac2 + [BvBase] (for [BvWf]) only. *)

From Stdlib Require Import ZArith NArith Lia.
From Stdlib Require Import PreOmega.
From Ltac2 Require Ltac2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.

(* ------------------------------------------------------------------------- *)
(** ** Division facts on demand                                                *)
(* ------------------------------------------------------------------------- *)

(** [lia] with the division/modulo pre-processing forced on. *)
Ltac lia_mod := Z.to_euclidean_division_equations; lia.

(** [nia] likewise. *)
Ltac nia_mod := Z.to_euclidean_division_equations; nia.

(* ------------------------------------------------------------------------- *)
(** ** Context pruners (Ltac2; the module keeps Ltac2's proof mode local)      *)
(* ------------------------------------------------------------------------- *)

Module LiaFastL2.
  Import Ltac2.

  (** The [prune_arith_ctx] shape test: a statement built from connectives over
      arithmetic atoms. *)
  Ltac2 rec arith_prop (ty : constr) : bool :=
    lazy_match! ty with
    | ?a /\ ?b => Bool.and (arith_prop a) (arith_prop b)
    | ?a \/ ?b => Bool.and (arith_prop a) (arith_prop b)
    | ?a <-> ?b => Bool.and (arith_prop a) (arith_prop b)
    | ~ ?a => arith_prop a
    | ?a -> ?b => Bool.and (arith_prop a) (arith_prop b)
    | True => true
    | False => true
    | @eq Z _ _ => true
    | @eq nat _ _ => true
    | @eq N _ _ => true
    | @eq positive _ _ => true
    | @eq bool _ _ => true
    | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
    | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
    | N.le _ _ => true | N.lt _ _ => true | N.ge _ _ => true | N.gt _ _ => true
    | Z.divide _ _ => true
    | _ => false
    end.

  Ltac2 arith_hyp (h : ident * constr option * constr) : bool :=
    let (_, body, ty) := h in
    match body with
    | Some _ => true                        (* keep let-definitions (zify knows them) *)
    | None => arith_prop ty
    end.

  (** ONE [Std.keep] (= [clear - ..]) of the arithmetic hypotheses; the
      variables they and the goal depend on stay automatically. *)
  Ltac2 prune_arith_ctx1 () :=
    let hs := Control.hyps () in
    let ids := List.map (fun (h : ident * constr option * constr) => let (id, _, _) := h in id)
                 (List.filter arith_hyp hs) in
    Std.keep ids.

  (** per goal (the Ltac1 callers may hand us several goals, e.g. [rewrite .. by ..]) *)
  Ltac2 prune_arith_ctx0 () := Control.enter prune_arith_ctx1.

  (** The [prune] shape test (kept whole conjunctions, bare sort hypotheses). *)
  Ltac2 is_arith (t : constr) : bool :=
    lazy_match! t with
    | _ /\ _ => true | _ <-> _ => true | _ = _ => true | _ <> _ => true | ~ _ => true
    | Z.le _ _ => true | Z.lt _ _ => true | Z.ge _ _ => true | Z.gt _ _ => true
    | le _ _ => true | lt _ _ => true | ge _ _ => true | gt _ _ => true
    | N.le _ _ => true | N.lt _ _ => true | Pos.le _ _ => true | Pos.lt _ _ => true
    | _ \/ _ => true
    | Z => true | nat => true | N => true | positive => true
    | _ => false
    end.

  (** Single pass, last hypothesis first: [clear] every non-arithmetic
      hypothesis; one a kept hypothesis depends on simply stays (its [clear]
      fails, cheaply).  Kept hypotheses are never touched, so the proof term
      references exactly what std [lia] would reference (capture-neutral
      inside Sections — a revert/intro formulation is NOT). *)
  Ltac2 prune () :=
    List.iter (fun h => match h with (id, _, ty) =>
                 if is_arith ty then () else
                 match Control.case (fun () => Std.clear [id]) with
                 | Val _ => () | Err _ => () end end)
              (List.rev (Control.hyps ())).
End LiaFastL2.

Ltac prune_arith_ctx := ltac2:(LiaFastL2.prune_arith_ctx0 ()).
Ltac alia := prune_arith_ctx; lia.
Ltac ania := prune_arith_ctx; nia.

Ltac flia_prune1 := ltac2:(Ltac2.Control.enter LiaFastL2.prune).
Ltac flia_clear_mod0 := repeat match goal with H : (_ mod _ = 0)%Z |- _ => clear H end.

(** the two-stage variant: try WITHOUT the [_ mod _ = 0] facts, then with them —
    but only when the GOAL itself mentions mod/div (every other
    first-attempt failure is a genuinely false goal used as a test inside
    [first [lia | ..]], and those must fail FAST). Refers to zify/xlia directly
    so that a [Local Ltac lia ::= flia1] rebinding does not loop. *)
Ltac flia1 :=
  flia_prune1;
  first [ solve [flia_clear_mod0; Zify.zify; xlia zchecker]
        | lazymatch goal with
          | |- context [Z.modulo _ _] => Zify.zify; xlia zchecker
          | |- context [Z.div _ _] => Zify.zify; xlia zchecker
          end ].

(** linear attempt: only for goals without div/mod; drops every hypothesis
    mentioning div/mod so the euclidean pass has nothing to do *)
Ltac flia_lin :=
  lazymatch goal with
  | |- context [Z.modulo _ _] => fail
  | |- context [Z.div _ _] => fail
  | _ => flia_prune1;
         repeat match goal with
                | H : context [Z.modulo _ _] |- _ => clear H
                | H : context [Z.div _ _] |- _ => clear H
                end;
         Zify.zify; xlia zchecker
  end.

(** FULL [lia] in the single-pass-pruned context. *)
Ltac flia_full1 := flia_prune1; Zify.zify; xlia zchecker.

(** [flia2]: linear attempt, then full — so, unlike [flia1], a goal that needs a
    [_ mod _ = 0] hypothesis without mentioning mod itself still goes through. *)
Ltac flia2 := first [ solve [flia_lin] | flia_full1 ].

(* ------------------------------------------------------------------------- *)
(** ** Closed goals                                                            *)
(* ------------------------------------------------------------------------- *)

Ltac lia_closed_has_var :=
  match goal with |- ?G => match G with context [?x] => is_var x end end.
Ltac lia_clear_all := repeat match goal with H : _ |- _ => clear H end.

(** [clia]: a variable-free goal is first tried in the empty context (no
    hypothesis is preprocessed); if that fails (a closed goal provable only
    from contradictory hypotheses) the plain call runs unchanged; an open goal
    takes the plain path directly — exactly the same goals are proved. *)
Ltac clia :=
  tryif lia_closed_has_var then (Zify.zify; xlia zchecker)
  else first [ solve [lia_clear_all; Zify.zify; xlia zchecker]
             | Zify.zify; xlia zchecker ].

Ltac cnia :=
  tryif lia_closed_has_var then (Zify.zify; xnia zchecker)
  else first [ solve [lia_clear_all; Zify.zify; xnia zchecker]
             | Zify.zify; xnia zchecker ].

(** closed arithmetic literals: decided by computation, no zify *)
Ltac is_zlit t :=
  lazymatch t with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | Z.pow ?a ?b => is_zlit a; is_zlit b
  | Z.add ?a ?b => is_zlit a; is_zlit b
  | Z.sub ?a ?b => is_zlit a; is_zlit b
  | Z.mul ?a ?b => is_zlit a; is_zlit b
  | Z.opp ?a => is_zlit a
  | Z.of_nat ?n => is_nlit n
  end
with is_nlit t :=
  lazymatch t with
  | O => idtac | S ?n => is_nlit n
  | Nat.add ?a ?b => is_nlit a; is_nlit b
  end.

Ltac zlit :=
  lazymatch goal with
  | |- ?a /\ ?b => split; zlit
  | |- (?a <= ?b)%Z => is_zlit a; is_zlit b; apply (proj1 (Z.leb_le a b)); vm_compute; reflexivity
  | |- (?a < ?b)%Z => is_zlit a; is_zlit b; apply (proj1 (Z.ltb_lt a b)); vm_compute; reflexivity
  | |- (?a <= ?b)%nat => is_nlit a; is_nlit b; apply (proj1 (PeanoNat.Nat.leb_le a b)); vm_compute; reflexivity
  | |- (?a < ?b)%nat => is_nlit a; is_nlit b; apply (proj1 (PeanoNat.Nat.ltb_lt a b)); vm_compute; reflexivity
  | |- @eq Z ?a ?b => first [is_zlit a; is_zlit b; vm_compute; reflexivity | ring]
  end.

(** [plia]: closed literals by computation, everything else pruned then [lia]. *)
Ltac plia := first [ zlit | alia ].

(* ------------------------------------------------------------------------- *)
(** ** Bit-vector literal well-formedness                                     *)
(* ------------------------------------------------------------------------- *)

Ltac bvwf_has_var t := match t with context [?x] => is_var x end.
Ltac solve_BvWf_fast :=
  lazymatch goal with
  | |- BvWf ?n ?v =>
      tryif bvwf_has_var v then fail else
      tryif bvwf_has_var n then fail else
      tryif has_evar v then fail else
      tryif has_evar n then fail else
      (vm_compute; exact I)
  end.
#[export] Hint Extern 9 (BvWf _ _) => solve_BvWf_fast : typeclass_instances.

(* ------------------------------------------------------------------------- *)
(** ** Self-tests (compiled with the file; they double as usage examples)      *)
(* ------------------------------------------------------------------------- *)

Module LiaFastSelfTest.
  Local Open Scope Z_scope.

  Goal forall (x y : Z) (l : list Z) (b : bool),
    length l = 3%nat -> b = true -> 0 <= x -> x < y -> x < y + 1.
  Proof. intros. alia. Qed.

  Goal forall (x y : Z) (l : list Z), length l = 3%nat -> 0 <= x -> x < y -> x * x < y * y.
  Proof. intros. ania. Qed.

  Goal forall x : Z, 0 <= x -> x mod 4 = 0 -> exists q, x = 4 * q.
  Proof. intros x Hx Hm. exists (x / 4). lia_mod. Qed.

  (* the mod fact is needed although the goal does not mention mod: flia2 goes through, flia_lin alone would not *)
  Goal forall (x : Z) (l : list Z), length l = 2%nat -> 5 <= x -> x mod 8 = 0 -> 8 <= x.
  Proof. intros. flia2. Qed.

  Goal forall (x : Z) (l : list Z), length l = 2%nat -> 5 <= x -> x < 7 -> x <= 6.
  Proof. intros. flia_lin. Qed.

  Goal forall (x : Z), 5 <= x -> x mod 8 = 0 -> x / 8 >= 1.
  Proof. intros. flia1. Qed.

  Goal (2 ^ 17 + 20 <= 2 ^ 64)%Z /\ (5 < 41)%nat.
  Proof. zlit. Qed.

  Goal forall (x : Z) (H : x = 3), (1 <= 8)%Z.
  Proof. intros. clia. Qed.

  Goal forall (x : Z) (H : x = 3), (1 <= x)%Z.
  Proof. intros. clia. Qed.

  Goal forall (x : Z), 0 <= x -> (0 <= 118464 < 2 ^ 64)%Z.
  Proof. intros. plia. Qed.

  Goal BvWf 64%N 3%Z.
  Proof. solve_BvWf_fast. Qed.

  Goal BvWf 8%N 255%Z.
  Proof. typeclasses eauto. Qed.
End LiaFastSelfTest.
