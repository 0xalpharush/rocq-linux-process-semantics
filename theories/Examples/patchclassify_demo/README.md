# patchclassify_demo: an instance of the patch-classifier statement

[`theories/EquivalenceDefinition/PatchClassifySpec.v`](../../EquivalenceDefinition/PatchClassifySpec.v)
states what a patch with two classifiers must prove. There are six images:
two original programs, their two patched versions, and two classifier
programs. There are five obligations: the two patched programs are
equivalent, each classifier decides its question on every input, and the
inputs that each classifier rejects have a bounded weight.

This directory proves all five obligations for the smallest possible case.
Read it if you must use `PatchClassifySpec.v` and want an example that you
can read in full. It uses no compiled binaries and no generated files. Each
image is three instructions, written by hand.

## The images

There are two programs:

- **exit 0**: `addi a7, x0, 93; addi a0, x0, 0; ecall`
- **exit 1**: the same, with `addi a0, x0, 1`

| Image | Program | Role |
| --- | --- | --- |
| `O1m` | exit 1 | first original program: the defect is that it always reports failure |
| `O2m` | exit 0 | second original program, already correct |
| `P1m` | exit 0 | patch of `O1m`: the defect is repaired |
| `P2m` | exit 0 | patch of `O2m`: no change |
| `C1m` | exit 1 | classifier for "the patch changes the behavior" |
| `C2m` | exit 1 | classifier for "the input is good" |

Both classifiers reject every input, and this is the correct answer. `O1m`
and `P1m` differ on every input, so the first classifier must reject every
input. `O1m` and `O2m` also differ on every input, so no input is good.

## Files

Read the files in this order:

| File | Contents |
| --- | --- |
| `Images.v` | The six images, and their `IMAGE_WF` checks. |
| `Verdicts.v` | The exit status of each image, for every launch and every input. |
| `Traces.v` | The trace set of each image: exactly `{[], [ExitEv c fs]}`. |
| `Distribution.v` | `DemoDist`, a geometric distribution on the length of standard input. |
| `Obligations.v` | The five obligations, and the checks that they are not vacuous. |
| `Sealed.v` | The ascriptions to `IMAGE_WF`, `SPEC_PATCH_CLASSIFY` and its error-free form. |

To build the directory:

```sh
dune build theories/Examples/patchclassify_demo
```

## The main lemma

The obligations are about every valid launch and every valid input. One
computation settles one run only. The main lemma,
`Verdicts.must_exit_everywhere_of_exits_c`, solves this problem. It applies
to a program that gets to its exit with the stack pointer, the writable
memory and the read-only memory left as variables. For such a program, the
exit status is the same for every launch and every input. One `vm_compute`
per program proves the premise. If a program read the stack pointer or the
input, the computation would stop on a variable, and the premise would not
be provable.

`Traces.v` uses the same method to get the full trace set of each image.

## What is degenerate

- Both classifiers reject every input.
- Both weight bounds are `b = 1`. The whole-space certificate of
  `MeasureLib` proves them.
- The two original programs are never equivalent, so the set of good
  inputs is empty.

`Obligations.v` shows that these results are not vacuous. An image with no
valid launch would satisfy the classifier obligations and the bounds with
no content (`Classifier.decides_vacuous_no_entries`). Thus the demo shows a
valid launch for each image, names inputs that each classifier rejects, and
shows that a distribution with weight 1 per input breaks the bound.

The lemmas `demo_b_zero_refutable` and `demo_b_half_refutable` show that the
bound is false for `b = 0` and `b = 1/2`. The demo does not show the least
`b`.

## What this demo does not show

The programs do not read their input. Thus the demo does not show:

- behavior that depends on the input,
- a classifier that rejects only some inputs,
- a non-trivial use of the distribution,
- a program that crashes,
- a compiled binary.

A program that reads its input needs a different proof method: a
simulation that relates the reads of the program to the input stream. The
other examples in `theories/Examples/` use that method.

## Two problems that you can avoid

- **`discriminate` without a name can hang.** Without a name,
  `discriminate` examines every hypothesis. A `Qeq` hypothesis about a
  `MeasureLib` witness can make it list all inputs below a length (about
  10^12 at length 6). Give the name: `discriminate Hb`.
- **An image with one segment fails `image_phdrs_readable`.** The program
  header table must be in a readable loaded segment. Thus each image here
  has a second, read-only segment for the table.
  `Images.phdrs_readable_needs_the_table` shows that the check fails
  without it.
