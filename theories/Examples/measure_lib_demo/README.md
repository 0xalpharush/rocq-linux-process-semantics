# measure_lib_demo: one instance of each MeasureLib combinator

This directory is not an equivalence proof. It has no binaries and no
snapshots. It shows how to use each combinator of
[`theories/EquivalenceDefinition/MeasureLib.v`](../../EquivalenceDefinition/MeasureLib.v)
to get a `Measure.weight_bound_T` statement.

Read it if you must prove a bound on the weight of the inputs that a
classifier rejects.

## Files

| File | Combinator |
| --- | --- |
| `NaryMixture.v` | `cd_mix` (a mixture of several distributions) |
| `StdinGeometric.v` | `stdin_geometric` (a geometric law on the length of standard input) |
| `EnvpGeometric.v` | `stdin_envp_geometric` |
| `FileGeometric.v` | `file_geometric`, `file_geometric_argv1` |
| `FileEnvpGeometric.v` | `file_envp_geometric`, `file_envp_geometric_argv1` |
| `FileGeometricPrefix.v` | `file_geometric_prefix`, `file_geometric_prefix_argv1` |
| `FileGeometricPrefixOver.v` | `file_geometric_prefix_over`, `file_geometric_prefix_over_argv1` |
| `FullSupportBase.v` | `full_support_base`, and the mixture of a structured distribution with it |
| `Calibrated.v` | `calibrated_mixture`, `cd_scale`, `cd_mix2` |

`MeasureLib.v` itself ends with a worked example of `finite_support`,
`cd_scale`, `cd_mix2` and `stdin_geometric`.

## What each file does

Each file does the same four steps:

1. It builds a distribution `(w, M)` with the combinator, at fixed numeric
   parameters. Named lemmas prove the side conditions of the parameters.
2. It ascribes a module to `Measure.DISTRIBUTION`. The library lemmas
   `cd_lift_nonneg` and `cd_lift_core_blind` prove the two obligations.
3. It proves a bound on a partial sum, as an exact rational number, and
   gets `Measure.weight_bound_T` from it. The classifier is used at one
   place only: the hypothesis that a rejected input has a "fire core".
4. It shows that the bound is not vacuous. Either the bound is attained,
   or the file names the gap. Also, an input outside the fire set breaks
   the bound, or an input with a different environment has weight zero.

The files do not show that an input is valid, and they do not show that a
classifier rejects an input. A real task must prove that its classifier
rejects only inputs in the fire set. Thus each `*_weight_bound_T_of` lemma
takes this fact as a hypothesis.

## Add a file

Copy the file with the nearest combinator. Change the `*_demo_*` prefix and
the parameters. You do not need to change a list or a dune file. Build the
file:

```sh
dune build theories/Examples/measure_lib_demo/<Name>.vo
```
