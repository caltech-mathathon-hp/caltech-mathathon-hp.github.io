# Checking the proof yourself

Install [elan](https://github.com/leanprover/elan), which installs Lean. Then,
in the folder `lean/`:

```sh
lake exe cache get
lake build
lake env lean checks/ShelfHardness.lean
```

The first command downloads compiled Mathlib, about 300 MB. The second compiles
the team's library and ours, which takes a few minutes the first time. Lean and
Mathlib are both `v4.24.0`, fixed by `lean-toolchain` and `lake-manifest.json`;
do not run `lake update`.

## What a successful build means

`lake build` succeeds only if Lean accepts every proof in every file. There is
no `sorry` in the project (a `sorry` is a step left unproved; the build would
print a warning for each one), and no `axiom` of our own.

## What the third command prints

For each main result, its statement and the axioms its proof depends on. The
expected output is in [`checks/publication-axioms.txt`](../checks/publication-axioms.txt).
Two things to look at:

- Every list of axioms is `[propext, Classical.choice, Quot.sound]`. These are
  the three axioms of Lean and Mathlib themselves. `sorryAx` would appear here
  if a proof had a hole anywhere below it.
- The three hardness results have the hypothesis
  `(hCL : ProteinFolding.SAT.CookLevin)` in their statement. This is the
  Cook–Levin theorem, that SAT is NP-hard. It is assumed, not proved, and it is
  the only assumption. It is a hypothesis and not an axiom, so the list of
  axioms does not show it: read the statement.

`lake env lean checks/Axioms.lean` prints the axioms of every lemma of the
paper, 53 results in all.

## What is not checked here

That the Lean statements say what the paper's theorems say is for a person to
read. The statements are short: `HPStringFoldNPComplete` and
`PerfectHPStringFoldNPComplete`, in the team's file
`vendor/protein_folding/ProteinFolding/Cubic/MainTheorem.lean`, with the
definitions they use. [model.md](model.md) says where these are.
