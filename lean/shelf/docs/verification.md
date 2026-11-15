# Checking the proof yourself

Install [elan](https://github.com/leanprover/elan), which installs Lean. Then,
in this project's folder, the one with `lakefile.toml`:

```sh
lake exe cache get
lake build
lake env lean checks/ShelfHardness.lean
```

The first command downloads compiled Mathlib, about 300 MB. The second compiles
the team's library and ours, 369 files. The first time this is about 33 minutes
of work shared among the processor's cores: 5 minutes on a laptop with 16
cores. Lean and Mathlib are both `v4.24.0`, fixed by `lean-toolchain` and
`lake-manifest.json`; do not run `lake update`.

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
- The final theorems come right after the three statements, and they have no
  hypothesis: the name is followed at once by the colon and the statement, as in
  `ProteinFolding.Shelf.Unconditional.hpStringFold_NPComplete : ProteinFolding.HPStringFoldNPComplete`.
  A hypothesis would stand in parentheses before the colon. A hypothesis is not an
  axiom, so the list of axioms would not show it: read the statement.

Further down the same results appear once more with
`(hCL : ProteinFolding.SAT.CookLevin)` before the colon. That is the step
before, where the Cook–Levin theorem, that SAT is NP-hard, is a hypothesis.
The line `ProteinFolding.SAT.CookLevinUniversal.cookLevin : ProteinFolding.SAT.CookLevin`
is the team's proof of it, and each final theorem is the result with the
hypothesis, applied to that proof.

`lake env lean checks/Axioms.lean` prints the axioms of every lemma of our
write-up, of the Cook–Levin theorem and of the final theorems, 59 results in
all. For a long name Lean breaks the list of axioms over three lines.

## The website's examples

The website folds the string of this project for a few small instances and says
how large each cube is: two bins of size 2 give `n = 42` and 74,088 letters `H`,
one bin of size 2 gives `n = 16`.

```sh
lake env lean checks/SmallInstances.lean
```

computes from the Lean definition of the reduction the side of the cube and the
number of `H`'s for the seven examples of the website's 3D view, and compares
them with the website's numbers. It prints nothing when they agree, and an error
for each one that does not. This is a computation and not a proof.

On 14 November 2026 we also compared the strings themselves, letter by letter:
the ones the website's script writes for its seven examples against
`Shelf.shelfReduction`. For the four examples with an odd number of bins, or
with items all of one size, the two strings are identical. For the other three
the number of bins is even, so the reduction adds one item of size `B`. Lean
puts it first in the list of items and the website puts it last, and with the
item moved to the end Lean's string is again identical to the website's.
Theorems 12 and 16 are proved for the items in any order, so they hold for both
strings.

## What is not checked here

That the Lean statements say what the theorems on the website say is for a
person to read. The statements are short: `HPStringFoldNPComplete` and
`PerfectHPStringFoldNPComplete`, in the team's file
`vendor/protein_folding/ProteinFolding/Cubic/MainTheorem.lean`, with the
definitions they use. [model.md](model.md) says where these are.
