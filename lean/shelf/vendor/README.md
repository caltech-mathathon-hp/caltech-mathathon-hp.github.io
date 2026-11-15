# Code copied from elsewhere

Everything in `protein_folding/` is the team's, and no file in it was edited.
It comes from two places.

## The team's Lean library

This library checks Berger and Leighton's proof. From it we take the statement
of the theorem, the proof that the two folding problems are in NP, the reduction
from SAT to EXACT PACKING, and the tools for building Turing machines.

- Copied from: the folder `lean/cubic` of the website repository,
  `caltech-mathathon-hp/caltech-mathathon-hp.github.io`.
- Commit: `7d747dd9ef01cbd7e39925d05162cd2e75da0305`, which is in the history of
  its branch `main`.
- Every file of the library at that commit is here, unchanged.

## The team's proof of the Cook–Levin theorem

The library at that commit has the Cook–Levin theorem, that SAT is NP-hard, as
a hypothesis: `SAT.CookLevin`, in `ProteinFolding/Common/CookLevin.lean`. The
team has since proved it. The theorem is
`ProteinFolding.SAT.CookLevinUniversal.cookLevin`, in
`ProteinFolding/Common/CookLevinProofUniversal.lean`.

The team keeps this proof as a Lean project of its own, the folder
`lean/cooklevin` of the website repository. It has the files of the library
that the proof needs and 63 new files, all named
`ProteinFolding/Common/CookLevinProof*.lean`.

- Copied from that project: the 57 of the 63 files that the proof of
  `cookLevin` imports. They are in the same place here,
  `protein_folding/ProteinFolding/Common/`.
- Not copied: the other six. They prove the theorem for formulas whose clauses
  have at most three literals, and we do not use that version.
- The files of that project that belong to the library are the same, byte for
  byte, as the ones we already had.
- [`cook_levin_files.sha256`](cook_levin_files.sha256) lists the 57 files with
  their SHA-256 sums.

To check that the 57 files here are the team's, run this in the folder of the
team's Cook–Levin project:

```bash
shasum -a 256 -c <path to this folder>/cook_levin_files.sha256
```

It prints `OK` for each file. In the website repository this project is the
folder `lean/shelf`, so there the command is

```bash
cd lean/cooklevin && shasum -a 256 -c ../shelf/vendor/cook_levin_files.sha256
```

The same command in `vendor/protein_folding`, with
`../cook_levin_files.sha256`, checks the copies here against the list.

The library's own root file, `ProteinFolding.lean`, does not import the 57
files. Our file `Shelf/Unconditional.lean` imports
`ProteinFolding.Common.CookLevinProofUniversal`, and that is how they get
compiled.

## Copying again

Do not edit the files in `protein_folding/`. A change to the library is made in
the website repository, and the folder is then copied again.

To copy a newer commit of the library, from a clone of the website repository
that has it:

```bash
rm -rf vendor/protein_folding && mkdir vendor/protein_folding
git -C <clone of the website repository> archive <commit>:lean/cubic | tar -x -C vendor/protein_folding
```

This removes the 57 files too. If the new commit does not have them, copy them
again from the team's Cook–Levin project, into
`vendor/protein_folding/ProteinFolding/Common/`, and check them with the command
above. Then write the new commit in this file and run `lake build` in this
project's folder.

The folder is a Lake package of its own, and our `lakefile.toml` uses it as a
path dependency. Lake puts its compiled files in `protein_folding/.lake/`, which
git ignores.
