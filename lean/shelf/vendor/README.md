# Code copied from elsewhere

## `protein_folding`: the team's Lean library

This is Antonio's library. From it we take the statement of the theorem, the
proof that the two folding problems are in NP, the reduction from SAT to
EXACT PACKING, and the tools for building Turing machines.

- Copied from: the folder `lean/cubic` on the branch `lean-certificates` of the
  website repository, `caltech-mathathon-hp/caltech-mathathon-hp.github.io`.
- Commit: `7d747dd9ef01cbd7e39925d05162cd2e75da0305`.
- The copy is unchanged: no file was edited, added or removed.

Do not edit the files in `protein_folding/`. A change to the library is made in
the website repository, and the folder is then copied again.

To copy a newer commit, from a clone of the website repository that has it:

```bash
rm -rf vendor/protein_folding && mkdir vendor/protein_folding
git -C <clone of the website repository> archive <commit>:lean/cubic | tar -x -C vendor/protein_folding
```

Then write the new commit above and run `lake build` in `lean/`.

The folder is a Lake package of its own, and `lean/lakefile.toml` uses it as a
path dependency. Lake puts its compiled files in `protein_folding/.lake/`, which
git ignores.
