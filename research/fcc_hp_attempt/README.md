# HP folding on the FCC lattice: NP-hardness attempt (project "Mathatom")

Archive made on 15 Nov 2026, after the twenty-fourth pass.

## State of the work

There is **no complete proof** that FCC-HP-FOLD is NP-hard.

* Completeness of the reduction from 3-PARTITION is proved (Theorem 54, Part III).
* Soundness is open. It follows from any one of three statements, none of them proved:
  Conjecture R (Part II), the inequality (L_n) (Part III, Section 45), or, for n >= 46,656 m + 2,
  the count (A) (Part III, Section 47).

The current status, the table of what is proved and what is open, and the estimate are at the top of
`project-docs/fcc-hp-hardness-attempt-part3.md`.

## What is in this archive

`project-docs/` holds the project documents that exist as files in the working session, under their project names:

| File | Content |
|---|---|
| `fcc-hp-hardness-attempt-part3.md` | Part III of the note: Sections 26 to 32 and 42 to 47 (passes 16, 17, 19 to 24), with the running status |
| `fcc-verification-code-14.md` | scripts and outputs of the sixteenth pass (completeness: Lemmas 49 to 53, Theorem 54) |
| `fcc-verification-code-16.md` | nineteenth pass (search against Conjecture R, Section 42) |
| `fcc-verification-code-17.md` | twentieth pass (Section 43) |
| `fcc-verification-code-18.md` | twenty-first pass (Section 44) |
| `fcc-verification-code-19.md` | twenty-second pass (Section 45) |
| `fcc-verification-code-20.md` | twenty-third pass (Section 46) |
| `fcc-verification-code-21.md` | twenty-fourth pass (Section 47) |

`workspace/` is the working directory of passes 16 to 24 as it stands: every script as a `.py` file, the helper
scripts that ran them (`runall19.sh`, `runall20.sh`) and assembled the code documents (`assemble*.py`), and in
`workspace/out/` every saved output. The scripts import one another, so run them from inside `workspace/`,
for example

    cd workspace
    python3 acount.py named
    python3 structure.py tips

They need Python 3 with numpy and scipy; a few of the older ones also use networkx.

## What is not in this archive

Seventeen project documents are not here, because the session could not save them as files (the project tool
returns them only as text in the conversation):

* `claude/fcc-hp-hardness-attempt.md` (Part I: Sections 1 to 11, the reduction, results 1 to 34)
* `claude/fcc-hp-hardness-attempt-part2.md` (Part II: Sections 12 to 25, results 35 to 48)
* `claude/fcc-hp-hardness-attempt-part4.md` (Part IV: Sections 33 to 41, written in another session)
* `claude/fcc-verification-code.md` and `claude/fcc-verification-code-2.md` to `-13.md` (scripts of passes 1 to 15)
* `claude/fcc-verification-code-15.md` (written in another session)

They are in the project "Mathatom" on claude.ai and can be opened or downloaded there. Part III refers to Parts I
and II for definitions and for results 1 to 48, so it is not self-contained without them. The scripts of
`workspace/` do not need the older scripts.
