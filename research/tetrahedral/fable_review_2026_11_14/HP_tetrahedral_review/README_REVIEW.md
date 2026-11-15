# HP folding on the tetrahedral (diamond) lattice — review package

Prepared 14 November 2026 for an independent check. Claim under review: the HP string-folding decision problem
on the diamond lattice is NP-complete (reduction from Bin Packing, following Berger–Leighton 1998 for the cubic
lattice). **Status: a complete proof manuscript with computer-assisted parts. Not formalised. Not independently
verified.** Two earlier audits found four real errors (listed at the end); assume there may be more.

## Contents

| Path | What it is |
| --- | --- |
| `HP_tetrahedral_proof.md` | The manuscript (current version). Every change since the first version is marked with its date. |
| `HP_tetrahedral_notes.md` | Working notes with the history of the construction, including failed attempts (§14–17: the audits). |
| `previous_versions/…_v1_0842.md` | First version (SHA-256 0cb3f2a5…a749f, the one the first audit saw). |
| `previous_versions/…_v2_1008.md` | After the padding repair (Lemma F(D–E)), before the second audit. |
| `code/` | All programs (Python 3, standard library only; one optional C++ file) and the logs of the runs quoted in the manuscript. |
| `sample_fold/` | One complete optimal fold (m = 24) as coordinates + string, as input for `code/verify_fold.py`. |

## What is proved how

| Part | Section | Status |
| --- | --- | --- |
| Isoperimetric inequality, Theorem 3 | §4 | hand proof |
| Unique optimum Oct(m), Theorem 5, Claim U, facts (O1)–(O7) | §5 | hand proof (audit 1 reported finite checks of Lemma 5.1 and Claim U for m ≤ 9) |
| Lemma T (corrected), Lemma T′, Lemma E | §5.6 | hand proof; numerical confirmation `transfer_cov.py` |
| The word; "only if" direction | §6, §7 | hand proof; **never audited by anyone else** |
| Foliation, lines, columns, skins, rows (Lemmas B, L, C, R) | §8.1–8.2 | hand proof; **never audited by anyone else** |
| Bulk Lemma, Claim 1 | §8.3 | Lemma K + Lemma T′ by hand; base cases m = 88, 89 by machine |
| Bulk Lemma, Claim 2 | §8.3 | parts (i)–(iv) by hand; ten certificates for m ≤ 60, table (a), (S2)–(S4) by machine + older hand argument |
| Lemma N (near field), (N1), (N2), (N5) | §8.4 | reduction (1)–(5) by hand to two test layouts; those by machine |
| Lemma N, (N3), (N4) (tethers) | §8.4 | hand argument, **not re-audited**; (N3) near vertices only through the test runs |
| Lemma F (far field), parts A–C | §8.5 | hand proof; executed literally by `build3.py` mode `text` |
| Lemma F, parts D–E (padding, L* = 1000(m+w+1)+6) | §8.5 | hand proof by the first auditor; re-checked (`faru3.py`, `build3.py text`) |

Standing assumption behind every "by machine": the programs implement what the text describes. They were written
by the author of the manuscript and nobody else has read them.

## Suggested order of checking

1. **§8.4, Lemma N.** Read the reduction (1)–(5). Check (3c) and (4) against the placement code in `build3.py`
   (frame, slots, anchors, track, rings). Re-implement Appendix C from the text on raw coordinates.
2. **§8.3, Claim 2.** Table (a) and (S2)–(S4) are the oldest and least polished argument. Re-derive the cover from
   rules 1–4 and Appendix B independently of `canon.py`, then re-run the certificate with the lexicographic Ω.
3. **§8.4 (N4)**, the tether routes, and §8.2 Lemma R on which they rest.
4. **§7**, the "only if" direction (pure hand proof, constants of §6).
5. **§8.5 A–C** and the interfaces: what Lemma F assumes about the near field (Part E) versus what Lemma N gives.
6. §4–§5.

## Reproducing the checks

Run everything from inside `code/`. Python 3.10+ (used: 3.13), no packages. Output files of `build3.py` are
written next to the `code/` directory. Times are for one core.

| Check | Command | Expect | Time / memory |
| --- | --- | --- | --- |
| Lemma T counterexample, Lemma T′, corrected Lemma T | `python3 transfer_cov.py` | counterexample line (depth 1 → −3), ten "every one has a valid transfer" lines, six "corrected Lemma T" lines | 2 min |
| Witness against the numerical Ω | `python3 certify_lex.py witness 30 47` | "P,Q,R as reported", "escape within 6 segments: False" | 15 s |
| Claim 2 certificates, lexicographic Ω | `python3 certify_lex.py cert 9 60` | every line "ties 0 ; strict local maxima 10 ; all certified within 6 steps: True", last line "ALL OK: True" (log: `certify_lex_9_60.log`) | 8 min |
| Claim 1 base cases | `python3 claim1.py 88 89` | "valid … shortest 6 sites" twice (log: `claim1_88_89.log`) | 2 min, 2 GB |
| Cover periodic along edges | `python3 edgeperiod.py 40 41 50` | "2-periodic for I <= i <= 2m-2-I with I = 12 … True" | 1 min |
| Lemma N test layouts and confirmations | `./sweepN.sh` | 18 lines "NEAR FIELD OK … Appendix C shapes: OK" (log: `sweepN_J14.log`) | 8 min, 1.5 GB |
| Lemma N, the two layouts the proof needs | `NCHECK=1 NEARONLY=1 python3 build3.py 80 4 "[[4],[4],[4],[4],[4],[4],[4],[4]]" 14 chain 0 natural T8` and `… build3.py 80 8 "[[4,4],[4,4]]" 14 chain 0 natural Tcut` | "NEAR FIELD OK" | 30 s each |
| Old padding defect | `python3 faru2.py` | "old construction only E = 0 (or 6) mod 8" | 5 s |
| Replacement padding (Lemma F(D)) | `python3 faru3.py` | "all checks passed: 28512 paths" | 20 s |
| Lemma F A–E literally, all residues | `python3 build3.py 24 4 "[[2,2]]" 8 chain 0 natural t24r text:resid` then `python3 verify_fold.py ../t24r_fold_coords.txt` (also with 25 for the other phase) | "OPTIMAL: True"; verifier "bound attained: True" | 10 s |
| Lemma F with the full threshold L* | `python3 build3.py 24 4 "[[2,2]]" 8 chain 0 natural t24L text:Lstar`, then the verifier | lengths [137006, 137007]; 7,693,861 monomers | 1 min, 3 GB |
| One string, several packings | `python3 build3.py 28 4 "[2,2,2,2];[[0,1],[2,3]]" 8 chain 0 natural tpA text:bound`, same with `[[0,2],[1,3]]` (tpB) and `[[3,0],[2,1]]` (tpC); compare `../tp?_fold_string.txt` | three identical strings (2,888,336 letters), three different folds | 20 s each |
| Any fold file | `python3 verify_fold.py ../sample_fold/demo4_m24_fold_coords.txt` | "valid self-avoiding walk … bound attained: True" | seconds |

`build3.py` arguments: `m CAP "PACK" [J1] [chain|nochain] [RFLIP] [natural|pad:files] [TAG] [FARMODE]`; PACK is a list
of bins of item sizes, or `"ITEMS;ASSIGN"`. FARMODE `text[:Lstar|:bound|:resid]` follows §8.5 literally.
`verify_fold.py` reads only coordinates and letters and shares no code with the builder.
Older checks quoted in Appendix A of the manuscript (`bulktable.py`, `lines.py`, `extents.py`, `regiontransfer.py`,
`sweep3.sh`, `sweepK.sh`, `nfinduct.py`, …) are included with their logs; their docstrings give the usage.
`nfinduct.py` (radius-5 comparison) is **withdrawn** as a proof step.

## Known weak spots

- Table (a) of Claim 2 for all m, and (S2): finite checks for a few sizes plus a hand argument that was not rewritten.
- (N4): the tether routes and their lengths; the word uses the shortest path inside the stated rows and columns.
- (3c) of Lemma N: "which objects exist" is asserted from the construction, not from an independent specification.
- Claim 1 is not covered for 61 ≤ m ≤ 87 outside {64, 68, …, 84, 80, 82}; the reduction only uses m ≥ 336.
- The test layouts use small track constants (J = 14, C = 4 or 8). The proof argues, and no run confirms, that the
  layouts of §6 (m ≥ 336) reduce to them.
- Sections 6, 7, 8.1, 8.2 have had no outside reader at all.

## Errors found so far (all repaired in the current version)

1. Lemma F(D), padding: reached one residue class modulo 8 (audit 1; the author's script had pooled start positions).
2. Bulk Lemma: potential with fixed constants 10⁴, 10⁹ fails from m = 50,004 (audit 2) → lexicographic potential.
3. Lemma N: base cases and induction did not cover the parameters of §6; search rule not local (audit 2) → family 𝓕,
   explicit links (Appendix C), reduction without induction.
4. Lemma T: insufficient hypothesis, counterexample m = 11 (audit 2) → corrected; shown unused; Lemma T′ and E added.
Also found by the author on the way: §9 asserted packing-independent linker parities without a reason (reason added).
