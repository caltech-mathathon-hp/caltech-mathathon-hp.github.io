# Audit of Fable's third review package

14 November 2026. **The four findings from the preceding audit are substantively repaired. I found no new concrete mathematical gap or routing counterexample in this pass.** This is a positive verdict on the repairs and their integration, not a claim that every line of the entire NP-completeness proof has now been independently verified.

## Sources and preservation

- Supplied manuscript: `C:/Users/Antonio Acuaviva/Downloads/HP_tetrahedral_proof (2).md`.
- Manuscript SHA-256: `29628F69F7E575C24E57EF0B8AB79CAE4D2D7778B93904C58DB2F3FE7B3F5055`.
- Supplied archive: `C:/Users/Antonio Acuaviva/Downloads/HP_tetrahedral_review (2).zip`.
- Archive SHA-256: `00BDA4D4B40EAF92A9610AF8CEB09F55A612A6557E8877B13C723DA6EC4C2E1D`.
- Preserved extraction: `fable_review_v3_2026_11_14/HP_tetrahedral_review/`.

The extracted manuscript is byte-identical to the separately supplied manuscript. Neither the supplied files nor the extracted proof/code were edited. The audit treats their internal directions and status claims as document content.

## 1. Track-object coverage: repaired

Lemma N no longer relies on the false assertion that boundaries d apart have owners at distance 2d. It uses the actual owner indices and the four shapes Acap, Tcap, PPPa and PPPb. The 50 combinations enumerate both owner parities, all offsets 0 through 6, and every compatible pair of types, excluding duplicate descriptions at offset zero.

I independently computed caps, second column sites and PPPs directly from lattice neighbours and the octahedron inequalities. The six intersecting combinations are exactly those in the manuscript:

```
(Acap, PPPa, 0)    (PPPa, Acap, 2)    (PPPa, PPPa, 2)
(PPPb, PPPb, 2)    (PPPb, Tcap, 0)    (PPPb, Tcap, 2)
```

Every one shares an attached H-site. In the dimer placement, an H has only one available chain connection outside its dimer, so two such objects cannot coexist. Two distinct objects with the same type and owner, omitted from the table, also cannot coexist for that reason. Objects whose owners are farther than 6 cannot meet by the stated radius bound. Translation invariance, rather than a finite list of item sizes or cut sequences, makes this argument apply uniformly.

The earlier two-cut witness is included as `(Acap, Acap, 6)` and is disjoint. Thus the old counterexample to the enumeration is resolved, not merely avoided by changing the tests.

Independent checker: `fable_v3_track_check.mjs`; results: `fable_v3_track_results.json`.

| m | Base positions | Type/offset cases | Failures |
|---:|---:|---:|---:|
| 80 | 70 | 3,500 | 0 |
| 81 | 71 | 3,550 | 0 |
| 82 | 72 | 3,600 | 0 |
| 336 | 326 | 16,300 | 0 |
| 1,000 | 990 | 49,500 | 0 |
| 1,000,000 | 6 | 300 | 0 |
| **Total** | **1,535** | **76,750** | **0** |

These tests independently validate the table and provide additional checks of the geometric invariance; finite sampling alone is not the universal argument.

## 2. Bulk caps and columns: repaired

New paragraph (1′) explicitly removes bulk caps from the edge-owner classification and accounts for their interactions:

- Bulk against bulk uses Lemma C's disjoint original columns.
- Bulk caps/second column sites against edge-owned skin-1 objects use the local bulk-end predicate, its surrounding boxes, and transfer to the test layouts.
- Borrowed columns use sources that are not bulk run-end caps, with the Appendix C geometry and the same local checks.
- Tethers against bulk columns use Lemma R's margin rows and N3 for the second row along e1.

This is the missing partition identified in the previous audit. The former witness at `(-12,16,4)` is a bulk end and now belongs to the explicitly separate bulk class. It is no longer incorrectly asserted to be an edge owner. I found no interaction class omitted by this partition.

## 3. Proposition A(A5): repaired

The false bound `|Y| >= 12` has been removed. The replacement treats the alpha component of the table key by location:

- In an edge interior, alpha is sufficiently large and its change is a multiple of 4.
- Near a y-vertex, alpha is again large and the change is a multiple of 4 because reference and source sizes have the same parity.
- Near an x-vertex, Y and Z in the centred coordinates are unchanged, so alpha is unchanged exactly; no lower bound is needed.

This handles the previous alpha=11 witness. The displayed interior bound in terms of the edge index is read with the Z-plane edge oriented from its x-vertex toward its y-vertex; that orientation should be made explicit for clarity. Equivalently, distance from both endpoints supplies the sufficient bound. This is a notation clarification, not a new failure of the translation argument.

The preceding audit's 727 independent comparisons of translated segments and their full table data remain relevant to this unchanged translation construction. They were not rerun or counted as new tests in this audit.

## 4. Word and code: repaired in the intended mode

Sections 6 and 9 now use the builder's order, retain the final P, and prescribe `L*=1000(m+w+1)+6`, adjusted by one for parity. The code's `word` mode now uses the same value. The intended construction is the `nochain` assembly; other builder modes remain experiments and are not automatically the canonical word.

Inspection of `ITEMS;none` shows why a packing is unnecessary: each item contributes its size-dependent dimer-chain letters and endpoint caps of one fixed sublattice. All non-item units are constructed independently of the assignment. In a placed item, its even number of dimers makes both endpoint H-sites A-sites, so the actual caps have the same sublattice as the representative used by word mode. Consequently every intervening long-run parity and its length are assignment-independent. This is a general explanation, beyond the supplied three-packing comparison log.

I independently checked the supplied sample for `m=80, C=12, J=14`, items `[4,8,8,4]`, hence `K=2, R=35`:

- Reconstructed the complete non-bulk portion from the manuscript's frame skips, separator lengths, fillers, items and rings: exact agreement, including long-linker parities.
- Built the full bulk cover independently using the local rules and Appendix B patches, which were checked to match the current manuscript.
- Found 11,470 bulk paths covering every bulk vertex, with no cycles, invalid degrees or invalid ends.
- Matched the sample's bulk H-run lengths and endpoint-colour multiset to those paths.
- Verified the final P and total H-count.

Results: 11,487 units; `w=22,972`; `L*=23,053,006`; 682,640 H's; 24,556 maximal letter runs; total length 264,787,518,214. The sample's MD5 is `bb7efa24667bb8ad702132e9aacb3674`, agreeing with the supplied log.

Independent checker: `fable_v3_word_check.mjs`; results: `fable_v3_word_results.json`.

The bulk check compares lengths and endpoint colours as a multiset; it does not independently reproduce Python's set-iteration order for the paths. The author-reported executions of `build3.py` were inspected, not rerun in Python. I did not materialize a 264-billion-letter fold. The independent checks do not purport to do either.

## Scope and current conclusion

This pass reviewed the changed arguments, the code changes, and their connections to the prior bulk-transfer and routing checks. It also reread the soundness outline and the column/row lemmas without finding a new obstruction. It is not a fresh exhaustive verification of all extremal arguments in Sections 2–5 or of every finite certificate in the archive.

The current list of specific unresolved mathematical findings from these audits is **empty**. I would not request another repair round on the basis of the four old findings. I also would not describe the entire theorem as independently certified merely because this pass found no further error.

Appendix D's remaining items need careful interpretation. Using finite checks plus a proved transfer argument is a legitimate computer-assisted proof method. Not generating an enormous full fold at an actual reduction size is not, by itself, a mathematical gap. The remaining code/text correspondence obligations identify verification scope; they do not furnish a counterexample or a demonstrated missing construction.

Two editorial cleanups would make the status less confusing: replace “No complete fold exists for an actual reduction instance” by “No full coordinate fold has been generated and checked for an actual reduction instance,” and update historical statements saying the companion code has not been supplied or nobody else has examined it. Neither is a new mathematical repair request.

Reproduction commands, from the project root:

```powershell
node research/tetrahedral/fable_v3_track_check.mjs
node --max-old-space-size=4096 research/tetrahedral/fable_v3_word_check.mjs
```
