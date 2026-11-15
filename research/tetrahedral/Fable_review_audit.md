# Audit of Fable's tetrahedral review package

14 November 2026, extended after the user's follow-up. Verdict: **substantial repairs, but the manuscript is not internally correct as written and the supplied checks do not yet certify precisely its stated construction.** There is a concrete tether-length discrepancy and a false object-radius bound in the near-field coverage argument. A further pass also found an elementary arithmetic error in Corollary 4. These are not counterexamples to NP-completeness, or even to the existence of the desired fold with a suitably specified construction.

Source archive: `C:/Users/Antonio Acuaviva/Downloads/HP_tetrahedral_review.zip`.

- Archive SHA-256: `18B5187833580E5E4CFCA77E1EC0072C4AE91885C4610C03A4B36630F6C29182`.
- Extracted manuscript SHA-256: `BD89C0A822D9DD4E5FB6E55770F532EF05BF5A96E3BD6AA0B4220E6AFCC1C177`.
- Extracted package: `fable_review_2026_11_14/HP_tetrahedral_review/`.
- The archive, extracted manuscript, and existing `_Astra` manuscript were not edited by this audit.

## 1. Confirmed inconsistency: the tether region and the claimed length disagree

The manuscript defines each tether length to be that of a shortest path inside its specified rows and columns (§6, lines 444–446; §8.4, lines 800–819). Appendix C fixes the borrowed column of a 2-slot's tether cap: relative to the slot's a-site, the cap is `(2,2,0)` and its second column site is `(3,3,1)`.

For `K=1, B=1`, the actual reduction constants are

```
Sigma*=58, lambda=66, C=66, J=132, R=133, m=336.
```

For entry tether `k=1`, `j_1=132` and its skin is `j=2`. Section 6 states `sigma_e(1)=6`, prescribing

```
2*j_1 + 3 + sigma_e(1) = 273 P-sites.
```

But with the stated Appendix C borrowed column, the shortest path in the stated rows and columns has **279 P-sites**, so its slack is **12**, not 6.

An exact coordinate witness:

| Object | Absolute diamond-lattice coordinates |
| --- | --- |
| Slot a-site `e1[6]` | `(0,676,-664)` |
| Slot b-site `e1[7]` | `(1,677,-663)` |
| Tether start cap | `(2,678,-664)` |
| Borrowed second column site | `(3,679,-663)` |
| Borrowed column's sub-surface site in skin 2 | `(4,680,-664)` |
| Separator first b-site | `(265,671,-405)` |
| Tether target cap | `(266,672,-406)` |
| Target column's sub-surface site in skin 2 | `(266,674,-408)` |

In the F'-bilayer coordinates of §8.2, the forced entry surface site is `(332,5,1)`. The two specified rows connect it through `(336,1,1)` to `(204,1,133)`. Their lengths are `2*4=8` and `2*132=264` bonds. Including the two column portions and the two connectors gives `278` bonds between caps, hence `279` P-sites including both caps.

This was also checked by breadth-first search on **all 1,354 sites in the two full rows and the two column portions**. This is a superset of the prescribed finite row portions, so the lower bound does not depend on restricting the row endpoints too tightly. The resulting shortest path is saved in `fable_tether_witness_results.json`.

The same discrepancy occurs for entry tether `k=2`: the manuscript's displayed slack is 18, but the shortest path in the specified region has slack 22 (`425` P-sites instead of `421`). With the Appendix C borrowing, the explicit entry route has length

```
2*j_k + 3 + (10*k + 2).
```

The independent check confirmed these shortest lengths for the nine entry tethers of the test layout T_8, and for both entry tethers in actual reduction layouts `(K,B)=(1,1)` and `(1,3)`. The printed numerical formula in §6 is explicitly claimed only for `K<=6`; T_8 is included to check the route, not to extend that textual claim.

### Why the author's runs can still pass

In `code/build3.py`, lines 218–238, `corridor_ok` and `tether` search an allowed portion of the **whole F'-bilayer**. They do not restrict the breadth-first search to `c=1` and `b=j-1` for entry tethers. Consequently, those runs do not establish the printed shortest lengths inside the narrower region specified in the manuscript. A shorter path elsewhere in the bilayer is entirely possible; the witness does not rule it out.

This leaves two incompatible readings of the word as currently written:

1. Use the displayed slack 6: the stated row construction does not realize that prescribed length.
2. Compute the shortest path in the stated rows: the word uses slack 12, contradicting the displayed formula and differing from the program whose checks are cited.

This is repairable in principle. The explicit slack `10*k+2` is even and remains below the existing bound `10*k+5`, so the main reduction constants need not automatically change. A consistent revision must choose its allowed routing region and lengths, update the word and checker together, and establish the accompanying avoidance claims. This audit does not silently make that choice for the author.

## 2. The supplied near-field certification is not for exactly the stated bulk units

Section 6, item 7, uses one separate H-run per path of the canonical bulk cover. However, `sweepN.sh` invokes `build3.py` with `chain`. At lines 260–289, that mode joins some bulk paths using additional PPP links and removes the joined ends from the set of long-linker caps. The final column check at lines 302–314 checks the resulting `linkercaps`.

Thus the advertised test layouts use a modified bulk assembly as well as a broader tether search. Those tests alone do not establish the universal column-avoidance statement for the exact unchained assembly of the text. Several earlier checks in the builder do protect all original bulk caps, so this observation is **not a demonstrated collision**. It is a concrete mismatch between the proposition claimed to be checked and the construction actually checked.

The direct remedies are to test the exact written construction without optional chaining, or to prove that the changes made by the test program preserve every property for which the test is cited. Either remedy must also address the tether-region discrepancy above.

## 3. Bulk coverage: supporting evidence, plus an inaccurate coverage assertion

The lexicographic potential removes the previous fixed-offset counterexample. Appendix B's six patch lists are byte-for-byte identical to those in the independently reconstructed `_Astra` cover. The strengthened transfer lemmas and the new locality argument are substantial improvements; I found no new coordinate counterexample to those repaired transfer statements in this review.

I independently reconstructed the table key and value used by `bulktable.py`, from the geometric cover rather than importing the author's Python. Results:

| m | Keys present at this size | Cumulative distinct keys in this audit |
| --- | ---: | ---: |
| 14 | 10 | 10 |
| 15 | 19 | 27 |
| 24 | 39 | 54 |
| 25 | 39 | 74 |
| 30, 44, 45, 50, 60 | 39 each | 74 |

There were no conflicting values for a key. The six-step vertex neighborhoods at the larger checked sizes contained the reported 233 segments in total, with maximum extent 43. These findings support the repaired bulk argument.

But the literal assertions that the 74-entry table is "the same for all m=14...44" (line 673) and that "all classes occur for m>=14" (line 732) are inaccurate under the program's stated key and inclusion criterion. The 74 entries are accumulated across sizes and phases; they are not all present at m=14. This does not itself produce a cycle or disprove the large-m classification. It needs a correctly stated representative-family and coverage argument, rather than conflating a cumulative table with each individual size.

Claim 1 also expressly leaves some sizes 61–87 uncovered while the Bulk Lemma is stated for every m>=9. That is a gap in the full stated lemma, but the reduction uses m>=336, so it is not by itself a gap in the hardness reduction.

## 4. Further confirmed defect: a PPP does not fit the claimed owner radius

In §8.4(2), line 838, the manuscript claims that every object other than a frame link lies within max-norm distance 2 of its owner. The subsequent translation and case-coverage argument treats these owners as edge-zigzag sites with indices. This radius claim is false for an ordinary PPP: there need not be **any** owner site on its edge within distance 2 of all its P-sites.

Use the same actual reduction `K=B=1, m=336, J=132`. Boundary 22 of the left filler joins the B-sites of dimers D_22 and D_23. Its H endpoints and its unique PPP are:

```
H = (45,671,-625)
P = (46,672,-626)
P = (47,673,-625)
P = (48,672,-624)
H = (47,671,-623)
```

All five sites are in the diamond lattice, consecutive sites are adjacent, and all three P-sites are outside Oct(336). This is an ordinary required link, away from the vertices.

Every possible owner on e3 has the form

```
e3[i] = (i, 670 + (i mod 2), -670+i).
```

To be within distance 2 of the middle P-site's y-coordinate 673, `i` must be odd. The first and last P-sites' x-coordinates 46 and 48 require `46 <= i <= 48`. Thus the only candidate is `i=47`. But e3[47] has z=-623, three units from the first P-site's z=-626. No such owner exists. The minimum possible radius is 3, attained at indices 45, 46 and 47. This has both a hand verification and an independent exact coordinate check.

**Consequence:** the stated radius-2 premise does not justify the derived interaction cutoffs 20/12/4, or the assertion that only the listed pairs of nearby boundary objects need testing. This does not demonstrate a collision. It demonstrates a false premise in the reduction from arbitrary layouts to the two finite test layouts.

The repair must specify owners precisely and then rederive the required radii and complete interaction classes. If the intended owner is a pair of sites rather than one edge site, its distance, box and translation conventions must be defined and the coverage argument rewritten accordingly. Merely replacing the numeral 2 in one sentence is insufficient: the associated cutoff and representative-case claims must be checked. For example, using a radius-3 bound for PPPs gives conservative frame/PPP and PPP/PPP cutoffs 13 and 6, unless sharper geometry is proved.

## 5. Further arithmetic error: the estimate in Corollary 4

At line 92 the manuscript uses

```
(4/3)*(m^2-1/2)^(3/2) <= (4/3)*m^3 - m + 1/(8*m).
```

This inequality has the wrong direction. At m=2 it says `7*sqrt(14)/3 <= 419/48`, whereas `112^2*14 = 175616 > 419^2 = 175561`. More generally, after multiplying the difference of the squares of the left and right sides by `576*m^2`, the result is `16*m^2-9 > 0` for every integer m>=1; both sides are positive.

The corollary itself is readily rescued, since for m>=1

```
(4/3)*(m^2-1/2)^(3/2)
  <= (4/3)*m*(m^2-1/2)
   = (4/3)*m^3 - (2/3)*m
   < (4/3)*m^3 - (1/3)*m = N_m.
```

This is an elementary erratum, not an obstruction to the reduction. It should nevertheless be corrected in a manuscript claimed to be complete.

Both new witnesses are reproduced by `node research/tetrahedral/fable_additional_witnesses.mjs` and saved in `fable_additional_witness_results.json`.

## 6. Independent positive checks and limits of this audit

Using raw diamond-lattice coordinates, I adapted the existing independent surface checker to Appendix C's exact borrowed tether arm and the displayed row route. The following actual reduction layouts passed checks of frame/PPP/tether disjointness and avoidance of long-linker columns, including the original unchained bulk-end columns:

```
(K,B,m) = (1,1,336), (1,3,732), (2,2,848),
          (6,1,1576), (6,3,4072).
```

The `(1,3)` layout was checked with both one item per bin and multiple items; the `(2,2)` and `(6,3)` checks also used multiple items. These are six concrete layouts. They use the explicit row-route lengths, including entry slack `10*k+2`; they do not validate the conflicting printed shorter entry lengths. The checks are supporting finite evidence, not a proof for all parameters. Ring orientations follow the independent checker's fixed convention, so these tests are not a byte-for-byte execution of every convention in the author's builder.

The author's Python programs were read, but not rerun in this environment: its `python` command is an inaccessible Windows application alias. All computations reported as independently run here used standard-library Node.js scripts. I did not claim to reproduce the author's large Python runs, and I did not complete a fresh audit of all extremal and soundness arguments in §§4–7.

Reproduction commands, from the project root:

```
node research/tetrahedral/fable_tether_witness.mjs
node research/tetrahedral/fable_bulk_table_check.mjs
node research/tetrahedral/fable_surface_check.mjs
node research/tetrahedral/fable_additional_witnesses.mjs
```

Results are in `fable_tether_witness_results.json`, `fable_bulk_table_results.json`, and `fable_surface_results.json`. The surface driver writes `fable_surface_generated.mjs` by adapting the already independent checker; it does not import or execute code from the archive.

**Conclusion:** the package improves the earlier proof substantially and has encouraging independent finite checks. Nevertheless, the tether definition, printed lengths, and certified program do not currently agree, and the near-field coverage argument uses a false owner-radius bound. The bulk coverage wording and lemma scope also need attention, and Corollary 4 contains a simple false estimate. Fixing the original tether discrepancy alone is not enough to resolve all identified issues. I would not endorse a claim that this version is already a complete, gap-free proof. Nor does this audit establish that the underlying theorem or construction is false, or guarantee that these are the only issues still present.
