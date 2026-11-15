# Audit of Fable's second review package

14 November 2026. **The revision implements the previous six repairs substantively, and the new independent tests below passed. I still found mistakes in the written coverage argument and specification alignment, but no new routing collision or counterexample to the reduction.** The remaining findings are smaller than the earlier tether-length failure. They should not be described as a disproof of the theorem.

Source files:

- `C:/Users/Antonio Acuaviva/Downloads/HP_tetrahedral_proof (1).md`, SHA-256 `334B7B0B45AFCDE3E2D93FE7DE7C307E57BF83C32DD0908CA561700392934565`.
- `C:/Users/Antonio Acuaviva/Downloads/HP_tetrahedral_review (1).zip`, SHA-256 `DCCD3D1D4C2DC17A22BEE51B63E0EB82CCDBA9BD7DEDC7458033B089B204FC71`.
- The manuscript extracted into `fable_review_v2_2026_11_14/HP_tetrahedral_review/` is byte-identical to the separately supplied manuscript. Source files and extracted manuscript were not edited.

## 1. Lemma N's boundary-owner counting is still incorrect

Relevant text: §8.4(2), (3c), (4), especially lines 945–1012. Owners are now specified as individual H-sites: a cap's owner is the H it caps, and a PPP's owner is its first H. These definitions do not support the later assertion that owners of boundaries d apart are at max-norm distance exactly 2d.

### A witness in an actual reduction instance

Take `K=B=1`, hence `m=336`, `J=132`. In the left filler, boundary 22 has a b–b PPP and boundary 23 has an a–a PPP. Their first-H owners are:

```
boundary 22: e3[45] = (45,671,-625)
boundary 23: e3[46] = (46,670,-624)
```

The boundary indices differ by one, but the owner distance is **1**, not the claimed **2**. Moreover, a cut boundary has two cap owners, one in each adjacent dimer; its right cap's owner has index `2i+2`, outside the stated alternatives `2i` and `2i+1`.

### A case outside the stated “at most three boundaries apart” enumeration

The valid family-F layout

```
m=80, K=1, J=14, C=12, R=49; items [4,4,4]
```

has cuts at boundaries 19 and 23. The right cap of the first cut and the left cap of the second cut have owners

```
e3[40] = (40,158,-118)
e3[46] = (46,158,-112).
```

They are at distance **6**, meeting the cutoff in (2), but their boundaries are **four** apart. This contradicts the assertion in (4)(β) that the relevant boundary pairs are at most three apart, and its ensuing exclusion of two different cut boundaries.

**Important qualification:** this is not a collision and is not proof that the two test layouts lack a geometric representative. I checked that these two cap/second-column-site objects are translates of the R/L cap objects at owner indices 32 and 38 in T_8. The translation is `(-8,0,-8)`. Thus this witness can be handled by a cross-type geometric identification, or excluded from collision consideration using sharper per-object radii. The manuscript currently does neither; its stated combinatorial enumeration is false.

**Required repair:** work with the actual individual owners, and account for the possible offsets of both cap owners. Prove the resulting interaction cases are covered, or prove that the additional cases are disjoint without invoking the test layouts. Do not merely repeat the 2d assertion or the distance-three cutoff. This finding concerns the written justification, not the validity of the displayed fold in this layout: the independent surface check passed on the three-item layout too.

## 2. The owner domain omits bulk-end objects

Line 945 states that owners are edge-zigzag sites or vertices. But (1) includes caps of run ends, with the run end itself as owner. The canonical bulk runs lie in `X_m = Oct(m) minus the edge zigzags`. Their ends are consequently **not** edge-zigzag sites or vertices.

For example, at `m=336` the independently reconstructed cover has a bulk end

```
H = (-12,16,4), with dangling cap P = (-13,15,5).
```

The H-site is in X_m, has cover degree 1, and is not an edge site. The many bulk-end caps cannot all be classified by the edge indices in (3)–(4).

There is an apparent straightforward intended repair: restrict the edge-owner case analysis to the frame, anchor, track, ring and vertex objects; treat all bulk caps and their columns as a separate forbidden set, using Lemma C for their mutual disjointness and the local bulk-end predicate for interactions with the other objects. The argument already uses elements of this approach. It needs to state the partition and discharge every type of interaction explicitly. This is not evidence of an actual bulk-cap collision.

## 3. Proposition A(A5) has an off-by-one supporting bound

Line 826 uses `|Y| >= 12` to justify `alpha > 5` for the relevant class-Z segment. At the actual reduction size `m=336`, the cover contains the row segment

```
P = {(-657,659,1), (-656,658,2)}.
```

Its two joints leave these sites towards `(-658,660,2)` and `(-655,657,1)`. The distances of the joint sites from the nearest vertex are 13 and 14, so P meets the proposition's requirement that both joints be farther than 12 from every vertex. Nevertheless, the first site has

```
Y = 659 - (2*336-2) = -11,
Z = 1-1 = 0,
alpha = 11.
```

Thus `|Y| >= 12` is false here. The needed conclusion `alpha>5` still holds for this witness, and the segment maps correctly to the reference size. This is a repairable numerical assertion, not a counterexample to the proposition's conclusion. The proof should derive a correct sufficient bound uniformly, rather than retain the false one.

## 4. Specification and documentation cleanup remains

The primary definition of the tethers in §6 and (N4) is now explicit, with the corrected lengths. However, the near-field overview at line 864 still calls them shortest paths, and §9, lines 1211–1212, still describes bounded frame search and shortest-path tether computation. Those descriptions should match the explicit construction.

There are also differences between the literal word of §§6,9 and `build3.py`'s word-mode output:

- Section 6 orders items before the fillers. The builder places the left filler before the items through `track_units=[left_unit]+items+[right_unit]`.
- Section 9 uses `L*=1000(m+w+1)+6`, adjusted for parity. Word mode uses `280m+240w+412`, adjusted for parity.
- Each builder bulk unit retains caps at both ends, including a final P at the end of the assembled chain; the last bulk unit in the written word ends with its H-run.

These differences have plausible benign explanations: Lemma F routes arbitrary pairings, its proved base-length estimate also supports the smaller threshold, and a trailing P can be removed from a valid fold. They are **not** demonstrated failures of hardness or of the local routing lemmas. But same-word tests of the builder should not be described as literal reproduction of the precise word specified in the manuscript without aligning these conventions or proving the relevant implication.

The README and some historical paragraphs also still contain superseded `chain` commands and references to an unresolved bulk argument that Proposition A now claims to resolve. These are documentation issues, distinct from the mathematical findings above.

## 5. Repairs and checks that passed

The earlier 273-versus-279 error is repaired: text and the new `tether_explicit` implementation use entry slack `10k+2` and exit slack `14K+22-6k`. The radius-3 correction is implemented in the PPP assertions. `sweepN.sh` now uses `nochain`. The manuscript corrects the per-parity bulk-table description, supplies logs for the missing small sizes, and replaces Corollary 4's false estimate with the valid elementary bound. The supplied log claims were read, not independently rerun in Python.

### Independent surface checks

The Node checker reconstructs the geometry independently of the author's Python. It passed on five layouts:

| Layout | m | K | Relevant feature |
| --- | ---: | ---: | --- |
| T_8 | 80 | 8 | First representative |
| T_cut | 80 | 2 | Second representative |
| Three items of four dimers | 80 | 1 | The boundary-pair witness above |
| Actual reduction K=B=1 | 336 | 1 | Original tether witness |
| Actual reduction K=12,B=1 | 4252 | 12 | K exceeds the representative's K |

The checks include the explicit frame paths, surface PPPs, borrowed columns, all explicit tether sites and lengths, mutual avoidance, and avoidance of original bulk-end columns using the local cover rules. They do not materialize the entire bulk or entire long-linker word. Ring orientations use the independent checker's fixed convention, as documented in the prior audit.

### Independent Proposition A translations

The new checker reconstructed segments from the local geometric rules and applied the actual translations stated in A3, A4 and A5. It compared the full table key and neighboring-segment value at the reference sizes, and checked that the mapped segment still has two far joints.

| m | A3 cases | A4 cases | A5 cases | Failures |
| --- | ---: | ---: | ---: | ---: |
| 81 | 103 | 36 | 42 | 0 |
| 82 | 104 | 36 | 42 | 0 |
| 336 | 104 | 36 | 42 | 0 |
| 1000 | 104 | 36 | 42 | 0 |

That is **727 sampled segment translations, all passing**. The tested edge indices include positions around the generic/vertex cutoff, central positions and both ends. This is supporting evidence for the new proposition, not an exhaustive test of all unbounded parameters. No substantive counterexample to its translation conclusion was found in this pass.

Appendix B's patches are unchanged from the previously independently reconstructed cover. Appendix C's coordinate templates are unchanged; the revision adds an explanation identifying the borrowed tether column's source site.

## 6. Reproduction and scope

From the project root:

```
node research/tetrahedral/fable_v2_proposition_check.mjs
node research/tetrahedral/fable_v2_coverage_witnesses.mjs
node research/tetrahedral/fable_v2_surface_check.mjs
```

The proposition driver generates a local-cover module from the independent implementation, reading this package's Appendix B and allowing long segments. The surface driver adapts the existing independent coordinate implementation to the five layouts above. Neither executes the author's Python code.

Results: `fable_v2_proposition_results.json`, `fable_v2_coverage_results.json`, `fable_v2_surface_results.json`.

**Assessment:** this revision is substantially closer. The earlier concrete routing-length error is gone, and the new bulk translations have encouraging independent evidence. Remaining mistakes concern the written near-field case reduction, its owner domain, one supporting numerical bound, and literal specification alignment. I would ask for those to be corrected before describing this exact manuscript as gap-free. I have not found a new collision or a counterexample to the theorem, and this audit does not guarantee that every other part is error-free.
