# HP folding on the FCC lattice: proof attempt, Part III (passes 16, 17 and 19 to 24, 14 and 15 Nov 2026): completeness of the reduction; a search against Conjecture R; a sharper conjecture about tops; soundness as one linear inequality

This continues `claude/fcc-hp-hardness-attempt.md` (Part I: Sections 1 to 11, results 1 to 34) and `claude/fcc-hp-hardness-attempt-part2.md` (Part II: Sections 12 to 25, results 35 to 48). Definitions and numbering carry on. From this pass on the running status is kept here; the status sections and tables of Parts I and II have not been rewritten and are out of date in the rows about completeness.

## Status

**There is still no complete proof that FCC-HP-FOLD is NP-hard.** One of the two halves is now done.

1. **Completeness of the reduction is proved** (Theorem 54). For every yes-instance of 3-PARTITION the word w of Section 6 has a fold with gap exactly 9m. The two constructions that were missing (B and C of Section 24) are written, and the first construction lemma (Lemma 45) is replaced by a stronger one. Whole folds were built for seven small yes-instances with the exact word of the reduction, up to 36.8 million residues, and a checker that knows only the coordinates and the word confirms gap = 9m for each.
2. **Soundness is exactly where it was.** It rests on Conjecture R (statements A1 and A2 of Section 24), which is open for long chains that do not start at a local top. Nothing in this pass bears on it.

So what is proved to date: if the 3-PARTITION instance is a yes-instance, the fold exists; the converse holds if Conjecture R holds, or (twenty-second pass) if the inequality (L_n) of Section 45 holds, or (twenty-fourth pass), for n ≥ 46,656·m + 2, if the count (A) of Section 47 holds.

**Seventeenth pass (same day): asked again to finish the proof, I could not, and nothing new is proved.** The pass went into Conjecture R, on paper only; no script was run. Three things were tried, recorded here so that they are not tried again without a new idea.

1. *Charging a long chain at both ends* (1.5 units at each end instead of 3 at its start). The end of a growing chain is an equator, whose convex corners are local tops of the lateral directions, and a local top can be such a corner for at most four chains. Counted this way the octahedron is tight (6 chains, 24 corners, 6 tops), and so are two octahedra tip to tip and two octahedra overlapping side by side (by hand: 40 corners on tops for 10 tops in both, 12 chains). The two chains in excess of the tops are then chains that end by merging, or equators with a blocked corner. These need units at a junction that are not top units, which is the missing statement of Section 15 seen from the side. No gain.
2. *Cutting below the neck.* Take a long chain that does not start at a local top, cut the body at a clean plane just below the first pieces of the chain, and close both parts by regular caps. In the lower part the chain now starts at a top. With Theorem 36 on both parts the count is exactly additive: the units of the caps equal 3 per new top, and the bound for the whole body comes out short by 3 for this chain. So an induction over such cuts returns only what is put in; the 3 units have to be found at the connection itself, as in Section 17.4.
3. *A reading of Lemma 34.* Applied repeatedly, in both orientations, it says: around every r × r block of a slice, the plane at distance i contains the concentric block of side r − i − 52·U inside one piece, unless a piece with χ ≤ 0 is met on the way. So the body contains an octahedron of radius about r − 52·U around every such block. (Each step loses 1 + 4u, and the irregular squares number at most 13·U. Not checked by machine.) This suggests a different statement to aim at: every inscribed octahedron that cannot be enlarged has, in each of the six directions, either a local top or a connection to the rest of the body that carries 3 units of its own. I have not shown that this implies Conjecture R, and it has the same hard case: a connection under a roof.

**Eighteenth pass: see Part IV** (`claude/fcc-hp-hardness-attempt-part4.md`, Sections 33 to 41, Lemma 55, code in `claude/fcc-verification-code-15.md`). It was written in another session and compares this attempt with a manuscript on the tetrahedral lattice; by its own summary it contains no new step of the FCC proof and nothing that bears on Conjecture R. Section numbers here continue after it.

**Nineteenth pass (same day): a search for a counterexample to Conjecture R found none. Nothing new is proved.** Before putting more work into a proof I tried to break the conjecture by machine (Section 42; code in `claude/fcc-verification-code-16.md`).

1. *What was searched.* All connected unions of two regular octahedra for four pairs of sizes (374 bodies); every body at one site from O_5, …, O_8 and at two sites from O_5 (22,471 bodies); local searches by single sites from 209 starting bodies, over the whole boundary and around the contact of two lumps; 538 bodies made of a roof over two legs, a crude version of the configuration for which Conjecture R has no argument. For each body the least number of units U* is computed exactly, and compared with what the body holds.
2. *What came out.* No body with more than U*/3 long chains (counted geometrically, see Section 42), none that holds more than Conjecture R allows, and no body other than a regular octahedron with 18 units or fewer. The cheapest connection between two lumps that turned up is one vertex next to another; it costs 8 units over the 36 of two separate octahedra, for every size tried, where the reduction needs it to cost 1. Local search did not lower it. (Corrected in the twentieth pass: a connection through one extra site costs 7; Section 43.5.)
3. *What it is worth.* It is evidence and not a proof. The bodies have at most 978 sites and the moves are single sites, so a counterexample that needs a large or intricate structure is out of reach. The risk that the route fails because Conjecture R is false is smaller than it was; the missing argument (a long chain that starts below a split) is as missing as before.

**Twentieth pass (same day): asked again to finish the proof, I could not.** The pass produced an exact formula, two counting lemmas, a new conjecture that would settle the split case, and one correction (Section 43; code in `claude/fcc-verification-code-17.md`).

1. *Proved.* The least number of units of a body is a sum over its boundary of (number of neighbours on the other side − 3), plus 3 for every coat site and every surface site that the two matchings leave out (Lemma 56). For a connected body the number of local tops is 6 − 2b + σ, with σ the number of splits and merges of slice pieces and b the number of independent cycles of the three piece graphs (Lemma 57). The chains that start at a local top or below a split number at most 2T − 6 + 2b, whatever their length (Lemma 58).
2. *Conjectured.* **Conjecture G: U ≥ 6·|𝒯| − 18** for every component with at least two sites, where Theorem 36 has 3·|𝒯|. In words: 3 units for each of six tops and 6 for every further one. It holds for all 651,629 connected sets with 2 to 7 sites, for 4,323 larger bodies, and no search has broken it. With Lemma 58 it gives: in a body whose piece graphs have no cycle, the chains that start at tops or below splits number at most U/3 (Proposition 59). That is the case for which I had no route. Conjecture G does not mention chains.
3. *Not settled by G.* G itself has no proof, and its equality cases include bodies other than the octahedron, so it does not give the sharp case. Long chains that start below a shrinking piece (waists) still have to be matched to tops with short chains or to splits and merges that start no long chain; that count is not proved. Starts next to holes and bodies with cycles are open; the obvious extension of G to cycles is false.
4. *Correction.* The cheapest connection between two lumps is not 8 units but 7 (Section 43.5). Still no connected body with two lumps and 36 units or fewer.

**Twenty-first pass (15 Nov): I tried to prove Conjecture G and could not.** What the attempt gave is in Section 44 (code in `claude/fcc-verification-code-18.md`).

1. *Proved, and small.* The formula of Lemma 56 holds for every fold, not only for the best decoration (Lemma 60). And everything the fold says about its H-set is four counts: its size, its boundary, its surface and its coat (Proposition 61). Soundness is the statement (E) that these four counts force m octahedra; no units or chains occur in it.
2. *G has no proof by local accounting.* The forms of G whose two sides are sums of local terms are false: the one with cycles (Section 43.3) and the one with the Euler characteristic of the surface (Section 44.3). Both hold for all sets with up to 7 sites and for the bodies with few units, and both fail for porous bodies. So a proof of G must use that the body has no handles, or that it has few units.
3. *What G says locally.* For a body with flat faces away from its units, G is the sum over the clusters of units of: units ≥ 6·(tops in the cluster) − 3·(curvature of the cluster). This fits every equality case, and it puts the least price of a connection between two lumps at 12 (13 is the least found, 7 is what the reduction needs). It is a reading of G, not a proof.
4. *Three inductions failed* (Section 44.6): on the number of sites, on the number of tops by cutting at a split, and one axis at a time.

**Twenty-second pass (15 Nov): asked again to finish the proof, I could not.** Soundness is now reduced to one linear inequality between three counts of a finite set, and one of the three terms into which it splits is proved non-negative (Section 45; code in `claude/fcc-verification-code-19.md`).

1. *Proved: a new sufficient statement.* For a finite set S with boundary ∂ and matching numbers ν₁, ν₂ put Λ_n(S) = (4n² − 9n + 3)·∂ − 3n·((2n − 6)·ν₁ + (2n − 3)·ν₂). Statement (L_n): Λ_n ≥ 0 for every connected set, with equality only for O_n. If (L_n) holds for the n of the reduction, the reduction is sound (Proposition 62). Λ_n(O_r) = 36·(n − r)². Volume, chains, the length J and the error polynomial F do not occur, n need not be large against m, and A1 and A2 are both contained in the one inequality.
2. *Proved: a decomposition.* Λ_n = M_n + 3B + 3D_n⁺ for every finite set (Proposition 64), where the three terms are defined by the runs of S on lattice lines that lie open on a face (silhouette runs). B ≥ 0 for every set (Lemma 63, by enumeration of 4,096 neighbourhoods) and D_n⁺ ≥ 0 by definition. So (L_n) follows from (M_n): M_n ≥ 0, which says that the silhouette runs with at most n sites are paid for by units.
3. *Evidence.* No set with Λ_n < 0 among 24,396 bodies of the families of Sections 42 and 43 and from 40 annealing starts; the least value over bodies that are not regular octahedra is 38. M_n ≥ 0 for every n ≥ 6 in all bodies tested. For n ≤ 5 it fails for some of them, so (M_n) can hold only from some n on. (**Corrected in the twenty-third pass:** for octahedra with an island on a face, a family not tested here, M_n < 0 up to n = 9. (M_n) is replaced by (M′_n) of Section 46.)
4. *Not proved.* (M_n), or (L_n) by any other way. In the model of Section 44.4 it asks, for each corner of a face, for 3/4 of a unit at a vertex and 3/8 at a saddle, which is 3 units for a vertex and 1.5 for a saddle; G asks for 3 at a saddle, and A1 for 3 where two growing pieces merge. In the lattice it is again a count that has to hold for every body, and I have no argument for it.

**Twenty-third pass (15 Nov): asked again to finish the proof, I could not.** One statement of the pass before turned out wrong and is corrected; the decomposition is repaired, and the open statement is sharper and has survived every test (Section 46; code in `claude/fcc-verification-code-20.md`).

1. *Correction.* (M_n) does not hold from n = 6 on. A one-layer triangular island on a face of an octahedron costs 3 units whatever its size, and with such islands M_n < 0 up to n = 6, 7, 8, 9 on O_9, O_13, O_17, O_21. The inequality (L_n) itself holds for all of them.
2. *Proved: the repaired decomposition.* Λ_n = M′_n + R_n with R_n ≥ 0 for every finite set (Proposition 65). M′_n counts the chords that are open at one end as well, at half weight. Also proved: E = H − H₂ − Π/3, where Π is the sum of a potential π that is defined at each surface site by its neighbours and the exposure of theirs, vanishes at every site of a face, of a ridge and of a regular trough, and is 9 at a vertex of an octahedron (Lemma 66). With it, M′_n ≥ 0 reads: the silhouette runs with at most n sites are paid for by the units, by n times the potential, and by the chords with a blocked end.
3. *Conjectured.* (I_n): M′_{n+1} ≥ M′_n for every n ≥ 3. Together with M′_4 ≥ 0 this gives (L_n) for every n ≥ 4. Among 24,212 bodies, including 425 with islands, (I_n) has no exception for any n, and M′_n < 0 only for n = 3 and six bridged pairs. Equality in (I_n) occurs for the octahedra and for an island at n = 4.
4. *What the count needs.* Where two growing pieces merge, no nested family of silhouette runs begins. So the configuration for which the count by chains had no argument, a long chain that starts below a split, needs no units here. Units are needed at the corners of faces and at the ends of short troughs, 3/4 for each at leading order. These are statements of the kind proved for tops and waists in Part II; none of them is proved.

**Twenty-fourth pass (15 Nov): asked again to finish the proof, I could not.** Soundness for n large against m now follows from a count in which n does not occur; the count is open (Section 47; code in `claude/fcc-verification-code-21.md`).

1. *Proved: a reduction.* Call a silhouette run active if its two end sites have the shape of a ridge, and let a_L be the number of active runs with exactly L sites. Statement (A): 3·a_L ≤ 4·U* − 1 for every L and every connected set with at least two sites that is not a regular octahedron. If (A) holds, the reduction is sound for every n ≥ 46,656·m + 2 (Theorem 69), which the reduction allows, because n = 3Bt + 2 with t free. (A) contains no n, no potential and no half-open chords; all of that is absorbed in an error term of 99n for each site that has not one of the three shapes of Lemma 20.
2. *Proved: the frame of the count.* An active run of L sites is the level L − 1 of one fan, the rows of a triangle counted from a corner (Lemma 68). Walking from its ends towards the tip along the two ridges one meets a site of irregular shape before or at the tip (Lemma 70), and for one length, face and line a site is met first by at most one run (Lemma 71). A fan that begins with two sites has its tip at a site with four occupied neighbours below and at least three empty ones beside it, and such a tip has in its own neighbourhood the 3/4 of a unit per fan that (A) asks for (Proposition 72 with Lemmas 20 and 44).
3. *Evidence.* (A) has no exception among 24,727 bodies, now including 540 with pits, and none was found by annealing. The least value of 4U* − 3·a_L over bodies that are not regular octahedra is 3, for octahedra with an island.
4. *Three counts are false* that would have done the same service: the number of fans (31 against 21 units), the number of beginnings of families of runs (33 against 21), and the number of beginnings counted along ridge segments (60 against 56). In each case a step on a face or on a ridge ends one family and begins another, at no cost. Only the number of runs of one length is bounded.
5. *Not proved.* (A). What is missing is the count of the local configurations at which fans begin against the units there, with the sharing between neighbouring ones. The charge of a run cannot simply stay at the nearest site of irregular shape: such a site on a ridge takes over runs from the vertex behind it.

| Item | State |
|---|---|
| Everything in the tables of Parts I and II that is not listed below | As there |
| Cut slice: a slice traversed so that the two sites at a cut are neighbours on one side (Lemma 49) | **Proved** (new); construction, checked by machine for every slice size up to 44 and every cut position |
| Pairing of the singly decorated sites around the run ends (Lemma 50; this was B of Section 24) | **Proved** (new); checked by machine for all positions of the run ends, n = 14, …, 24 |
| Interior paths with fixed outer ends and neighbouring ends at each cut (Lemma 51; replaces Lemma 45) | **Proved** (new); checked by machine for every cut position, N up to 22 |
| One octahedron of the intended fold, for every triple (Proposition 52) | **Proved** (new); checked on instances of the reduction up to n = 122 |
| P-runs of one common length (Lemma 53; this was C of Section 24) | **Proved** (new); explicit routing |
| Completeness of the reduction (Theorem 54) | **Proved** (new); seven complete folds checked independently |
| Conjecture R (A1 and A2 of Section 24) | **Open**; implies soundness. A machine search for a counterexample found none (Section 42, nineteenth pass). Since the twenty-second pass it is one of two sufficient statements; the other is (L_n) below |
| U* = W + 3·def₁ + 3·def₂, with W a sum over the boundary graph and the shortfalls in Hall form (Lemma 56) | **Proved** (twentieth pass) |
| T = 6 − 2b + σ for a connected body (Lemma 57); chains that start at a top or below a split number at most 2T − 6 + 2b (Lemma 58) | **Proved** (twentieth pass) |
| Conjecture G: U ≥ 6·|𝒯| − 18 | **Open** (new, twentieth pass); no violation in 651,629 small sets, 4,323 bodies and the searches; with Lemma 58 it gives Conjecture R for chains that start at tops or below splits in bodies without cycles (Proposition 59). No proof by local accounting exists (Section 44.3) |
| U = W + 3n₀ + 3u for every fold (Lemma 60); the H-set of a fold with gap at most 9m has |S| = m·|O_n|, ∂ ≤ 12mn², s ≥ m·s_n, c ≥ m·(c_n − 12) (Proposition 61) | **Proved** (twenty-first pass) |
| (E): a set with these four properties is m copies of O_n | **Open**; it is what soundness needs, stated without units |
| (L_n) implies soundness for that n (Proposition 62); Σ(|C| − ½) ≤ ∂ over the silhouette runs C (Lemma 63); Λ_n = M_n + 3B + 3D_n⁺ (Proposition 64) | **Proved** (twenty-second pass); Lemma 63 rests on an enumeration of 4,096 neighbourhoods |
| (L_n): Λ_n(S) ≥ 0 for every connected set, with equality only for O_n | **Open** (new, twenty-second pass); implies soundness without Conjecture R; no violation in 24,396 bodies and from 40 annealing starts |
| (M_n): the silhouette runs with at most n sites are paid for by units; (K): at most (4/3)·U·j silhouette runs with at most j sites | (M_n) implies (L_n), but **fails up to n = 9** for octahedra with islands (twenty-third pass) and is no longer used. (K) is open; no violation, least slack 0 for an island |
| Λ_n = M′_n + R_n with R_n ≥ 0, where M′_n counts half-open chords too (Proposition 65); E = H − H₂ − Π/3 with a local potential π that vanishes on faces, ridges and regular troughs (Lemma 66); the increment M′_{n+1} − M′_n (Proposition 67) | **Proved** (twenty-third pass); identities, checked by machine on bodies |
| (I_n): M′_{n+1} ≥ M′_n for n ≥ 3; and M′_4 ≥ 0 | **Open** (new, twenty-third pass); together they give (L_n) for n ≥ 4. No exception in 24,212 bodies |
| Active runs and fans; blockers and open ends by shape; ridge segments end at sites of irregular shape (Lemma 68). Λ_n ≥ (2n² − 3n)·U* − 3·Σ_L a_L·(n + ½ − L)₊ − 9n·def₁ − 99n·|I|, and (A) implies soundness for n ≥ 46,656·m + 2 (Theorem 69). Roots (Lemma 70); one run per site, face and line (Lemma 71); tips of fans that begin with two sites (Proposition 72) | **Proved** (twenty-fourth pass); Lemma 68 and Proposition 72 rest on enumerations of 4,096 neighbourhoods and of the 24 kinds of fan; all checked by machine on bodies |
| (A): 3·a_L ≤ 4·U* − 1 for every L, for every connected set with at least two sites that is not a regular octahedron | **Open** (new, twenty-fourth pass); no n occurs. No exception in 24,727 bodies; least slack 3 |
| The number of fans, of beginnings of families, of beginnings along ridge segments is at most 4/3 (or 8/3) of the units | **False** (twenty-fourth pass; Section 47.5) |

**What changed in the reduction.** Nothing in the word. Two parameters that Section 6 left open are now fixed (Section 26): n = 3Bt + 2 with t even and t ≥ 4, and λ = 92mn² + 188mn + 14n + 46.

**What is superseded.** Lemma 45 and the sweep along the x-axis (Section 19): replaced by Lemma 51. Lemma 46 is not used. Lemma 47 is used without switches. Lemma 48 is the case of Lemma 50 without run ends. The parity criterion of Section 25 is not needed: the pairing no longer depends on n modulo 4.

**Estimate.** Unchanged: about 1 in 5 for a complete written proof within the next several passes of this size, a little under 1 in 2 eventually along this route. Both figures were set by Conjecture R. After the nineteenth pass I leave both where they are: the search makes it less likely that the conjecture is false, but the figures were mostly about whether I can find the argument for splits, and on that there is nothing new. After the twentieth pass: the near-term figure stays at 1 in 5; the eventual one I now put at about 1 in 2. The split case has a route that needs no argument over many planes (Conjecture G with Lemma 58), but the route rests on a new inequality that is sharp in several ways and has no proof, and the count for waists is still to be done. After the twenty-first pass: near term about 1 in 6, a shade lower, because the most direct way to prove Conjecture G is now excluded; eventually about 1 in 2, unchanged. After the twenty-second pass: near term about 1 in 6, unchanged; eventually a little over 1 in 2. The target is now one exact inequality that a machine can test on any body, it needs half of what G needs at a saddle, and one of its three terms is proved. What is left is still a count that must hold for every body, and for that I have no argument. After the twenty-third pass: near term about 1 in 5, eventually about 3 in 5. The count in its repaired form has no exception in any body tried and is exact at every scale, and the case that blocked the count by chains (a start below a split) does not occur in it. Against that: the pass before this one recorded a threshold that was wrong, which is a reminder of how little the tests cover; and the local statements that are needed now (units at corners of faces and at the ends of troughs, with the sharing between them) are not proved. After the twenty-fourth pass: unchanged, near term about 1 in 5, eventually about 3 in 5. The open statement no longer contains n, lower-order terms or half-open chords, and its frame is proved. What is left is the sharp count of local configurations against units, with sharing, which is the step that has been missing since the fourteenth pass; and three forms of it that looked natural turned out false in this pass, which says that the right form is narrow. Part II expected the two constructions to take two or three passes; they took one, which removes a risk that was small.

**Caveat on the new proofs.** Lemmas 49 to 53 are constructions. Each proof is a description that can be followed case by case, and each is backed by a script that runs the construction over a range and checks the result from the definitions. In the range of the reduction itself (n = 3Bt + 2 ≥ 38) the parts were checked separately; a whole fold there has several hundred million residues at least and was not built. The whole folds that were built have n = 8, …, 14.

## 26. The reduction with all parameters fixed

As in Section 6, with

* n = 3Bt + 2, where t is even, t ≥ 4, and t is at least as large as soundness requires (Proposition 30 and the remark after Conjecture R). So N := n − 2 = 3Bt is even and at least 36, |O_N| = Bt(2N² + 1), and M = t(2N² + 1);
* λ = 92mn² + 188mn + 14n + 46 (even).

    w = P^λ · Π_{i=1..3m} ( H^{a_i·M+2} P^λ ) · ( H P^λ )^{m(16n−18)} · ( HH P^λ )^{m(2n²−12n+9)}.

n even is used in Lemma 50 (each piece has an even number of sites); t ≥ 4 keeps the cuts away from the equator (Lemma 51(d)); the value of λ comes from Lemma 53. The soundness arguments of Parts I and II use only the numbers of H's with zero, one and two neighbours P and the lengths of the item runs, so they are not affected.

## 27. The cut slice

A slice of O_N by a plane z = const is a square of k × k cells with the adjacency of the square grid (Section 19). Rows and columns are numbered 0, …, k − 1. The *row snake* takes the rows in order, alternating direction, from (0, 0).

**Lemma 49 (cut slice).** Let k ≥ 3 and 1 ≤ o ≤ k² − 1. The k × k square has a Hamiltonian path that starts at the corner (0, 0), ends at a corner, and whose cells number o and o + 1 are adjacent and lie on one side of the square (the *cut pair*). Its mirror image in the diagonal through (0, 0) is another such path. If the cut pair contains a corner, then in one of the two paths this corner is the clockwise end of the side that contains the pair, and in the other the counterclockwise end.

Proof. Write o = qk + s with 0 ≤ s < k.

*Plain* (s = 0 or q = 0): the row snake. For s = 0 the cut pair is the end of row q − 1 and the start of row q, in one column; for q = 0 it lies in row 0.

*Forward* (1 ≤ q ≤ k − 2, s ≥ 1). Row q − 1 of the snake ends in a column A, which is 0 or k − 1. The first part consists of rows 0, …, q − 2 as in the snake, row q − 1, and s cells of row q:

* s odd: row q − 1 up to the last s columns before A; then these s columns, two cells at a time (rows q − 1 and q), towards A. It ends at (q, A), and the second part starts at (q + 1, A).
* s even: row q − 1 up to the last s + 1 columns; then the s columns before the column A, two cells at a time; then (q − 1, A). The second part starts at (q, A) and goes to (q + 1, A).

In both cases the cells of row q that are left form a *ledge* of ℓ cells at the side opposite A, ℓ = k − s for odd s and ℓ = k − 1 − s for even s, and the second part stands at (q + 1, A) with the rows q + 1, …, k − 1 untouched.

* ℓ even: row q + 1 from A to the ledge; the ℓ columns under the ledge two cells at a time (rows q + 1 and q), which ends in row q + 1 at the far side; then rows q + 2, … as a snake.
* ℓ odd, ℓ ≥ 3 and q ≤ k − 3: now k − ℓ is odd. The k − ℓ columns that are not under the ledge two cells at a time (rows q + 1 and q + 2), which ends in row q + 2; then the 3 × ℓ block under the ledge: up its first column to row q, row q to the far side, one cell down, row q + 1 back to the second column of the block, one cell down, row q + 2 to the far side; then rows q + 3, … as a snake.

*Reversed*: the forward construction for k² − o, read backwards and reflected so that it starts at (0, 0).

*Special* (k even). o = 2k − 2: row 0 up to column k − 2, row 1 back to column 0; the cut pair is (1, 0), (2, 0); then the rows 2, …, k − 1 column by column from column 0, which ends at (2, k − 1); then (1, k − 1), (0, k − 1). o = 2k − 1: row 0, then column k − 1 down to (k − 1, k − 1); the cut pair is (k − 1, k − 1), (k − 1, k − 2); then column k − 2 up to row 1, row 1 to column 0, and the rows 2, …, k − 1 of the columns 0, …, k − 3 as a snake from (2, 0), which ends at (k − 1, 0). And the reversals of these two.

*All cases are covered.* ℓ is odd exactly when k is even. So for odd k the plain and forward constructions cover every o with q ≤ k − 2, and q = k − 1 is covered by the reversed one (then k² − o < k). Let k be even. Forward fails only for ℓ = 1 (s = k − 1 or k − 2), for q = k − 2, and for q = k − 1; reversed, which is forward with q′ = k − 1 − q and s′ = k − s, fails only for s = 1 or 2 and for q = 1 (for q = k − 1 it is plain). Both fail only for q = 1 with s ∈ {k − 1, k − 2} and for q = k − 2 with s ∈ {1, 2}, that is for o = 2k − 1, 2k − 2 and their complements k² − o, which are the special cases.

*The mirror image.* Reflection in the diagonal fixes the corner (0, 0), maps sides to sides and reverses the sense of rotation. ∎

Check (`slicepath.py`): for k = 3, …, 44 and every o, the constructions give a path with all the stated properties, and for every cut pair that contains a corner the mirrored pair lies on the other side at its corner.

## 28. The pairing

**Rows of a piece.** Take the decoration of Lemma 47 without switches, n even. In the piece with x, y > 0 the singly decorated sites are (ξ, η, z) with ξ ≥ 2, η ≥ 1, ξ + η + |z| = n − 1, except (n − 3, 1, ±1) and (n − 2, 1, 0). The *row* z consists of the sites with that z, ordered by ξ; its *left end* has ξ = 2. The rows z = n − 4, …, 2, 1, 0, −1, −2, …, −(n − 4) have 1, …, n − 5, n − 5, n − 4, n − 5, n − 5, …, 1 sites. Two sites of the piece are adjacent exactly if they are neighbours in a row, or one is the i-th site of a row z ≠ 0 and the other the i-th or the (i + 1)-th site of the next row towards the equator. The other three pieces have the same structure, with ξ = |y| and η = |x| where xy < 0 (`surface.py` checks all of this for n ≤ 30). The right end of a row has η = 1, except in the row 0 and in the rows ±1. The two *tips* of a piece are its rows ±(n − 4).

Consequences: (S1) the left ends of two consecutive rows are adjacent, and so are their right ends. (S2) List the sites of two consecutive rows alternately from the left, starting with the row nearer to the equator: u_1, u_2, u_3, …. Then u_i is adjacent to u_{i+1} and to u_{i+2}. So if a set Q contains no two consecutive u_i, the sites outside Q form a path in this order; and the first two sites of that path may be exchanged if they are u_1, u_2 and the third is u_3, likewise the last two.

A *band* is a row, traversed from one end to the other, or a *strip*: two consecutive rows, traversed in the order of (S2) or backwards.

**Defects.** A defect of kind (a) is a pair of neighbouring sites of one row z. A defect of kind (b) is the pair of right ends of two consecutive rows. A defect is *admissible* if its rows have 4 ≤ |z| ≤ n − 9; it is an upper or a lower defect according to the sign of z.

**Lemma 50 (pairing).** Let n ≥ 14 be even, P a piece, and R the union of at most one admissible upper defect and at most one admissible lower defect; for the piece x, y > 0, R may in addition contain the two tips. Then the sites of P outside R form a path, and since their number is even they fall into adjacent pairs.

Proof. A sequence of bands that contains every row once, in order from the top, is a path as soon as each band starts at a site adjacent to the last site of the band before. By (S1) this holds for rows without removed sites. A strip of two rows without removed sites can be entered at the left end of its upper row and left at the right end of its lower row, or the same with left and right exchanged: take the order of (S2) or its reverse and exchange the first two or the last two sites if necessary. So every band leads from one side of the piece to the other, and replacing two consecutive rows by a strip changes the side on which all later bands are entered.

*An upper defect.* Let a_1, …, a_L be the row z of the defect, c_1, …, c_{L−1} the row above, b_1, …, b_{L+1} the row below and d_1, …, d_{L+2} the row below that; L ≥ 6.

Kind (a), a_i and a_{i+1} removed. The order of (S2) for the rows a, b is b_1, a_1, b_2, …, b_L, a_L, b_{L+1}; the removed sites are not consecutive in it. If i ≥ 2, exchanging the first two sites gives a path from a_1 to b_{L+1}; a_1 is adjacent to c_1 and b_{L+1} to d_{L+2}. If i ≤ L − 2, the reverse order with its first two sites exchanged is a path from a_L to b_1; a_L is adjacent to c_{L−1} and b_1 to d_1. So the strip a, b can be entered from the left unless i = 1 and from the right unless i = L − 1.

Kind (b), a_L and b_{L+1} removed. Entered from the left: the rows a, b, d as single rows, a_1 … a_{L−1}, b_L … b_1, d_1 …. Entered from the right, at a_{L−1}, which is adjacent to c_{L−1}: the row a_{L−1} … a_1, then the strip b, d, whose order d_1, b_1, d_2, …, b_L, d_{L+1}, d_{L+2} without b_{L+1} is a path; exchanging its first two sites gives a path from b_1 to d_{L+2}. So a defect of kind (b) can be entered from either side.

*A lower defect* is the mirror image in the plane z = 0, and a path read backwards is a path; so the same holds with "left at" in place of "entered from".

*Assembly.* Take single rows everywhere, except the strips named above. The side on which the top row starts is free (for the piece x, y > 0 without its tips the top row has two sites); choose it so that the upper defect is entered from an allowed side. The rows 1 and 0 are untouched, since all rows named above have |z| ≥ 2. Taking them as two rows or as one strip changes the side on which the bands of the lower half are entered; choose so that the lower defect is left on an allowed side. ∎

Check (`pairtest.py`, `strips.py`). `surface.pairing` searches exactly this family: rows and strips in order, the first two or the last two sites of a strip exchanged or not. For the piece x, y > 0 without its tips and for the piece x < 0 < y, every upper defect, every lower defect, and the combinations of one upper and one lower defect (all of them, or 6,000 random ones where there are more) were paired without a failure: with the defects in the rows 4 ≤ |z| ≤ n − 9 for n = 14, …, 24, and in the wider range 3 ≤ |z| ≤ n − 7 for n = 12, …, 20. At most three strips were needed (n = 14, 16, 18). Outside the range of the lemma the search can fail: with all rows 1 ≤ |z| ≤ n − 6 allowed it fails for 2 of 961 combinations (n = 12) and 2 of 2,500 (n = 14), namely when the two defects sit at the same end of the rows 1 and −1.

## 29. The interior paths

Notation: N ≥ 8, the slice z = c of O_N is the square of k × k cells with k = N − |c|; its four sides are the sets σ_x·x ≥ 0, σ_y·y ≥ 0, |x| + |y| = k − 1 for the four sign pairs σ, and its four corners lie on the four half-axes. Say that the half-axis +x *belongs* to σ = (+, +), +y to (−, +), −x to (−, −), −y to (+, −): to the side that follows it counterclockwise. For a side σ, the corner on its own half-axis is its *good* corner, the other its *bad* corner. W(c) is the number of sites of O_N with z > c. A cut after the first C sites *falls into* the slice c if W(c) < C < W(c) + k², and *between* the slices c + 1 and c if C = W(c).

**Lemma 51 (interior paths).** Let C_1 < C_2 be cuts that fall into or between slices with 2 ≤ |z| ≤ N − 4. Then:

(a) O_N is the disjoint union of three paths with C_1, C_2 − C_1 and |O_N| − C_2 sites. The first starts at (1, 0, N − 2), the third ends at (1, 0, −(N − 2)).

(b) At each cut, the last site p of one path and the first site q of the next are adjacent, and there is a sign pair σ such that either p and q lie on the side σ of one slice and neither is its bad corner, or p and q are the corners of two consecutive slices on the half-axis that belongs to σ.

(c) With n = N + 2 and the decoration of Lemma 47: e = p + (σ_x, σ_y, 0) and f = q + (σ_x, σ_y, 0) are singly decorated sites of the piece σ of O_n, adjacent to p and q. In the first case of (b) they form a defect of kind (a) in the row z of p and q; in the second a defect of kind (b).

(d) In the reduction (N = 3Bt, cuts C_1 = a_1·M and C_2 = (a_1 + a_2)·M with B/4 < a_i < B/2 and a_1 + a_2 + a_3 = B), C_1 falls into or between slices with t ≤ z ≤ N/4 and C_2 into or between slices with −N/4 ≤ z ≤ −t.

Proof. (a), (b). The path: (1, 0, N − 2), the top vertex, (0, 1, N − 2), (−1, 0, N − 2), (0, −1, N − 2); then the slices z = N − 3, …, −(N − 3), each from a corner to a corner; then three sites of the slice z = −(N − 2), the bottom vertex, and (1, 0, −(N − 2)). The corner of a slice on a half-axis is adjacent to the corner of the next slice on the same half-axis, and the next slice is entered there; the first of these slices is entered at (0, −2, N − 3). A slice without a cut is traversed by the row snake. A slice into which a cut falls, after o of its sites, is traversed by one of the two paths of Lemma 49, placed so that (0, 0) is the entry corner. If the cut pair contains no corner, either path will do. If it contains a corner, then by Lemma 49 one of the two paths has it as the clockwise end of the side of the pair, which is the good corner of that side. For a cut between two slices the pair consists of the two corners on one half-axis. The last slice, of 3 × 3 cells, must be left on the y-axis, so that the path can continue (0, ±1, −(N − 2)), (−1, 0, −(N − 2)), (0, ∓1, −(N − 2)), bottom vertex, (1, 0, −(N − 2)): if it is entered on the y-axis the row snake ends at the opposite corner; if on the x-axis, use (0,0), (0,1), (0,2), (1,2), (2,2), (2,1), (1,1), (1,0), (2,0), which ends at a neighbouring corner.

(c) Let σ = (+, +) and |z| ≥ 2. A site of the side that is not the bad corner is (a, b, z) with a ≥ 1, b ≥ 0, a + b + |z| = N − 1 = n − 3; so e = (a + 1, b + 1, z) has ξ ≥ 2, η ≥ 1, ξ + η + |z| = n − 1 and is not one of the three exceptional sites. Two neighbours on the side differ by (1, −1, 0), and so do e and f. On the half-axis +x, p = (a, 0, z) gives e = (a + 1, 1, z), the right end of its row. For σ with σ_xσ_y < 0 exchange the roles of |x| and |y|; the bad corner is then the one with y = 0.

(d) Let j = a_1 or a_1 + a_2, so that the cut is C = j·|O_N|/B; then 2j ≠ B, because a_1 < B/2 and a_1 + a_2 = B − a_3 > B/2. Hence |C − |O_N|/2| ≥ |O_N|/(2B) = t(2N² + 1)/2 > tN². The sites with |z| ≤ t − 1 are fewer than (2t − 1)N² and occupy a block of consecutive positions of the path, symmetric about its middle. A cut pair with a site in this block would have |C − |O_N|/2| ≤ (t − 1/2)N². So both sites of each cut pair have |z| ≥ t; C_1 < |O_N|/2 < C_2 gives the signs. If a site of the first cut pair lies in a slice z_0 > 0, then C_1 is at most the number of sites with z ≥ z_0, so N³/6 < |O_N|/4 < C_1 ≤ (N − z_0 + 1)³/3 and z_0 < 0.21N + 1 ≤ N/4 for N ≥ 36; the second cut is the mirror image. ∎

Check (`interior3.py`, `canon.py`): for N = 8, …, 22, every first cut with more than a quarter and less than half of the sites, and two second cuts (the mirror position and a random one): 8,757 pairs of cuts without a cut pair in the slice z = 0, no failure of (a), (b), and for the cut pairs in slices |z| ≥ 2 the run ends found by search are those of (c). Cut pairs that touch the slice z = 0 fail in about four cases of ten (for one thing, the four vertices of the interior have no singly decorated neighbour); by (d) they do not occur.

**Proposition 52 (one octahedron).** Let n = 3Bt + 2 with t even, t ≥ 4, and a_1 + a_2 + a_3 = B with B/4 < a_i < B/2. Then there is an arrangement on O_n of three paths of H's with a_i·M + 2 sites, 2n² − 12n + 9 adjacent pairs of sites and 16n − 18 single sites, covering O_n, and an assignment of coat sites (*slots*) to the two ends of each path (one each), to the sites of the pairs (one each) and to the single sites (two each), such that in every fold in which these are the H-runs of an isolated copy of O_n and the chain P's sit on the slots, the copy carries exactly 18 defect units.

Proof. Slots: the decoration of Lemma 47 without switches. Interior: Lemma 51 with C_1 = a_1·M, C_2 = (a_1 + a_2)·M; by (d) its hypothesis holds. Ends of the three paths: the tips (2, 1, n − 4) and (2, 1, −(n − 4)) of the piece x, y > 0, which are adjacent to (1, 0, N − 2) and (1, 0, −(N − 2)), and the sites e, f of Lemma 51(c) at the two cuts. These six sites are different: the first cut gives sites with t ≤ z ≤ N/4, the second with −N/4 ≤ z ≤ −t, and N/4 < n − 4. In each piece the removed sites are at most one upper and one lower defect, admissible because 4 ≤ t ≤ |z| ≤ N/4 ≤ n − 9, and the tips in one piece; Lemma 50 pairs the rest. The doubly decorated sites are the single sites. The units depend only on the H-set and on the chain P's of each H (Theorem 5), and for this decoration they are 3 at each vertex (Lemma 47). ∎

Check (`octa.py`): the arrangement was built and verified from the definitions (cover, counts, adjacency, 18 units) for all triples of the instances (B, t) = (3, 4), (7, 4), (10, 4), (10, 2), (11, 2), (13, 2), (17, 2), n up to 122 (those with t = 2 are below the range of the reduction), and, outside the range of the reduction, for n = 18, …, 24 with every first cut whose slices have |z| ≥ 3 (1,542 pairs of cuts); no failure.

## 30. P-runs of one common length

**Setting.** m copies of O_n are placed at (0, 0, jD), j = 0, …, m − 1, with D = 2n + 6; all coordinates below are those of the common lattice. A *slot* is a coat site of one of the copies. Slots are grouped into disjoint pairs, except two single ones. P is the number of slots, P ≤ m(4n² + 8n − 12).

**Lemma 53 (routing).** For every λ ≥ 92mn² + 188mn + 14n + 46 there are pairwise disjoint paths, one for each pair of slots, with exactly λ sites, from one slot of the pair to the other, and one for each single slot, with λ sites, starting at it, such that no path meets a copy of O_n, and no path meets the coat of a copy except in its end slots.

Proof. For a slot p = (x, y, z) let d_p = (s_x, s_y, 0) with s_x = sign x, s_y = sign y, a zero counting as +. Let val(p) = x − y if s_xs_y > 0 and x + y otherwise. Order the slots first by s_x (plus before minus), then by decreasing val, ties broken arbitrarily, and give the i-th slot the radius ρ_p ∈ {R + 3i, R + 3i + 1} of the parity of |x| + |y|, where R = 2n + 4. Number the paths and give the r-th the height Z_r = (m − 1)D + n + 4 + 2r.

The *route* of a slot p up to a height Z consists of

* the ray p + i·d_p, i = 0, …, until |x| + |y| = ρ_p;
* the arc: at height z, along |x| + |y| = ρ_p in the direction of increasing x, to (ρ_p, 0, z); for s_x < 0 it passes the corner (0, ±ρ_p, z);
* the column (ρ_p + (i mod 2), 0, z + i), i = 1, …, Z − z.

The path of a pair p, p′ with number r is the route of p up to Z_r, a bridge, and the route of p′ backwards. The bridge, in the plane z = Z_r, goes from the top (A, 0) of one column along (A + 1, 1), (A + 2, 2), (A + 3, 1), … to (X − 1, 1), then (X, 0), (X − 1, −1), (X − 2, −2), … to (A′ + 1, −1) next to the top (A′, 0) of the other column; here X has the parity of A, which is that of A′. A *kink* replaces a step from (x, 1, Z_r) to (x + 1, 2, Z_r) by the two steps through (x + 1, 1, Z_r + 1); up to three kinks are put on the first steps. The path of a single slot is its route followed by (A + 1, 1), (A + 2, 2), … for as long as needed.

*Each path is a path*: all steps are among the 12 vectors.

*Disjointness.* Rays: for i ≥ 1 the site p + i·d_p has |x| + |y| + |z − jD| = n + 1 + 2i for the copy j of p, so it is outside that copy and its coat, and it stays in the heights of that copy, which no other copy or coat reaches (D > 2n + 2). It has x, y ≠ 0 with the signs of d_p; so from the site one reads off d_p, then i, then p: rays of different slots are disjoint.

Arcs and columns lie in |x| + |y| ≥ R > n + 1, outside all copies and coats. Arcs of different slots lie on different radii. An arc and the ray of another slot p̃ can only meet if both slots belong to one copy and have the same z, and ρ_p̃ > ρ_p; the ray then crosses the radius ρ_p in one site c, with val(c) = val(p̃) and in the quadrant of d_p̃. If p̃ has s_x > 0 and p has s_x < 0, then ρ_p̃ < ρ_p by the order. If s_x < 0 for p̃ and s_x > 0 for p, the arc of p has x ≥ 0 and c has x < 0. If the s_x agree and the s_y differ, the arc and c lie on different sides of y = 0. If d_p̃ = d_p, then val(p̃) ≤ val(p) by the order, with equality excluded because two slots of one copy on one line of direction d_p would have different values of |x| + |y| + |z − jD|; and the arc of p, inside the quadrant of d_p, has val ≥ val(p). In no case is c on the arc.

Columns lie in the plane y = 0 with x in {ρ_p, ρ_p + 1}, different for different slots. Rays have y ≠ 0 outside the coat. An arc meets y = 0 only in its last site (ρ_p̃, 0, z).

Bridges lie in the heights Z_r and Z_r + 1, which are different for different paths and above everything else except columns; their only site with y = 0 is (X, 0, Z_r), and X is chosen larger than all ρ + 2.

*Length.* Let l, l′ be the numbers of sites of the two routes. The path has l + l′ + 2X − A − A′ − 1 + κ sites with κ kinks. Given λ, choose κ in {0, 1, 2, 3} so that λ − l − l′ + A + A′ + 1 − κ ≡ 2A (mod 4), and X from 2X = λ − l − l′ + A + A′ + 1 − κ. This is admissible if X ≥ ρ_max + 14. A route has at most ρ_p/2 + 1 sites on its ray, 2ρ_p on its arc and Z_r − z in its column, with ρ_p ≤ 2n + 3P + 2 and Z_r − z ≤ (m − 1)(2n + 6) + 2n + 4 + P; so λ ≥ 10n + 23P + 4mn + 12m + 36 suffices, and the bound of the lemma is larger. ∎

**Theorem 54 (completeness).** If a_1, …, a_{3m} can be split into m triples each summing to B, then the word w of Section 26 has a fold with Loss = 2n_1 + 2.5n_2 + 9m, that is, with gap 9m.

Proof. Place m copies of O_n as in Lemma 53; no two of them contain adjacent sites. Assign the triples to the copies and arrange each copy by Proposition 52. The blocks of H's of w, in order, are the 3m item runs, the m(16n − 18) single H's and the m(2n² − 12n + 9) pairs; map the item runs to the paths of Proposition 52 for their items, the single H's and the pairs to those of the copies, in any order. Each block has a slot at its first and at its last H (for a single H its two slots). The P-run between two consecutive blocks must join the slot at the end of one to the slot at the start of the next; the first and the last P-run have a free end. Every slot occurs exactly once, so Lemma 53 gives all P-runs, with exactly λ sites each. The result is a fold of w. Its H-set is m isolated copies of O_n, and every H has its chain P's on its slots; by Proposition 52 each copy carries 18 units, and 2·gap is the number of units (Theorem 5). ∎

Check (`fold.py`, `check.py`, `controls.py`). The fold was built in full for seven yes-instances: n = 8 (B = 73) with m = 2 in two arrangements and with m = 3; n = 10 (B = 43) in two arrangements; n = 12 (B = 10); n = 14 (B = 17). In the second arrangements the items of the two triples alternate in the word. The chains have 4.6 to 36.8 million residues. `check.py` reads only coordinates and word: consecutive residues adjacent, no site used twice, the word equal to that of Section 26 with λ = 92mn² + 188mn + 14n + 46, Loss counted from the definition, Lemma 1 satisfied, and gap = 9m in all seven. It rejects three altered inputs. These n are not of the form 3Bt + 2 with t ≥ 4, so they test the assembly and the routing, and the arrangement of Proposition 52 only as far as it happens to exist for small n.

## 31. What a complete proof still requires

Only statement A of Section 24: Conjecture R, as A1 (the count: at most U/3 long chains over the six directions, whatever their starts) and A2 (the sharp case). B and C are done. The position on A is that of the fourteenth pass: proved for chains that start at local tops; one chain per waist paid for; for splits no local count can work, and I have no argument.

After the search of Section 42 the order of work I would follow is: (i) the waist that starts a long chain in both orientations (Theorem 38 gives 3 units, 6 are needed, and the one example of the search has 14 around the waist); (ii) waists that take several planes; (iii) splits, where an idea is still missing. The search also says where not to look for tightness: at a connection between two lumps the count has at least 6 units to spare in every example (7 before the correction of Section 43.5), so an argument for (i) and (ii) may be allowed to lose a constant per connection.

After the twentieth pass the order changes: first Conjecture G (Section 43.3), which would replace (iii); then the count of Section 43.4 for the starts below shrinking pieces, which would replace (i) and (ii); then holes, cycles and the sharp case.

After the twenty-second pass there is a second way, which needs neither Conjecture R nor G: the inequality (L_n) of Section 45 for the one n of the reduction. For it, it is enough to prove (M_n) of Section 45.3 for that n. I would work on (M_n) first: it is exact, a script decides it for any given body, and holes, cycles and the sharp case are not separate questions in it.

After the twenty-third pass: not (M_n), which is false for small n in a range that grows with the body, but M′_4 ≥ 0 and (I_j) for 4 ≤ j < n (Section 46.4). The order of work is in Section 46.8.

After the twenty-fourth pass there is a third sufficient statement, (A) of Section 47.2, for n ≥ 46,656·m + 2. I would work on (A) first: it has no n in it, and the lower-order terms, the potential and the half-open chords of Section 46 do not occur. The order of work is in Section 47.6.

## 32. Machine checks of the sixteenth pass

Code and outputs: `claude/fcc-verification-code-14.md`. The scripts are self-contained (they do not import those of earlier passes); `surface.py` recomputes the decoration of Lemma 47 and its 18 units from Theorem 5.

* `slicepath.py`: Lemma 49.
* `surface.py`: decoration, pieces, rows and strips (the statements at the head of Section 28) for n = 8, …, 30; the pairing search.
* `pairtest.py`, `strips.py`: Lemma 50 over all defects.
* `interior3.py`, `canon.py`: Lemma 51.
* `octa.py`: Proposition 52.
* `fold.py`: the routing of Lemma 53 and the whole fold of Theorem 54. `check.py`: the independent checker. `controls.py`: altered inputs.

## 42. A search for a counterexample to Conjecture R (nineteenth pass)

Sections 33 to 41 are in Part IV. Nothing in this section is a proof. Everything is a computation on finite bodies, done to find out whether Conjecture R is false before more work goes into proving it.

**What is computed for a finite set S with N sites.**

* U*(S) = 2∂(S) − 3(ν₁ + ν₂), the least number of defect units over all decorations of S (Section 8), and n2*(S) = ν₂ − ν₁, the number of doubly decorated sites of a decoration that attains it. Both come from two bipartite matchings between surface and coat (`gmin.py`; it reproduces every value listed in Section 8).
* The *excess* n2*(S) − 16·(3N/2)^{1/3}: what S holds beyond one regular octahedron of its size. L4 of Section 10.2 with q = 1 says that the excess is at most A·U for every connected body with at most 36 units.
* X₃(S), the sum over the three axes of the Euler characteristics of the slices (Section 9), and

      K(S) = ((X₃ + 3)³ / (9N))^{1/2},      Ψ(S) = U*(S)/3 − K(S).

* L(S, J), the number of *long geometric chains* over the six directions. For a piece p of a slice let D(p) be the set of the lower neighbours of its sites. Write p → p′ if p′ = D(p) and p′ is a whole piece of the next slice; a geometric chain is a maximal sequence p_1 → p_2 → … → p_k, and it is long if k − 1 > J (`lgeo.py`). This is what a sequence of regular growing pieces with one parent each looks like, and it needs no decoration. L = 6 for O_n, and 12 for two octahedra with a vertex of one next to a vertex of the other; there two of the twelve do not start at a local top.

*Why K.* Conjecture R and Proposition 29 give X_axis ≤ (3·k_axis²·N)^{1/3} + F(U) for each axis, with k_x + k_y + k_z ≤ U/3, and ≤ (U − 1)/3 for a body that is not a regular octahedron. Since k ↦ k^{2/3} is concave, X₃ ≤ (9k²N)^{1/3} + 3F(U) with k = k_x + k_y + k_z. So K is a lower bound for the number of long chains, to leading order in the size of the body: it is the number of pyramids, over the six directions, that S is worth. The "+ 3" replaces X_axis by X_axis + 1 and makes K(O_n) = 6·(1 + 1/(2n²))^{−1/2}, just below 6. To leading order Conjecture R says Ψ ≥ 0 for every body and Ψ ≥ 1/3 for every body that is not a regular octahedron.

*What would count.* F(U) is a large polynomial, so one small body with Ψ < 0 would not refute anything. A family with Ψ < 0 that persists as the bodies grow would. The simplest such family would be two lumps with a connection that costs nothing: a connected body with U* ≤ 36 that holds as much as two octahedra. The search therefore looks for a cheap connection, in bodies small enough for exact computation, and then asks whether its price depends on the size.

**Results.**

| Family | Bodies | Result |
|---|---|---|
| All connected unions O_a ∪ (O_b + v) up to symmetry, (a, b) = (7, 7), (9, 9), (5, 8), (6, 9) (`scan2.py`, `psi.py scan`, `lscan.py`, `price.py`) | 79 + 146 + 61 + 88 | U* ≤ 36 only when the overlap is at least 39% of the smaller octahedron, and then n2* is at most 0.900 of the capacity of one octahedron of that size. Touching unions have U* ≥ 44. Least Ψ = +0.816 (O_9 and its translate by (1, 1, 0)). 3L ≤ U* − 2 for every union (J = 2, and J = 3 for O_9). 215 of the unions have a long chain that does not start at a local top; for these 3L ≤ U* − 3 |
| Bodies that differ from O_n in one site, n = 5, …, 8; in two sites, n = 5 (`near.py`) | 1,416; 21,055 | Least U* = 19 (a vertex removed) and 20 (two vertices removed). Least Ψ = +0.534. None with U* ≤ 18 |
| Local search on Ψ: any site of the surface may go, any site of the coat may come, the body stays connected; descent, annealing, descent. Starts: O_5 and 36 unions of two O_5; O_6 and 51 unions of two O_6 (`psi.py search`) | 89 starts | The two searches that start at an octahedron stay there. Least Ψ at the other ends +0.913; none below 1/3 |
| Junction search: only sites within distance 2 or 3 of the contact of two lumps may change; minimise U* while the excess stays above 0.4 of that of the two lumps apart. O_6, O_6 with radius 2 and with radius 3 and annealing; O_7, O_7 with radius 2 and annealing (`junction.py`) | 120 starts | Among the ends whose excess stays above the bound, least U* = 44 in each of the three runs. Ends with U* ≤ 36 occur only from starts that already hold less than one octahedron of their size (28 and 30 for O_6, 30 for O_7), and they end with negative excess. No body with U* ≤ 36 and positive excess |
| Roof: O_N at the origin, legs O_n + (a, b, −c) and O_n + (−a, −b, −c), all connected positions; (N, n) = (6, 5), (7, 5), (7, 6), (6, 6), (8, 4) (`roof.py`) | 538 | No body with 3L > U* or Ψ < 0. 336 bodies have a long chain that does not start at a local top; for these 3L ≤ U* − 4. In 18 bodies both legs start under the roof (seen from above, two long chains that do not start at a local top); these have U* ≥ 110 and 3L ≤ U* − 56 |

*Fused bodies.* For O_6 and its translates by (4, 3, 3) and (4, 4, 4) the search reaches U* = 28 and 30 by adding four and six sites in the gap. These are not counterexamples. Two octahedra that meet along a face hold less than one octahedron of their combined size even before the search (excess −11.5 and −7.5), and after it they are one lump, with n2* = 108 and 114 against a capacity of 120 and 122. The first version of the search minimised U* alone and reported these two as its best results; the guard on the excess was added so that starts which do hold more than one octahedron cannot win in the same way.

**The cheapest connection.** In all of the above the cheapest way to join two lumps is to put a vertex of one next to a vertex of the other: O_n ∪ (O_n + (2n − 1, 1, 0)). For n = 6, 7, 8, 9 this body has U* = 44 and n2* = 2(16n − 6) − 28: the connection costs 8 units and 28 doubly decorated sites, whatever n is. It has 12 long geometric chains and 10 local tops. Theorem 36 accounts for 30 units and Theorem 38 for 3 more at the waist formed by the two hidden vertices; A1 asks for 36 and A2 for 37; the body has 44. Three octahedra joined in this way, in a row or at a right angle, have U* = 70 = 54 + 2·8. No local search lowered the 44, neither with moves near the contact nor with moves over the whole boundary. (Corrected in Section 43.5: outside these families there is a connection that costs 7.)

*The price of a pyramid.* Over all unions of two octahedra with K > 6.1 the least value of (U* − 18)/(K − 6) is 4.90 (O_9 and its translate by (17, 1, 0); it tends to 26/6 as n grows, if U* stays 44), and 6.62 among those that overlap. Conjecture R needs it to exceed 3.

**What this shows and what it does not.**

1. No counterexample to Conjecture R, and none to the stronger L4, among the bodies above, which have up to 978 sites.
2. The sharp case looks right near the octahedron: every body at one site from O_5, …, O_8, and every connected body at two sites from O_5, has at least 19 units.
3. Long chains that do not start at a local top, the ones Theorem 36 does not pay for, occur in 551 of the bodies scanned, and none of them comes closer to the count than 3 units. But the roof itself, the configuration without an argument, is tested only weakly. In the one family tried, three octahedra, the bodies in which both legs start under the roof carry at least 56 units more than the count needs, because a leg that comes out of a face of the roof leaves a notch along the whole intersection, and notches cost units in proportion to their length. A cheap roof, if there is one, does not look like this, and single-site moves from these bodies would not find it.
4. Limits. The bodies are small and the moves are single sites: a counterexample that needs a structure of size polynomial in U, which is where J(U) matters, cannot be found this way. K and L are stand-ins for the chains of Section 12 and not the same definition: for O_n both give 6, as Section 12 does, and beyond that they were not compared with `chains.py` in this pass. The search started from octahedra and their unions, so bodies of a different kind (with holes, or with many small parts) were reached only as far as single-site moves lead there.

So the conjecture survived the attempt, and the missing argument is still missing.

Code and outputs: `claude/fcc-verification-code-16.md`.

## 43. Tops, splits and merges: an exact formula and a sharper conjecture (twentieth pass)

Asked again to finish the proof, I could not. This section holds what the pass produced. Only 43.1 and 43.2 are proved; 43.3 is a conjecture with evidence.

### 43.1 The least number of units as curvature plus shortfall

For a finite set S let s and c be the numbers of its surface sites and coat sites. Its *boundary graph* has these s + c sites as vertices and the adjacent pairs (h, p), h in S and p outside, as edges; it has ∂(S) edges. Put

    W(S) = 2∂ − 3s − 3c = Σ over the vertices v of the boundary graph of (deg v − 3),
    def₁ = s − ν₁,      def₂ = c − ν₂,

with ν₁ and ν₂ the two matching numbers of Section 8.

**Lemma 56.** (a) U*(S) = W(S) + 3·def₁(S) + 3·def₂(S). (b) def₂ is the largest value, over sets X of surface sites, of (number of coat sites all of whose neighbours in S lie in X) − 2|X|; and def₁ is the largest value, over sets Y of coat sites, of (number of surface sites all of whose empty neighbours lie in Y) − |Y|.

Proof. (a) is U* = 2∂ − 3(ν₁ + ν₂) rewritten. (b) is the defect form of Hall's theorem, for ν₂ with every surface site allowed twice. ∎

So a lower bound for U* amounts to a choice of X and Y, and the rest is local. A site of a {111} face has three empty neighbours and a coat site over a face has three occupied ones: faces contribute nothing to W. Along a ridge the site (degree 5) and the coat site over it (degree 1) cancel. A vertex of an octahedron contributes 5 − 4·2 = −3 to W, and X = {the vertex} contributes 4 − 2 = 2 to def₂: 3 units, as in Theorem 19.

Values (`wdef.py`): W = −18 for O_n, n = 2, …, 8, with def₂ = 12 for n ≥ 5; W = −36 for O_9 with a cavity O_3; W = 6k − 24 for the tetrahedra with k = 4, 6, 9 sites per edge; W = −16 and def₂ = 20 for two octahedra with a vertex next to a vertex (−16 + 60 = 44). W can be below −18 for a body with one boundary sphere: −24 for a straight rod of ten sites.

*Remark (not used below).* If the boundary graph is embedded in a closed surface Σ so that its faces are discs, Euler's formula gives W = −3χ(Σ) + ½·Σ over the faces of (6 − length of the face). On a {111} face the boundary graph is the hexagonal lattice. So W is a curvature in the sense of Gauss and Bonnet, and the term −3χ explains why joining two bodies gains units even when nothing else changes.

### 43.2 Tops against splits and merges

Fix an axis. Its *piece graph* has the pieces of all slices as vertices and the pairs (piece, child) as edges. For a piece π let u(π) and d(π) be the numbers of its parents and children. Let T_a be the number of local tops of the two directions of the axis, that is, the number of pieces without parent plus the number of pieces without child; σ_a = Σ_π ((u(π) − 1)₊ + (d(π) − 1)₊), the merges and splits counted with multiplicity; and b_a the cycle rank of the piece graph. T, σ and b are the sums over the three axes; T = |𝒯|.

**Lemma 57.** For a connected set and each axis, T_a = 2 − 2b_a + σ_a. Hence T = 6 − 2b + σ.

Proof. Two adjacent sites lie in one piece or in a piece and one of its children, so the piece graph is connected, and E − V = b_a − 1 for its V vertices and E edges. Now Σ_π (d(π) − 1) = E − V, and the left side is Σ_π (d(π) − 1)₊ minus the number of pieces without child. The same holds with u and the pieces without parent. Add the two. ∎

**Lemma 58.** Fix an orientation of an axis and a predecessor map that cannot be extended (Section 12). Then the starts of kind (E) of Section 14 number at most Σ_π (d(π) − 1)₊. Consequently the chains whose start is a local top or of kind (E), over the six directions, number at most T + σ = 2T − 6 + 2b.

Proof. Assign every start of kind (E) to a parent ρ as in (E); ρ is eventful with χ = 1. If some child of ρ is not a start, at most d(ρ) − 1 starts are assigned to ρ. Suppose all children of ρ are starts. They are eventful pieces of 𝒫 without predecessor, and ρ is the predecessor of no piece. If P_0(ρ) is empty, or lies in one child π, then pred(π) = ρ satisfies (P1) to (P3) and extends the map. Otherwise P_0(ρ) is not fully occupied, since a fully occupied block is side-connected and lies in one child; then by Lemma 34 a child of ρ has a hole, so its χ is at most 0 and it is not a start. Either way there is a contradiction. The chains that start at local tops number at most the pieces without parent. Sum over the six directions and use Lemma 57. ∎

Lemma 58 counts all chains of these two kinds, long or not.

### 43.3 Conjecture G

**Conjecture G.** Every component C with at least two sites has U(C) ≥ 6·|𝒯| − 18.

Theorem 36 gives 3·|𝒯|. The two agree for six tops, and G is stronger for more: 3 units for six of the tops and 6 for every other one. For a body whose three piece graphs are trees, Lemma 57 turns G into U ≥ 3T + 3σ: three units for every local top and three more for every split and every merge.

**Proposition 59 (conditional).** If Conjecture G holds for a component, its chains that start at local tops or at starts of kind (E), over the six directions, number at most U/3 + 2b. If its three piece graphs are trees, they number at most U/3.

Proof. Lemma 58 and G: 3·(2T − 6 + 2b) ≤ U + 6b. ∎

So G, which mentions neither chains nor J, would dispose of the starts below splits in bodies without cycles, the case for which Sections 15 and 17 had no route. It does not contradict Lemma 44(d), by which a square under a roof has only one unit of its own: G asks for 3 units per split in total, not at the split. In Lemma 57 every split or merge comes with a further top, and in the examples the units sit partly there.

**Evidence** (`gprime.py`, `gcheck.py`, `bridge.py`, `gsearch.py`; U* stands for U, which is at least U*).

* All 651,629 connected sets with 2 to 7 sites, up to translation: U* − 6T + 18 ≥ 8.
* The 2,328 bodies of the families of Section 42 (unions of two octahedra, bodies at one site from O_n, roofs) and the 1,995 bridged pairs of 43.5: U* − 6T + 18 ≥ 0.
* Annealing on U* − 6T + 18 by single sites, four runs with 178 starts in all (octahedra, unions, the bodies with equality or near equality named below, random connected sets of 8 to 60 sites; starting temperatures 3, 1 and 0.4): no negative value.
* Equality holds for O_n and for other bodies: O_7 ∪ (O_7 + (2, 0, 0)), with T = 10 and U* = 42, and two octahedra joined by a zigzag of two sites between two vertices, with T = 12 and U* = 54. One site between two vertices gives T = 10 and U* = 43.

So G is sharp in several ways, and the octahedron is not its only equality case: G does not give A2.

**What is false.** The extension that would pay for cycles, U ≥ 3T + 3σ for every connected body (6 more units for every cycle of a piece graph), holds for all sets with up to 7 sites but fails for porous bodies: annealing on U* − 3T − 3σ reaches, for example, U* = 1,592 with T = 69 and σ = 551, where 3T + 3σ = 1,860 (`gprime.py search`). In those bodies no chain is long.

### 43.4 What is still missing if G holds

1. *A proof of G.* By Lemma 56, if all tops are single sites and the four cells of each top have no other neighbour in S, then X = the set of tops gives def₂ ≥ 2T, and G becomes W ≥ −18: an inequality of Gauss–Bonnet type for the boundary graph. In general W and the shortfalls have to be bounded together (W < −18 for a rod, def₂ < 2T when a top is a block or when cells are shared). Lemma 44(d) is the local form of G at splits of forms (a) and (b) next to one-site tops. The roof form (c) shows that a proof cannot go split by split.
2. *Chains that start below a shrinking piece* (kind (S): waists, thin or thick). With G, the budget U/3 covers T + σ chains. A long chain of kind (S) then has to be matched to a top whose own chain is short, or to a split or merge that starts no long chain. At a neck between two lumps there are four such splits and merges, two in each lateral axis, because beyond the reach of the neck the slices of the two lumps are separate pieces; and in every example the number of long chains is at most 2T − 6. This count is not proved.
3. *Holes and cycles.* Starts of kind (H), and the term 2b of Proposition 59.
4. *The sharp case A2.*

### 43.5 The cheapest connection, corrected

Section 42 reported 8 units as the price of the cheapest connection between two lumps. That was the cheapest in the families searched there, and it is not the cheapest. `bridge.py` takes two copies of O_n that are not adjacent and joins them by every connector of one or two sites (769 bodies for n = 5, 1,226 for n = 6). The least U* is 43, for O_n, O_n + (2n, 2, 0) and the single site (n, 1, 0) between the two vertices (also for the translate by (2n, 1, 1) with the site (n, 0, 1)): a price of 7. No body has U* ≤ 36. The searches of Section 42 could not reach this body, because moving a lump is not a move of single sites. It has T = 10, so G gives 42.

Code and outputs: `claude/fcc-verification-code-17.md`.

## 44. An attempt to prove Conjecture G (twenty-first pass)

I could not prove G. This section records two exact statements that came out of the attempt (44.1, 44.2), two extensions of G that are false (44.3), a local reading of G (44.4), and the methods that failed (44.5, 44.6).

### 44.1 The unit count of a fold

**Lemma 60.** In every fold of an HPH-free word and for every component C of its H-set,

    U(C) = W(C) + 3·n₀(C) + 3·u(C),

where n₀(C) is the number of surface sites of C without a chain P and u(C) the number of coat sites of C that are not a chain P of a site of C.

Proof. 2∂(C) = U(C) + 6n₁(C) + 9n₂(C) (Section 9, proof of Theorem 21). The surface of C has n₀ + n₁ + n₂ sites. The chain P's of the sites of C are n₁ + 2n₂ different coat sites, so c = n₁ + 2n₂ + u. Substitute in W = 2∂ − 3s − 3c. ∎

So Lemma 56(a) holds for the fold itself and not only for the best decoration: the units are W, plus 3 for every vertex of the boundary graph that the chain does not use.

### 44.2 Soundness as a statement about four counts

**Proposition 61.** Let a fold of the word w of Section 26 have gap at most 9m, and let S be its H-set. Then

    |S| = m·|O_n|,      ∂(S) ≤ 12mn²,      s(S) ≥ m·s_n,      c(S) ≥ m·(c_n − 12).

Proof. The first is the number of H's of w. The word has n₁ = m(4n² − 24n + 24) H's with one neighbour P in the chain and n₂ = m(16n − 18) with two. All of them are surface sites, so s ≥ n₁ + n₂ = m·s_n. Their chain P's are coat sites, and they are n₁ + 2n₂ = m(c_n − 12) different sites, because no P of w lies between two H's. Finally 2∂(S) = U + 6n₁ + 9n₂ ≤ 18m + 6n₁ + 9n₂ = 24mn². ∎

**(E).** For n large against m: a finite set S with these four properties is the union of m copies of O_n, no two of them adjacent.

(E) with the counting lemma of Section 6 is soundness, and the fold gives nothing about S beyond the four counts. Units, decorations and chains do not occur in (E). For m copies of O_n the second and third hold with equality and the fourth with 12m to spare. In the notation of 43.1 the last three say W(S) ≤ 18m with s and c large; m copies of O_n have W = −18m.

### 44.3 Two extensions of G that are false

In a proof by local accounting both sides of the inequality are sums of terms defined in bounded neighbourhoods. The 18 in G is not such a sum. The Euler characteristic χ of the boundary surface of the body is: it equals the number of tetrahedra and octahedra of the lattice with sites on both sides, minus ∂, where a centre at which the surface pinches is counted once for each sheet (`euler.py`). For a body bounded by one sphere χ = 2. So the local form of G would be

    (G_χ)      U ≥ 6T − 9χ,

which is G for one sphere, asks 18 more units for every handle, and is additive over components. The statement U ≥ 3T + 3σ of Section 43.3 was the other candidate. **Both are false.** G_χ holds for all 651,629 connected sets with 2 to 7 sites and for the bodies with few units that were tried (the ring of four octahedra: U* = 104 against 96). But annealing on U* − 6T + 9χ reaches porous bodies that violate it, for example U* = 1,135 with T = 52 and χ = −104, where 6T − 9χ = 1,248 (`gchi.py`). In those bodies a handle costs about 16 units.

**Consequence.** G cannot be proved by local accounting alone: charges defined in bounded neighbourhoods that are non-negative and add up to U − 6T + 9χ would prove G_χ for every body. A proof of G has to use that the body has no handles, or that it has few units for its size.

### 44.4 G as an inequality between units and curvature

Take a body that, away from the sites that carry units, is bounded by {111} faces, octahedral ridges and shallow troughs (Section 9). Its units sit in clusters. For a cluster K let u(K) be its units, t(K) the number of local tops in it, and k(K) the Gauss curvature of the surface inside it in units of 120°, so that the k(K) add up to 3χ. Then G_χ is the sum over the clusters of

    (*)      u(K) ≥ 6·t(K) − 3·k(K),

and for a body bounded by one sphere G is this sum. Values found, from the U* of the bodies of Sections 42 and 43 (k from the angle sum of the faces around the cluster, or from the total 6):

| Cluster | t | k | units found | (*) asks |
|---|---|---|---|---|
| vertex of an octahedron | 1 | 1 | 3 | 3 |
| two one-site tops over one site (O_7 and its translate by (2, 0, 0)) | 2 | 1 | 9 | 9 |
| saddle where two ridges and two troughs meet (translate by (4, 0, 0)) | 0 | −1 | 6 | 3 |
| vertex half covered by a second octahedron (translate by (2, 2, 2)) | 0 | 0 | 1 | 0 |
| two vertices next to each other | 0 | −4 | 14 | 12 |
| two vertices joined by one site | 0 | −4 | 13 | 12 |
| two vertices joined by a zigzag of two sites, each a top | 2 | −4 | 24 | 24 |

So G says: 3 units for every top, and 3 for every 120° of curvature that is not at a top, counted without sign. A connection between two lumps has curvature −4 and so costs at least 12 units if G holds; the cheapest found costs 13 and the reduction needs 7. (*) fails for a hole in a {111} layer one site thick (9 units for curvature −6), which is how G_χ fails; such a hole makes a handle.

This is a reading of G and not a proof: (*) has been checked only on the clusters above, through the bodies that contain them.

### 44.5 Adding one site

Let g be an empty site with a neighbours in S′, let c be the number of empty neighbours of g that are adjacent to S′, and i the number of sites among g and its neighbours that have no empty neighbour once g is added. Then

    W(S′ ∪ {g}) − W(S′) = −12 − a + 3c + 3i

(`addsite.py`: 2,000 random cases). U − 6T is not monotone under adding or removing a site: each of the 1,416 bodies at one site from O_5, …, O_8 has U* − 6T + 18 ≥ 1, and O_n has 0 (`gcheck.py`). The octahedron is a strict local minimum, so an induction on the number of sites has no first step.

### 44.6 What was tried for a proof of G

1. *Local accounting.* Excluded by 44.3.
2. *Induction on the number of sites.* Excluded by 44.5.
3. *Induction on the number of tops, cutting at a split or merge.* Cutting a adjacent pairs lowers the units by at most 4a (Section 17.4), and the two parts have k more tops between them than the body. The step closes only if 6k ≥ 18 + 4a. For the zigzag of 44.4, cut in its middle, k = 2 and a = 1; there the step works only because both parts have units to spare (29 against 24). So the induction needs a statement stronger than G for the parts, and I found none that is true and is inherited. (Theorem 36 with 3 more units for every top beyond six fails by 1 for O_7 with one site over an edge.)
4. *One axis at a time.* W is the sum of three terms, one for the slices of each axis, but they do not follow the tops of their own axis: for two octahedra with a vertex next to a vertex they are −4, −4, −8, against 2, 4, 4 tops (`waxis.py`).

What is left as a way in: (*) cluster by cluster, for bodies with few units. That needs a list of the clusters that can occur, or an argument that a large cluster has units to spare; I have neither.

Code and outputs: `claude/fcc-verification-code-18.md`.

## 45. Soundness as one linear inequality; silhouette runs (twenty-second pass)

I could not finish the proof. This section holds: an inequality (L_n) that implies soundness, with the proof of the implication (45.1); the evidence for it (45.2); an exact decomposition of it into three terms, one of which is proved non-negative (45.3); what the remaining term asks, and where it fails (45.4); the same computation in the model of Section 44.4 (45.5); statements tried on the way that are false (45.6); a remark on G_χ (45.7); what a proof now requires (45.8). Proved: Proposition 62, Lemma 63, Proposition 64. Everything else is conjecture, computation or model.

### 45.1 The inequality

For a finite set S let ∂ be its boundary and ν₁, ν₂ its two matching numbers (Section 8), and for an integer n ≥ 3 put

    Λ_n(S) = (4n² − 9n + 3)·∂ − 3n·((2n − 6)·ν₁ + (2n − 3)·ν₂).

With p = ∂ − 3ν₁ and q = ∂ − 3ν₂, so that U* = p + q, this is

    Λ_n = (2n² − 3n)·U* − 3n·p + 3∂ = (2n² − 6n)·p + (2n² − 3n)·q + 3∂.

**(L_n).** Λ_n(C) ≥ 0 for every finite connected set C, with equality only if C is a copy of O_n.

**Proposition 62.** (a) For every decoration of S, with n₁ singly and n₂ doubly decorated sites and U units,

    (4n² − 9n + 3)·U + 18·n₁ − 9(n − 3)·n₂ ≥ 2·Λ_n(S).

(b) Λ_n(O_r) = 36·(n − r)² for r ≥ 5, and Λ_n of a single site is 30n² − 72n + 36 > 0. (c) If (L_n) holds for the n of the reduction, the reduction is sound.

Proof. (a) U = 2∂ − 6n₁ − 9n₂ (Section 9). With this the left side is 2(4n² − 9n + 3)∂ − 6n·((4n − 9)n₁ + 6(n − 2)n₂), and (4n − 9)n₁ + 6(n − 2)n₂ = (2n − 6)(n₁ + n₂) + (2n − 3)(n₁ + 2n₂). One chain P for each decorated site is a matching, so n₁ + n₂ ≤ ν₁; all the chain P's use every surface site at most twice, so n₁ + 2n₂ ≤ ν₂; and both coefficients are at least 0.

(b) For r ≥ 5, U*(O_r) = 18 with ν₁ ≤ s_r and ν₂ ≤ c_r − 12 (the vertices in Lemma 56(b)) forces ν₁ = s_r and ν₂ = c_r − 12, and ∂ = 12r². The rest is arithmetic; `lin.py` confirms it for r = 5, …, 10 and n = 3, …, 39. A single site has ∂ = 12, ν₁ = 1, ν₂ = 2.

(c) Take a fold of w with gap at most 9m and let C_i be the components of its H-set, with U_i units, n₁^i sites with one chain P and n₂^i with two. As in the proof of Proposition 61, Σ U_i ≤ 18m, Σ n₁^i = m(4n² − 24n + 24) and Σ n₂^i = m(16n − 18). Hence

    Σ_i ((4n² − 9n + 3)·U_i + 18·n₁^i − 9(n − 3)·n₂^i) ≤ m·(18(4n² − 9n + 3) + 18(4n² − 24n + 24) − 9(n − 3)(16n − 18)) = 0.

By (a) the sum of the Λ_n(C_i) is at most 0, so by (L_n) every component is a copy of O_n. There are m of them, because the H-set has m·|O_n| sites, and no two are adjacent, because they are different components. The counting lemma of Section 6 does the rest. ∎

**Remarks.**

1. *What is gone.* (L_n) is a statement about three counts of one finite set. Volume, slices, chains, the length J and the error polynomial F(U) do not occur. Proposition 62 needs (L_n) for one value of n only, so "n large against m" is not needed either, although a proof of (L_n) may well work only for large n. A1 and A2 are not separate: to leading order a body that is worth k pyramids of heights ℓ_1, …, ℓ_k has Λ_n ≈ 2n²·(U − 3k) + 6·Σ(ℓ_i − n)², so (L_n) says U ≥ 3k, and that a body with U = 3k has all its pyramids of height n.
2. *All n at once.* Λ_n = 2U*·n² − (9/2)·Y·n + 3∂ with Y = n2* + U* = 2(∂ − 2ν₁ − ν₂). So Λ_n ≥ 0 for every real n is the same as

       27·(n2* + U*)² ≤ 32·U*·∂:

   what a body holds, plus its units, is at most the square root of (32/27)·units·boundary. Equality holds for every O_r, r ≥ 5. This form fails for a single site and for two adjacent sites (which is harmless: there Λ_n > 0 for all integers n ≥ 3), and it holds for the 1,790 bodies of the first two rows of the table below (`dscan.py`).
3. *Where it is trivial.* By (a) and its proof, Λ_n ≥ 0 whenever n2* ≤ 3.2·U*, because (4n² − 9n + 3) ≥ 3.2·9(n − 3) for all n ≥ 3. A body with at least two sites has at least 18 units (Theorem 17), so (L_n) is a statement about bodies that hold more than 57 doubly decorated sites; porous and small bodies are not in question. This is the difference to G_χ.
4. *Relation to (E).* (E) of Section 44.2 uses the four counts of the whole H-set. (L_n) is a property of each component by itself, and it is additive: that is what makes it usable.

### 45.2 Evidence for (L_n)

For each body the least Λ_n over all integers n ≥ 3 is computed exactly (`lin.py`, `lintest.py`).

| Family | Bodies | Least Λ_n |
|---|---|---|
| Unions O_a ∪ (O_b + v) of Section 42 | 374 | 190 (O_7 and its translate by (1, 1, 0), n = 7) |
| Bodies at one site from O_5, …, O_8 | 1,416 | 38, 60, 86, 116 (a vertex removed, n = r) |
| Connected bodies at two sites from O_5 | 21,055 | 76 (two vertices removed) |
| Two copies of O_5 or O_6 joined by one site; of O_5 joined by two sites | 379; 623 | 176 (O_5, O_5 + (10, 1, 1) and the site (5, 1, 0); U* = 43) |
| Roofs of Section 42 | 538 | 572 |
| Eleven other bodies: cavities, the ring of four, three in a row and at a right angle, tip to tip, the zigzag of Section 43.3 | 11 | 558 |

No body has Λ_n < 0, and none other than a regular octahedron has Λ_n = 0 for any n. Annealing by single sites on (least Λ_n)/∂, followed by descent (`linsearch.py`): seven runs with 40 starts in all (O_5, O_6, O_7 at two temperatures; 22 unions of two O_5 or two O_6; three of the cheapest connections of Section 43.5; three overlapping pairs; six random connected sets of 40 to 150 sites). The runs that start at an octahedron end there; the least end value elsewhere is 0.27.

As in Section 42 this is evidence and not a proof, with the same limits: the bodies have at most 978 sites and the moves are single sites.

### 45.3 Silhouette runs: an exact decomposition

For ν in {+1, −1}³ let R_ν be the three of the twelve vectors r with r·ν = 2. A site h of S is *ν-exposed* if the three sites h + r, r in R_ν, are empty (a site of a face with outer normal ν has exactly these three empty neighbours). A *chord* is a maximal run of ν-exposed sites on a lattice line whose direction d satisfies d·ν = 0; there are three such directions for each ν. An end of a chord is *open* if the next site of the line is empty and *blocked* if it is in S.

A chord with two open ends is a whole run of S on its line, all of whose sites are exposed for one ν: a **silhouette run**. The same run counts once for each such ν. In the slices of Section 7.6 it is a straight side of a slice piece that goes from one convex corner to another, with all the grid corners on it empty in the plane above (or below). Write |C| for the number of sites of a run C, H for the number of silhouette runs of S, and H_j for the number of those with at most j sites. For O_r: H_j = 24·min(j, r); the runs parallel to one side of a face have 1, 2, …, r sites, starting at the opposite vertex.

**Lemma 63.** For every finite set S, the sum of |C| − ½ over its silhouette runs is at most ∂. More precisely

    B := ∂ − Σ_C (|C| − ½) ≥ (3/4)·(number of chords with exactly one open end).

Proof. For a site h let deg be the number of its empty neighbours, e the number of ν for which it is exposed, and o the number of pairs (ν, r) with h exposed for ν, r·ν = 0 and h + r empty; o counts the open ends of chords at h. For each of the 4,096 sets of empty neighbours, 12e − 4·deg ≤ o (`chordB.py`). Every exposed pair (h, ν) lies on three chords, so the lengths of all chords add up to 3·Σe ≤ ∂ + (1/4)·Σo, and Σo = 2H + (number of chords with one open end). Remove the chords that are not silhouette runs; each has at least one site. ∎

**Proposition 64.** For n ≥ 1 put

    D_n = Σ over the silhouette runs with |C| ≤ n of (n + ½ − |C|),      D_n⁺ = Σ over those with |C| > n of (|C| − n − ½),
    M_n = (2n² − 3n)·U* + 3n·(H − p) − 3·D_n.

Then Λ_n = M_n + 3B + 3D_n⁺ for every finite set.

Proof. Σ_C (|C| − ½) = n·H − D_n + D_n⁺, so 3∂ = 3B + 3nH − 3D_n + 3D_n⁺; substitute in Λ_n = (2n² − 3n)U* − 3np + 3∂. ∎ (`chordM.py` asserts the identity for n = 3, 5, 8 on every body of its own runs.)

For O_r with r ≥ n all the difference lies in the long runs: M_n = 0, B = 0 and 3D_n⁺ = 36(r − n)².

**(M_n).** M_n(S) ≥ 0.

By Proposition 64 and Lemma 63, (M_n) implies Λ_n ≥ 0. Two other ways to write it. With D_n = Σ_{j<n} H_j + ½·H_n, the slack κ_j = (4/3)·U*·j − H_j and δ = U* + p − H = (3/2)(n2* + U*) − H:

    M_n = 3·(κ_1 + … + κ_{n−1} + ½·κ_n) − 3n·δ,

and M_n ≥ 0 is the same as n·p ≤ (2n²/3 − n)·U* + Σ_C min(|C| − ½, n). The first form separates a count from a correction:

**(K).** H_j ≤ (4/3)·U*·j for every j ≥ 1 and every set with at least two sites: at most (4/3)·U·j silhouette runs have at most j sites.

For O_r, (K) holds with equality for j ≤ r. A piece of k × k squares has four sides of k squares, so for square pieces (K) is the count of Conjecture Q with k_x + k_y + k_z = U/3. (K) says κ_j ≥ 0; (M_n) says that the κ_j, on average over j ≤ n, are at least δ. In the 24 named bodies of `chordM.py families` δ ≥ 0, with δ = 0 for the octahedra O_r, r ≥ 5, and for a single site; δ = 4 for O_6 without a vertex, where the four sites left at the top have 4 units and no sharp corner.

**Evidence** (`chordM.py`, `chordM2.py`, `lintest.py`, `msearch.py`).

* (K): no violation among the 374 unions and the 1,416 bodies at one site from O_5, …, O_8; the least slack κ_j is 1, at j = 1 (O_5 and O_8 + (2, 2, 1), with U* = 21 and 27 runs of one site). A single site violates it (24 runs, 15 units).
* (M_n), for every n from 2 to the longest run plus 3, on 24,163 of the bodies of 45.2 (all but the 233 pairs of O_6 joined by one site): **no failure for any n ≥ 6.** For n ≤ 5 it fails often: the largest n with M_n < 0 is 2 for most bodies (347 have none), 3 for about one body in seven, 4 for ten bridged pairs, and 5 for O_7 and O_9 with their translates by (2, 2, 2).
* Annealing on the least M_n over n ≥ 6, divided by ∂, from six bodies (O_6; O_7 with its translate by (2, 2, 2); O_6 with its translate by (1, 1, 0); two bridged pairs; O_6 without a vertex), two runs: no negative value. No move was accepted that lowered the starting value, so this says little.
* O_9 with its translates by (2, 2, 2), (4, 4, 4), (6, 6, 6) and by eight other small vectors (`steps.py`): the range of n in which (M_n) fails does not grow with the height of the step; higher steps carry more units.

So the statement that survives is: **(M_n) for all n from some fixed n_0 on** (6 in the bodies tested). That is enough: the reduction has n ≥ 38.

**Correction (twenty-third pass).** The bodies above contain no islands. For an octahedron with a one-layer island on a face, M_n < 0 up to n = 9, and the range grows with the island (Section 46.1). So 6 is not the threshold, and I do not know that any fixed threshold exists. What replaces (M_n) is (M′_n) of Section 46.2, which has no exception for n ≥ 4. Remark 2 of 45.4 below (long troughs are free) stays true; remark 3 does not survive as stated: an island has 3 units at any size and begins three families of runs, and in M_n its units cover them only for n ≥ 12.

### 45.4 What (M_n) asks

In a face of O_r the silhouette runs parallel to one side form a nested family with 1, 2, …, r sites that starts at the opposite vertex. There are 24 families, four at each vertex. A family that begins with a run of L_0 sites contributes (n − L_0 + 1)²/2 to D_n. A vertex contributes 3 units, and 3 to H − p (it has 16 open ends, worth 8 runs, against deg − 3 = 5). So M_n = 0 for the octahedron reads: every family is paid 3/4 of a unit and 3/4 of H − p by the vertex at which it starts.

For another body, (M_n) asks that every family of nested silhouette runs that begins with a run shorter than n is paid by units near its beginning, in proportion to (n − L_0 + 1)². Three things follow from this form.

1. *Blunt tops are no exception.* O_6 without a vertex has four families that begin with two sites instead of one, 4 units at the top instead of 3, and δ = 4. (K) holds with little room (κ_5 = 2.67) and (M_n) holds for every n ≥ 3.
2. *Long troughs are free at scale n.* A family that begins at a trough begins with as many sites as the trough is long. If the trough is longer than n, the family does not occur in D_n. So a wide neck between two lumps needs no units in this count, and a narrow one needs them in proportion to (n − length)². In the count by chains a neck starts two long chains whatever its width.
3. *Why it fails for small n.* A site on a face of O_6 adds 6 units, raises δ by 9 and D_3 by 14.5: M_3 = 2·9·6 − 9·9 − 3·14.5 = −16.5. The units enter with 2n², the two corrections with n. In all bodies tested the corrections are bounded by a constant times the additional units, which is why a fixed n_0 suffices there. I have not proved such a bound.

### 45.5 The same count in the model

Take the model of Section 44.4: a surface made of {111} faces, octahedral ridges and shallow troughs, with units only at its vertices. This is a computation in the model, not a statement about lattice bodies.

1. *Vertices.* The four planes x ± y ± z = 0 cut the sphere of directions into 8 triangles (the octants) and 6 squares (around the half-axes). At each direction of type (1, 1, 0) four cells meet, two triangles and two squares, and of these the body contains none, or one square (a ridge along that direction), or one triangle and one square (flat), or two triangles and one square (a shallow trough), or all four. It follows that the tangent cone at any point is determined by the set Q of half-axes it contains: it consists of the squares of Q and of the octants with at least two of their three half-axes in Q. Up to symmetry Q gives ten cones: empty; the apex of a pyramid (one half-axis; curvature +1 in units of 120°); two pyramids tip to tip; a ridge; a face; the saddle with two ridges and two troughs (three half-axes, two of them opposite; curvature −1); a trough; the complement of two pyramids tip to tip; a pit (five half-axes; curvature +1); full. So the only vertices are apexes, pits, saddles and the two pinched forms.
2. *Faces.* In the plane of a face, a side across which the surface bends by an octahedral ridge and a side across which it bends by a shallow trough have opposite orientations: for each of the three directions of the plane, the side at one end can only be a ridge and the side at the other end only a trough. So a face is the intersection of a triangle △ whose sides are ridges with a reversed triangle ▽ whose sides are troughs: a triangle with up to three corners cut off. Its corners are apexes (ridge meets ridge, 60°), pits (trough meets trough, 60°) and saddles (ridge meets trough, 120°).
3. *One face.* Let △ have side L and let the cut corners have sides t_1, t_2, t_3, with t_i + t_j ≤ L. The silhouette runs of the face minus its runs with two blocked ends number 3ℓ with ℓ = L − t_1 − t_2 − t_3, the face has (L² − Σt_i²)/2 sites to leading order, and

       ℓ² ≤ L² − Σ t_i²,      because Σ t_i² + Σ_{i<j} t_i·t_j ≤ L·Σ t_i.

   To leading order the face contributes 4n²·u_F + 9·(L² − Σt_i²) − 18n·ℓ to 2Λ_n, where u_F is its share of the units. With ℓ > 0 this is at least 4n²·(u_F − 9/4) + 9(n − ℓ)², and with ℓ ≤ 0 it is positive.
4. *The count.* So in the model (L_n) holds if every face with ℓ > 0 gets 9/4 units: 3/4 from each corner at an apex or a pit, 3/8 from each corner at a saddle. An apex or a pit has four faces and a saddle four, which makes **3 units for an apex, 3 for a pit and 1.5 for a saddle**. The values found for lattice bodies are 3 for an apex and 6 for the saddle of Section 44.4 (pits were not computed). G asks for 3 at a saddle, as does the count of long chains where two growing pieces merge.
5. *Connected bodies of the model.* By Section 10.3 they are unions of regular octahedra, two overlapping ones displaced along a coordinate axis. For J octahedra of radii r_i, the i-th meeting the earlier ones in an octahedron of radius ρ_i ≤ r_i (ρ_1 = 0), what the body holds is 16·Σ(r_i − ρ_i) and its boundary 12·Σ(r_i² − ρ_i²), to leading order, and (Σ(r_i − ρ_i))² ≤ J·Σ(r_i − ρ_i)² ≤ J·Σ(r_i² − ρ_i²). So there (L_n) needs only that J octahedra joined in this way carry at least 18·J units. A neck has four saddles and hides one vertex of each of the two octahedra, so with 1.5 units for a saddle the body has 18J − 6(J − 1) + 6(J − 1) = 18J: exactly enough, and with the 6 units found at a saddle 18 to spare at every neck. This is Lemma 25 with the boundary in place of the volume.

### 45.6 Statements that are false

Tried as intermediate steps, and refuted by the bodies named (`chords.py`, `slopes.py`, `chordM.py`).

1. ∂ − 3ν₂ + H ≥ (3/2)·max_j H_j/j. Equality for O_r; −3.2 for O_6 without a vertex, −9 for O_7 with its translate by (2, 2, 2). It would have given (L_n) together with (K). The loss is in replacing the runs by their worst ratio H_j/j.
2. H ≥ p + U* (that is, δ ≤ 0). False for most bodies.
3. H_j ≤ (4/3)·U*·j − δ for each j. False at j = r − 1 for O_r without a vertex; only the average over j holds.
4. "Slopes". Call a silhouette run a start if neither neighbouring line of its plane carries a silhouette run of one site less nested in it; count max(1, number of nested runs of one site more) for each start. The statement 3·(this number) ≤ 4·U* is false: 32 against 19 units for O_6 without a vertex, 42 against 24 for O_7 with its translate by (2, 2, 2). Single long runs count as much as families that start at a point. The families have to be weighted by where they begin, which is what D_n does.
5. (M_n) for n ≤ 5.

### 45.7 The smallest violators of G_χ

Annealing on (U* − 6T + 9χ) + 0.5·(number of sites) from random connected sets, six runs (`minviol.py`): the smallest set found that violates G_χ has 133 sites (U* = 850, T = 49, χ = −62, two units short); the others have 137 to 195 sites. All are porous. So there is no small local pattern behind the failure of G_χ; it comes from many small handles together, as Section 44.3 said. This search did not lead anywhere else.

### 45.8 What a proof now requires

(Superseded by Section 46.8: (M_n) is replaced by (M′_n).)

One of two things: Conjecture R as before, or (L_n) for the n of the reduction. For (L_n) it is enough to prove (M_n) for all n from some n_0 on, with equality only for the octahedra with at least n sites on an edge; then Λ_n = 0 forces D_n⁺ = 0 as well, and the octahedron is O_n.

What a proof of (M_n) would have to contain, as far as I can see:

1. A statement that every family of nested silhouette runs begins at sites that carry units. From Lemma 20 one expects that a run whose two ends are regular ridge sites has a nested run of one site less on one side, so that a family can begin only where a site at an end of the run, or next to it, is irregular; I have not written this out. A family that begins with one site begins at a site with at least five empty neighbours.
2. The count: 3/4 of a unit for each family, weighted by its first run as in D_n, and with the correction δ. For families that begin at one site this is (K) with j = 1, a statement of the kind of Theorem 36, and probably within reach of the methods used there. For families that begin at a longer run the units sit at its two ends, which are far apart; in the model that is the trough with a saddle at each end.
3. A bound for the corrections (δ, and the short runs that a defect adds) by a constant times the units of the defect, to get n_0.

I have none of the three. Compared with the count of long chains: the target is exact and can be tested on any body by a script; there is no length J, no predecessor map and no volume; a merge needs 1.5 units where chains need 3; holes, cycles and the sharp case are not separate questions. Against that, it is again a count that must hold for every body, the families extend over distances up to n as chains do, and the place where the count by chains broke down (units at a split that are also the units of tops nearby) may well come back as families that begin next to one another.

Code and outputs: `claude/fcc-verification-code-19.md`.

## 46. Half-open chords, a local potential and a sharper conjecture (twenty-third pass)

Again no proof of soundness. This section holds: a correction to Section 45.3 (46.1); the repaired decomposition of Λ_n (46.2, proved); a local potential and what M′_n looks like with it (46.3, proved); the increments of M′_n and the conjecture (I_n) (46.4); the evidence (46.5); what pays for what, and why merges cost nothing in this count (46.6); statements that are false (46.7); what a proof now requires (46.8). Proved: Proposition 65, Lemma 66, Proposition 67. They are identities and do not bring soundness nearer by themselves.

### 46.1 Correction: (M_n) fails for islands

Take O_r and put on its face x + y + z = r − 1 a triangle of the next lattice plane with k sites per side, pointing the same way as the face. For k ≥ 3 this body has U* = 21 whatever k is and wherever the island sits (all positions on O_9; Section 10.3 had 3 units for three sizes); for k = 1, 2 it has 24. `islands.py`, `islands2.py`, `chordM3.py`:

| Body | M_n < 0 for | M′_n < 0 for (46.2) | least Λ_n |
|---|---|---|---|
| O_9, island k = 3 at (1, 1) | n = 3, …, 6 | none | 330 |
| O_13, island k = 4 at (0, 4) | n = 3, …, 7 | none | 744 |
| O_17, island k = 6 at (1, 4) | n = 3, …, 8 | none | 1,332 |
| O_21, island k = 9 at (1, 5) | n = 3, …, 9 | none | 2,106 |

Over all positions and sizes: 6 of the 110 islands on O_9 have M_6 < 0, and 43 of the 315 on O_13 have M_7 < 0. The inequality (L_n) holds for every one of them.

*Why.* An island has 3 units, lowers the potential Π of 46.3 by 9, and has three nested families of silhouette runs of its own, with 1, …, k sites. By formula (3) of 46.3 it changes M_n by about 6n² − 18n − 9kn + 4.5k² when k ≤ n, which is negative for some k as soon as n ≤ 11. In M′_n the island is saved by the rows of the face that pass under it: they become chords with one blocked end, and each of these has a credit in M′_n that M_n does not have. So for single islands the failures of (M_n) should stop at n = 12; I have not confirmed this beyond n = 9, and I do not know whether another defect pushes the range further. The statement "(M_n) from n = 6 on" of Section 45.3 is false, and "(M_n) from some fixed n_0 on" is open. (M_n) is not used below.

### 46.2 The repaired decomposition

Notation of Section 45.3. Let H, H₁, H₂ be the numbers of chords with two, with one and with no open end. For a site h let β(h) = deg − 3e + o/4, which is at least 0 by the enumeration behind Lemma 63.

**Proposition 65.** For a finite set S and n ≥ 1 put

    A_n = Σ over the chords with two open ends of (n + ½ − |C|)₊  +  Σ over the chords with one open end of (n/2 + ¼ − |C|)₊,
    M′_n = (2n² − 3n)·U* + 3n·(H + H₁/2 − p) − 3·A_n,
    R_n = 3·Σ_{two open ends} (|C| − n − ½)₊ + 3·Σ_{one open end} (|C| − n/2 − ¼)₊ + 3·Σ_{no open end} |C| + 3·Σ_h β(h).

Then Λ_n = M′_n + R_n, R_n ≥ 0, and M′_n ≥ M_n.

Proof. Summing deg(h) = 3e(h) − o(h)/4 + β(h) over the sites, with Σ 3e = total length of all chords and Σ o = 2H + H₁, gives

    ∂ = Σ_{two open ends} (|C| − ½) + Σ_{one open end} (|C| − ¼) + Σ_{no open end} |C| + Σ_h β(h).

Write |C| − ½ = n − (n + ½ − |C|) and |C| − ¼ = n/2 − (n/2 + ¼ − |C|), split each bracket into its positive and negative part, and substitute in Λ_n = (2n² − 3n)U* − 3np + 3∂. M′_n − M_n = 3·Σ_{one open end} (n/2 − (n/2 + ¼ − |C|)₊) ≥ 0. ∎

**Open ends.** Give an open end ε of a chord C the *half-length* ℓ(ε) = |C| if the other end of C is blocked and |C|/2 if it is open. Then A_n = Σ_ε (n/2 + ¼ − ℓ(ε))₊ over all open ends, and

    M′_n = (2n² − 3n)·U* − 3n·p + 3·Σ_ε min(ℓ(ε) − ¼, n/2).

So M′_n ≥ 0 says n·p ≤ (2n²/3 − n)·U* + Σ_ε min(ℓ(ε) − ¼, n/2): every open end gives a credit equal to how far it sees along its chord (to the middle, if the far end is open too), up to n/2, and the units pay the rest. A ridge site has four open ends and contributes 2 to p, so it is in balance when each of its four chords is seen for at least n/2.

**(M′_n).** M′_n(S) ≥ 0.

By Proposition 65, (M′_n) implies Λ_n ≥ 0, and it is weaker than (M_n).

### 46.3 A local potential

For a surface site g let o(g) be the number of open ends at g (Lemma 63), and bl(g) the number of chord ends that g blocks: the pairs (ν, d) with d·ν = 0 such that g + d is ν-exposed and g is not. Put

    π(g) = (3/2)·(o(g) − bl(g)) − 3·deg(g) + 9,      Π(S) = Σ_g π(g).

π(g) is determined by the sites within two steps of g.

**Lemma 66.** (a) E = H − H₂ − Π/3, where E = ∂ − 3s. Hence p = H − H₂ − Π/3 + 3·def₁. (b) π(g) = 0 if the empty neighbours of g form a face or a ridge of Lemma 20; π(g) = 6 − (3/2)·bl(g) ≥ 0 if they form a trough, with π(g) = 0 when g blocks four ends, as it does in a trough between two exposed faces; π(g) = 9 if g has eight empty neighbours and four exposures (a vertex of an octahedron).

Proof. (a) Every blocked end is blocked by one site, the next site of the line, which is in S and not exposed; so Σ_g bl(g) = H₁ + 2H₂, and Σ_g o(g) = 2H + H₁. Then Π = (3/2)(2H − 2H₂) − 3·Σ_g (deg(g) − 3). (b) By enumeration of the 4,096 sets of empty neighbours (`blocked.py`), which gives o and an upper bound for bl for each set: a face has o = 0 and can block nothing, a ridge has o = 4 and can block nothing, a trough has o = 0 and blocks at most four ends, a vertex has o = 16 and can block nothing. ∎

Values at other sites (`sharp.py`, `blocked.py`): 3 at a site with seven empty neighbours and three exposures (the top corner of an island, a vertex half covered by a step); −6 at the site of the face at the foot of each corner of an island; −9 at each of the four saddles of a neck along an axis; −12 at each of two vertices that are next to each other; −3 at each site of a tetrahedral edge; 45 for a single site. For every site π ≥ −39. Π = 54 for O_r, 45 for O_r with an island or without a vertex, 36 for O_7 with its translate by (2, 2, 2), −36 for the tetrahedron with 6 sites per edge.

With Lemma 66(a), and D_n as in Proposition 64,

    M′_n = (2n² − 3n)·U* + n·Π − 9n·def₁ − 3·D_n + 3·Σ_{one open end} min(|C| − ¼, n/2) + 3n·H₂.        (3)

So (M′_n) says: the silhouette runs with at most n sites, each weighted with n + ½ − |C|, are paid for by 2n² − 3n for each unit, by n times the potential, by up to 3n/2 for each chord with one blocked end and by 3n for each chord with two; 9n is lost for each surface site that the first matching leaves out. For O_r with r ≥ n this is 36n² = 18·(2n² − 3n) + 54n. Also M_n = M′_n − 3·Σ_{one open end} min(|C| − ¼, n/2), which is the loss described in 46.1.

### 46.4 Increments, and the conjecture (I_n)

Let N(x) be the number of open ends with half-length at least x, H_j and h_j the numbers of silhouette runs with at most j and with exactly j sites.

**Proposition 67.** For n ≥ 1,

    M′_{n+1} − M′_n = (4n − 1)·U* − 3p + (3/4)·(N(n/2 + 1) + N((n + 1)/2))
                    = (4n − 1)·U* + Π − 9·def₁ − 3·H_n − (3/2)·h_{n+1} + (3/2)·#{C with one open end, |C| > (n + 1)/2} + (3/4)·#{C with one open end, |C| = (n + 1)/2} + 3·H₂.

Proof. From the form of M′_n with open ends: min(ℓ − ¼, (n + 1)/2) − min(ℓ − ¼, n/2) is 0 for ℓ ≤ n/2, ¼ for ℓ = (n + 1)/2 and ½ for ℓ ≥ n/2 + 1. The second line follows with Lemma 66(a). ∎ (`check67.py` confirms Lemma 66(a), formula (3) and both lines on eleven bodies for every n.)

**(I_n).** M′_{n+1}(S) ≥ M′_n(S).

In words, from the second line: three times the number of silhouette runs with at most n sites, plus 3/2 times those with n + 1, is at most (4n − 1) per unit, plus the potential, plus 3/2 for each long half-open chord and 3 for each closed one. For O_r with r > n both sides are 72n + 36.

**What gives what.** (L_n) for a given n ≥ 4 follows from M′_4 ≥ 0 and (I_j) for 4 ≤ j < n. (M′_3 can be negative: 46.5.) For equality, Λ_n = 0 needs M′_n = 0 and R_n = 0.

Since (I_n) holds for each n separately in every body tried, it is a statement at one scale: it compares the runs of length about n with the units, and does not average over shorter ones. I do not see that this makes it easier to prove, because H_n is still a count of all runs up to n.

### 46.5 Evidence

For each body, (I_n) is tested for every n from 3 to past the longest chord, and M′_n for every n ≥ 3 (`ends.py`, `chordM3.py`, `stacks.py`).

| Family | Bodies | (I_n) fails | least increment | M′_n < 0 |
|---|---|---|---|---|
| Unions of two octahedra (Section 42) | 374 | 0 | 12 (translate by (2, 2, 2), n = 3) | never |
| Bodies at one site from O_5, …, O_8 | 1,416 | 0 | 2 (O_5 without a vertex, n = 3) | never |
| Connected bodies at two sites from O_5 | 21,055 | 0 | 4 | never |
| Islands of both orientations on a face of O_9 and of O_13, all sizes and positions | 425 | 0 | 0 (O_13, k = 6 at (2, 2), n = 4); 3 on O_9 | never |
| Two copies of O_5 or O_6 joined by one site | 379 | 0 | 44 | at n = 3 in six bodies (least −30), never for n ≥ 4 |
| Roofs of Section 42 | 538 | 0 | 98 | never |
| Thirteen special bodies (those of 45.2, and two bridged pairs) | 13 | 0 | 47 | at n = 3 in one of the bridged pairs |
| O_9 with islands on all eight faces (seven sizes and positions), and with two or three islands stacked on one face (five) | 12 | 0 | 24 | never |

In all, 24,212 bodies and no exception to (I_n). The increment is 0 for the octahedra (for every n < r) and for an island of six sites per side near a corner of a face of O_13, at n = 4; so (I_n) is sharp at a body that is not an octahedron. For n ≥ 4 the least value of M′_n over bodies that are not regular octahedra is 14 (O_5 without a vertex).

Annealing by single sites on the smaller of the least increment and the least M′_n with n ≥ 4, from octahedra, bodies at one or two sites from them, islands, unions and bridged pairs (`isearch.py`; eight runs, stopped when 17 starts had finished): no start was improved. As in 45.3 this says little; the starting bodies are local minima for moves of one site, and the run from random sets had not finished a start.

Limits as before: bodies of at most a few thousand sites, families chosen by me. The islands were not among the families of Section 45, and they refuted a statement made there; there may be other defects I have not thought of.

### 46.6 What pays for what

1. *Budget of a defect.* By (3), a group of irregular sites with u units and potential π has (2n² − 3n)·u + n·π to spend, and a nested family of silhouette runs that begins there with one site costs up to 3·(1 + 2 + … ) = (3/2)n². A vertex of an octahedron: 3 units and potential 9 give 6n², and four families begin there: equality. A corner of an island: 1 unit, potential 3 − 6 = −3, one family: 2n² − 6n against (3/2)n², enough only for n ≥ 12. For smaller n the half-open chords that the island makes out of the rows under it pay the difference; for one island they pay it exactly in (I_4). This is the defect with the least room that I know: 4·u = 4 against 3·(families) = 3.
2. *Regular troughs pay for themselves.* A site of a regular trough has τ = 2 in the notation of 45.3 and blocks four chords, two in each face; in (I_n) its credit of 6 is what four short half-open chords cost. So chords that run from a ridge into a trough never need units, whatever their length.
3. *Merges and splits begin no family.* In the slices of Section 7.6 a silhouette run is a side of a piece between two convex corners. A side-connected piece without holes has 4 + (number of sides between two reflex corners) such sides. When two growing squares meet at a corner and continue as their union, the eight sides become four: four families end and none begins. So in this count a merge needs no units, and the same holds, read upwards, for a split of a shrinking piece. The count by chains needed 3 units there (a long chain that starts below a split), could not find them at the split, and Sections 15, 17 and 43 are about that. In the count by runs the question does not arise.
4. *What needs units.* (i) A family that begins with one site: a corner of a face, that is a site exposed for some ν whose two neighbours on a line of the face are empty. At leading order 3/4 of a unit each. A one-site top has four such corners and 3 units (Theorem 36); a site with seven empty neighbours has one and, in the examples, 1 unit. (ii) A family that begins at a run next to a trough: in the sweep along an axis this is a side of a growing piece that comes out from under a shrinking one (the starts below shrinking pieces of Section 14, among them waists). It costs 3/4 times (1 − t/n)², t the length of the trough, shared between the two ends of the trough; each trough has two such families, one on each of its faces. A corner of a waist is the end of two troughs and so needs 1.5 units; the saddles computed have 6. (iii) Families that begin at irregular sites of other kinds.
5. *Twin tops are cheap, not dear.* For O_7 with its translate by (2, 0, 0) the four faces between the two tops are strips two sites wide: their families at the tops have one run each, and the rest of their rows are short half-open chords paid by the trough. The body has 42 units and Π = 54 and the least increment is 216.

### 46.7 Statements that are false

1. (M_n) from n = 6 on (46.1).
2. The number of open ends with half-length at most x is at most (16/3)·U*·x, the analogue of (K) for open ends. A step two sites wide makes short half-open chords along its whole length at no cost: −172 for O_9 with its translate by (2, 2, 2), false for 127 of the 315 islands on O_13 (`ends.py`). The trough has to be credited, as in (I_n).
3. (I_n) without the credit for long half-open chords, that is 3H_n + (3/2)h_{n+1} ≤ (4n − 1)U* + Π − 9·def₁: false at n = 3 for islands (−9 for O_9 with k = 3 at (1, 2); `sharp.py`).
4. M′_3 ≥ 0: false for six of the pairs of octahedra joined by one site (least −30).

### 46.8 What a proof now requires

M′_4 ≥ 0 and (I_j) for 4 ≤ j < n, n the size in the reduction; or (M′_n) for that n in any other way; with equality in Λ_n only for O_n.

As far as I can see a proof would consist of:

1. *The structure of families.* A silhouette run of L ≥ 2 sites whose two end sites are regular ridge sites should have, in the next row towards the apex of its triangle, either a silhouette run of L − 1 sites nested in it or an interruption (a site that is not exposed). This should follow from Lemma 20 and is not written. It makes every family begin at a corner of a face, next to a trough, or at an irregular site.
2. *Local bounds*, of the kind of Theorems 36 and 38 and with the same tools: for a group of irregular sites, 4·(units) ≥ 3·(corners of faces + ends of short troughs at the group), and in the case of equality the potential has to be at least 9/4 per corner, as it is at a vertex. For one-site tops this is Theorem 36 together with π = 9. For the other kinds of corner, for trough ends, and for the sharing when several lie in one group, nothing is proved. The island shows that the bound for corners has no room to spare beyond what is there: 1 unit for a corner that needs 3/4. A first attempt at the corners fails as it stands: the units at the corner site itself, bounded from below through its own neighbours only (α, the part of β that no neighbour can remove, and γ of Theorem 5), are fewer than 3/4 per corner for 507 of the 1,317 neighbourhoods that have a corner, and can be 0 (`corner.py`). A site with a corner is never regular (a ridge of Lemma 20 contains no two opposite steps), so a unit sits at it or next to it; the count has to move units from the neighbours, as the proofs of Theorems 16 and 36 do.
3. *Lower-order terms*: def₁, families that begin with more than one site, short families, and the base M′_4.
4. *The sharp case*: M′_n = 0 and R_n = 0 only for O_n.

Compared with the end of Section 45: the target is now right at every scale in every body tried, where (M_n) was wrong for small n in a way that grows with the body; and item 3 of 46.6 removes the case that was the obstacle since the eighth pass. What is new on the debit side: half-open chords must be carried along, and the potential π brings in the neighbours' neighbours.

Code and outputs: `claude/fcc-verification-code-20.md`.

## 47. Fans: a count for each length, and soundness for large n from it (twenty-fourth pass)

I could not finish the proof. This section holds: the structure of the silhouette runs whose two ends are regular (47.1); a theorem that reduces soundness, for n large against m, to a count (A) in which n does not occur (47.2); the evidence for (A) (47.3); where the runs of one length come from, with two lemmas and a proposition (47.4); three counts that are false (47.5); what a proof of (A) requires (47.6). Proved: Lemma 68, Theorem 69, Lemmas 70 and 71, Proposition 72. Open: (A).

### 47.1 Shape-regular sites and fans

Notation of Sections 45.3 and 46. For a site h of S let E(h) be the set of its steps to empty sites. Call h *shape-regular* if E(h) is empty, or R_ν for an octant ν (a face), or R_ν ∪ R_ν′ for two octants that differ in one sign (a ridge; the two octants share one step), or R_ν ∩ R_ν′ for two such octants (a trough; one step). These are 1 + 8 + 12 + 12 sets, the shapes of Lemma 20. Otherwise h is *shape-irregular*, and I(S) is the set of these sites. This is a property of the set S alone; no decoration enters. By Lemma 20, in a fold every shape-irregular site carries a unit or has a neighbour in S that does, so a component with U units has |I| ≤ 13·U.

Write R_ν = {r_1, r_2, r_3}. The steps d with d·ν = 0 are the six differences r_i − r_j. A ridge site h of ν whose second octant shares r_i with ν has, in the plane of ν, exactly the empty neighbours h + r_i − r_j and h + r_i − r_k. So the face lies on a fixed side of each of its three kinds of ridge line; this is the orientation rule of 45.5, item 2.

*Fans.* For k in {1, 2, 3} and {i, j} the other two indices put a = r_k − r_j and b = r_k − r_i, so that a·b = 1. For a lattice point X, the **fan** (ν, k, X) consists of the segments from X + t·a to X + t·b for t ≥ 0. Level t has t + 1 sites and the direction b − a = r_j − r_i. X is the *tip*, and the lines through X in the directions a and b are the *a-line* and the *b-line* of the fan. The rows of a triangular face parallel to one side, counted from the opposite corner, are the levels of one fan; a face of O_r carries three fans, one at each corner. The three fans of ν = (σ_x, σ_y, σ_z) have their tips towards the three axis directions σ_x·e_x, σ_y·e_y, σ_z·e_z, and a level of a fan is a side of a slice piece in the slices orthogonal to that axis (45.3).

Call a silhouette run **active** if its two end sites are shape-regular, and let a_L(S) be the number of active runs with exactly L sites.

**Lemma 68.** (a) A chord end can be blocked only by a trough site or by a shape-irregular site. A trough site blocks at most 4 chord ends; any site blocks at most 16 and has at most 48 open ends. (b) The site at an open end of a chord is a ridge site or shape-irregular. If it is a ridge site, the chord belongs to ν and has the direction r_j − r_i, and the empty site beyond the end is reached by the step r_i − r_j, then its ridge is the one whose second octant shares r_i with ν, and the line of that ridge has the direction a. (c) An active run has at least two sites. An active run with L sites is the level L − 1 of exactly one fan, with its end sites on the a-line and on the b-line; so a fan has at most one active run at each level, and a_L is the number of fans with an active run at level L − 1. (d) The two neighbours of a ridge site on the line of its ridge are in S, and each of them is a ridge site of the same ridge or shape-irregular. So a maximal run of ridge sites of one ridge on its line, a *ridge segment*, ends at a shape-irregular site of S on both sides.

Proof. (a) and (b) are enumerations of the 4,096 sets E (`acount.py local`). A site g can block the chord of ν that ends at g − d only if g is not ν-exposed, g − d is in S, and g + (r − d) is empty for the step r of R_ν with r·d = 1, because that site is a neighbour of the exposed site g − d by a step of R_ν. Counted over all (ν, d) this gives 0 for interior, face and ridge sets, 4 for trough sets and at most 16 for the others. A ν-exposed site with an empty neighbour in the plane of ν has E strictly larger than R_ν; among the 33 sets these are the three ridges of ν, and the one that contains r_i − r_j is the ridge that shares r_i. (c) One site cannot lie on two ridges, so L ≥ 2. Let e_1 be the end from which r_i − r_j leads out and X = e_1 − (L − 1)·a. The other end is e_1 + (L − 1)(b − a) = X + (L − 1)·b, and by (b) the two ends lie on ridges with the directions a and b. (d) For each of the 12 ridges and both directions, the steps of the next site that the ridge site forces to be empty or occupied are compatible with only one of the 33 sets, that of the same ridge (`structure.py tips`). On bodies: `structure.py`, check (1). ∎

*Weights.* With o(g) and bl(g) as in 46.3 put χ(g) = (3/2)·o(g) − 3·deg(g) + 9 = π(g) + (3/2)·bl(g). Because Σ_g o(g) = 2H + H₁ and p = Σ_g (deg(g) − 3) + 3·def₁,

    M′_n = (2n² − 3n)·U* + n·Σ_g χ(g) − 9n·def₁ − 3·A_n.        (4)

χ = 0 at face and ridge sites and χ = 6 at trough sites.

### 47.2 Soundness for large n from a count without n

**(A).** For every finite connected set S with at least two sites that is not a regular octahedron O_r with r ≥ 5, and for every L ≥ 2: 3·a_L(S) ≤ 4·U*(S) − 1.

In words: for each length, the runs of that length between two regular ridge sites number less than 4/3 of the units. For O_r with r ≥ 5, a_L = 24 for 2 ≤ L ≤ r − 1 and U* = 18, so 3·a_L = 4·U*.

**Theorem 69.** (a) For every finite set S and every n ≥ 3,

    Λ_n ≥ M′_n ≥ (2n² − 3n)·U* − 3·Σ_L a_L·(n + ½ − L)₊ − 9n·def₁ − 99n·|I|.

(b) If 3·a_L(S) ≤ 4·U*(S) − 1 for every L, then Λ_n(S) ≥ (n − 1)²/2 − 9n·def₁ − 99n·|I|, which is positive as soon as (n − 1)² > 18n·(def₁ + 11·|I|).

(c) If (A) holds, the reduction of Section 26 is sound for every n ≥ 46,656·m + 2: the H-set of a fold of w with gap at most 9m consists of m copies of O_n, no two adjacent.

Proof. (a) Λ_n ≥ M′_n is Proposition 65. In (4), split A_n by chords. An active run with L sites costs 3·(n + ½ − L)₊. By Lemma 68(b) every other chord with two open ends has a shape-irregular end site z; charge it to z. It costs less than 3n, and the number of chords charged to z is at most o(z). By Lemma 68(a) a chord with one open end is blocked by a trough site or by a shape-irregular site; charge it to the blocker. It costs at most 3·(n/2 − ¾). A trough site g has n·χ(g) = 6n and is charged at most 4·3·(n/2 − ¾) = 6n − 9. A shape-irregular site z is left with at least n·χ(z) − 3n·o(z) − (3/2)n·bl(z) = −n·(3·deg + (3/2)·o + (3/2)·bl − 9), and the bracket is at most 99 for every set E (`acount.py local`; 99 is the single site). Face and ridge sites have χ = 0 and are charged nothing.

(b) Σ_{L=2..n} (n + ½ − L) = (n − 1)²/2, so 3·Σ_L a_L·(n + ½ − L)₊ ≤ (4U* − 1)(n − 1)²/2, and (2n² − 3n)·U* − 2·U*·(n − 1)² = (n − 2)·U* ≥ 0.

(c) Let C be a component of the H-set, with U units in the fold; U ≤ 18m. As in the proof of Proposition 62(c), the sum of Λ_n over the components is at most 0. A single site has Λ_n > 0 and O_r with r ≥ 5 has Λ_n = 36(n − r)² (Proposition 62(b)). For any other component, U*(C) ≤ U; def₁(C) is at most the number of surface sites of C without a chain P, each of which carries a unit, so def₁ ≤ U; and |I(C)| ≤ 13·U. Then 18n·(def₁ + 11·|I|) ≤ 18·144·18·n·m = 46,656·n·m < (n − 1)², and by (A) and (b) Λ_n(C) > 0. So every component is a copy of O_n, and the proof ends as that of Proposition 62(c). ∎

`acount.py` asserts the inequality of (a) against M′_n computed from the definition, for n = 3, 8, 38, 200 on the named bodies and for n = 4, 38 on every twentieth body of the scans of 47.3.

**Remarks.**

1. *What is gone.* (A) contains no n, no potential, no half-open chords and no lower-order terms. All of these are in the term 99n·|I|, which is paid by the half square (n − 1)²/2 that the −1 in (A) leaves. The price is the size of n: n ≥ 46,656·m + 2 instead of n ≥ 38. The reduction allows it: n = 3Bt + 2 with t free, so t ≥ 15,552·m/B will do, and the word stays of polynomial length.
2. *(A) one length at a time.* (K) of Section 45.3 counts all silhouette runs with at most j sites together. For one length the count of all runs is false: O_9 with an island of side 3 has 30 silhouette runs of 3 sites against (4/3)·U* = 28, and O_6 without a vertex has 32 runs of 5 sites against 25.3. The runs in excess have a shape-irregular end site (the three edges of the island, each seen from the top and from the side; the rows that end at a cut site or at a vertex) and go into 99n·|I|. Counting active runs only, the two bodies have a_L ≤ 27 and a_L ≤ 24.
3. *(A) in slices.* An active run of a fan whose tip points along a coordinate axis is a side of a slice piece that runs from one convex corner to the next, is exposed above, and has regular corners. A regular growing square has four. So (A) says: over the six directions, the growing sides of any one length number less than 4/3 of the units. This is A1 of Section 24 counted by sides and one size at a time, with the sharp case A2 in the −1. A merge of two growing squares lowers the count (46.6, item 3).
4. *(A) is not weaker than what is needed at one n.* A fan that begins at a trough of 1,000 sites costs nothing in (L_n) for n = 38, and counts in a_L for L > 1,000. In the bodies computed this is harmless: the saddles at the ends of such troughs carry 6 units each.

### 47.3 Evidence for (A)

a_max is the largest a_L (`acount.py`).

| Family | Bodies | Least 4U* − 3·a_max |
|---|---|---|
| Unions O_a ∪ (O_b + v) of Section 42 | 374 | 6 (O_7 and O_9 with their translates by (2, 2, 2): U* = 24, a_max = 30) |
| Bodies at one site from O_5, …, O_8 | 1,416 | 4 (a vertex removed: U* = 19, a_max = 24) |
| Connected bodies at two sites from O_5 | 21,055 | 8 (two vertices removed) |
| Islands on a face of O_9 and of O_13 (46.1) | 425 | 3 (U* = 21, a_max = 27; 95 bodies) |
| One-layer pits in a face of O_9 and of O_13: the triangles of the islands, in both orientations, taken out of the face layer, the body staying connected (one-site pits occur twice in the list) | 540 | 4 (a pit of one site at a vertex of the octahedron); at least 12 for all others |
| Two copies of O_5 or of O_6 joined by one site | 379 | 28 (U* = 43, a_max = 48) |
| Roofs of Section 42 | 538 | 40 |
| Named bodies: tetrahedra, rod, layer, cavities, ring of four, three in a row, tip to tip, zigzag, steps, O_2, O_3, O_4 | 40 | 3; the value 0 occurs only for O_5, …, O_9 |

No body other than a regular octahedron has 3·a_max ≥ 4·U*; the scans hold 24,727 bodies. Annealing on 4U* − 3·a_max by single sites, seven runs with 24 starts (octahedra, bodies next to them, islands, unions, steps; `asearch.py`): no violation. From an octahedron the least value reached on another body is 4, a vertex removed; from the islands nothing below the starting value 3 was reached. As in Sections 42, 45 and 46 the searches moved little, so they add little.

The limits are those of the earlier sections: at most 1,547 sites, moves by single sites, families chosen by me.

### 47.4 Where the runs of one length come from

Fix an active run C, the level t of the fan (ν, k, X). Walk from its end on the a-line towards the tip. By Lemma 68(d) the sites X + s·a, s = t − 1, t − 2, …, are ridge sites of the ridge of the a-line until the first one that is not, and that one is in S and shape-irregular. Let t_1 < t be its level, and t_2 the same for the b-line. A level can be negative: the ridge may run on past the tip.

**Lemma 70 (roots).** max(t_1, t_2) ≥ 0.

Proof. Otherwise X is a ridge site of the ridge of the a-line and of the ridge of the b-line. ∎

Call the site or the two sites at level τ = max(t_1, t_2), on the line or lines where the maximum is attained, the *nearest roots* of C. For a fan that begins at a corner of a face both are the tip.

**Lemma 71 (one run per root, face and line).** Fix L, ν, k and one of the two lines. A shape-irregular site is a nearest root, on that line, of at most one active run with L sites.

Proof. Let z be a nearest root on the a-line of C in the fan with tip X and of C′ in the fan with tip X′, both at level t = L − 1, with z = X + τ·a = X′ + τ′·a. If τ = τ′, the two fans are the same and so are the runs. Let τ′ < τ. Then X′ = X + (τ − τ′)·a. Since τ′ is the level of the nearest roots of C′, the sites X′ + s·b with τ′ < s ≤ t are ridge sites of the ridge of the b-line. Take s = t − τ + τ′; then τ′ < s < t, and τ′ ≥ 0 by Lemma 70, so 1 ≤ s ≤ t − 1. The site X′ + s·b = X + t·a + s·(b − a) is the site number s of C counted from its end on the a-line, an interior site of C. Both its neighbours on the line of C are in S. But a ridge site of the b-line has the empty neighbour in the direction b − a. The b-line is the same with a and b exchanged. ∎

**Corollary.** a_L ≤ 4·(number of ridge segments), for every L: a nearest root on a line, with the face, is one end of one ridge segment with one of its two faces.

This bound has the wrong constant by a wide margin (for O_r it gives 48 against 24, and it does not see that the two faces at the edge of an island behave differently), and with it Theorem 69(a) gives nothing. It is the frame in which the sharp count has to be made: every active run of L sites is held by one or two shape-irregular sites, and no site holds two runs of one length on the same face and line.

`structure.py` confirms Lemma 68(d), Lemma 70 and Lemma 71 on 810 bodies (103,045 active runs, 201,401 charges), and also the following: a silhouette run for which all sites of the run, and all sites of S on the line before it that are adjacent to it, are shape-regular has on that line a silhouette run with one site less whose shadow it is.

**Proposition 72 (tips).** Let a fan have an active run at level 1, and let its tip X point in the axis direction e. Then X is in S, the four neighbours X + r with r·e = −1 are in S, and three of the four neighbours with r·e = 0 are empty: the one reached by the step of R_ν orthogonal to e, and the two on the line through X parallel to the run. Hence a site is the tip of such fans for one axis only; for one direction of that axis it is the tip of at most 4 of them, and of at most 1 unless all four neighbours in the plane orthogonal to the axis are empty.

Proof. The two sites of the run are ridge sites of known ridges, and each fixes four of the neighbours of X (`structure.py tips`, all 24 pairs (ν, k)). A second axis would need two of the neighbours that the first one needs empty. ∎

*Units at a tip.* If all four are empty, X is a site with four empty side neighbours and four occupied lower neighbours, and Lemma 44(a) gives at least 3 units at X and its neighbours (3, 5, 9, 13, 14, 17 according to the occupied upper corners): 3 units for 4 fans, the ratio of (A). If exactly three are empty, X is shape-irregular, because two of its empty steps are opposite, and Lemma 20 gives one unit at X or next to it: 1 unit for 1 fan. So every tip of this kind has, in its own neighbourhood, the 3/4 of a unit per fan that (A) asks for. This does not prove (A) for L = 2: tips two steps apart share neighbours, and the units found there may be the same.

*Charges move.* Charge each active run of L sites 1 in total, to its nearest roots (`charges.py`). In O_6 every vertex is charged 4 for every L. In O_9 with an island of side 3 away from the edges, the three corners of the island are charged 1 at L = 2 and nothing else, and three vertices of the octahedron are charged 3 instead of 4 for the lengths at which the island interrupts their rows. Put the same island in a corner of the face, and the vertex next to it becomes a site with seven empty neighbours that is charged up to 2; two ridge sites below the corners of the island, with four empty neighbours each, are charged 3/2 for L = 5, …, 8, and the vertices at the far ends of their ridges are charged 2 instead of 4 for L = 6, 7, 8. The whole body has 21 units and a_L ≤ 24. So a shape-irregular site on a ridge takes over, for the longer runs, the charge of the vertex behind it. The count has to be made for groups of sites, or the vertex has to lend. I have not computed how the 6 units that this body has beyond its five intact vertices are distributed over the sites around the island.

### 47.5 Three counts that are false

Each of these would have given (L_n) for large n by the same computation as Theorem 69, and each fails on bodies for which (L_n) holds.

1. *Fans.* The number of fans with at least one active run is at most (4/3)·U*. False: 31 fans against 21 units for O_9 with an island of side 3 in a corner of the face, and for O_5 with O_8 + (3, 1, 1) (`fans.py`). It stays false if a fan whose first active level is t_0 is weighted by (1 − t_0/n)²: 28.83 against 28 at n = 48. The island lengthens some rows of two neighbouring faces by one site; these rows leave the fans at the vertices and form four new fans whose tips lie outside the body. Fans are born and die at such steps; only their number at one level is bounded.
2. *Sources of runs.* Match silhouette runs on neighbouring lines of a plane, a run with the run before it if they are adjacent and the later one is shorter by at most one site, and call the unmatched later runs sources. Then the cost Σ (n + ½ − |C|)₊ of all runs is at most n²/2 for each source, plus n for each site by which a matched run falls short of one more than the run before it (`sources.py` asserts this), and the number σ of sources would have to be at most (4/3)·U*. False: σ = 33 against U* = 21 for the islands, 42 against 24 for O_7 with its translate by (2, 2, 2). An edge of an island, seen from the side, is a family of one run; and the rows of the face under an island begin again behind it. Both are counted as new families, and neither costs what a family costs.
3. *Ends.* Go along each ridge segment, for each of its two faces and each of the two directions of chords, from the side of the tip, and call an end a source if it is the first one of the segment or if its chord has not grown. The cost of the ends at ridge sites is then at most n²/4 for each source (`endsrc.py` asserts this), and the number Σ of sources would have to be at most (8/3)·U*. True for the islands away from the edges (54 against 56), false for the island in the corner: 60 against 56. A step on a ridge cuts it into segments, and each segment begins again.

The count that survives all three kinds of example is the one per length.

### 47.6 What a proof of (A) requires

For each L, an assignment of the active runs of L sites to shape-irregular sites, or to groups of them, in which a group with u units receives fewer than (4/3)·u runs, the vertex of an octahedron with its 3 units and 4 runs being the one case of equality. Lemmas 70 and 71 give the candidates, the nearest roots, and bound what one site can receive from one face and line. Three things are missing.

1. *The starts that are not tips.* Proposition 72 covers the fans that begin with two sites. In the scans the others are of three kinds (`fans.py`): the two ridges begin at two different shape-irregular sites (a cut vertex, a run next to a trough); one ridge begins at a shape-irregular site and the other runs on; neither does, and a shape-irregular site lies on the first run or on the level before it. For the unions of two O_7 the numbers are 2,812 fans at vertices, 116 at other tips, 106, 300 and 36. For each kind the units near the start have to be found, as Lemma 44 does for apexes.
2. *Sharing and lending.* Units found near two starts must not be counted twice, and the charge must be allowed to move back along a ridge to the vertex behind (47.4). In the proof of Theorem 36 the first problem is solved for tops; I have not looked at whether that proof extends to tips of the second kind of Proposition 72, which are not tops. The second problem is a condition of Hall's type on runs and groups, for each L.
3. *The −1.* A connected body in which every group has equality is an octahedron. With equality only at vertices of octahedra this is the statement that a connected body all of whose shape-irregular sites are such vertices is an octahedron. I expect this to follow as in the model case of Section 10.3 and have not written it. With other cases of equality, if there are any, it is open.

Compared with the end of Section 46: the open statement is simpler, and its frame (fans, roots, one run per site, face and line) is proved. The step that is missing is the one that has been missing since the fourteenth pass, a sharp count of local configurations against units with the sharing between neighbours; three forms of it that looked natural are false; and the two routes now differ in what they need at the start: (I_n) with M′_4 ≥ 0 works for n ≥ 38 and needs the potential and the half-open chords, (A) needs neither and works for n ≥ 46,656·m + 2.

Code and outputs: `claude/fcc-verification-code-21.md`.
