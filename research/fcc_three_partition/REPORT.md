# Ordinary FCC HP from unary 3-Partition: continuation, 13 November 2026

## Result and scope

Ordinary unpinned binary FCC-HP hardness remains unproved. This continuation
establishes a substantially stronger obstruction to the programmed-ribbon route,
and a weaker sufficient soundness condition that does not require a unique
container or perfectly confined items.

**New constructive theorem.** For every binary program sigma of even length
`L=2m`, the exact notebook word `W_sigma` has an ordinary self-avoiding fold with

```
E = 51m - 15 = (51/2)L - 15.
```

The intended ribbon scores only `50m-15`. Four compatible, explicitly listed
36-residue tiles realize the new bound for **every** program, with exactly the
same occupied H set regardless of the program. This is an extensive improvement,
not an endpoint effect. All P sites and all contacts are included. Consequently
the proposed global selector bound at `25L-15` is false, even if one additionally
restricts the H set to seven sites in each of L consecutive triangular layers.
No upper bound on unrestricted optimum is claimed for the new construction.

**New conditional soundness theorem.** Suppose an energy threshold forces all
but D item H residues into q specified-capacity bins, whose mutual lattice
distances exceed `2(D+1)`. Scaling every item and capacity by an integer `r>D`
then suffices to recover an exact 3-Partition. Neither straight item paths nor
outward P positions nor exact bin filling is needed. A perturbation version of
the forest-hole argument supplies `D <= 2 epsilon + 16 s` if the labelled
scaffold H set is within s exchanges of a suitable octahedral template and the
total score is within epsilon of its full-H contact count. For the actual
separated straight bins, a refinement improves this to `D <= 2 epsilon + 12 s`.
Using the two backbone P neighbours of every item H further improves the
displacement bound to `floor((2 epsilon + 12 s)/3)`.

The unresolved task is to force that labelled scaffold approximation, with a
small enough error bound, by a polynomial-size *freely folding* binary prefix.
The existing programmed words cannot supply the proposed forcing theorem.

No existing repository file was edited. No Lean theorem or hardness statement
was added. All files for this continuation are in this directory. No literature
priority claim is made.

## 1. Conventions and input model

Use FCC sites `x+y+z` even and steps that permute `(+-1,+-1,0)`. Auxiliary
coordinates are those of notebook Sections 37 and 42:

```
(r,s,k) -> (r+k, -r+s, -s+k).
```

Within a fixed r layer, transverse steps are `+-(1,0), +-(0,1), +-(1,1)`.
Positive-r steps have transverse increments `(0,0),(1,0),(0,-1)`.
Every FCC edge changes r by at most one. The same is true of s.

Scores below exclude consecutive H-H pairs. For comparison with the repository's
cubic conventions, the raw induced H-edge count is the ordinary score plus the
word's fixed number of consecutive H-H pairs. The compatibility import
`ProteinFolding/Statement.lean` points to `ProteinFolding/Cubic/Statement.lean`;
none of its cubic geometric lemmas is used as an FCC statement here.

Coordinates in our certificates describe witness folds, not resources in the
target input. Each tested target consists solely of one H/P word and a threshold.

## 2. A universal competitor to the programmed ribbons

Retain the notebook's exact words

```
U0 = (PHP)^2 PHH (PHP)^3 = PHPPHPPHHPHPPHPPHP
U1 = HHP (PHP)^5.
```

Each has length 18, seven H residues, one consecutive HH pair, and ends in P.
For any `sigma in {0,1}^{2m}`, set `W_sigma = product U_sigma[i]`. This is an
explicit word of length `36m`; its original proposed selector threshold is
`K_ribbon=50m-15`.

### 2.1 Four finite tiles

The complete coordinate tables are in [universal_tiles.md](universal_tiles.md),
generated from the four `periodic_threaded_*_cell_universal.json` certificates.
Column ab folds the exact word `U_a U_b`. The tile translation is

```
T = (2,1,0) auxiliary = (2,-1,-1) physical.
```

Every tile has the **same** fourteen H positions, `A union B`, where

```
A = {(0,s,k): (s,k) in
     {(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,1)}}
B = {(1,s,k): (s,k) in
     {(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)}}.
```

Let `Q=(1,1,2)`, `V=(1,0,1)`, and `H0=(0,0,1)`. The four tables satisfy:

1. Each is an injective FCC walk with exactly the prescribed H/P labels.
2. Every last residue is the P at V.
3. A tile whose first bit is 0 starts with P at `Q-T=(-1,0,2)`;
   a tile whose first bit is 1 starts with H at H0.
4. All positions other than the possible first P lie in r=0 or r=1.
5. No tile occupies Q.
6. V is adjacent both to Q and to `H0+T`.

These are finite integer conditions verified directly by
`universal_competitor.py`. The certificate is the displayed coordinate table,
not a solver status.

### 2.2 Proof of validity for arbitrary programs

For pair j, use column `sigma[2j] sigma[2j+1]`, translated by jT. Conditions
2, 3 and 6 give the backbone edge between every successive pair of tiles.

The main positions of tile j lie in layers 2j and 2j+1, so distinct tiles'
main positions cannot collide. Its optional initial P lies at `Q+(j-1)T`, in
the preceding tile's reserved Q position. Condition 5 leaves this site empty
in every choice of that preceding tile. These exceptional initial sites are
distinct from one another. This proves global injectivity for arbitrary mixing,
including all P residues. There are no prescribed positions or obstacles in
the folding instance.

### 2.3 Exact contact count

Each A and B has eleven internal triangular edges. There are sixteen A-B
edges inside a tile, hence 38 raw H-H edges per tile. Across successive tiles
there are fifteen raw H-H edges. No H contacts can skip a tile, because an FCC
edge changes r by at most one. Thus

```
raw H edges = 38m + 15(m-1) = 53m-15.
consecutive HH pairs = 2m.
ordinary score = 51m-15.
```

The H set is independent of sigma, and each of its 2m r layers has exactly
seven sites. Every individual P route, the HH correction, and all intertile
contacts have therefore been accounted for. The proof gives the result for
arbitrary m. Exhaustive checks of all programs with 2, 4, 6 and 8 modules
(340 examples) supplement that proof.

For instance `sigma=00110110` gives a 144-residue chain with score 189,
where the notebook ribbon threshold is 185. Its full physical-coordinate
certificate is `universal_example.json`.

For odd length `L=2m+1>=3`, append a dummy zero bit, use the even construction,
then remove its final eighteen residues. This gives the exact score
`51m-3+5*sigma[L-1]`: the final half-tile adds respectively twelve or seventeen
contacts to the preceding m full tiles. Thus every odd-length program with
L>=29 also strictly beats its intended ribbon score. The checker exhausts
all 680 odd programs of lengths 3,5,7,9. Parity does not offer an asymptotic
escape from this competing construction.

### 2.4 Consequences and limits

* Any threshold at or below the intended ribbon score admits this competing
  fold. Raising the threshold above that score discards the intended ribbon
  completeness witness. An O(1) end correction cannot repair a gap of m.
* Repeating bits or enlarging the original programmed word does not remove
  the obstruction: the construction accepts every even-length program.
* Merely proving seven-H-per-layer occupancy would not rescue the intended
  ribbon threshold: the competitor already has that occupancy.
* This does not rule out a modified word, a different optimal phase, or a
  whole-chain construction where additional item/scaffold interactions force
  useful geometry. Isolated scaffold scores cannot simply be added to item
  scores in such a construction.
* It does not disprove the notebook's conditional formula *on its own family*,
  nor the six-H-per-layer theorem, nor the conjectured private-P coefficient
  for `(PHP)^h`. Our word contains HH and shared backbone P sites.

There is also an exact statement in the general defect accounting of Section 13.
For a program of length L, the HP-edge count is `12L-sigma[0]`, h=7L, and the
HH correction is L. The intended ribbon has

```
D_defect + 2V + R_H + R_P = 56L + 120 + 6 sigma[0].
```

The new construction has instead

```
D_defect + 2V + R_H + R_P = 52L + 120 + 6 sigma[0].
```

Thus a whole-chain lower bound at the old defect budget is false for these
words. The four nonnegative terms remain valid; the missing lower bound was
the problem. The private-P formulas cannot be substituted for this general
identity on words containing HH.

## 3. Additional explicit failures and search scope

Before finding the universal competitor, local search found:

| Word or construction | Ribbon score | Certified competing score |
|---|---:|---:|
| `(PHP)^6` | 9 | 12 |
| `U0` | 10 | 14 |
| `U0^2` | 35 | 37 |
| `U0 U1 U0 U1` | 85 | 88 |
| `U0^L`, replace just its first module, L>=2 | `25L-15` | `25L-14` |
| `U0^L`, replace both ends, L>=3 | `25L-15` | `25L-13` |

The first four are individual witnesses, with no optimum claim. The last two
have closed-form cap coordinates in `cap_theorem.py` and proofs by finite
interface accounting. The left cap has eleven internal raw H edges and sixteen
edges to the unchanged next module; all of its P sites have r<=0. The right cap
has all sites in the last r layer or the next layer. Each contributes a net
gain of one and the caps do not interact for L>=3.

More generally retain the notebook's geometric bits b in the interior of an
all-U0 word, setting its first and last two bits to zero, and attach both caps.
The exact score is `25L-13-sum(b)`. Accordingly two incorrect interior bend bits
can be compensated by the caps at the original threshold. The 126-residue
example in `wrong_bends_certificate.json` has bits `0010100` and score 160,
exactly the original seven-module threshold. This is a specific failure of
program enforcement, not a proof that these deviations destroy every possible
bin decoder.

`search_folds.js` uses randomized segment regrowth, lattice pivots and interval
reversals. Initial runs freezing the end modules found no strict improvement
in four- and six-module all-U0 ribbons. That negative search outcome has no
optimality implication. `search_periodic.js` also failed to improve its initial
one-, two- and four-module cells in the recorded runs. The successful route was
instead to enumerate dense seven-site H layers and then thread the resulting
core with `thread_core.js`. This contrast is a warning against interpreting
local-search failure as geometric evidence.

`enumerate_layers.py` exhaustively grows connected triangular shapes up to
translation. The counts through size seven are 1,3,11,44,186,814,3652. Exactly
30 seven-site shapes have eleven internal edges and one has twelve. Among the
tested two-layer periods with arbitrary integral transverse shear, 87 ordered
shape/offset cases have at least 53 raw edges per period; six pass the necessary
P-neighbour degree test. Passing that test alone does not prove threading.
The four coordinate tables above supply actual threading for one of those
cores. No enumeration result is used as a global FCC upper bound.

### 3.1 Testing other one-marker words

Let M_i be `(PHP)^6` with its P at zero-indexed position i recoloured H;
there are twelve possible indices. This includes M_8=U0 and M_0=U1.
The following is a new exact bound over the **entire original ribbon family**,
allowing the marked position to vary arbitrarily from module to module:

```
E <= 25L + floor(L/2) - 15.                           (5)
```

`marker_family_bound.py` checks all 24 module states (marker index, geometric
bend bit) and all 576 ordered interfaces, with the actual consecutive-HH
correction. A module alone scores at most ten. Appending a module adds at most
25 contacts except for the single transition

```
(marker 9, bend 1) -> (marker 8, bend 0),
```

which adds 26. Such exceptional transitions cannot be consecutive. There are
therefore at most floor(L/2) of them, proving (5). This proof uses only the
finite interface table and the fact that no edge skips an r layer. The saved
transition matrix and an independently checked rational potential also give
the same bound.

The bound is attained for every L by truncating the alternating words and bits

```
V U0 V U0 ... ,        bits 1,0,1,0,...,
V = M_9 = (PHP)^3 HHP (PHP)^2.
```

In particular `(V U0)^m`, length 36m, has a ribbon fold with score `51m-15`.
This is a concrete better candidate phase than the old `25L-15` construction.
Its completeness within the specified family is proved. Its unrestricted
optimality and its ability to force walls or bins are unproved.
For a fixed marked word, its score on F_b remains affine in the bend bits;
this broader extremal calculation does not introduce interactions between them.

Even the stronger candidate does **not** force each sequence module into one
plane at that threshold. The valid 36-residue witness `marker_9_8.json` has
score 36, the exact two-module threshold. The first module's H positions are

```
(1,0,1), (1,1,0), (2,1,-1), (2,0,0),
(1,0,-1), (1,1,-2), (1,2,-3)       [physical coordinates].
```

The differences from the first point to the second, third and fifth have
determinant 2. These H positions do not lie in *any* plane. The total occupied
H set still equals A union B. This is a failure of module-to-layer registration,
not of that occupied core shape. Recovering a partition might not require such
registration, so it is not claimed to rule out every use of the new phase.

The broader marker search and its second pass are recorded separately in
`marker_search_log.json` and `marker_retry_log.json`. Each successful
`marker_i_j.json` is an independently verified full chain on the same H core.
Their common ports permit arbitrary concatenation of successful tiles:
the raw H-H contact count is `53m-15`, and the ordinary score subtracts the actual HH
backbone count. Allowing a marker on the last P can add a boundary HH pair,
so that correction must not be assumed to equal 2m in this expanded family.
`marker_verification.json` records the final covered pairs and the remaining
uncertified pairs. The two bounded passes produced certificates for 124 of the
144 ordered marker pairs; 20 remain uncertified. The common-port conditions
were checked on every saved tile, and 100 randomly mixed finite chains were
checked independently. A missing tile is an unsuccessful bounded search, not an
impossibility result. The original four U0/U1 tiles are fully covered regardless
of the outcome of this broader experiment.

## 4. Robust partition extraction without exact item paths

This lemma is independent of the failed programmed-word family.

**Lemma (separation and rounding).** Let a unary 3-Partition instance have
`a_1,...,a_{3q}`, total qB, and `B/4<a_i<B/2`. Choose integers D>=0 and r>D.
Let q pairwise disjoint bins `U_j` each have rB sites and suppose

```
dist_FCC(U_j,U_k) > 2(D+1) for j != k.
```

In one self-avoiding chain, let the designated item blocks be
`H(PH)^(r*a_i-1)`. Suppose at most D of their total rqB H residues lie outside
`U = union U_j`. Then the fold determines a valid 3-Partition.

**Proof.** Every item has at least r>D H residues, so it has an H in U. If one
item visited two bins, take two successive visits to different bins with no
visit to U between them. There are at most D intermediate H residues, all
outside U. Successive item H residues are separated by exactly two backbone
edges, regardless of their P positions. The endpoints would be at FCC distance
at most `2(D+1)`, a contradiction. Thus each item has a unique bin assignment.

Let d_j be the number of sites of U_j not occupied by item H, and t_j the number
of outside-U H belonging to items assigned to j. Both are at most D. The total
assigned item size in bin j is therefore

```
r sum_{i assigned to j} a_i = rB - d_j + t_j.
```

Its difference from rB is a multiple of r of absolute value at most D<r, hence
zero. Cancel r. The strict source size window implies exactly three items in
each bin. QED.

No outward-P condition, straightness, layer condition, or local zero-defect
assumption was used. Long P separators between different items are harmless
for this argument because it only follows consecutive H *within* an item.

The strict rounding margin is material. At r=D=1, the no-instance
`B=15, (a_i)=(4,4,4,6,6,6)` admits groups of sums 14 and 16, each within one of
15. None of its possible triples sums to 15. A capacity error of one is enough
to lose the conclusion if scaling is omitted.

For the standard face bins

```
U_j = {(r0,G*j,0) auxiliary: 0<=r0<rB},
```

their FCC distance is at least G, because each edge changes s by at most one.
Thus `G=2D+4` suffices. This supplies an explicit geometric separation parameter,
without relying on item straightness for soundness.

## 5. A perturbed, labelled-scaffold contact bound

**Lemma.** Let C be a finite set in a Delta-regular graph, U a subset inducing
a forest, every U vertex having at least rho neighbours in C, and every vertex
outside C having at most b neighbours in C. Put `S0=C\U`. Let S and A be
disjoint actual H sets with `|S|=|S0|` and `|A|=|U|`. S denotes the designated
scaffold labels and A the item labels. Define

```
D_U = U \ (S union A),  d=|D_U|,
s0 = |S0 \ (S union A)|,
s = |S0 \ S| = |S \ S0|,
g = (Delta+b)/2.
```

Then

```
e(C)-e(S union A) >= (rho-1-g)d + c(D_U) - g*s0.       (1)
```

**Proof.** Removing D_U from C loses at least
`rho*d-e(D_U) >= (rho-1)d+c(D_U)` edges. Subsequently removing the missing S0
vertices cannot restore an edge. Since the total H count is |C|, the actual H
set has exactly d+s0 vertices outside C. The degree/outside-neighbour calculation
from the forest-hole lemma bounds all contacts gained by these vertices by
`g(d+s0)`. Subtraction proves (1). All H-H interactions, including scaffold-item
and item-item contacts, are included. There is no addition of separately
optimized gadget scores. QED.

For the notebook's octahedron with all (111) faces, use Delta=12, rho=9, b=3:

```
e(C)-e(S union A) >= d/2+c(D_U)-(15/2)s0.              (2)
```

If the ordinary score is at least `e(C)-c_HH-epsilon`, where c_HH is the fixed
backbone HH count of the entire word, then (2) gives `d<=2epsilon+15s`.
There are at most s scaffold H in U. Counting item H in U now yields

```
|A \ U| = d + |S intersect U| <= 2epsilon + 16s.      (3)
```

This explicitly tolerates some scaffold H invading the bins. Translation or
FCC isometry of the template may depend on the fold; uniqueness of the template
orientation is unnecessary. The approximation must concern the *labelled*
scaffold subset S. Knowing only that the combined H set resembles C does not
identify which sites are available to the items.

`robust_checks.py` independently checks (1)-(3) on 1,000 reproducible perturbed
and relabelled configurations of a 489-site FCC octahedron. The displayed
counting proof is the result; the randomized tests are supplementary.

**Refinement for the actual straight, well-separated face bins.** For these
bins, `C\D_U` has minimum degree at least four. Indeed an FCC octahedron of
radius at least two has minimum degree four: choose a nonzero coordinate and
the four steps decreasing its absolute value; at the centre all twelve steps
are available. Any C vertex adjacent to U is well inside the selected face
or the next inner layer, hence has at least nine neighbours in C. It can be
adjacent to at most two U sites: a line intersects its radius-sqrt(2) sphere
at at most two points, and bin separation greater than two rules out neighbours
in two bins. Deleting D_U therefore leaves degree at least seven at these
affected vertices, and at least four elsewhere.

Consequently deleting the additional s0 missing scaffold sites loses at least
`2s0` further edges. For any subset Z of a graph of minimum degree four,
the edges incident to Z number `sum_deg(Z)-e(Z) >= sum_deg(Z)/2 >= 2|Z|`.
Keeping this term in (1) improves (2) and (3) to

```
e(C)-e(S union A) >= d/2+c(D_U)-(11/2)s0,
|A \ U| <= 2epsilon+12s.                              (4)
```

The same finite perturbation tests also verify (4). The coarser bound (3)
remains valid for the more general forest-hole setting without this degree
condition.

**Sequence-aware refinement.** The regular-graph calculation can also retain
the two chain-P neighbours of each outside item H. Pad the final item with a P;
the prefix connector already precedes the first item with P. Then every item H
has two distinct non-H neighbours, so its actual H degree is at most ten.
No corresponding degree-ten assumption is made about scaffold H.

Let `O=(S union A)\C`, `a_out=|A\C|`, and `B'=e(O,(S union A) intersect C)`.
The actual degrees, unlike degrees into unfilled template sites, satisfy

```
2e(O)+B' <= 12|O|-2a_out,       B' <= b|O|.
```

Thus the gained contacts are at most `g|O|-a_out`. Write
`w=|S intersect U|`, `v=|A intersect S0|`, and `t=|A\U|`. Then

```
t=d+w,       s0=s-v,       a_out=t-v,       w<=s.
```

For rho=9 and b=4, without any minimum-degree refinement, substituting these
identities into the original deletion bound gives

```
e(C)-e(S union A) >= t+c(D_U)-8s+7v >= t+c(D_U)-8s.
```

Consequently `t<=epsilon+8s`. In particular a completely fixed scaffold with
b=4 loses at least `d+c(D_U)` when d item H leave the bins; the generic forest
lemma counted only `c(D_U)`. The two P neighbours supply the additional margin.

For the octahedral straight-bin construction, keep also the `2s0` deletion
term from the preceding refinement. The loss is at least

```
d/2+c(D_U)-(11/2)s0+a_out
 = (3/2)t+c(D_U)-(11/2)s-w/2+(9/2)v
 >= (3/2)t+c(D_U)-6s.
```

Therefore the strongest bound obtained here is

```
|A \ U| <= floor((2epsilon+12s)/3).                  (6)
```

For s=0 the loss is at least `3d/2+c(D_U)`. The argument accounts for the
occupied P vertices through the degree-ten constraint; it never counts edges
to vacant holes as if they were H contacts. Without terminal P padding, up to
two endpoint H can have only one backbone P neighbour and these constants
cannot be used unchanged. `routing.py` checks the padded item-chain witnesses.
The finite perturbation checker also verifies the stronger inequalities whenever
the tested outside item sites have H degree at most ten.

## 6. Parameters, completeness routing, and the exact remaining obligation

For a *prospective* scaffold construction with known polynomial error bounds
epsilon and s, take

```
D = floor((2epsilon+12s)/3),
r = 2(D+1),                 Cbin = rB,
G = 2D+4,
R = 2(Cbin+Gq+10).
```

Use the octahedron `|x+R|+|y+R|+|z+R| <= 3R` in FCC and the face bins of Section 4.
Every hole has nine neighbours inside it; outside vertices have at most three.
The holes form q separated paths. The radius gives ample margin from face edges.
All these parameters are polynomial if the error bounds are polynomial in the
unary source length. The bounds must be justified at the chosen scale: a bound
growing faster than r cannot be inserted into this prescription circularly.

The designated item word is explicit:

```
J = W_(r*a_1) P^M W_(r*a_2) ... P^M W_(r*a_(3q)),
W_t = H(PH)^(t-1),
M = 20(q+1)(Cbin+G+1)+12q.
```

Given a partition, put each triple consecutively along its bin and use even r
so every item starts at an even r0-coordinate and ends at an odd one. The
notebook Section 6 routing extends to any row spacing G>=4: launch through
`(r0,Gj+1,1),(r0,Gj+2,1),(r0,Gj+2,2)`, fan out to doubled r0, shear bin j by
`2*Cbin*j`, then route each connector at a distinct deeper k plane via a remote
s row. All final columns are distinct. Increasing that remote row by one adds
two edges, so the above common even M pads every route to exactly M P residues.

`routing.py` implements the full construction and checks the literal single
item-chain word, global injectivity, every FCC step and exclusion from the
octahedron for every P. Three interleaved-order examples with 12,534, 21,606 and
45,899 residues pass. All P routing is outside the top face, so it contributes
no additional H residues or H-H contacts. This is a completeness construction
for the item chain next to a *given* region, not a construction of the scaffold.

A full ordinary reduction would have the shape

```
S_input = G_scaffold P^(connector length) J P,
K = e(C)-c_HH(S_input)-epsilon.
```

This is a **conditional interface, not a completed candidate reduction**:
`G_scaffold` and its prefix-to-item connection have not been constructed here.
The missing theorem must supply all of the following together:

1. An explicit polynomial-size binary word `G_scaffold` with exactly `|C\U|`
   H residues and a computable integer threshold for the entire chain.
2. A partition-dependent self-avoiding fold placing its H at `C\U`, routing all
   of its P and the connection to J without collisions, and attaining K.
3. For **every** threshold-reaching fold of the entire ordinary chain, a
   recognizable translated/isometric template with scaffold exchange error
   at most s, where `floor((2epsilon+12s)/3)<r` and the bins satisfy the separation margin.
   All compensating contacts with items and connectors must be included.

Under these hypotheses, (6) and the separation-and-rounding lemma finish
soundness and recover the original triples. This narrows the forcing obligation
and removes exact confinement and unique-fold requirements. It does not provide
the hypothesis. Pure programmed-module words also cannot fill a macroscopic
solid H bulk by themselves: each of their H residues has a backbone P neighbour,
whereas an H at a degree-twelve interior site of a filled region has none.
A bulk-support construction would require additional sequence structure.

The existing contact-defect stability theorems do not currently imply the
required labelled-scaffold approximation. They constrain local stars and
bilayer components, not a particular footprint with labelled holes. The
notebook's zero-energy backbone switches show why occupied-set information
alone does not control labelled blocks. At the homogeneous PHP ribbon score,
the deficit from `(9/2)h` is already linear in h, so its stated exceptional-site
bound gives no small error budget. On programmed words containing HH, the
isolated-H stability theorem cannot be invoked at all without an additional
argument. The valid general defect identity was used explicitly above instead.

Nor can the scaling prescription be closed merely by citing a vanishing
*fraction* of bad scaffold sites. It needs the absolute certified error bound
to be smaller than the item scale r. Enlarging a container increases its
boundary and can increase that bound; widening the bin separation also enlarges
the container. These dependencies must be solved together, rather than treating
s as fixed while scaling the geometry that produced s.

## 7. Audit against the four reduction requirements

| Investigated object | Explicit size and threshold | Completeness | Soundness | P routing and competitors |
|---|---|---|---|---|
| Original programmed selector `W_sigma` | length 18L, threshold `25L-15` | notebook ribbon folds are valid | proposed global selector/optimality statement is false | four new tiles handle all programs, every P and every contact |
| Constant-word cap repair | length 18L, scores `25L-14` or `25L-13` | explicit cap and tail tables | no global bound; universal competitor beats any fixed end correction for long words | cap locality and both interfaces verified |
| Improved `(V U0)^m` phase | length 36m, threshold `51m-15` | explicit ribbon folds attain the sharp one-marker-family bound | no unrestricted bound; even planar registration of individual modules fails at threshold | nonplanar-module witness and common-core threading verified |
| New universal competitor | length 36m, score `51m-15` | fully proved for arbitrary programs | a lower-bound construction, not a bin gadget or an optimum theorem | complete arbitrary tile mixing proved |
| Robust scaffold-plus-items interface | item word and numerical parameters explicit; scaffold word absent | item routing proved; scaffold threading and its join missing | partition extraction proved conditional on a global labelled-scaffold error bound | whole-set energy bound accounts for unintended contacts; the error bound itself remains unproved |

No fixed scaffold, finite-box optimizer, periodic quotient, or chosen-family
optimum is identified with ordinary FCC hardness. Periodic quotients were used
only to discover explicit infinite/finite ordinary-chain constructions. The
finite fold certificates themselves require no periodic boundary condition.

## 8. Reproduction

Python checks use only the standard library. From this directory run:

```
python verify.py
python cap_theorem.py
python verify_periodic.py
python universal_competitor.py
python robust_checks.py
python routing.py
python enumerate_layers.py
python marker_family_bound.py
python verify_markers.py
```

Alternatively `python check_all.py` runs all these checks and saves
`check_results.json` and `certificate_hashes.json`. It does not run a search.

The JSON verification files record the results. Heuristic searches are optional
and use Node.js; their wall-time limits make exact search trajectories dependent
on the host. Rechecking saved coordinates and the arbitrary-length tile proof
does not depend on rerunning a heuristic. The direct `python` command on this
host is an unavailable Windows alias; the checks were run with the Python
executable supplied by the Codex dependency runtime.

Final check run: all nine scripts in `check_all.py` passed. This includes 1,364
original program/fold formula checks, 340 new even programs, 680 odd programs,
the finite common-port proof, 1,000 perturbation checks (all also satisfying the
tested degree-ten hypothesis), three complete routing examples, the seven-site
shape enumeration, the one-marker transition bound, and all 124 broader marker
certificates. These are reproducible certificate checks and mathematical proofs
at the stated scope, not a machine-checked complexity reduction.

Source background read: notebook Sections 42-47 and the earlier defect,
forest-hole, surface-path and routing sections; `background/README.md`;
`research/reduction_routes.md`; and the existing cubic statement conventions.
