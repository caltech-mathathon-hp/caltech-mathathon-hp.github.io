# Further attempt: thin containers and an explicit failed reduction

No Lean files were changed. Ordinary unpinned FCC HP hardness is still not
proved. This continuation tried to turn the improved confinement estimate into
a smaller container, then tested the simplest possible scaffold prefix. The
thin template works as a counting lemma; the all-H prefix fails, with a complete
ordinary-chain false positive for a well-formed no-instance of 3-Partition.

## 1. A two-layer container with exterior degree three

Use the established auxiliary coordinates

```
(r,s,k) -> (r+k,-r+s,-s+k).
```

For integers n,m>=2, define

```
C(n,m) = {(r,s,k): 0<=r<n, 0<=s<m, k in {-1,0}}.
```

This container has **2nm H sites**, not a cubic number. All six bounding
planes are (111)-type planes in physical coordinates. In particular:

* the normals for constant r,s,k are respectively `(1,-1,-1)`, `(1,1,-1)`,
  and `(1,1,1)`;
* an FCC step increases each specified auxiliary coordinate in exactly three
  ways and decreases it in exactly three ways;
* any exterior site violates one of the six box inequalities, and only those
  three steps towards the violated bound can enter the box.

Consequently every exterior site has at most **three** neighbours in C(n,m).
The notebook's coordinate-bounded two-layer slab had bound four; using this
different, entirely (111)-bounded box retains the octahedron's stronger bound.
This is an elementary geometric observation, not an extremality claim for C.

Every top-layer site with a one-site margin from the four lateral boundaries
has nine neighbours in C: six in its layer and three below. The raw H-H count is

```
e(C) = 2(3nm-2n-2m+1) + (3nm-n-m)
     = 9nm-5n-5m+2.                                  (T1)
```

The first term counts the two triangular rhombi; the last counts their three
types of cross-layer edges. All contacts are included.

For scaled bin capacity rB and separation G>=4, one may choose

```
n=rB+4,  m=(q-1)G+5,
U_j={(a,2+jG,0): 2<=a<=rB+1}.
```

These are q disjoint induced paths, each with rB vertices and degree nine into
C. Distinct bins have FCC distance at least G. The scaffold size is now
`O(rB*q*G)`. It remains an analysis template: no word forcing it is asserted.

## 2. Robust confinement for this thinner template

Retain the notation and hypotheses from REPORT.md Section 5: S0=C\U,
designated scaffold H set S, item H set A, `|S|=|S0|`, `|A|=|U|`,
scaffold exchange error s, and ordinary threshold `e(C)-c_HH-epsilon`.
Every item H must have two chain-P neighbours, as ensured by the final P
padding and the prefix/interitem P connectors.

The thin box has minimum degree at least three: at every point at least one
step in each of the three independent auxiliary coordinate directions remains
inside it. A point adjacent to one of the interior bins has degree at least
nine in C and is adjacent to at most two bin sites. It cannot touch two bins
because their distance exceeds two. After deleting any subset D_U of U,
minimum degree therefore remains at least three.

Deleting an additional s0 missing scaffold sites loses at least `(3/2)s0`
edges. The sequence-aware gained-contact bound from the preceding report is
`(15/2)|O|-a_out`: each outside item H has H degree at most ten, while scaffold
H is only bounded by twelve. Thus, with d=|D_U| and c=c(D_U),

```
loss >= d/2 + c - 6s0 + a_out.
```

Put t=|A\U|, w=|S intersect U| and v=|A intersect S0|. As before,
`d=t-w`, `s0=s-v`, `a_out=t-v`, and `w<=s`. Substitution gives

```
loss >= (3/2)t + c - 6s - w/2 + 5v
     >= (3/2)t + c - (13/2)s.
```

Therefore

```
|A\U| <= floor((2epsilon+13s)/3).                    (T2)
```

The error coefficient is slightly worse than the octahedron's 12s, but the
template uses only two H layers. For s=0, the same strong fixed-scaffold loss
`3d/2+c(D_U)` holds. The separation-and-rounding decoder from REPORT.md applies
unchanged if r exceeds this displacement bound and G>2(D+1).

This still does not establish a reduction: neither proximity of S to S0 nor
its realization by a binary prefix has been forced.

## 3. An explicit polynomial candidate and its false positive

To test whether an all-H prefix could suffice once a compact core is forced,
consider the following complete proposed map from a unary 3-Partition instance:

```
a_1,...,a_(3q),  sum a_i=qB,  B/4<a_i<B/2,
A_total=2qB,
n=A_total+4,  m=10q+4,
p=2nm-A_total,
M=40(n+11)+4(3q+1),
W_a=H(PH)^(a-1),

S = H^p P^(M+1) W_(2a_1) P^M W_(2a_2) ... P^M W_(2a_(3q)) P,
tau = e(C(n,m))-(p-1)
    = 7nm-5n-5m+A_total+3.                           (T3)
```

This input contains only one freely folding binary sequence and a threshold.
Its length is O(q^2 B), polynomial in the unary source size. There is no scaffold
or region in the target input. The intended interpretation is that H^p supplies
the scaffold and the alternating blocks fill q bins, for example the q interior
top-face paths of length 2B at rows `2+10j`.

**The proposed map is false: every well-formed source instance is sent to a
yes-instance.** It therefore cannot establish hardness. The following is a
closed-form complete fold, including all P routing, independent of a partition.

### 3.1 Replacing the bins by one track

Place all item H, in their input order, at

```
U_alt={(a,0,0): 0<=a<A_total}.
```

Cut this one track into lengths 2a_i. Between consecutive H of each item put
P at `(a,0,1)`, the standard outward HPH bridge. Every item starts at an even
track coordinate and ends at an odd one. There is no requirement to split the
items into triples.

### 3.2 An actual all-H scaffold path

The H^p prefix has a Hamiltonian path through `C\U_alt`:

1. Traverse all bottom-layer rows s=0,...,m-1 as a serpentine path, starting at
   `(0,0,-1)`. Since n and m are even, it ends at `(0,m-1,-1)`.
2. Step to `(0,m-1,0)`.
3. Traverse top rows s=m-1 down to 1, starting each successive row at the side
   where the preceding row ended. The final point is `(n-1,1,0)`.
4. Step to `(n-1,0,0)` and traverse the four remaining top-row sites down to
   `(A_total,0,0)`.

These are FCC steps along the auxiliary basis vectors. They visit every required
site exactly once. The prefix endpoint at track coordinate A_total is distinct
from all item endpoints and has an available outward launch.

### 3.3 All connectors, with their exact lengths

Apply the previously verified fanout routing with all terminals on row zero,
width parameter n, and one routing row. Launch a terminal at coordinate a
through `(a,1,1),(a,2,1),(a,2,2)`, fan out to coordinate 2a at height n+1,
and give each connector its own deeper plane and remote row. Terminal columns
are distinct. These paths lie entirely at k>0, outside the H container.

The prefix endpoint A_total and first item start 0 both have even coordinates;
use an H-to-H path of M+2 edges, hence M+1 interior P. Each subsequent item end
is odd and the next start even; use M+1 edges, hence M interior P. Increasing
the remote row adds two edges, so the displayed common M supplies exact padding.
The final P at `(A_total-1,0,1)` is unused by any short bridge or long connector.

The code in `thin_container.py` constructs every residue of this walk and
checks all backbone steps, lattice membership, global injectivity, literal
word agreement and the complete ordinary score. This is a positive coordinate
certificate, not a search claim.

### 3.4 Exact score and a no-instance

The total H-occupied set is exactly C(n,m), even though every item is on the
single substitute track. It has the contact count (T1). The only consecutive
HH pairs are the p-1 pairs in the prefix. Hence the fold scores exactly tau.
All unintended H contacts have been included in this calculation.

For the well-formed no-instance

```
q=2, B=15, a=(4,4,4,6,6,6),
```

no triple sums to 15: every item is even. The source size window is satisfied.
The resulting ordinary target nevertheless has a fully verified fold with

```
n=64, m=24, M=3028,
3072 H residues, including a 3012-H prefix,
raw H contacts = 13386,
ordinary score = tau = 10375.
```

The full word and physical-coordinate certificate are saved in
`thin_false_positive.json`. The checker also confirms that the intended bins
all have degree nine, that the exterior degree bound is three, and that the
actual item H track is disjoint from every intended bin.

**Scope.** This disproves the explicit all-H-prefix map (T3). It does not prove
that all possible thin-container words fail. In particular, it does not rule
out a carefully patterned prefix that encodes wall/anchor structure. What it
does establish is that even *perfect knowledge of the total H container* is
insufficient for this candidate: its failure already occurs while that occupied
set is exactly the intended C. A theorem forcing only total H occupation would
leave this false positive intact.

## 4. What must replace the failed prefix

The next necessary result concerns labelled geometry or an equivalent topological
certificate: the prefix must prevent the items from replacing q bins by one
long track (or another capacity-changing arrangement) at the threshold. It need
not force one coordinate conformation. A successful proof could still use the
thin template and (T2), but must force its hypotheses for every fold and must
construct the patterned prefix and its P routing.

There is also a quantitative limitation on using the current robust decoder
with only a coarse boundary-size error estimate. For q>=2 and D>0, choosing
G>2(D+1) in the thin template gives

```
|C| = 2(rB+4)((q-1)G+5) > 4rB(q-1)D.
```

If the only certified budget used is `D=ceil(c sqrt(|C|))` for a fixed c>0,
then `D>=4c^2 rB(q-1)`. For sufficiently large source instances this conflicts
with r>D. This is a limitation of that conservative parameter choice, not a
lower bound on the actual error in an optimum fold. It means a future proof
must improve or localize the error control, enforce bin separation differently,
or establish exact constraints. A small error *fraction* alone does not close
the amplification argument.

The previous notebook's frozen-matching theorem would provide useful straight
tracks if its moment and boundary conditions could be forced. The defect and
core-enumeration results read during this continuation do not provide those
conditions. No exact finite FCC core-uniqueness theorem or unrestricted bilayer
classification was assumed.

## Reproduction

Run `python thin_container.py` in this directory. It uses only the standard
library and the existing local verification/routing helpers. The full no-instance
certificate is checked from coordinates; no optimizer is required. The earlier
report, checkers and certificates are preserved.

`python check_thin_perturbations.py` additionally checks all 256 hole-deletion
subsets of an eight-hole thin template, then 1,000 seeded perturbed/relabelled
configurations under the exterior item-degree condition. This supplements the
counting proof of (T2), not its global forcing hypothesis.
