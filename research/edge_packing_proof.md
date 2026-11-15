# A single chain proof by packing one cube edge

This construction reduces unary 3-Partition to ordinary cubic HP folding by putting all items on one geometric edge of a forced cube. Two crossings of a square face anchor a sequence of separators; short exterior connections and a length count force equal gaps between them. The rest of that square is one rectangular snake. The construction and the arguments below give both directions for every source instance. The coordinate checker supplies additional finite certificates, not a substitute for the universal arguments. This is a mathematical proof, not a new Lean formalization.

The cube extremality strategy, the words `(PHP)^t` and `(PHHP)^(t/2)`, and the initial cube frame follow the Berger–Leighton approach and the existing [project proof](cubic_three_partition_proof.md). The one-edge separator construction and its occupied-neighbor distance lemma are the modification developed here. No claim of priority over other literature is made. The original paper is [Berger and Leighton, RECOMB 1998](https://computingbiology.github.io/docs/berger1998.pdf).

## 1 Model and statement

The lattice is the fixed graph on the integer triples, with Manhattan-distance-one adjacency. A fold of an HP word is injective and takes successive letters to adjacent sites. There are no pinned vertices, obstacles, prescribed regions, or additional residue types. The bond score counts all unordered adjacent H pairs, including backbone pairs.

**Theorem.** From an instance of unary 3-Partition one can construct a single HP word S with exactly n cubed H residues such that the following are equivalent:

1. The instance has a 3-partition.
2. The H residues of S can occupy exactly a translated n by n by n cube.
3. S admits a fold of bond score at least `3 n²(n−1)`.

The output word has length `n³ + O(n²)`, and n is linear in the original unary input length. For the convention excluding backbone H–H pairs, the equivalent threshold for this word is `2 n³−4`. Consequently both perfect cubic filling and cubic HP threshold folding are NP-complete, using the standard NP-completeness of unary 3-Partition as the external complexity fact.

## 2 Parameters and the literal word

Start with `3q` positive integers whose sum is `qB`, satisfying `B/4 < a_i < B/2`. Assume `q≥2`; a valid one-bin instance is always a yes-instance. Double every item and B. This preserves exactly the feasible partitions and ensures

\[
B\ge6,\qquad 2\mid B,\qquad a_i\ge2,\qquad 2\mid a_i.
\]

No inequality relating B to q is needed. Set

\[
g=B+6,\qquad d=(q+1)g+qB,\qquad n=d+2,\qquad L=d+1,\qquad K=8n.
\tag{1}
\]

In particular d is even, `d≥18q+12≥48`, and `B+5<g<L`. Work in the cube `C=[0,L]³` when constructing a witness. Define

\[
E_t=(PHP)^t,\qquad F_t=(PHHP)^{t/2}\quad(t>0\text{ even for }F).
\]

Use the blocks

\[
\begin{aligned}
A&=E_{9d+8}F_{d^2}E_d,\\
D&=P H^{d^3+2}P F_{d^2-2},\\
W&=E_1F_d E_g(P^{B+2}E_g)^q F_d E_{d-1},\\
G&=F_{d(d-2)}.
\end{aligned}
\tag{2}
\]

The output, expanded as an ordinary finite word, is

\[
\boxed{
S=A P^K(F_{d^2}P^K)^3D P^K W P^K G
\prod_{i=1}^{3q}(P^K E_{a_i}).
}
\tag{3}
\]

Only the completeness certificate uses a partition. Every parameter, connector length, and letter of S is determined by the instance alone.

The H count, separated by word type, is

| Part | H count |
| --- | ---: |
| A's edge words | `10d+8` |
| W's edge words | `d+(q+1)g` |
| All item words | `qB` |
| All F words, including the two crossings and G | `6d²−2` |
| The bulk H run | `d³+2` |

Because `(q+1)g+qB=d`, the E words contain exactly `12d+8` H's. The total is `(d+2)³=n³`.

## 3 Every perfect filling yields a partition

Fix an arbitrary perfect filling and translate its cube to C. Every P is outside C.

### 3.1 Compress the paths and saturate the skeleton

An H adjacent to P is on the surface. An H flanked by two P's needs two distinct exterior neighbors, and therefore lies on the edge skeleton, including its corners.

In any HPPH substring the two H sites have odd distance at most three. Distance three would make the three-step backbone a Manhattan geodesic, contained in the coordinate box between the H endpoints and therefore inside C. Its two P's cannot be inside C. Thus the H sites are adjacent. Deleting P's compresses each E or F block to a simple H path, and the same compression holds across an adjacent E–F or F–E join.

Exactly the `12d+8` H's of the E words are flanked by P's. The cube skeleton has exactly `12d+8` sites. Those H's therefore fill the whole skeleton; no F or bulk H occupies it. Each F path consequently stays within one face interior.

A simple skeleton path that visits t corners has at most `t+1` intervening segments, each with at most d non-corner edge sites. Its size is at most

\[
t+(t+1)d\le8+9d.
\]

Equality for `E_(9d+8)` forces all eight corners and nine complete edge interiors. Both endpoints are non-corners, so every corner is internal to this path and uses two incident geometric edges. The three unoccupied edges are pairwise nonincident. Their interiors are separate components after the occupied corners are removed. A's final `E_d` fills one complete component. Precisely two edge interiors remain available for W and the items. Call these the rails; each has d sites.

### 3.2 All remaining face blocks share one face

The four `F_(d²)` words fill four distinct face interiors. The `F_(d²−2)` word occupies a fifth face, leaving only two sites there. Each of W's two `F_d` crossings and G has more than two H's. Being connected paths in face interiors, all three must occupy the sixth face, called the working face.

### 3.3 The two crossings anchor the separator train

Each E block not in A is an interval in one rail. W's `E_(d−1)` fills all but one site of one rail. Every separator `E_g` and every item `E_(a_i)` has at least two H's, so cannot occupy its one remaining site. They all occupy the other rail. W's singleton `E_1` must fill that last site, because every skeleton site is occupied by an E-word H.

Both `F_d` crossings join these two different rails. Their endpoints are adjacent, after compression, to rail sites on the boundary of the working face. Thus the two rails bound this face. They are nonincident, so they are opposite sides. Choose face coordinates with the anchor rail at `x=0`, the packing rail at `x=L`, and rail coordinates `1≤y≤d`.

Including its rail endpoints, each crossing has `d+1=L` steps and changes x by L. Every step has x increment at most one; equality in the sum forces every increment to be one. Each crossing is a straight row. In particular its rail endpoints have equal y coordinates.

The long anchor is either the interval `[1,d−1]` or `[2,d]`; the singleton is the missing endpoint d or 1. The end of the long anchor attached to a crossing is one of its two interval endpoints. Consequently the two ends of the separator train have y separation either 1 or `d−1`.

### 3.4 Long separators force a single order

Each separator interval has length g. Successive separators are joined by exactly `B+2` inserted P's. Including the P supplied by each E block, their terminal H sites are connected by `B+5` backbone steps.

Suppose a separator is traversed in increasing y and finishes at b. Its interval is `[b−g+1,b]`. An interval of length g lying to its left has both endpoints at distance at least g from b. An interval to its right, entered at its far endpoint, also requires distance at least g. Both possibilities are excluded because `B+5<g`. The next separator must lie to its right and be traversed in increasing y. Reflection gives the same conclusion for decreasing traversal.

Induction makes all `q+1` separators occur in their backbone order along the rail, with one common orientation. Their endpoint separation is at least `(q+1)g−1>1`. The separation allowed by the crossings is therefore `d−1`, not 1. The train extends from one end of the packing rail to the other, with exactly q intervening gaps.

### 3.5 Occupied exterior neighbors bound every gap

**Gap lemma.** Let two consecutive separators have r edge sites between them. Their `B+5`-step connector forces `r≤B`.

For `r=0` this is immediate. Suppose `r≥1`; the H endpoints have distance `r+1`. Every intervening edge site contains an E-word H. Such an H has exactly two exterior neighbors, and its two flanking P residues occupy both. Neither of those residues belongs to the connector under consideration. Thus injectivity forbids the connector from using either exterior neighbor of any intervening H.

An exterior path between the endpoints needs at least two transverse steps, to leave and return to the edge. If its length were at most `(r+1)+2`, equality would force monotone movement along y and exactly one transverse step out and one back. All intermediate y levels would then be traversed at the same outward unit normal: the path would visit a forbidden exterior neighbor of an intervening H. Therefore this length is impossible. Path length has the parity of its endpoint distance, so the connector requires at least

\[
(r+1)+4=r+5
\]

steps. Its actual length is `B+5`, proving `r≤B`.

The rail has d sites and the separators use `(q+1)g`. Hence the q gaps have total size

\[
d-(q+1)g=qB.
\]

Each has size at most B, so every gap has size exactly B. This deduction is why the connector is `P^(B+2)`: a length count that ignored the already occupied exterior neighbors would give the wrong bound.

### 3.6 Items give the partition

Every item is an interval on the packing rail. It cannot cross an occupied separator, so it lies in one gap. The items contain `qB` H's in total and fill all gaps. Their sizes in each gap sum to B. The source bounds force exactly three items per gap. This recovers a 3-partition from every perfect filling and completes soundness.

## 4 A partition gives the entire single chain

Assume a partition is given. We first specify all blocks, including every nearby P, and then supply all inserted P connections of their literal lengths.

### 4.1 Three elementary placements

**Rectangular and box snakes.** Traverse rows alternately forward and backward. For a box, reverse the whole row snake in alternate layers. Adjacent rows and layers join at adjacent endpoints.

**Face words.** On an even simple H path with outward face normal v, realize each PHHP pair as

\[
h_{2j-1}+v,\ h_{2j-1},\ h_{2j},\ h_{2j}+v.
\]

The intervening P–P joins are adjacent because their H projections are adjacent.

**Straight edge words.** On a straight edge, alternate the two exterior normals for successive H–P–P–H links. Choose each H's incoming and outgoing P normals to be different. An even-length E block can have the same normal for its initial and final P; an odd-length block has different endpoint normals.

For the initial skeleton path, each compressed step has two common exterior normals at its H endpoints. Starting with a prescribed final P normal, label steps backwards, always choosing a common normal different from the next label. At the first H choose an incoming normal different from its outgoing label. This lifts any such simple path to its E word. Each exterior lattice site adjacent to C has a unique neighbor in C, so P's assigned to different H sites cannot collide.

### 4.2 Place the initial frame and the bulk

For A use the skeleton polyline

\[
\begin{aligned}
(d,L,L)&\to(0,L,L)\to(0,L,0)\to(L,L,0)\to(L,L,L)\\
&\to(L,0,L)\to(L,0,0)\to(0,0,0)\to(0,0,L)\to(d,0,L).
\end{aligned}
\]

It consists of two square perimeters joined by an edge and contains `9d+8` sites. Lift it with final P normal pointing out of the back face. Next, snake through the back face with x decreasing from d to 1 and y alternating from 1 to d. Finish by traversing `(0,y,L)`, `y=1,…,d`, as `E_d`, with both endpoint P's pointing back. The two unfilled rails are exactly `x=0,z=0` and `x=L,z=0`.

Fill the left, bottom, and right face interiors by snakes with the following endpoints. Their P normals are the corresponding outward face normals.

| Block | First H | Last H |
| --- | --- | --- |
| A | `(d,L,L)` | `(0,d,L)` |
| Left face | `(0,1,1)` | `(0,d,1)` |
| Bottom face | `(d,0,d)` | `(d,0,1)` |
| Right face | `(L,1,d)` | `(L,d,d)` |
| D | `(d,L,1)` | `(d−1,L,1)` |

For D, begin with P at `(d,L+1,1)` and H at `(d,L,1)`. Snake through the interior in layers `z=1,…,d`, starting at `(d,d,1)` and ending at `(d,d,d)`. In the first layer traverse y and x from d down to 1 as an ordinary alternating row snake; reverse that entire layer path in each successive layer. Because d is even, the final endpoint is as stated. Then visit H at `(d,L,d)` and P at `(d,L+1,d)`.

Complete D with a top-face snake with its first and last sites removed. The untrimmed snake runs from `(d,L,d)` to `(d,L,1)`, with z decreasing and x alternating from d to 1. Its trimmed path runs from `(d−1,L,d)` to `(d−1,L,1)` and realizes `F_(d²−2)`. This places every H and P of D, fills the interior, and leaves no top-face holes.

### 4.3 Place W and the remaining square interior

The packing rail is `(L,y,0)`. Define separator intervals

\[
I_j=[1+j(g+B),\ g+j(g+B)],\qquad 0\le j\le q.
\tag{4}
\]

They leave q gaps of B sites. W starts on the anchor rail with `E_1` at `(0,d,0)`, with initial P normal left and final P normal front. Its first `F_d` crosses row d from x=1 to d. Traverse the separators on the packing rail in decreasing y, starting with `I_q`, and give each E block both terminal P normals front.

For two successive separators whose terminal H rows are b and c, the gap size B gives `b−c=B+1`. Join their supplied endpoint P's by

\[
(L,b,-1)\to(L,b,-2)\to(L,c,-2)\to(L,c,-1).
\tag{5}
\]

This path has `B+3` edges between the supplied P's and exactly `B+2` new intermediate P's, as required. These connections lie over disjoint gap intervals at front depth two.

After the final separator reaches row 1, W's second `F_d` traverses that row from x=d down to 1. Finish with `E_(d−1)` on `(0,y,0)`, `y=1,…,d−1`, with initial P normal front and final P normal left. Thus W's first H is `(0,d,0)` and last H is `(0,d−1,0)`, both with external terminal P normal left.

Place G by a snake in the rectangle `1≤x≤d`, `2≤y≤d−1`, `z=0`, with x initially decreasing. It starts at `(d,2,0)` and ends at `(d,d−1,0)`; its P normal is front. Together G and W's two crossings fill the whole front face interior.

### 4.4 Place the items

Assign the groups to the q gaps in any order. In each gap, place its items successively in increasing y, in any chosen order, and realize item i as `E_(a_i)`. Give both terminal P's the rightward normal `(1,0,0)`. Even item sizes permit this choice.

Every gap begins at an odd y coordinate and each item has even size. Each item therefore starts at odd y and ends at even y. Since L is odd, every item starts at an even H and ends at an odd H. Its two endpoint rows differ, and all item endpoint rows are distinct globally. Every item row is at most `d−g<d−1`.

Item P's lie at front depth one or rightward depth one. W's short connections lie at front depth two and x=L. These placements do not collide. In particular, item connections will escape to the right, avoiding W's connections in front.

At this point all fixed blocks are injectively placed. Their H's occupy C exactly. All their P's lie outside C in the first two exterior layers.

### 4.5 Seven connections around cube corners

All blocks start and end in P. Their first H is even and last H odd, so a `P^K` separator must supply an H-to-H path of exactly `K+3` edges: two intermediate P's are already supplied by the endpoint blocks, leaving K new ones.

Here is one explicit route for ports on two adjacent faces. Use outward signed coordinates u and v for those faces, with common-edge coordinate t. After swapping the two ports if necessary, write their H sites as

\[
p=(0,-s,t_0),\qquad q=(-r,0,t_1),\quad 0\le r,s\le L,\quad t_0>t_1.
\]

For depth h and `T>t_0`, take the axis segments

\[
\begin{aligned}
(0,-s,t_0)&\to(h,-s,t_0)\to(h,h+1,t_0)\to(h,h+1,T)\\
&\to(h+1,h+1,T)\to(h+1,h+1,t_1)\\
&\to(-r,h+1,t_1)\to(-r,0,t_1).
\end{aligned}
\tag{6}
\]

Reverse the route back if the ports were swapped. Its first and last steps use the prescribed face normals. The inequality `t_0>t_1` ensures the returning arm does not cross the outgoing track. The first arm and the returning track are separated in u. The turn is beyond both endpoint t coordinates. Thus the route is simple and all its non-H sites are exterior.

Give connection j depth `h_j=4+2j`, `j=1,…,7`, in the following block order:

\[
A,\ \text{left},\ \text{bottom},\ \text{right},\ D,\ W,\ G,\ \text{item }1.
\]

The faces and common-edge port coordinates are:

| j | Faces | Common-edge coordinates before the optional swap |
| --- | --- | --- |
| 1 | Back and left | `d,1` |
| 2 | Left and bottom | `1,d` |
| 3 | Bottom and right | `1,d` |
| 4 | Right and top | `d,1` |
| 5 | Top and left | `1,0` |
| 6 | Left and front | `d−1,2` |
| 7 | Front and right | `d−1,y_1` |

Here `y_1≤d−g` is item 1's first row. All paired coordinates are distinct.

**Separation of the seven routes.** Their outward stems have distinct H projections. Every stem is clear of fixed blocks except for its own terminal H and supplied P: every other fixed P at depth one has a different H projection; W's depth-two connections have x=L and point front, whereas item stems point right and G's front stems have x=d. The other stems are behind the front face or on the anchor rail.

Arms are bounded by the expanded cube `[-h,L+h]³` with h replaced by `h_j+1`. Every arm of a later connection has a coordinate at outward depth at least `h_j`, greater than the depth of every earlier arm or stem. An earlier arm could meet a later stem only on their shared face. The required clearance is explicit:

| Face | Earlier arm and later port separation |
| --- | --- |
| Left | The first arm has `y=1` and `z≥1`; the next has `z=1`; W's ports have `z=0`. W's first port moves toward the top from `y=d`, avoiding W's final port at `y=d−1`. |
| Bottom | The earlier arm has `z=d`; the later port has `z=1`. |
| Right | Both full-face arms have `z=d`; item ports have `z=0`. The earlier full-face arm moves from `y=1` toward 0, avoiding the later full-face port at `y=d`. |
| Top | The earlier arm moves from `x=d` toward L; the later port has `x=d−1`. |
| Front | The earlier arm has `y=2`; the later port has `y=d−1`. |

The two tracks and their turn form an outer part with both assigned outward coordinates in the band `{h_j,h_j+1}`. Outer parts cannot meet stems, which have only one coordinate outside C. Two outer parts share an assigned axis; their bands are disjoint or their outward signs are opposite. An outer part and an arm with the same assigned axes are separated by depth. With different pairs of axes, one exterior coordinate of the outer part is the arm's common-edge coordinate, which lies in `[0,L]`; they cannot meet. These facts prove mutual disjointness, including turns, for arbitrary independent values of T. All non-stem parts have depth at least six and miss the fixed blocks.

At `T=max(t_0,t_1)+1`, the length of (6) is

\[
\ell_j=4h_j+s+r+|t_0-t_1|+6\le3L+78=3n+75<K+3.
\]

It is odd because the endpoint H parities differ. Increasing T by one adds two steps without changing any separation argument. Set

\[
T=\max(t_0,t_1)+1+(K+3-\ell_j)/2.
\]

Every one of these seven connections then supplies exactly the required `P^K`. The first two and last two vertices of its H-to-H path are already in the neighboring blocks; insert only the intervening K vertices.

### 4.6 Connect the remaining items in input order

There are `k=3q` items. The same argument also works for any exact packing of positive even sizes, where `k≤qB/2<d/4`. For `i=1,…,k−1`, connect item i's final H `(L,u,0)` to item `i+1`'s first H `(L,v,0)` using depth `h_i=20+i` and

\[
\begin{aligned}
(L,u,0)&\to(L+h_i,u,0)\to(L+h_i,u,-R_i)\\
&\to(L+h_i,v,-R_i)\to(L+h_i,v,0)\to(L,v,0).
\end{aligned}
\tag{7}
\]

All endpoint rows are distinct. Hence every outward stem has its own row. An arm stays on one endpoint row and meets no other stem; the segment joining the two rows has `z<0` and meets no stem at `z=0`. Different connections have different planes `x=L+h_i`, so their plane paths do not meet. Each rectangle is simple because `u≠v` and `R_i≥1`.

The seven earlier routes also miss these connections. Earlier routes using the right face and bottom or top have right-face arms at `z=d` and outer parts at `y<0` or `y>L`. The front-right connection to item 1 has rightward depth at most 19 and its front arm has `y=d−1`; every item route plane has rightward depth at least 21, and all item rows are below `d−1`. Its entry stem is on item 1's first row, which no later item connection uses. Other earlier routes have `x≤L`. This covers both the later plane paths and their stems.

At `R_i=1` the length is

\[
2h_i+2+|u-v|\le d+2k+39<\tfrac32d+39<K+3.
\]

The endpoint rows have opposite parity, so set

\[
R_i=(K+3-2h_i-|u-v|)/2.
\]

This is a positive integer and makes (7) have exactly `K+3` edges. As above, insert only its K unsupplied intermediate P's. Every T, R, and coordinate is `O(n)`.

All blocks and all separators now form exactly S in its original item order. Every backbone step is an edge, every residue position is distinct, every P is outside C, and every H site of C is occupied. This proves completeness for every partition.

## 5 The HP threshold forces the cube

For completeness, the needed extremality theorem has a short proof. Let a nonempty finite set V of lattice sites have size N, and let a, b, c be its three coordinate-projection sizes. With projection indicators `f_xy`, `g_xz`, `h_yz`, put `G_x=Σ_z g_xz` and `H_y=Σ_z h_yz`. Cauchy–Schwarz twice gives

\[
\begin{aligned}
N&\le\sum_{x,y,z}f_{xy}g_{xz}h_{yz}
\le\sum_{x,y}f_{xy}\sqrt{G_xH_y}\\
&\le\sqrt{a\sum_{x,y}f_{xy}G_xH_y}
\le\sqrt{a\left(\sum_xG_x\right)\left(\sum_yH_y\right)}
=\sqrt{abc}.
\end{aligned}
\]

If `N²=abc`, equality in the last inequality makes `f_xy=1` for every active x and y. Equality in the first Cauchy–Schwarz step makes each nonzero pair of indicator fibers `g_xz` and `h_yz` identical. They have one common nonempty support Z. Equality in the first bound then gives `V=X×Y×Z` for the active coordinate sets X, Y, Z.

On each nonempty coordinate line, k sites have at most `k−1` internal edges, with equality only for an interval. Summing over the three directions and using arithmetic–geometric mean yields

\[
e(V)\le3N-(a+b+c)\le3N-3(abc)^{1/3}\le3N-3N^{2/3}.
\]

For `N=n³`, equality requires `a=b=c=n²`, a Cartesian product as above, and interval fibers. Hence its factors are intervals of length n, and V is a translated n-cube. Conversely such a cube has exactly `3n²(n−1)` internal edges. Since S has n cubed H's, its bond threshold is attained exactly by perfect fillings.

All F words together have `6d²−2` H's and contribute `3d²−1` backbone H–H pairs. The bulk run contributes `d³+1`. Thus the fixed number of backbone H–H pairs is `d³+3d²`, and

\[
3n^2(n-1)-(d^3+3d^2)=2n^3-4.
\]

This proves the theorem for either scoring convention.

## 6 Size and complexity

Doubling the unary source changes its size by a constant factor. Since its item sum is qB, (1) gives n linear in that unary length. The bulk contributes `d³+2` letters. The other H residues number `O(n²)`, E and F words use a constant number of letters per H, W's short connections use `q(B+2)=O(d)` letters, and the `3q+6` long separators use `O(qn)=O(n²)` letters. Therefore `|S|=n³+O(n²)` and the expanded reduction is polynomial, with a cubic bound in the original unary input length.

Malformed source instances can be rejected directly. Valid instances with `q=1` map to a fixed yes-instance. For bond thresholds use `(H,0)` and `(H,1)` as fixed yes- and no-instances. For perfect filling use `(H,n=1)` and `(H^7PH,n=2)`; the latter has five H's of one backbone parity and three of the other, whereas a 2-cube has four of each lattice parity.

For NP membership, translate the first residue of an N-letter fold to the origin. All coordinates then have absolute value at most N, so a polynomial-size coordinate certificate suffices. Injectivity, backbone adjacency, scores, and cube coverage can all be checked in polynomial time. Together with unary 3-Partition hardness, this completes the NP-completeness argument.

## 7 Verification and comparison

Run the independent, standard-library checker with:

```text
node research/check_edge_packing.mjs
```

The [checker](check_edge_packing.mjs) constructs the entire chain, including the bulk and every inserted P, without importing the earlier construction or verifier. It checks the literal word, every backbone step, global injectivity, every H/P cube label, exact coverage, the all-bonds score, and the non-backbone score. It also checks shortest local connector distances by breadth-first search for gap sizes 0 through 12, and exhausts small separator placements without assuming their geometric order.

The [saved results](edge_packing_verification.json) contain five complete certificates, four of them strict 3-Partition instances. They include nonuniform items, reordered groups, different placements of item 1, and a general even-size packing. Together they check 3,023,224 residue positions; the largest example has 1,825,956 residues and 1,728,000 H's. All checks passed. The universal lemmas in Sections 3 and 4 establish the proof beyond these examples.

Compared with the existing face-bin construction:

| Feature | Rectangular face bins | One-edge bins |
| --- | --- | --- |
| Item word | `F_(d a_i)` | `E_(a_i)` |
| Repeated crossings of the face | `2q` | `2` |
| Bin forcing | Opposite-rail anchors and straight wall rows | Long separators, occupied-neighbor distance, total edge length |
| Remaining working-face filling | Per-item strip snakes | One rectangular snake G |
| Extra source condition | `B>2q` after normalization | Only even sizes and capacity |
| Fixed long connections before the first item | Five | Six |
| Total long connections | `3q+5` | `3q+6` |
| Item ports | Collinear by choosing strip snakes | Collinear automatically because items are intervals |
| Routing in the written constructions | The latest illustrated proof uses one corner lemma for all joins | Seven corner connections, then rectangular item connections |

The packing argument and local item placement are simpler and genuinely one-dimensional. The occupied-neighbor gap lemma replaces the old anchor-counting argument; it is an additional geometric idea rather than a consequence of edge confinement alone. The whole proof still needs cube extremality, skeleton forcing, two end crossings, and exterior routing. The [latest illustrated face-bin proof](../output/cubic_hp_frozen_proof/main.tex) already uses one corner lemma for every long connection, so the present two-family routing is not a simplification over that version. Both constructions use a linear number of long connections, each of length O(n). For the same already-normalized B, the edge construction's d is larger, so this is not a claim of smaller numerical examples. The old proof and its Lean files remain unchanged.
