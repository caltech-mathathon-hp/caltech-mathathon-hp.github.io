# Model and assumptions

These choices are part of the formal statement, not proof shortcuts.

* The graph is the fixed infinite cubic lattice `Fin 3 → ℤ`, with Manhattan
  distance-one adjacency. It is not an input graph, finite box, or pinned model.
* A fold is an injective placement of **all H and P residues** with adjacent
  consecutive positions. All H–H lattice bonds count, including backbone bonds;
  each unordered pair is counted once. Energy is the negative bond count.
* HP instances contain an explicit H/P sequence and an integer lower bound on
  bonds. The sequence uses one symbol per residue. The threshold uses a sign
  and binary magnitude. Tagged pair alphabets and a separator are unambiguous.
  The length is `|S| + 2 + bitlength(|m|)`, without padding.
* Perfect instances use raw pairs `(Sequence × ℕ)`, with binary side length n.
  A wrong H count is a no-instance. Acceptance requires exactly n³ hydrophobic
  residues occupying exactly a translate of the n × n × n cube. P residues
  cannot occupy those sites. A valid nonempty input already has at least n³
  sequence symbols; binary n remains compact even on malformed inputs.
* Empty and singleton sequences, negative HP thresholds and n = 0 are allowed.
  Natural subtraction makes `cubeBondThreshold 0 = 0`. Coordinates and indexing
  use integers and zero-based `Fin`, respectively.
* Encodings are mathlib `Computability.FinEncoding`, with proved decode/encode
  laws. Polynomial time means an actual mathlib `Turing.TM2ComputableInPolyTime`
  witness, wrapped in `Nonempty` for proposition-valued predicates.
* `InNP` is the polynomially bounded verifier definition measured in encoded
  word lengths. Certificates have a finite alphabet and a **surjective** encoder
  onto all words, preventing an arbitrary encoding image from hiding a
  certificate-validity problem. Polynomial bounds have natural coefficients.
* Karp reductions are total functions preserving both yes- and no-instances.
  NP-hardness quantifies over every `Type` (universe zero), every finite encoding,
  and every predicate in the project's NP class. This matches the universe
  restriction of the pinned TM2 API. On strings outside the image of a typed
  input encoding, machine behavior is unspecified; no equivalence theorem for
  arbitrary exotic encodings and textbook string languages is claimed.
* Cook–Levin is explicitly the universal NP-hardness of CNF-SAT under the same
  complexity definitions. CNF variable identifiers are binary. It is a theorem
  parameter in this distribution, never an additional global axiom.
* Source numerical packing fields are unary and polynomially bounded in the
  CNF input length. The reduction does not silently replace binary source
  sizes by unary or assume a merely weak numerical NP-hardness theorem.

The alternative proof method is explained in [proof-route.md](proof-route.md).
The six frozen model/encoding/complexity files are identified in the source
manifest and must retain their meanings. Passing Lean's kernel checks verifies
the formal propositions; their fidelity to the paper also requires inspecting
these modelling choices.
