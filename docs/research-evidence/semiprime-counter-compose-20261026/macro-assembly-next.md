# Next actual macro-compiler assembly proof

Read-only follow-up on current Lean modules and frozen `/tmp/semiprime-counter-20261026/factor_network.py`, chiefly `Builder.add`, `Vertex.entry`, `make_input`, `transform`, carry construction, and subdivision. No source changes.

## Verdict

**Yes, the remaining arithmetic/count assembly appears obtainable by composition of the now-proved identities, without a new mathematical ingredient.** It is nevertheless a real uncompleted finite-graph proof, not justified by the signal count alone. The next implementation should construct a typed word/bit port graph, prove its producer/consumer endpoint bijection, and prove its accepted-assignment equivalence to the stage relations. It must not equate the existing larger inverse-relation contraction directly with the actual small-port graph.

## 1. Exact source vertex table

Write n=nfft, W=n+1, b=n/4, d=ceil(L/b), n=r*t. All full word ports have **W bits**, including carries; flags have one bit. Signal values are decoded little endian.

| Source vertex | Number | Ordered input/output words or bits | Actual local gate |
|---|---:|---|---|
| digit(side,i), i<d | 2d | no inputs; word W then flag 1 | word<2^min(b,L-i*b); lowest-digit flag is word>=2, others word!=0 |
| input-zero(side,i), d<=i<n | 2(n-d) | no inputs; word W | word=0 |
| OR(side,s), 0<=s<d-1 | 2(d-1) | previous flag, digit flag s+1; output flag | out=previous OR new |
| input-one-check(side) | 2 | final OR/sole digit flag | input=1 |
| first DFT(transform,j1) | 3r | t words in j2 order; t words in k2 order | all words canonical; root w^r; no normalization |
| twiddle(transform,j1,k2) | 3n | one word; one word | output=input*w^(j1*k2) modulo 2^n+1 |
| second DFT(transform,k2) | 3t | r words in j1 order; r words in k1 order | root w^t; normalization 1 forward, n^-1 inverse |
| point-product(k) | n | left, right; output | canonical output=left*right modulo modulus |
| initial carry constant | 1 | no inputs; word W | word=0 |
| carry(k) | n | coefficient, carry k; carry k+1 | coefficient<modulus; both carries<2^n; INTEGER coefficient+carry=targetdigit+2^b*next |
| terminal carry zero-check | 1 | carry n | word=0 |
| equality host after subdivision | Epre | two bits | equality |

The inverse transform uses w=4^-1. `inverseRoot=4^(n-1)` is proved to be that same inverse, and `length_normalizer_exists` licenses n^-1 in the literal ring. The inverse normalization is folded into **each output of the second DFT**, not a separate scale stage; adding such a stage would change the exact edge count.

**Bundle outputs.** A first DFT is one vertex checking all t output equations, and a second DFT one vertex checking all r equations. `MacroValid` is a conjunction of those equations, so regrouping is legitimate. Treating every output equation as a separate tensor vertex would repeat all input ports and lose the intended occurrence/size bound.

## 2. A concrete port type and endpoint construction

Use typed vertex constructors exactly as above. Let `arity(v)` be its literal number of Boolean ports; define `HostPort := Sigma v, Fin(arity(v))`.

Use `SignalBit n d` from MacroBitNetwork as the generated signal-bit type, or a refinement retaining coordinate pairs rather than immediately flattening them. A word bit is `(wordSignal,ell)` with ell:Fin W. A flag bit is its tagged flag signal. Define separately:

- `producer : SignalBit -> HostPort`, the actual output position;
- `consumer : SignalBit -> HostPort`, the unique later input position;
- `endpoints : SignalBit x Bool -> HostPort`, choosing producer/consumer.

The key new theorem is **`endpoints` bijective**. This simultaneously proves every port belongs to one signal endpoint, every signal has exactly two distinct hosts, and the total number of ports is twice the signal count. It cannot be replaced by `signal_bit_count`.

After subdivision take `Edge := SignalBit x Bool`; each edge connects its selected original host to the corresponding input of the equality vertex indexed by that signal. Original vertices have side 0, equality vertices side 1. Give explicit source ordering only when matching Python numeric edge IDs; mathematical graph correctness is invariant under a proved edge-ID renaming.

### Producer/consumer table

- Input word(side,i): producer digit/zero vertex; consumer first forward DFT(side,j1=i mod r), input j2=i/r. The decomposition i=j1+r*j2 and finite bounds are the required bijection.
- First output(transform,j1,k2): producer first DFT, output word k2; consumer its twiddle input.
- Twiddle output(transform,j1,k2): producer scale output; consumer second DFT(transform,k2), input word j1.
- Forward second output(side,k2,k1): producer second DFT(side,k2), output word k1; consumer point-product at flat k=k2+t*k1, left/right input selected by side.
- Point-product(k): producer product output; consumer inverse first DFT(j1=k mod r), input j2=k/r.
- Inverse second output(k2,k1): producer inverse second DFT(k2), output word k1; consumer carry(k2+t*k1), coefficient input.
- Carry k: producer initial constant when k=0, else carry(k-1) output; consumer carry(k), previous-carry input when k<n, else terminal zero-check.
- Digit flag(side,0): if d=1 consumer is one-check, else OR(side,0)'s first input.
- Digit flag(side,i), i>=1: consumer OR(side,i-1)'s second input.
- OR output(side,s): consumer OR(side,s+1)'s first input if s+1<d-1, else one-check.

For a DFT with q input/output words: input-word j bit ell has port j*W+ell, output-word k bit ell has port (q+k)*W+ell. Scale has input ell/output W+ell; product and carry have two inputs at 0,W and output 2W; digit flag is port W; OR inputs are 0,1 and output 2; one/zero checks use 0. These are the exact ordered positions in `Builder.add`.

### Source-ID ordering caution

The first/twiddle signal creation order is outer j1, inner k2, hence numeric word order k2+t*j1. Second-stage creation order is outer k2, inner k1, hence k1+r*k2. Its **result array** is nevertheless indexed k2+t*k1. Do not identify creation order with final flat-frequency order. `flatOutput` already proves the latter arithmetic mapping. The typed coordinate graph avoids this trap; a source-order enumeration can then be proved separately.

## 3. Concrete representation mismatches to discharge

1. **Carry width.** BooleanNetwork stores `BitVec n` carries; Python physically allocates `BitVec(n+1)` for every carry, then each carry vertex forces the value below 2^n. Prove zero-extension from n to n+1 bits is a bijection onto that subset, including the initial/terminal constants. The high carry bit is forced false, so this adds no accepted multiplicity. Use actual quarter capacity already proved. Signal counts correctly use W bits, not n.
2. **Input digit width and padding.** BooleanNetwork uses d arrays of b-bit digits. Python stores n words of W bits; i>=d are zero constants, and the last source digit may have `min(b,L-i*b)<b` active bits. Prove zero-padding/zero-extension equivalence. For valid nontrivial products N<2^L, every factor is <2^L, so the top-digit cap discards no valid factor pair; this implication needs its explicit integer proof, not an assertion that every b-digit input already satisfies the cap.
3. **Canonical ring words.** MacroArrays uses a canonical-word subtype. Python uses unrestricted W-bit words but rejects noncanonical values at its DFT/scale/product vertices. Prove the corresponding accepted-subtype equivalence. Input digit/zero predicates already imply canonicality because b<=n and the modulus is 2^n+1. Inverse coefficient canonicality is checked both by the inverse DFT and carry predicate; the duplicate check changes no assignments.
4. **Flags.** BooleanNetwork's two direct operand flags are replaced by actual digit flags and d-1 OR outputs. `actual_input_flag`, `or_valid_iff`, `or_unique_extension`, and exact output lengths now supply the needed semantics/unique bits. Assemble them into the finite graph; do not add extra physical flag bits for the mathematical OR prefix's fixed starting value.
5. **Normalizer and inverse root.** Both are public gate parameters, not signal words. Root and normalizer uniqueness in the ring relate the Python `pow(...,-1,modulus)` values to the proved powers/unit inverse; no primality or unknown-order hypothesis is needed.
6. **No accidental repeated scope variables.** Prove each vertex's ordered ports are distinct: DFT input slots are a div/mod bijection, outputs belong to new tagged families; left/right product inputs are different signal tags even if equal in value; coefficient/carry slots are distinct; adjacent OR inputs are distinct signals. Equality vertices use two distinct new edge tags. This is needed by the actual layout/counter API.

## 4. Count composition theorem to implement

For fixed finite input bits, prove accepted graph assignments correspond bijectively to:

1. padded canonical input arrays and their deterministic digit/OR flags;
2. unique left and right forward `MacroArrays`;
3. unique canonical point-products;
4. unique inverse `MacroArrays`, with final words the arithmetic convolution coefficients;
5. unique bounded carry words satisfying the actual integer carry equations.

Use `macro_extension_count` twice forward and once inverse, or build the direct finite witness equivalence using `macro_valid_unique`; use `residueValue_injective` for products; use `flatOutput_inverse` and arithmetic-network soundness/converse for carries. The prior arithmetic converse gives actual bounded carries, and strict quarter capacity handles their n-bit value range. OR-chain uniqueness eliminates flag multiplicity.

Only after the complete endpoint/equation correspondence should one invoke the already proved Boolean factor-pair count and equality-subdivision preservation. This yields the exact original/subdivided graph count without an assumed graph-semantic equivalence. Prefix restriction maps to the producer-host edge of each original active P bit, exactly as Python chooses edge 2e; this preserves scopes and does not insert new vertices.

## 5. Counts and eventual scaling after assembly

The now-proved generated signal cardinality is

`Epre=(13*n+1)*(n+1)+4*d-2`, `Eafter=2*Epre`.

Once endpoints is bijective, total_ports=2*Eafter and every edge has occurrence exactly two. Until then these are a signal-family count and a proposed actual graph-edge count, respectively.

The original vertex count is also directly derivable from the table: input/flag/check vertices `2n+2(d-1)+2=2n+2d`; transform vertices `3(r+n+t)`; products n; carries/initial/terminal n+2. Thus `Vpre=7n+3(r+t)+2d+2`; subdivision adds Epre equality vertices. This is a proposed next finite cardinality theorem, not currently claimed compiled.

Maximum non-equality degree is bounded by max of `2tW`, `2rW`, `3W`, `W+1`,3, and W; the proved arity bound is a safe envelope. Public `r<=t<=2r`, `rt=n`, and minimal dyadic n with n^2>=16L give n^2<64L and the desired O(L) wire/O(L^(3/4)) scope bounds. These are ordinary finite/integer estimates but are not yet an actual graph cost theorem.

No new analytic transform, factoring algorithm, order supplier, or tensor identity appears necessary. The remaining work is a concrete dependent-index compiler and its count/resource composition; it must still be executed and kernel checked.
