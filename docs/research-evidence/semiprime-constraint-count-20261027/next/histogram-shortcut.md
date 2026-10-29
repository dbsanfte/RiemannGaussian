# Removing the original quadratic score-term list

This scratch successor does not modify any canonical or sealed source. It gives exact all-reachable-prefix formulas for the original score and a constructive sparse-histogram algorithm. The ring/update/order portion is checked in `HistogramDifference.lean`; the original finite-sum and executed dictionary joins below remain a proof/implementation plan, not a claim that the public runtime already uses this shortcut.

## Original finite object and prefix order

Let V be the n original vertices, E the F original factors, and I the actual dependent incidence set of size M. Put

```
a[v,e] = #{i∈I : owner(i)=v and factor(i)=e}.
d[v] = Σe a[v,e],       d[e] = Σv a[v,e].
L = r^Q,               U = L².
```

The original term enumeration is exactly I×I, together with Q×V×V; it includes loops, ordered pairs and distinct parallel incidences. Thus weighted regrouping by a[v,e] preserves multiplicity. In particular, corrections involving Σa[v,e]² must NOT be replaced by M. For example, parallel incidences at the same vertex/factor each contribute all their ordered self-cell pairs.

The actual indexed variable list is all `.inl v` first, then all `.inr e`. A reached fixed prefix, including every candidate prefix evaluated during the next choice, therefore has one of two forms:

* vertex phase: some vertices fixed, every factor free;
* factor phase: every vertex fixed, some factors fixed.

The reverse storage of the chosen prefix changes neither this set of fixed keys nor their actual assigned values. Resolve labels through the actual fixed/default/override semantics; free keys are not constrained by their current default. No locality restriction or new coverage promise is required. The existing exact incidence pair-average theorem gives the kernel below for every prefix.

## One weighted equality quadratic form

For one namespace let F be its fixed keys, A its free keys, and α the fixed whole-word labels. The exact conditional equality kernel is

```
K(v,w) = 1                         if v=w,
         1/L                       if v≠w and either key is free,
         [α(v)=α(w)]               if both are fixed.
```

For any nonnegative integer weights z_v define

```
P(z)=Σfixed v z_v;     T(z)=Σfree v z_v;
S(z)=Σfree v z_v²;
h_c(z)=Σfixed v:α(v)=c z_v;      H(z)=Σc h_c(z)².
B(z)=L H(z)+2 P(z)T(z)+T(z)²+(L−1)S(z).
```

Then exactly

```
Σv,w z_v z_w K(v,w) = B(z)/L.                 (1)
```

Proof: fixed/fixed contributes H; fixed/free ordered cross pairs contribute 2PT/L; free/free contributes T²/L plus the diagonal correction (1−1/L)S. This partitions every ordered pair, including all loops. Equivalently, K=(J+(L−1)D_free+L C_fixed−f fᵀ)/L. The nonnegative B form is preferable to signed cancellation in an executable counter.

## Vertex-phase full incidence lane

Let vertex labels be the only fixed labels. Write B_V for (1) on vertices, d for their total degrees, and a_e(v)=a[v,e]. Since all factors are free,

```
K_E(e,f)=1/L+(1−1/L)[e=f].
```

The actual padded incidence count, summed over ALL original I×I terms, is therefore

```
I = L² * ( B_V(d) + (L−1) Σe B_V(a_e) ).       (2)
```

This is direct finite distributivity/Fubini applied to Σv,w,e,f a[v,e]a[w,f]K_V(v,w)K_E(e,f), multiplied by L⁴. There is no statistical approximation, omitted diagonal, division by an unknown order, or sum over an unacquired full truth table.

Acquire (2) using:

* global fixed word histogram H_c=Σfixed v:label=c d[v], fixed/free port masses P,T and free degree-square sum Σfree d[v]²;
* per factor, fixed word histogram h[e,c]=Σfixed v:label=c a[v,e], fixed/free masses p[e],t[e], and free multiplicity-square sum Σfree v a[v,e]².

Only nonzero histogram records need storage. Across all per-factor histograms there are at most M records; all original incidence coefficients come from one sparse count/sort of the M actual ports. No n×F dense matrix is needed.

## Factor-phase full incidence lane

All vertices now have fixed words. For each observed vertex label c put

```
z_c(e)=Σv:label(v)=c a[v,e].
```

Let B_E apply (1) on factors using their current fixed labels β. The exact lane is

```
I = L³ Σc B_E(z_c).                            (3)
```

Explicitly the bracket is

```
L Σc,β (Σfixed e:label(e)=β z_c(e))²
 + Σc (2 P_c T_c+T_c²)
 + (L−1) Σc,free e z_c(e)².
```

All its sparse records derive from actual ports grouped first by their vertex label. There are at most M nonzero z_c(e) cells. At the common boundary, when every vertex is fixed but no factor is fixed, (2) and (3) both give

```
L³ [ Σc (Σe z_c(e))² + (L−1) Σc,e z_c(e)² ].
```

So no phase-transition correction or changed source family is introduced.

## Head lane without Qn² terms

Let p be the number of fixed vertices, f=n−p the number still free, and h[q,a] the fixed-vertex coordinate histogram at q. For Q>0 put G=r^(4Q−1), as in the actual proved head shortcut. At every vertex prefix,

```
H = L⁴ [ Σq,a h[q,a]² + Q f ]
    + G Q [ 2pf + f(f−1) ].                    (4)
```

Reason: fixed/fixed coordinate matches give Σh²; free diagonal matches give f per coordinate; the other 2pf+f(f−1) ordered pairs match with probability 1/r. These are all ordered pairs, including loops. Coordinate histograms can be acquired in O(nQ) records rather than Qn² terms. During the whole factor phase f=0 and H=L⁴Σh² is constant, so it need not be recomputed for each factor candidate.

For Q=0 the head sum is empty and H=0. Define the actual G as r^(4Q−1) using natural subtraction if desired; its value at Q=0 is irrelevant because every occurrence is multiplied by Q. There is no spurious coordinate division at Q=0.

## Exact candidate differences: a stronger useful shortcut

These formulas can score every candidate using sparse histogram READS rather than recomputing even the aggregate squares.

Moving one free key with weight z into a fixed label bin of current mass h changes

```
H→H+2hz+z²,  P→P+z,  T→T−z,  S→S−z².
```

Exact ring arithmetic gives

```
B_after(h) = B_before + 2z(Lh−P),
B_after(hc)−B_after(hd)=2zL(hc−hd).              (5)
```

All squares cancel. No assumption about positivity of either score coefficient is needed. The signed differences are taken in ℤ or ℚ; do not silently use truncated Nat subtraction for the algebra.

At a vertex choice v, let c be a candidate word, and use the OLD fixed histograms. The candidate-dependent incidence/head parts are

```
I_after(c) = candidate-independent constant
 + 2L³ [ d[v] H_c + (L−1) Σe a[v,e] h[e,c] ],
H_after(c) = candidate-independent constant
 + 2L⁴ Σq h[q,c(q)].                            (6)
```

At a factor choice e and candidate word β, let z_c=z_c(e) and h[c,β]=Σalready-fixed f:label(f)=β z_c(f). Then

```
I_after(β) = candidate-independent constant
 + 2L⁴ Σc z_c h[c,β],                           (7)
```

and H_after is candidate-independent.

The existing exact original source cancellation gives integer weights

```
A = n² λ² U²  (incidence),       D = 4M² (head).
```

Keep both inside the reduced score. At a vertex the new nonnegative reduced candidate score is

```
R_v(c)=A [d[v] H_c+(L−1)Σe a[v,e] h[e,c]]
       +D L Σq h[q,c(q)].                       (8)
```

For any c,d, the difference of the original integer weighted scores is exactly

```
2L³ [R_v(c)−R_v(d)].                            (9)
```

At a factor use

```
R_e(β)=A Σc z_c(e) h[c,β],
original weighted difference =2L⁴[R_e(β)−R_e(γ)]. (10)
```

Since r>0 gives L>0, these multipliers are positive. Weak order AND equality are preserved. Compose with the already proved original score denominator clearing (r>0,λ>0,U>0) to preserve every original comparison and every deterministic first-candidate tie. The shared offset is absent from all differences. This applies to any exact λ and ties; λ has not been rounded or dropped.

Do not divide R_e by A without a positivity argument. Keeping A inside avoids all n=0/M=0 exceptions. If n=0, a well-typed owner forces M=0; there are no vertex choices and every incidence/head score is zero. If M=0 but n>0, A may be positive while all degree/histogram terms vanish and D=0, so every reduced score is zero and the original first candidate is preserved. F=0 likewise entails M=0. If r=1, L=1, all actual labels coincide and every candidate difference vanishes; if Q=0, the bank has exactly one word and the same conclusion holds. Formulas (1)–(10) cover these cases without fictitious free-colour choices.

## Paid deterministic data structure, no hash oracle

An executable successor should NOT call the current `Metadata.acquire`/`compileAll` and then ignore their quadratic lists. It should acquire only the M original ports, vertex/factor index lists and Q coordinates, and prove the finite-sum regrouping against the old complete term list. Building that list is the very cost being removed.

One concrete implementation uses deterministic ordered dictionaries (or padded-key binary tries), with stored records keyed by `(factorID,wordID)`, `(vertexWordID,factorWordID)`, `(q,colour)`, and single IDs. Every absent record returns literal zero after an actual paid lookup. Sort original ports by `(v,e)` to acquire a[v,e], multiplicities and degree totals. Dictionaries have O(M+nQ) nonzero records; counts and intermediate frequency counters are ≤M or n, and square/sum accumulators are ≤M² or Qn². Thus compact canonical binary counters need O(log(M+n+Q+1)) bits. No exact score or histogram answer is input advice.

A balanced comparison tree gives O(log K) visited records times the actual key comparison/copy length. A binary trie gives O(Bkey) visited Boolean nodes. Initialization, insertion, lookup, default-zero, key acquisition and pointer/index manipulation must all appear in a concrete report. These are algorithms that can be implemented; neither data structure is claimed already proved in the current source. A list-only deterministic alternative is valid but scans O(K) records per lookup, so it removes T construction yet does not justify the near-linear bound. Do not call it a near-linear hash table.

For each candidate vertex word use only its incident factors and Q coordinate bins. Candidate work is O(degDistinct(v)+Q) dictionary lookups, plus bounded coefficient products/additions; chosen-label updates use the same sparse row and Q bins. At a factor use only the distinct vertex-word labels on its incident ports. Sum of those sparse row sizes over all vertices/factors is O(M). Therefore an elementary whole source-search envelope is

```
setup/sorts + O( L*(M+nQ+n+F) * paid-lookup/word-arithmetic factor )
```

rather than constructing/scanning M²+Qn² score descriptors for every candidate. Zero-arity factors can optionally choose the first candidate immediately, but the displayed bound does not assume that optimization.

Important bank-access qualification: do NOT perform the current linear `bank.readRow` from the head for every candidate ID, which would silently add L² visits. During a vertex candidate sweep, zip the already acquired IDs and rows once and traverse that cached ordered pair list. Score from the current physical row and return only its ID. Factor candidate scoring needs no coordinate row. This preserves the exact existing indexed zero-first candidate order (the acquired bank/indexed equivalence already proves it), including ties. Paying a full Q-coordinate copy/read per vertex candidate is covered by nLQ. Bank acquisition and the zip/list construction remain explicit setup reports.

Actual keys can use the existing acquired ID payload width if one only wants a conservative fixed-polynomial resource envelope. For the sharper near-linear bit expression, prove the actual ascending IDs have O(log L) bits or use fixed padded Boolean keys of that length with paid encoding, rather than silently replace the already proved coarse 2L cap. Each numeric score in (8) is ≤A L M² +D L Qn, and (10) is ≤A M². Together with A=n²λ²L⁴, their bit lengths are polynomial in log(n+M+λ+1)+Q log(r+1). The common omitted constants need never be constructed.

## What the scratch Lean file actually proves

`HistogramDifference.lean` strictly checks:

* `after_update`, `after_difference`: (5) on actual squared-bin/mass updates;
* `vertexI_difference`: the finite factor-sum difference in (6);
* `vertexH_difference`: the exact head difference;
* `vertex_weighted_difference`: (9) with both original weights retained;
* `factor_weighted_difference`: (10) with the constant head term retained and cancelled;
* `order_of_difference`, `tie_of_difference`: weak-order/equality preservation for any positive common factor.

All intermediate subtraction is honestly in ℚ. No binomial, random collision, generic graph rank, modular order or numerical experiment is assumed. The remaining formal theorem is the actual original finite-sum regrouping (1)–(4), followed by actual reachable-prefix histogram-state invariants, candidate zip traversal, deterministic dictionary construction/lookup/update, and paid clock/refinement to the existing source producer. The algebra helper does NOT assert those execution/state premises are already closed. No canonical implementation was made in this read-only successor investigation.
