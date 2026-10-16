

## Arbitrary short annihilators: paid extraction and direct balanced setup (2026-10-16)

The new evidence packet is
[semiprime-wide-annihilator-20261016](research-evidence/semiprime-wide-annihilator-20261016/README.md).
It preserves the twenty preceding packets and distinguishes a positive
supplied-certificate recovery bound from the still-open whole-query acquisition.

Let m=Theta(N^(1/6)) and N=P Q be a balanced distinct odd semiprime.
For a unit gamma with ODD local orders r_P,r_Q and indices
(P−1)/r_P,(Q−1)/r_Q<m, ANY supplied nonzero global annihilator K with
polylogarithmically many bits now suffices to factor deterministically in
soft-O(N^(31/192)). No primality, distinctness or index-coprimality condition
on the local orders is needed; no bound on |K|/ord_N(gamma) and no
factorization of K is supplied.

The proof removes only the2-part of K. For every trial unit a,
b=a^(K_odd) has local orders dividing the two small indices and retains
the2-primary parts of a's local orders. An ordinary monic multipoint
baby/giant detector costs soft-sqrt(m) and returns a factor or the EXACT
common local order. A Jacobi-minus base is located with only cheap gcd/Jacobi
work through N^(5/32), followed by ONE detector call. If it does not factor,
the2-adic valuations of P−1,Q−1 differ. A second scan through N^(5/64),
using the detector per base, must factor by a nonresidue at the field with
larger2-valuation. Lau--Wu's unconditional cubefree-character Burgess theorem
pays both cutoffs, including the composite-modulus Jacobi character.
The second cost exponent is5/64+1/12=31/192<1/6. Bounded-scan failure has an
explicit ordinary-factoring fallback and occurs only at finitely many
promised inputs, so no unknown threshold is an algorithm input.

There is also a direct paid SAME-INPUT balanced setup, under the additional
numerical hypotheses N<=m^6 and P+Q<=3m³. Harvey--Hittmeir's
large-GLOBAL-order routine at16m², odd projection, and the universal detector
return a factor or an odd-order gamma with both indices<m. A common-odd-order
branch either separates through2-powers or computes a common full order r
with r²|phi(N), recovering the factor sum by a remainder. Further raising
gamma to N−1 gives coprime local orders by EXISTING compiled arithmetic.
A saturated common-order return is therefore1 and supplies the explicit
annihilator K=N−1 of the original small-index gamma, handled by the new
extractor. Otherwise both projected orders exceed16m², so their global
product exceeds256m⁴. A further q=beta^(m²) detector returns a factor or
certifies all1−q^k units for1<=k<=16m². Total setup bit cost is soft-O(m).
This is a paid composition, not a new coprimality identity or the first
algebraic kernel closure: October3 recursive kernel descent already removed
unresolved kernel leaves, with complete setup/backend bit costs still open.

On the inherited qualified raw-energy family, the preceding representative
relation argument now applies to supplied FULL-INPUT-adaptive explicit
relative origins, positions and assignments, with total origin encoding
soft-O(m) and k²T soft-O(m). Trim only the short-origin proof witness;
energy forces a nonzero polylog-bit relation K. A cover in either hidden
field makes its gcd nontrivial. A proper gcd factors; a global collapse is
handled by the new extractor. Thus the previous numerical span and
small-multiple restrictions are removed, without a new source exception.
Factors conversely construct a one-point global cover, so these supplied
certificate-acquisition and factoring tasks reduce to each other within
soft-O(m) on that source. This is not an operation lower bound, and the
reorigining converse does not assert coverage of the original intervals.

One specific acquisition shortcut is rigorously excluded on the actual
inherited majority family: the large-order routine returns its FIRST base2
above the target before accumulating any exact orders, leaving M=1.
Its retained M is not even a local annihilator, before or after odd
projection. This refutes reusing that accumulator as the needed K; it does
not rule out another computation on the full input or algorithm state.

Independent exact-file reviews check the extractor, detector, setup,
refinement, cover bridge and retained-data argument. Primary paper metadata
is pinned, without copying full research papers. No native source, Lean
theorem, example collection, broad build or publication is added. The new
setup does not automatically transfer or recompile the original collision
controller. The whole-family restriction-stable soft-O(m) sufficient query,
its all-input controller and complete Lean bit-complexity proof REMAIN OPEN;
the general soft-O(m^(3/2)) query bound is unchanged.
