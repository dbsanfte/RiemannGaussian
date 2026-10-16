# Independent verification: prescribed row-specific index libraries

2026-10-15. Verdict: **the proposed counting extension is sound**, conditional on the frozen actual balanced supply, selector-menu envelope and exclusions specified below. This is an independent classical derivation, not a Lean endpoint or a general scalar-query lower bound.

## Contract and quantifiers

At scale X=M³ fix one prescribed library I_(m,j) of at most B_lib integer indices for each public candidate m and tag 1<=j<m. Index values may be signed and arbitrarily large. At fixed m,j the list must remain fixed as the input partner Q varies in the counting argument; in particular it may not depend on N=PQ. A choice of libraries fixed in advance for each scale M is allowed. The resulting retained majority family may depend on that prescribed library. This does not assert one common counterfamily that defeats every possible library simultaneously.

Use the frozen supply P,Q~M³, m~M, P,P-1,Q,Q-1 units modulo m², and projected gamma of exact prime local orders R_P,R_Q>16m². Use the original seed slope/lift

    a j²=PQ mod m,  1<=a<m,
    D=(PQ-a j²)/m,
    b=-I_j D mod m,  I_j*j=1 mod m,
    delta=a+m b-2aj,  -3m²<=delta<=m².

Only congruences of b are needed; the actual centered representative supplies the delta bound. The local order R_P is fixed once P is fixed; it is not an additional summed parameter. The actual source's projection may vary with N,m, but its retained exact local order does not.

## Per-box bound

Fix an admissible first prime P, candidate m, and a half-open Q box of width at most m². Fix one tag j and one prescribed i in its library. A P-field zero of the actual residual is equivalent to

    Q+delta-m²i=K R_P.                          (1)

This uses P=1 mod R_P and gamma's exact order. Across every Q in the box and every permitted slope a, the left side lies in one interval of length at most 5m². Since R_P>16m², at most one K can occur for this fixed (j,i). Indeed the interval bound would hold across all tags, but a common K across different row-specific indices is neither assumed nor required. Arbitrary index magnitude merely moves this short interval.

Modulo m, multiplying (1) by P and substituting PQ=a j² gives

    a A_j=P K R_P mod m,
    A_j=j²-2Pj+P mod m.                       (2)

There are three cases.

**Nonexceptional false tags.** If A_j!=0 modulo m, equation (2) fixes at most one slope a. For a false tag j!=P modulo m, two qualifying Q,Q' with that same state satisfy m|Delta Q and

    m Delta b=-P I_j Delta Q mod m².

Subtracting (1) gives Delta Q+m Delta b=0 as an integer, so

    (1-P I_j) Delta Q=0 mod m².

The coefficient is nonzero modulo m, hence a unit modulo m². Thus Delta Q=0 modulo m²; the half-open box contains at most one such Q. Consequently each prescribed index of a nonexceptional false tag contributes at most one bad partner.

**Exceptional tags.** A_j=0 is a monic quadratic equation in j over F_m, so there are at most two exceptional tags. None is the own tag: at j=P modulo m,

    A_j=P(1-P)!=0 mod m,

using the frozen P and P-1 unit exclusions. For an exceptional tag, (2) may allow all m-1 slopes a when its right side is zero. But each slope still has the false-tag uniqueness property just proved. Thus each index contributes at most m-1 bad Q, and all exceptional-tag library entries contribute O(m B_lib) partners. If P-1 were not excluded, this own/exceptional separation would fail; the hypothesis is essential to this proof.

**Own tag.** At j=P modulo m, A_j!=0, so (2) fixes a. The slope congruence then fixes Q modulo m. A width-at-most-m² half-open box contains at most m integers of one residue class modulo m (the weaker bound m+1 is also sufficient). Hence each own-tag index contributes O(m) partners and its entire library contributes O(m B_lib). No geometric index bound or seed-index localization is needed here.

Summing all nonexceptional false tags gives O(m B_lib), and adding the at-most-two exceptional tags and the own tag preserves O(m B_lib) bad partners per box. The count is for a union of bad Q; summing duplicate states can only overcount, which is harmless.

## Global count and majority

The frozen necessary selector envelope p_(-K_*)(m)^6<PQ<=m^6 gives O(G_m+1) Q boxes, where G_m=m-p_(-K_*)(m). Summing the per-box count over O(M³) admissible first prime values and all public m~M, with

    sum_m (G_m+1)=O(K_* M),

gives

    O(B_lib M³ sum_m m(G_m+1))
      = O(K_* B_lib M⁵).

Exchanging P,Q costs only a factor two; the same fixed libraries remain unchanged under that counting argument. Thus the estimate covers zeros in either hidden field. If B_lib=0 there are no probes and no deletions.

For K_*=O(M^.020) and B_lib<=M^.970, the new deletion bound is O(M^5.990). Union with the frozen soft O(M^5.994) losses is still o(M⁶/log²M), so an Omega(M⁶/log²M) retained actual supply has every prescribed-library residual a unit in BOTH fields. The full canonical product still has its already compiled coverage witness; the new statement excludes only acquisition from this fixed sparse residual library.

## Meaning and limits

The theorem permits adaptive selection of entries from the prescribed library after seeing N. It does not permit the library itself to move with N. Products and inverses of observed unit residuals remain units, and their gcd with N is 1; arbitrary additions or other factorization algorithms are outside this argument.

For coverage, signed indices of arbitrary bit length are legitimate and the count is unchanged. To claim paid soft O(m) acquisition when B_lib is polylogarithmic, index bit lengths and modular powering costs must ALSO be polylogarithmic in N, or another explicitly paid representation must supply those powers. Cardinality alone does not pay enormous exponent inputs. Polynomial-size menus or B_lib=M^.970 may be granted free for this coverage obstruction; they are not claimed to be globally nearlinear acquisition.

Endpoint bands and fixed padded-length bands are special cases. The new count is stronger because it no longer needs own-index separation: the rare own-tag hits themselves fit the same deletion budget. No claim is made that every N-dependent low-cardinality probing strategy has such a fixed-library envelope.


## Final full-report review and byte pin

Independently reviewed the FULL report `/tmp/semiprime-query-followup-20261015/cancellations/prescribed-tag-catalog-obstruction.md`, not merely the initial outline. Final SHA-256: `f3352537846c716c36f4ad3e191be857c484993f986f887fc770eba3e6ccfca4`.

Verdict: **PASS**. Its theorem, three local tag classes, full-source lift congruences, whole-menu count, retained-majority estimate and multiplicative-unit consequences agree with the independent derivation above. The final constant convention B_*=O(M^.970), with an arbitrary fixed implicit constant, is sound and explicitly includes endpoint libraries with 4w+2 entries at w<=M^.970. It changes no exponent or counting mechanism. The report correctly fixes each library before varying N, permits adaptive selection only within a prescribed bounded union, separates coverage-only huge indices/polynomial menus from paid bit complexity, and makes no universal input-dependent sampling or scalar-query lower-bound claim. No blocking correction remains.
