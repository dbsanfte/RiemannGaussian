# Several public polynomial top bands still cannot supply the proper-factor rows by products

2026-10-15. New classical actual-source arithmetic obstruction. This is an obstruction to a specified coefficient-stream representation route, not a lower bound for general acquisition, additive cancellation, or factoring. It does not improve the current soft O(m^(3/2)) general query bound.

## Contract

Use the same original order-qualified balanced prime-pair supply as the exclusive-own-row theorem. In a size bin P,Q=Theta(M^3), N=PQ, the original supply has Omega(M^6/log^2 M) ordered inputs. Every candidate m=Theta(M) has local prime orders R_P>P^.677=Omega(M^2.031) and R_Q>Q^.677. The large divisor R_P is intrinsic to P, independent of its admissible partner Q and of the qualifying candidate m. It is used for a counting proof, never supplied to an algorithm. All frozen deletions, including exclusive-own-row and unit-row conditions, are imposed on this same supply; their union has soft O(M^5.994) inputs. No intersection of unrelated thin prime families is used.

For each size bin prescribe a library of B nonconstant monic integer polynomials F_b(T), of degrees at most D_*. The library is fixed as N varies in that bin, and is common to all m. Its coefficients may depend on M; no coefficient-size or construction-cost assertion is needed for this impossibility result. Let BD_*<=M^.010; in particular any fixed or polylogarithmic library and degrees qualify eventually.

Allow the algorithm to select any number of stream origins

    T=F_b(N)+s,   |s|<=C_s m^2,

and any indices 0<=k<=C_k m^2, for fixed constants C_s,C_k. Both s and k may depend on the full input N, the row, previous observations, or private advice. The entire band of integer s is covered simultaneously. Thus this is not a catalog of m-only indices or a bound on the number of adaptive selections. In particular bounded source offsets delta_j are allowed as s.

For each stream, permit any supplied unit base eta whose order in each hidden field equals R_P or R_Q respectively; examples are gamma and q=gamma^(m^2). More generally gamma^v works if v is coprime to the two orders. This order condition is a promise about the actual branch, not an acquired order oracle. Define

    C_k(T;eta)= product_(0<=r<k)(eta^T-eta^r)
                 / product_(1<=r<=k)(1-eta^r).

For nonnegative T and k<=T this is the coefficient of X^k in P_T(X;eta); the displayed prefix formula also defines the stream for arbitrary integer T whenever its denominator is a unit. Huge T need not be materialized as a polynomial: eta^T can be powered succinctly. No horizon-inflation argument is used.

## The arithmetic deletion

Choose constants c_-,c_+ with c_-M<=m<=c_+M throughout the size bin. If a numerator in a selected stream vanishes modulo P, then

    R_P | T-r = F_b(N)+s-r

for some 0<=r<k. Because P=1 modulo R_P, this is equivalent to

    F_b(Q)=t modulo R_P,   t=r-s.

Every possible candidate, shift, row, index and numerator has t in ONE fixed interval of O(M^2) integers: for instance

    -C_s c_+^2 M^2 <= t <= (C_k+C_s)c_+^2 M^2.

This common interval is the reason there is NO union factor for m, its candidate menu, the number of shifts, selected indices, or stream invocations.

Fix an actual qualified P and its intrinsic prime R_P. For each b,t the polynomial F_b(X)-t remains nonzero of positive degree at most D_* modulo R_P because it is monic. It therefore has at most D_* roots in F_(R_P). In the entire possible integer Q bin, of length O(M^3), each residue class contains O(M^3/R_P+1) integers. Counting all integers, rather than assuming any short-progression prime-density estimate, gives

    # bad Q for this P
      <= O(B D_* M^2 (M^3/R_P+1))
       = O(B D_* M^2.969).

There are O(M^3) possible P. Thus at most O(B D_* M^5.969) ordered inputs have ANY permitted stream numerator vanish in the P field. Repeating with P and Q interchanged costs only a factor two. Duplicated residue roots, overlapping bands, and repeated selections only decrease this union bound. No sum over possible cofactors is required: R_P is fixed for each actual P in the inherited supply.

For BD_*<=M^.010 the new deletion is O(M^5.979)=o(M^6/log^2 M). Taking its direct union with all frozen deletions still leaves Omega(M^6/log^2 M) inputs. This is a counting bound, not an algorithm's running time or the cost of finding those inputs.

On every surviving input, all permitted numerators are nonzero in BOTH hidden fields, simultaneously for all candidates, all bases with the promised local orders, and all adaptive s,k. Also k=O(M^2)<R_P,R_Q eventually, so all denominator factors 1-eta^r are nonzero in both fields. Consequently every permitted C_k(T;eta) is a UNIT modulo N.

The same proof permits any prescribed nonconstant polynomials whose leading coefficients are units modulo all actual local orders. Monicity is a public sufficient condition. Constant tops are deliberately excluded: F_b(X)-t could then be identically zero and the root bound would not apply.

## What this excludes

The surviving family retains the prior exclusive-own-row property. At every native candidate and every 2m^2+2<=L<=4m^2 there are two distinct private own tags with

    gcd(N,P_L(z_(P mod m);q))=P,
    gcd(N,P_L(z_(Q mod m);q))=Q.

Any expression obtained from the permitted stream values using multiplication, unit division, integer powers and unit prefactors remains a unit. This is true for any number of streams, selections and multiplicative stages, including private-factor-dependent index/shift advice within the stated bands. Therefore it cannot equal either proper-factor row value. No rowwise representation of the entire actual row list by this multiplicative interface can exist on this family.

This is stronger than applying the earlier one-stream nested-support argument separately to a few streams: here all permitted values in all these public top bands are units. The counterfamily may depend on the prescribed polynomial library; the earlier one-stream theorem instead used a family independent of every stream. Arbitrary factor-aware two streams do encode both exclusive supports, as the separate two-stream report demonstrates, so that previous support theorem cannot simply be relabelled a multi-stream theorem.

This result also prevents these particular short-prefix numerator/denominator tests from revealing a proper factor directly: their gcds are all one. It does not exclude using some other acquisition stage before, after, or in place of them.

## Limits and remaining target

Sums and differences of units can vanish, including modulo only one hidden factor. Thus additive formulas, determinant cancellations, coefficient or jet extraction, and arbitrary rational functions with nonunit intermediate numerators are NOT excluded. A public formula in that larger class must still construct all its constants and selected inputs within the desired budget, but no lower bound for it follows here.

Nor does this proof cover arbitrary m-dependent polynomial tops, floor or quotient constructions such as floor(N/m^2), arbitrary N-dependent top rules outside the prescribed bounded-shift bands, bases whose orders change, longer indices, nonunit prefactors, or norm-only and factor-only algorithms. An m-dependent top is covered only if its values actually lie in these same fixed polynomial bands. In particular the full canonical long-row progression has exponent stride m^2 and total span Theta(m^4); it is not a short contiguous numerator prefix. The theorem must not be applied to that long progression itself.

No examples, benchmarks, Lean additions, backend certificates, or heuristic equidistribution assumptions establish this result. The proof is the elementary prime-field polynomial root bound, the intrinsic-order premise, and the explicit same-supply union above. The inherited exclusive-row theorem supplies the actual nonunit rows. Acquiring a restriction-stable soft O(m) long query, through additive cancellation or another public observable, remains open, followed by the full bit/memory/controller proof in Lean.

## Exact prerequisites

The adjacent polynomial-top-source-pins.json records byte hashes for the actual source, same-supply arithmetic premise, and prior exclusive-own-row proof. No newly searched external theorem is used in the new count. The private orders, factors and tags in this proof are not algorithm inputs or advice delivered by this theorem.
