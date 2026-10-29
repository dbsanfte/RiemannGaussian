# Independent review of order-residue-supplier.md

26 October 2026. Read-only finite algebra and cost review. No examples,
tests, campaign, source edits or repository changes.

**PASS on the paired AP certificate, both-prime order conclusions and
factor/residue distinction.** One sentence about “full cyclotomic norm
before selection” should be clarified as indicated below; the subsequent
fixed-residue norm calculation is correct.

## Integer AP acquisition and both-prime coverage

With B=floor(sqrt N)<Q, every tested integer 2<=a<=B is coprime to Q.
Thus any nonunit of the full integer product has gcd exactly P, never N.
No extension norm or global-annihilator argument is needed on this branch.
The cap and exclusion of 1 prevent trivial/unit degeneracies.

For a class r mod M choose the exact first representative a0>=2,
clip at B, and write a=a0+Mj. Since M is a supplied unit modulo N,
factor out M^L and evaluate the consecutive scalar factorial in
j+a0/M. The usual monic product/BSGS routine costs soft sqrt L,
L<=B/M+1, including coefficients, block starts, tail and modular gcd.
It does not invert any factor of the queried product. All exponents
and starts have O(log N) bits at the actual moduli in this report.

If P=1 mod M, class1 contains P. If Q=1 mod M, N=PQ implies
P=N mod M, so the SECOND class contains P. Hence unit results exclude
1 at BOTH primes, without knowing their order or which was large.
The -1/-N argument is exactly analogous. Empty or duplicate classes
are harmless; it is the FULL B cap that licenses the conclusion.
A shorter unsuccessful prefix cannot certify an exclusion at an
unreached factor.

## Valuation and root-clock conclusions

For M=3^a, unit continuation gives v3(p-1)<=a-1 for p=P,Q.
Since ord_p(beta) divides p-1,

    v3(ord_p(q))=max(v3(ord_p(beta))-2e,0).

Thus a<=2e+1 suffices to make q 3-coprime. At a=2e+1 the AP length
is O(k), hence soft sqrt k readout. For M=3^(e+1), v3(p-1)<=e,
and every exponent H/d with d|k has 3-adic valuation >=e. All clocks
beta^(H/d), including rho=beta^k and q, therefore remove precisely
the entire 3-primary part of the odd beta order and have EXACTLY the
same remaining local order. No 2-primary correction is needed because
the supplied beta orders are odd. Their order exceeds16H because q's
does. This uses the ACTUAL source q, not an unscreened changed base.

At M=3^(e+1)=3k/2, B/M<=2k^2/3; the two AP products cost soft k.
The older M=k/2 gives a slightly stronger valuation bound but the
same exponent. The clocks n|k used by restricted HH also remain
large automatically, since n^2|H and q=(beta^(n^2))^(H/n^2).
The order certificate is not needed for that last implication, but
is consistent with it.

## Faithful phase test and its actual readout

For primitive auxiliary zeta of order d|k, local q-order coprime to d
implies the only intersection of <q> and <zeta> is1. Therefore a
factor of (3) vanishes precisely when q^(Cb-h)=1 and h=rho mod d.
This holds in EVERY primitive local component, so its scalar norm
has exactly the desired fixed-residue nonunit predicate at both
primes. Omit h=Cb before constructing the filter; a zero exponent
is not a licensed annihilator.

The extension rank phi(d) must be charged. The stated conservative
rank-dependent coefficient/norm completion is an upper bound, and
direct AP evaluation is better. Refining modulo successive powers
of3 is a valid bounded search, but its first constant-modulus tests
still pay soft sqrt(VW), so it has not acquired a soft-k supplier.
No root-clock inverse or modular phase projector is free.

**Wording clarification:** a primitive cyclotomic norm for ONE FIXED
rho does NOT return the powered WHOLE unfiltered query. As the very
next paragraph correctly states for prime d, it retains
(1-x)^(d-1) on that class and Phi_d(x) on other classes, the latter
being units under the certificate. Thus it is a faithful rho-FILTER.
To say the norm returns the whole query one must explicitly combine
ALL rho channels, or use the corresponding full channel product.
For example product_(rho mod d)(1-x*zeta^(h-rho))=1-x^d;
its zero predicate equals 1-x under the coprime-order gate. This
clarification does not change the missing-selection conclusion:
a norm for a supplied rho is evaluable, but the useful rho is not
selected by the phase-faithfulness proof.

## Arbitrary auxiliary modulus and information scope

For a public prime ell in[k,2k], the classes1,N mod ell through B
again exclude ell|p-1 at both primes. Sieve acquisition and two
length-O(k^2) AP products cost soft k. The resulting residue consumer
has V*(W/ell+1)=O(k^2), but obtaining that residue remains separate.
Root extension rankTheta(k) and cross-modulus collision matching are
correctly not treated as free.

Neither unit continuation nor equal root-clock orders supplies P mod n,
the actual phase t, or a quotient character of <q>: with r=ord(q)
coprime to d, q^(h+r)=q^h makes an intrinsic h mod d character
impossible. This is the correct narrow interpretation, not a general
arithmetic/discrete-log impossibility result. The old odd-axis bridge
uses external integer labels and therefore remains valid.

No substantive arithmetic or cost correction is required beyond the
one norm/channel wording distinction. All AP factor branches are
proper-gcd branches, and the report retains once-only T_ext only
where a separate short-label saturated consumer is actually used.
