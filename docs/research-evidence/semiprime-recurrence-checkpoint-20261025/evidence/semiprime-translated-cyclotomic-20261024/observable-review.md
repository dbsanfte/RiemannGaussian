# Independent observable audit

2026-10-24. Verdict: **PASS**, with wording clarifications below. No repository edits.

Exact reviewed file: `/tmp/semiprime-translated-cyclotomic-20261024/observable-attempt.md`

SHA256: `aa5b21052038ba096114bb84e7246976fd94ec4b6ffeb7bd9ebaa24bcc1d9b52`

The pinned original cyclotomic-cancellation README was independently read earlier in this session; its SHA256 is `992e31ea5ece408e448dba91771a1616228b4629668552960c15311c9aafad6e`.

## Checks

- Unit certificate: multiplying the alternating geometric sum gives beta^m+Z^m with the displayed positive sign because m is odd. Odd local beta orders imply beta^m cannot equal -1 in either odd characteristic. Thus u and all signed native powers really are acquired units. This uses the actual odd-semiprime prepared context.
- Power/row ledger: f and q cost soft m at polylogarithmic exponents; one full row costs soft m, and independently materializing m rows costs soft m^2. The report does not treat rows or their comparison lists as supplied inputs.
- Star ratio: the displayed quotient follows from the commuting involution and sigma automorphisms. At an own hit it retains (w^(m^2))^I; no period or separation certificate for w is supplied. A pointwise nonzero ratio is not itself covered factor support.
- Euler derivative carry: with pr=s+(Z^m-1)Q, the product derivative reduces to delta(s)=(delta p)r+p(delta r)-mQ. The minus sign is correct. The power formula has the same correct minus sign. Only the reduced quotient carry is needed; it is acquired from supplied n,R_n using the displayed equation and the certified inverse of m. The unknown native n=m^2 I is not supplied by the own-tag promise.
- Algebra derivations: differentiating zeta^m=1 over R forces D(zeta)=0 because m and zeta are units. Thus the proposed derivation cannot be rescued within this etale cyclic algebra by silently treating zeta as a free variable.
- Beta tangent: differentiation is legal because the defining relation is independent of B. N=0 in R makes the derivative of (B+zeta)^N zero. The acquired logarithmic derivative ell/u+a/(beta+zeta^j) is exact, including signed ell. At own j=P mod m, sigma_(j^-1)(f(B)) reduces modulo P to (B^P+zeta)^Q, exactly as displayed. Its B-derivative vanishes, whereas the comparison power has logarithmic derivative (Q+ell)/u. The resulting extra requirement a*u/(beta+zeta^j)=Q is correct and is not inherited from pointwise Frobenius.
- In fact for own j!=1 the tangent requirement is impossible in the full cyclic algebra: after cross-multiplication, (a-Q)beta+a zeta-Q zeta^j=0 would contradict independence of its degree-<m coefficient basis, since a and Q are nonzero modulo P. This strengthens, and does not contradict, the report's stated failure. For j=1 an extra scalar equality a=Q modulo P is still required and not promised.
- Recovery: a global equality for beta+zeta or its scalar augmentation/norm does not carry the original beta local-order certificate. The report correctly refuses to invoke the old beta decoder. Exact tuples modulo N also miss merely local tuple equalities; projected tuple collisions can introduce saturation without an inherited global-leaf decoder. The fallback is correctly not declared a complete factoring algorithm.

## Wording clarifications

The star-ratio sentence “this is not forced to be one globally” should mean that the OLD self-reciprocity theorem no longer forces it. The report does not prove nonidentity at every prepared beta, and should not be read that way. A precise replacement is: “The old theorem does not force this ratio to one; it may still equal one on particular inputs, and no useful nonzero-support guarantee is supplied.” Similarly, “Being nonzero globally repairs the old degeneracy” is conditional on acquiring such a nonzero value; nonselfreciprocity alone does not certify that value. The final paragraph already states the correct limited conclusion.

In the supplied-exponent carry discussion, “the corresponding carry” means its residue modulo Z^m-1. The full integer-polynomial quotient has degree growing with n and is not acquired at soft m. Equation (2) and all actual uses need only the reduced carry, so the charged algorithm is correct with that qualification.

No substantive false sign, tangent identity, unit claim, recovery claim, or rate gain was found in the reviewed bytes. The soft-m covered translated query remains unconstructed.
