# Independent review: character compression

26 October 2026. Read-only mathematical/cost review; no experiments or repository edits.

**PASS with one small unit-range correction:** Section 2 must explicitly require **n positive** and `1 <= n*ell < min(ord_P(q),ord_Q(q))` for its displayed order-based certification. Merely saying `n*ell below both local orders` includes zero and negative multiples, for which that argument does not apply. (Some individual denominators at n=0 remain units, but 1-q^(n*ell) is then zero, so it is not the stated certification.) This does not affect the intended positive-frequency application.

## Exact arithmetic identities

The single-prime Gauss identity is correct with the stated sign convention. In the cyclotomic algebra,

    sum_(s=1)^(ell-1) chi(s)/(1-z*zeta^s)
      = [sum_(r=0)^(ell-1) z^r sum_s chi(s)zeta^(sr)]/(1-z^ell)
      = G*S_ell(z)/(1-z^ell).

The inner sum is zero for r=0 and chi(r)*G otherwise. Since G^2=chi(-1)*ell, G is a unit when ell is coprime to N. Multiplying out gives equation (1) as a rational/polynomial identity. The residue-or-zero mask has coefficient 1 at zero, coefficient (1+chi(r))/2 otherwise, exactly equation (2). For the corrected positive short range, 1-q^(n*ell) is a unit. The product of all 1-q^n*zeta^s, including s=0, equals that unit; therefore each factor is a unit in the extension. This proves legality even if the cyclotomic algebra splits differently at the two primes; no field-only division is needed. Outside that range the finite polynomial identity remains valid, but a numerical rational evaluation needs its own unit checks.

For CRT representatives u_ell in [0,B), the E,R,c definitions give exactly E=R+Bc. Hence the product of tuple polynomials is sum z^R(z^B)^c, with coefficient 1 for each residue tuple. Uniqueness of CRT identifies each tuple with one R. Reduction modulo z^B-1 removes c; substitution z=q^n does not. The cutoff R<=m is likewise a real additional restriction, not obtained by multiplying the independent tuple sums. The carry range is polynomial in the small prime sizes since 0<=c<sum_(ell|B)(ell-1), but the report correctly does not infer a bounded-state contraction from its range alone.

Equation (5) follows by the exact integer equality [ar]_B=ar-B*floor(ar/B). The Bloch algebra T^B=q^B has roots q*zeta_B^r after the relevant auxiliary extension, rather than q^r. Thus both proposed replacements indeed address a different alphabet unless an additional identity/acquisition is supplied. All these are arithmetic statements, independent of complexity conjectures.

## Parameter and cost bookkeeping

With J=soft(k), M=Theta(k^(3/2)), a density reduction of k^(-1/2) requires t approximately log(k)/(2 log 2) in the ideal half-density model. The largest of the first t primes is Theta(log k loglog k), and log B=Theta(log k loglog k). Thus B is superpolynomial in k and B/2^t is still superpolynomial. In particular B>>M, so a finite original clock interval is entirely a cutoff tail, not a full B-period. Polylogarithmic row counts or the usual small per-prime density corrections do not repair this power-level mismatch.

The auxiliary fixed-subalgebra rank at most 2^t (roughly sqrt(k) at that t) is an output-size statement. It neither supplies the cyclotomic relative norm nor evaluates the q-arithmetic cutoff. Acquiring that many independent coordinates for each of soft(k) rows is also not within the desired soft-k budget without a shared contraction. The current initialized geometric-product bound soft(J+sqrt(JM)) is correctly retained as the available fallback.

## Scope

The review validates a failure of the **specific** compression which drops CRT carries or substitutes arithmetic q for an auxiliary root of unity. It does not show that the carry/cutoff contraction is computationally hard, nor exclude other compressed masks or semiprime-specific methods. The report consistently preserves that distinction. Rejecting a physical-factor witness does not certify its arithmetic difference as a unit, so the warning against dividing rejected products is also correct. Actual retained indices still carry the original labels and recovery contract.

No further gap found. Make n>0 explicit before archiving the unit-range statement.
