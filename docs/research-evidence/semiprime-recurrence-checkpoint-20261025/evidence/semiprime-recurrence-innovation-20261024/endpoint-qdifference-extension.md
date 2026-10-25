# Constructive endpoint specialization of the adjoint algorithm

24 October 2026. This follow-up tests the extra q-difference relation, rather than relying on the degree-Jh denominator of a generic logarithmic derivative. No repository edits or finite examples.

## Paid relation and exact endpoint problem

Let B(t)=det(I-tC), acquired in soft J from F, and E(t)=product_(i<h)B(q^i t). All arguments also apply to C inverse with the already paid scalar conversion to the native norm. There is an explicitly acquired order-one q-difference equation

    B(t) E(qt)=B(q^h t) E(t),   E(0)=1.                 (1)

B and B(q^h t), including q^h, are acquired in soft(J+log h). Thus the first O(J) scalar moments plus an actual short equation are available. This is more than a bare rational Padé input.

The tested specialized algorithm is to reduce (1) modulo (t-1)^r, solve it fraction free at the endpoint, and extract either a proper factor or the residue E(1). The defect is explicit: q-shift does not induce an endomorphism of R[t]/(t-1)^r. The ideal is not stable. For example t-1 vanishes at t=1, while its q-shift qt-1 has unit constant q-1 under the order screen. Knowing E modulo (t-1)^r therefore does not give E(qt) modulo that ideal. Polynomial modular inversion of B at t=1 can be paid when B(1) is a unit, but it does not supply this shifted unknown jet.

One can repair the algebra by carrying separate jets

    e_k(u)=E(q^k(1+u)) mod u^r.

Then (1) becomes the initialized transition relation

    B(q^k(1+u))*e_(k+1)(u)
      =B(q^(h+k)(1+u))*e_k(u).                        (2)

All transitions are short polynomials, but no e_k is acquired from E(0)=1: zero is not on this multiplicative orbit. In particular evaluating the original product for e_0 is the original endpoint acquisition. Carrying h orbit points or evaluating their transition coefficients explicitly costs soft(J+h), and block multiplication returns the old soft(J+sqrt(Jh)) scalar algorithm. Equation (2) by itself is a transport rule, not a boundary initializer.

At a local prime where the transition coefficients at a given center are nonzero, division merely expresses e_(k+1) as a scalar-unit multiple of e_k. If an interior factor makes E(q^k)=E(q^(k+1))=0, the value-level equation reads 0=0 and conveys no hit witness. Fraction-free elimination preserves the valid equation but does not resolve this loss of terminal information. A nonunit B(q^k) discovered during explicit transition acquisition can indeed factor N; paying for finding such k is exactly the missing operation. One must not assume every interior hit appears in the two initially available endpoint coefficients B(1), B(q^h).

The first r coefficients at zero are not an endpoint boundary condition. Evaluating a t-adic truncation at t=1 leaves the exact tail

    E(1)=sum_(n<r)[t^n]E + [sum_(n>=r)[t^n]E].

Equation (1) recursively determines that tail, but no short endpoint functional of the recurrence has been acquired. This is an initialization audit, not an assertion that the known short equation cannot support another faster algorithm.

## Fraction-free approximants and orbit moduli

A Padé approximant from the short zero jet can be evaluated safely by cross multiplication. Its residual divisibility by t^r implies no divisibility by t-1, since t^r is a unit modulo t-1. To certify the endpoint value one needs the residual at 1 or an acquired certificate that it vanishes there. The q-difference equation does not turn a residual divisible by t^r into that certificate without transporting/acquiring the same missing endpoint boundary. A nonunit in a fraction-free algorithm may provide a proper factor, but no argument guarantees that a nonunit pivot occurs whenever the original product has an interior hit.

A finite set of endpoint centers can support q-shift modulo its vanishing polynomial only when multiplication by q preserves that center set. Starting at 1 forces its entire q-orbit. The local order guard excludes orbit closure at a public size <=h. Thus the obvious finite orbit modulus does not repair the algorithm at soft J. This is specific to this orbit-jet realization; it does not rule out implicit compressed operations on it.

## Ledger and result

| Operation | Acquired cost | Remaining datum |
|---|---:|---|
| B(t), B(q^h t), q^h | soft(J+log h) | none |
| First J moments/zero jet | soft J | none |
| Endpoint polynomial inverse B^-1 mod (t-1)^r | soft(J+r), if unit; else gcd | shifted E jet remains unknown |
| Fraction-free local q-difference equation | soft(J+r) for supplied center | e_k boundary not initialized |
| Explicit h-center coefficient acquisition | soft(J+h) | exceeds target |
| Existing scalar blocking | soft(J+sqrt(Jh)) | actual endpoint scalar acquired |

This endpoint-focused attempt fails at a shifted-jet boundary, independently of the earlier generic denominator count. There is no soft-J factor-or-specialized-determinant algorithm obtained. The useful next primitive would have to evaluate the normalized solution of (1) at 1 directly, or acquire a factor-aware residual certificate at 1, without supplying e_0 or the h-center transport data.

## Native logarithmic-denominator refinement supplied by root review

There is also an actual-source refinement of the earlier generic Padé degree check. In either residue field F_p, fix one supplied target Y_j. Local order(q)>h implies its h potential poles t=(q^i Y_j)^(-1), 0<=i<h, are distinct. At each such pole, each of the J targets contributes at most once, again by local order(q)>h. The total multiplicity mu therefore satisfies 1<=mu<=J. Unit-separated nonzero targets imply J<=p-1, so mu is nonzero in F_p. In the logarithmic derivative E'/E the residue is precisely mu and cannot cancel. Thus its reduced denominator has at least h distinct poles on every nonempty native target restriction. For a nonempty index restriction, replace h by its number of distinct indices within the guarded horizon. This proves that exact degree-O(J) rational reconstruction is unavailable when that cardinality is much larger than J, even on actual native inputs. It does not exclude an endpoint-only algorithm or prove an arithmetic lower bound for the scalar value E(1).
