# Independent character-resultant support-cleanup audit

2026-10-24. **PASS. No required fixes.** Scratch review only; no source or repository edits.

Exact reviewed source: `/tmp/semiprime-character-endpoint-20261024/character-resultant.md`

SHA256: `87c7b82b0bcc516f63d8ff4f1f81f2214f1e8c4e3e23083072470d7c2a672fb1`

The root review character-review.md was read, but the resultant signs, quartic expansion, root-count supports and complete cleanup branches below were independently checked. This is a mathematical/acquisition audit, not an independent certification of every external primary-source complexity theorem.

## Fixed-degree identity and nonunit square support

For monic degree-n A,B, C=A-B and D=c^2B-(cX+h)C with the generic degree profile n-1,n-2, exchanging the resultant arguments gives

    Res(A,B)=(-1)^n Res(B,C).

The ordinary remainder is D/c^2 on the unit-c branch. The resultant remainder update gives Res(B,C)=c^2 Res(C,D/c^2), while scaling the second operand by c^2 contributes c^(2(n-1)). Thus

    Res(C,D)=(-1)^n c^(2n-4) Res(A,B).

The sign (-1)^n is correct. The identity first holds universally in symbolic coefficients and therefore specializes over R with the same nominal/fixed degrees. At degree drops the padded Sylvester resultant convention is needed; the report states it explicitly and never treats the formula as a modular division by a nonunit.

For n>=3 the positive even c exponent leaves exactly its unit/nonunit support after squaring the Jacobi symbol. Boolean zero cannot be canceled. The n=2 exponent-zero exception is correctly separated. Formal q-hook scalar units can be removed, but endpoint zeros of their pivot polynomials cannot. This distinction agrees with the tensor report's prequotient exact-division theorem.

## Linear and quartic support polynomials

Let A1,A2,A3 be the top three nonleading A coefficients and B1,B2,B3 the corresponding F coefficients. Substituting c=A1-B1/Y, d=A2-B2/Y^2 into the acquired first Schur numerator yields exactly the report's quartic P2 after multiplying by Y^4. In particular its constant and leading terms are B2^2-B1B3 and A2^2-A1A3, and its Y,Y^2,Y^3 coefficients have the displayed signs.

P1 has unit leading coefficient A1. P2's leading coefficient is the square-partition q-hook value

    q^2 (1-q^(n-1))(1-q^n)^2(1-q^(n+1))
         /[(1-q)(1-q^2)^2(1-q^3)],

which is a certified unit for n>=3 under the short guard. Therefore P1 and P2 have exact local degrees one and four, regardless of the native F coefficients. They have at most one and four zeros on either distinct local outer grid. Multiplying by the Laurent-clearing Y powers introduces no endpoint zeros because all outer nodes are units.

## Complete soft(n+t) cleanup

The procedure evaluates EACH constant-degree polynomial at every retained outer node and takes EACH scalar gcd. This is the necessary complete guard: if no proper gcd occurs, a value is either a unit modulo both primes or zero modulo N. Thus its bad-node list is exact and public; disjoint local support could not be hidden in a saturated product. Each scan costs soft t.

At an actual bad node y_b, the inner slice has n explicit nodes q^a*y_b and the acquired degree-n F. One monic MPE, product and original-row localization cost soft n. A proper gcd factors. A saturated ORIGINAL scalar leaf is at index a+s*b<st inside the retained original horizon, so its bounded-beta decoder applies. The auxiliary pivot zero itself is never assigned that decoder. All different-local-row or different-local-seed saturation cases are handled by descent through the already acquired original values.

If the original slice is unit, its ACTUAL scalar factor is retained. Removing y_b by monic exact division is then support safe: the original total product is that acquired unit factor times the product over remaining nodes. Node differences remain units. On the residual CRT algebra the processed pivot is a genuine unit because every remaining endpoint value was individually certified unit.

At most one first-stage node and four second-stage nodes are removed, irrespective of overlaps. Thus two scans, at most five original n-point slices, monic modulus updates and any inverse-value interpolation cost soft(n+t). For small t a bounded number of direct slices suffices. If every node is removed, the already acquired original slice factors are the whole rectangle; the empty remaining product is one. No nonunit original slice is discarded.

This verifies all branches of the claimed positive refinement, not just its generic/unit case. It legitimately improves the prior immediate-fallback policy for these TWO auxiliary support sets.

## Scope and later stages

Both first pivots are unit on the remaining algebra, so the corresponding unit-pivot updates and square cancellations are then lawful. This does not acquire subsequent mixed pivots. Their degree bounds, q-hook origins or monic reversals do not supply their endpoint values or support. The stated nt charges for repeated full scans or original slices are implementation ledgers, not generic lower bounds.

The fallback can reacquire the complete original rectangle at the inherited soft(J+sqrt(JL)) bound, avoiding any dependence on a newly irregular remaining outer grid and avoiding division by an unknown removed value. Every removed factor was actually acquired and unit. Original labels/indices and saturation recovery remain attached throughout.

The character interface and root-level zero warning are correctly credited as prior work. The report does not claim a completed soft-m restricted character detector, automatic pivot genericity, hidden-field input, altered decoder or improved factoring exponent. The exact reviewed bytes support the positive at-most-five-node cleanup and the explicitly unchanged whole-query bound.
