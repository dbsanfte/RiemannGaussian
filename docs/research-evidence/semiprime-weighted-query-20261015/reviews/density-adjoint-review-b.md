# Second independent review: actual row density and finite-ring adjoint sectors

2026-10-15. PASS. No mathematical correction required.

Reviewed report: /tmp/semiprime-weighted-query-20261015/source/actual-row-density-adjoint-obstruction.md
Report SHA256: 723472c4e1dba27e23f490fbab953d240c032d65ffc7e79e87e98962f35939e9
Report bytes: 8621
Source-pins SHA256: 566dca1bf09f8fddf130caaeb8639658995d02552fc185898a976ac4fcfcd46c

Both supplied hashes and report byte length were independently recomputed. ALL TEN individual source hashes in density-source-pins.json matched exactly, including the canonical catalog proof and original seed/lift Lean sources. Historical prime supply/order/menu hypotheses remain inherited inputs, not newly proved analytic facts or algorithmic oracles.

## Actual row-incidence count

The full-prefix count matches my independently derived full-row-hit-count-review.md. In a width-m² Q box the possible phase multipliers k number O(m^4/R+1)=O(M^1.969). At a fixed k, modulo m² the variable m²i disappears, so the literal-lift uniqueness proof remains valid even though i is not fixed. Nonexceptional false tags contribute one Q per tag; at most two exceptional quadratic tags contribute O(m) total slopes/Q; the own tag contributes O(m) Q in one residue class modulo m. For each Q,j,k the exact integer equation determines i. The exact prime order R>4m² also ensures at most one local zero per row across the prefix. Thus there is no extra index multiplicity.

The total O(K_*M^6.969) incidence count and Markov deletion O(K_*M^5.972)=O(M^5.992) are correct. The menu and field labels are already counted, so Markov introduces no second menu factor. At a surviving input, the union of hit rows from both fields has at most2M^.997=o(m) tags. Counting maximum length4m² makes the conclusion simultaneous for all shorter prefixes without a length union. Existing forced coverage is compatible with this sparsity and is not negated.

## Finite Laurent functional

The q-binomial coefficient recurrence is a polynomial identity with no divisions:

    (1-q^(k+1))c_(k+1)=(q^L-q^k)c_k.

After f_k=u^k c_k on [0,L] and zero extension, it holds for ALL integer k. At k=-1 the potential f_0 term is multiplied by1-q^0=0; at k=L the potential f_L term is multiplied byq^L-q^L=0. Beyond those endpoints both relevant f values vanish. Negative powers of q and gamma exist because they are supplied units, rather than unknown residual inverses.

Evaluating sigma^-1((1-q x^d)p) at gamma^k gives (1-q^k)p(gamma^(k-1)). Reindexing the FINITE support of f therefore gives precisely the displayed recurrence coefficients, so Lambda annihilates the entire R-linear image of L_op^*. No infinite convergence argument, nonzero-divisor division or characteristic-zero transfer is hidden here.

With u=gamma^(-N-3d) and e_j=3d-delta_j, u gamma^e_j=z_j exactly. Hence Lambda(x^e_j)=P_L(z_j;q). If that row product is a unit (indeed merely nonzero), x^e_j cannot lie in im L_op^*. This argument remains valid in R=Z/N with zero divisors. The quotient here is an R-MODULE quotient; no claim that the operator image is an ideal is needed or made.

The explicit monomial operator formula is correct: applying sigma^-1 contributes gamma^(-e) to both terms because q=gamma^d. Thus

    L_op^*(x^e)=(gamma^(-e)-u q^L)x^e+(u-gamma^(-e))x^(e+d).

It preserves exponents modulo d, and projections onto each finite-Laurent residue sector commute with the operator. Its image and module quotient therefore decompose by those sectors over any commutative ring, including this composite ring.

## Actual nonzero weighted sectors

The exact low-digit relation delta_j j²=N(1-2j) mod m gives, for a proposed digit c, the polynomial c j²+2Nj-N. It is nonzero over F_m because m is odd and m does not divide N. Hence each digit has at most two tags, and each finer e_j mod m² sector has at most two tags. The m-o(m) unit rows occupy Omega(m) distinct sectors.

Extending the operator coefficientwise in FORMAL independent weights preserves the direct sector decomposition. In a given sector, a coefficient attached to a unit row is already a nonzero monomial class; a different formal weight cannot cancel it. This establishes the stated Omega(m) nonzero actual weighted sectors without requiring numerical weight choices, generic roots, reducedness of the quotient, or independence of evaluations at all gamma powers.

Finite-order coefficient zeros and evaluation aliasing do not defeat this proof: the nonzero functional value witnesses failure of membership in the operator image directly over the actual ring. It is therefore a genuine actual-family statement, not an unsupported transfer of a generic characteristic-zero obstruction.

## Exact limitations

The conclusion is failure of a specified endpoint-only certificate in the image of this finite-Laurent adjoint. It does not prove Omega(m²) dense remainder size, a scalar circuit lower bound, or more than soft O(m) work to acquire the Omega(m) surviving sparse sectors together. Rational certificates with poles, other operators, nonlinear methods, sums evaluated only at chosen source points and norm-only acquisition remain outside the claim. Collision sparsity does not give cheap identification of the few hit rows. No fast evaluator, new Lean theorem or guaranteed sixth-rate algorithm is claimed.

Only this local review file was written. No repository edits or builds were performed.
