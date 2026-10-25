# Independent exponent/lift review

24 October 2026. Reviewed exact current bytes of /tmp/semiprime-translated-cyclotomic-20261024/literature-and-exponent.md.

SHA-256: `a5aec97ae267a4d1b242aa38a09bd52176c895a52cf18d43f6a2d9b155928ac5`.

Verdict: **PASS. No required fixes.** This is a mathematical/algorithmic audit of the supplied-power extraction, mixed-lift mismatch and recovery hypotheses. No repository edits, examples or claim that all bibliography was independently re-fetched.

## Actual supplied g² power: soft-m extraction is initialized

Let g=X^m-1 and suppose H is ACTUALLY u^n modulo g². A different representative differs by g²V, whose derivative is divisible by g; hence H' modulo g is well defined. Reducing the ordinary identity u*(u^n)'=n*u^n gives

    u*(H' mod g)=n*f, f=H mod g.

Because u is a unit, f is a unit. All explicit inputs have degree O(m). Polynomial differentiation, modular multiplication, and guarded fast polynomial inversion therefore acquire w=u H' f^-1=n*1 in soft m residue operations. A nonzero nonunit pivot exposing a proper gcd returns a factor; globally zero pivots must be treated as zeros, not inverted. Under the promise, successful inversion gives the claimed scalar element. An implementation may also verify the computed inverse by one modular multiplication.

The result is n modulo N, not an unrestricted integer discrete logarithm and not the exponent modulo the order of q. Multiplying by d^-1 modulo N gives I modulo N because n=dI. The promised interval 0<=I<=L<N makes I unique as an integer representative even if q has small order. No q-order hypothesis is needed with this STRONGER supplied lift. If endpoint convention enlarges L by a constant, retain that enlarged interval explicitly in an implementation; its size and I<N are unaffected on the prepared branch. Binary powering verifies the candidate reduced power in soft m. The extraction's decisive extra input is H itself, not the verification.

## The reduced element does not provide the needed derivative

For the exact division u^n=f+gQ, differentiating and using u*(u^n)'=n*u^n gives

    u f'-n f+m X^(m-1)u Q=0 modulo g.

This agrees with the report's sign and coefficient. Since m, X and u are units, for each putative n this equation merely determines a corresponding Q modulo g; it does not extract n from f. Differentiation of the canonical representative f sets the actual missing quotient jet to zero and is generally not differentiation of u^n modulo g².

The etale lift is also correctly initialized: y=X-Xg/m has y^m=1 modulo g² and y'=0 modulo g. For an acquired degree-<m f,

    f(y)=f(X)-(Xg/m)f'(X) modulo g²,

so its construction is genuinely soft m, without invoking generic modular composition. Its derivative modulo g vanishes. This verifies the report's positive acquisition claim while explaining why it erases the exponent-bearing normal derivative.

## Natural mixed lift: uniform Q/u mismatch is correct

In U=raw_u^ell*(beta+y^j)^a*sigma_k((beta+y)^N), the two etale factors have derivative zero modulo g, and negative raw ell is legal because raw_u is a unit modulo g² whenever its reduction is a unit. Thus, globally modulo (N,g),

    U'/U=ell/raw_u.

On the own prime p=P, the reductions of the etale factors agree with the original cyclic row. Hence U mod g=u^n with n=aP+Q+ell. The actual raw power has logarithmic derivative n/raw_u, and their difference is

    (n-ell)/raw_u=Q/raw_u modulo (P,g).

Since P and Q are distinct primes, Q is a scalar unit modulo P; u is an algebra unit. Therefore this difference is a unit in EVERY factor of the cyclic algebra over F_P. The mismatch is uniform, not merely a generic example. No assumption on Q<P is needed. The raw-power extractor on U returns ell, not n; dividing by m² leaves the nonzero discrepancy Q/m² modulo P. The report correctly avoids the stronger false assertion that the fully etale lift must differ from the raw power in derivative on every input: n modulo P can vanish.

## Unit and recovery conditions

The inverse certificate for u is correct. Vanishing beta^m+1 in either hidden field would force beta^(2m)=1, contrary to the stated local-order screen. This checks the unit condition under the report's own hypotheses; an unguarded weaker beta assumption would not suffice. The full cyclic norm beta^m+1 and cyclotomic norm (beta^m+1)/(beta+1) are correctly distinguished. The screen also makes beta+1 a unit, so the latter division can be guarded lawfully.

The actual raw lift theorem does not solve native local equality: native coverage supplies T=q^I only modulo one unknown prime, not a global R-algebra promised raw lift. The report consistently preserves this distinction. Generic exact-vector BSGS is a legitimate global promised bounded-log search at soft(m sqrt L)=soft m², including vector storage and comparison costs. If q has small order, it may return any bounded matching exponent; uniqueness is not implied. A local-prime hit may be missed by modulo-N tuple matching.

A scalar-image BSGS branch is soft sqrt L only for a supplied scalar target and appropriate global order/uniqueness hypothesis, followed by full algebra verification. The stated high order of beta does not establish such an order for beta+1 or beta^m+1. A global scalar candidate can fail algebra verification, and a native one-prime equality need not produce a global candidate. Ambiguity or failure cannot certify absence of a native hit. The report correctly declines to import the original beta collision decoder to translated q, and does not count scalar norm processing as a new all-row algorithm.

## Final scope

All-row acquisition remains soft m² in the explicit construction. The soft-m lift extractor is a valid constructive operation under strictly stronger actual-power input; its initialization from native reduced rows is uniformly refuted for the tested mixed lift. The report leaves other observables open, states no all-input lower bound, and claims neither a new query exponent nor N^(1/6) factoring. These qualifications are mathematically faithful.
