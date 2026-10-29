# Root review: collective character sieve and axis continuation

26 October 2026. Reviewed the two scratch reports by direct algebra and
counting. PASS for their stated complete-nonaxis-catalogue operation and
the sufficient axis-discharge branch. No whole-instance improvement or
sixth-exponent theorem follows. No numerical tests were used.

## Exact residue counts

For `f(I)=H I^2-2 lambda I+(lambda^2-4abN)/H`, the discriminant is
`16abN`. At a selected prime ell>3 not dividing N, H is a square unit.
If ell does not divide ab, completing the square gives
`sum_I chi(f(I))=-1` and `#roots=1+chi(abN)`. Thus the number of square
or zero values is `(ell+chi(abN))/2`. If ell divides ab, the discriminant
is zero and the polynomial is a square, so all ell residues must remain.
No randomness or distribution premise about the unknown factors is used.

At a true witness, `aP=bQ mod k`, so the reported quotient
`(aP-bQ)/k` is an integer and `f(I)` is its square. Swapping a,b changes
neither ab nor lambda; it must inherit the same physical interval and
mask. Therefore the two-prime common-index witness survives. Working on
the original signed catalogue avoids assuming that a newly filtered
one-sided knot polynomial has unchanged predicates.

## Complete-catalogue density and acquisition

The row-count estimate is valid for this catalogue. Factor `|ab|=u*v`,
where u is supported on 2,3 and v is coprime to 6. Its number of uncentered
conic phases is bounded by a constant times sqrt(u); ordered coefficient
pairs contribute tau(u)tau(v). For squarefree D coprime to 6, summing
`v=Dw` gives

    O(k*tau(D)*log(k)/D) * sum_u tau(u)/sqrt(u).

The final sum converges as a product of two geometric derivative sums.
The estimate also covers D>=k, when the relevant catalogue is empty.
Summing `2^omega(gcd(|ab|,L))` by divisors gives precisely the reported
Euler product. Primes of size Theta(log k) make its excess over 1 bounded.
This proves the collective upper bound without assuming uniformly
distributed a,b or independent character signs.

The common modulus is essential. Explicit per-prime tables take soft(k)
work; CRT expansion costs soft(sum A_j), including intermediate lists
because every extension has at least one allowed residue. Intersecting
each list with a physical window gives a known AP with common ratio q^L.
Its count is at most `h_j*A_j/L+A_j`, including clipped endpoints.
Consequently the original variable-window evaluator pays

    soft(k + k*L*2^(-t) + sqrt(k*(M+L)*2^(-t))).

The same fixed masks may be clipped at each prefix. First-zero
localization still returns an original leaf with its original nonzero
integer exponent. One must retain the row, residue, AP start and local
index to reconstruct that label. No division by a collision value occurs.

With `t=(1/4-o(1))*log k/loglog k` and the report's explicit margin,
`log L <= (1/4-1/sqrt(loglog k)+O(1/loglog k))*log k`.
Thus mask construction is below the square-root term, and that term has
the claimed factor `exp(-(log(2)/8+o(1))*log k/loglog k)`.
Polylogarithmic costs are absorbed by the o(1) term. This changes no power
exponent and is asserted only for nonaxis rows.

## Axis branch and precise scope

The virtual lattice has determinant k after the congruence and determinant
`k*P^2*N` after scaling `(a,b)` to `(aP^2,bN)`. The rank-two Hermite bound
therefore excludes a shortest horizontal axis when `kP^2>gamma2*N`,
and excludes the vertical axis for P<=Q and k>gamma2. The resulting
nonaxis vector satisfies `|ab|<=k/sqrt(3)` and
`|a|P+|b|Q<=sqrt(2*gamma2*k*N)`, within the original horizon.

The condition `3k^2 P^4>4N^2` is a proved **sufficient** condition,
not a necessary threshold for all nonaxis coverage. Calling it an exact
threshold refers to its exact arithmetic expression, not sharpness.
Integer comparison permits a safe public ceiling T. A bounded factor
search through T either finishes or certifies the condition for P.
Because T<sqrt(N), its full integer-product gcd cannot contain both
distinct prime factors. The existing bounded-search cost is soft(sqrt(T)),
which equals soft(k^(5/4)) at the stipulated sixth-root scale.

The square-residue sieve itself has density 1 on axis conics. Introducing
the local equation pq=N does not halve that density: every nonzero p
determines q=N/p and has square semiprime discriminant. A prime-factor
wheel can exclude p=0 modulo ell, which is only a 1/ell exclusion here.
The previous root-coset collapse also retains length Theta(km).

Accordingly the reports supply a paid collective operation plus a fully
specified baseline-cost completion. They do not establish soft-k
acquisition, a faster whole-instance factoring algorithm, a universal
axis impossibility theorem, or a lower bound against other filters.
