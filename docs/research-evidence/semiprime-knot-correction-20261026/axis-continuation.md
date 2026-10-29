# Axis continuation: a sufficient nonaxis threshold and paid branch

26 October 2026. The axis loophole can be closed by an explicit stronger small-factor branch, but its current paid cost is soft(k^(5/4)), so it absorbs the nonaxis character sieve's subpower saving. No soft-k axis discharge is established.

## 1. Nonaxis replacement after an exact factor-size threshold

Let P<=Q be the actual factors and gamma2=2/sqrt(3), the rank-two Hermite constant. For the native lattice aP²=bN mod k, use the *virtual* Euclidean scaling

    (a,b)->(aP²,bN).

Its determinant is kP²N. A shortest nonzero vector has squared norm at most gamma2*k*P²*N. The shortest horizontal axis vector has squared norm k²P^4, and the shortest vertical axis vector has squared norm k²N². Since P²<=N and k>gamma2, the vertical axis cannot be shortest. The horizontal axis cannot be shortest when

    kP²>gamma2*N,
    equivalently 3k²P^4>4N².                            (1)

Thus beyond (1) a genuinely nonaxis native witness exists. Its product satisfies |ab|<=k/sqrt(3)<k. Also

    |a|P+|b|Q <=sqrt(2gamma2*kN)<4sqrt(kN),

so the already licensed native clock horizon M covers it. No algorithm needs to know P or compute this virtual vector: the complete native catalogue already contains it. Public exact-zero deletion, complete swaps, central processing and the half-center opposite fold preserve the witness as in the authoritative proof.

This supplies an exact arithmetic sufficient condition for replacement, rather than assuming the axes form O(1) rows. It is not claimed to be a necessary or sharp threshold for all nonaxis witnesses. It uses no dyadic-bin loss because the complete scalar catalogue has no algorithmic factor-size mask; the unknown exact P scaling is used only in the existence proof.

## 2. Paid stronger branch

Acquire the public integer

    T=ceil[(4N²/(3k²))^(1/4)].

It can be computed by integer fourth-root and rational comparison. Run a bounded small-factor search through T. If it finds P, finish. If it certifies no factor <=T, then the actual P>T satisfies (1), and ALL axis rows may be discarded from the coverage source. The continuing nonaxis source retains a common-index swap witness, so its zero-only endpoint is guaranteed, not merely a one-prime nonunit.

A standard division-free factorial/product-tree small-factor search through T costs

    soft(sqrt(T))=soft((N/k)^(1/4))=soft(k^(5/4))

at N=Theta(k^6). Here T<sqrt(N) for large k, so if a factor appears, the other prime is above T; the bounded integer product's gcd is proper rather than saturated. This is a fully paid coverage-safe axis discharge, but it does NOT make the whole algorithm inherit the nonaxis subpower improvement. Calling a known faster full factoring algorithm in this branch would already solve the entire instance and is not counted as progress for this constructor.

Without this branch, a nonaxis vector such as the known first Euclidean row (g,1) always exists, but its physical sum can require a clock as large as O(k²) on the present hard factor-size range. It is not a replacement within the old O(k^(3/2)) horizon with the desired support cost. No shorter replacement theorem is supplied by its mere existence.

## 3. Why the proposed local discriminant sieve does not filter axes

For an axis a=k,b=0, lambda=tk, the physical equation is P=kI-t (with the exact harmless sign/phase convention retained per row). The candidate discrimination condition is automatically square: T=aP, and (aP)^2-4abN=(aP)^2. This explains the degenerate character counts in conic-character-filter.md.

Trying to add PQ=N modulo an auxiliary prime ell does not create a new quadratic obstruction. For any candidate pbar!=0 modulo ell, there is exactly the compatible residue qbar=N/pbar, and

    (pbar+qbar)²-4N=(pbar-qbar)² mod ell.

Thus the semiprime discriminant is automatically square at every locally invertible axis candidate as well. A safe local prime-factor filter can reject pbar=0 when the candidate exceeds ell; it removes only one residue out of ell. It cannot be charged as the one-half-density conic filter. Exact integrality N/(kI-t) in Z remains a divisor test, not a newly acquired local character condition.

The known root-coset collapse of the O(k) axis phases is still useful: with rho=beta^k and q=rho^k, complete portions become one finer-base scalar orbit of length Theta(km), with the previously documented deleted-row boundaries handled explicitly. Its initialized evaluation costs soft(sqrt(km)), equal to soft(k^(5/4)) at m~k^(3/2). The facts rho^k=q and large order do not reduce that length to m or turn rho into an auxiliary root of unity.

## Outcome

There is an exact threshold and a legal paid branch after which all remaining coverage is nonaxis, and then the collective character filter applies to the whole continuing source. The threshold branch itself currently retains the old soft(k^(5/4)) cost. A genuinely cheaper bounded-factor search through T, or a stronger nonaxis short-witness theorem below (1), is required to convert the nonaxis sieve saving into a whole-instance improvement within this route.
