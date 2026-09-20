# The full dominant-prime sector is now paid

The exact retained carrier has a new independent arithmetic bound. After
the earlier wing/companion coupling, Lean pays every remaining term with
an eligible selected prime carrying at least `13/20` of the total logarithm.
This extends the previous bounded sector
`21/32 <= log(p)/log(n) <= 47/64` and removes its upper endpoint.

The source remains in a smaller original signed sum. On its nonzero
support every prime factor satisfies

$$
\log p<\frac{13}{20}\log n.
$$

The independent cofinal signed floor is still open. No restricted zero
exclusion or new zero-free region follows from this component estimate.

## The actual arithmetic bound

Keep the physical length `L_N`, selected prime set `A_N`, original mask,
count schedule, and exact allocation fraction `theta_N(n)` from
[the allocation ledger](zeta-riesz-joint-allocation.md). Let `D_N` be the
newly deleted subset of the previously retained support. Its atoms remain

$$
(1-\theta_N(n))c_{L_N}(n)b_N(n),\qquad
b_N(n)=\frac{(\log n)^N}{N!}e^{-(3/2+iy)\log n}.
$$

Put

$$
\sigma_*=\frac{12001}{12000},\qquad
r_H=\frac{503}{1000}\frac{12000}{5999}e^{-1/160},\qquad
r_L=e^{-1/2000}.
$$

`rates_bounds` proves `0 <= r_H,r_L < 1` using exact rational and
exponential inequalities. For every `N>=320`, every prime-count cutoff
`K`, every real height `y`, and `1/2<=u<=exp(-11/16)`,
`dominantSector_bound` proves

$$
\left|u^{N+1}\sum_{n\in D_N}(1-\theta_N(n))c_{L_N}(n)b_N(n)\right|
\le (r_H^N+r_L^N)\,\mathcal M(\sigma_*).
$$

Here `M(sigma)` is the existing genuinely summable divisor-majorant mass
`zetaMoebiusLogMajorantMass sigma`. It is independent of the height,
count cutoff, radius and order. It is not numerically evaluated. The
bound concerns the **unassigned coefficient after the signed coupling**;
it does not assert decay of the same integers with their unallocated
original coefficients.

## The correlation that pays the missing endpoint

For a selected prime divisor, set `x=log(n/p)/log(n)`. The unpaid allocation
orders are exactly `k<=floor(13N/32)` and `5(N+1-k)<4N` after order 320.
The new bound keeps both missing tails:

$$
1-\sum_{k\in U_N}\binom{N+1}{k}x^k(1-x)^{N+1-k}
\le \frac{87}{80}e^{-N/160}
+e^{(N/5+1)\log(6/5)}(1-x/6)^{N+1},\qquad 0\le x\le\frac7{20}.
$$

The first term is a conventional binomial-tail saving. The second is
**not** replaced by a uniform small coefficient. It stays coupled to the
actual factorial kernel. The same selected prime has `log(p)<=L_N`, so

$$
(1-x/6)\log n=\frac56\log n+\frac16\log p
\le\frac56\log n+\frac16L_N.
$$

Applying the exponential factorial envelope at tilt `5999/10000` leaves
the summable exponent `12001/12000`. The proved physical length bound
`L_N<=139N/100`, combined with source scaling and the exact missing-order
threshold, yields `r_L^N`. Keeping this cutoff correlation pays the entire
upper prime-log endpoint, where the allocation fraction alone need not be
close to one.

## The current contradiction target

`nondominantBand` deletes only this newly bounded sector from the previous
retained band. No original mask, phase or signed coefficient is changed.
`nondominant_prime_log_lt` proves the displayed prime-log cap for every
nonzero coefficient from dyadic index 32 onward. The support itself supplies
squarefreeness, at least three prime factors, the count ceiling, prime
coprimality, and both selected-prime cutoff conditions. These are proved,
not added as unverified conditions on the actual source.

`tendsto_arithmetic_sub_nondominant_moving` pays the complete aggregate
reduction error for arbitrary moving heights. Under the original exposed-zero
hypotheses and `1/2<u<exp(-11/16)`, `tendsto_nondominant_exact_source` gives

$$
R_j^{\rm nd}\longrightarrow-m+m^2c_{\rm ret}(u),\qquad
c_{\rm ret}(u)=\frac{\log(32/13)}{-2u\log u}-\log(19/13)<\frac{37}{40}.
$$

For a simple exposed zero the real part is eventually below `-3/40`.
An independent cofinal floor `Re R_j^nd >= -3/40` would contradict that
source. The remaining sum still includes balanced products, the signed
Riesz divisor sum, all lower prime counts together, the factorial envelope,
the full phase, and the nonnegative unassigned fraction. The prime-log cap
does not supply their signed floor by itself.

Sources:
[allocation tails and cutoff scalar](../RiemannGaussian/ZetaRieszDominantAllocation.lean),
[the complete arithmetic sector bound](../RiemannGaussian/ZetaRieszDominantSector.lean),
[support and exact source](../RiemannGaussian/ZetaRieszNondominantCarrier.lean).

The [current explorer](https://dbsanfte.github.io/RiemannGaussian/rh-proof/)
ends at the exact source on this smaller support. Its
[dominant-prime view](https://dbsanfte.github.io/RiemannGaussian/rh-proof/#endpoint=dominant-prime-sector)
links the independent bound, support theorem, complete error transfer and
source-forced deficit. The [compiled proof audit](rh-proof-explorer/audit.json)
records the transitive axioms; the independent signed floor remains open.
