# Concrete wide-owner completion: a checked no-go result

This local test starts from `f3f2f0c94c3b9ef2fe58195b88b7011a6ea3863c`.
It uses the requested radius and completion parameters, without changing
`LocalizedTypeIIBound` or continuing the scalar boundary-renewal route:

$$
\frac12<u\le U=\frac{10001}{20000},\qquad
\theta=\frac{27}{40},\quad \ell=\frac{11}{8},\quad
q=\frac{27}{55},\quad \sigma=1+\frac1{262144}.
$$

For the source coordinate $u=3/2-\Re\rho$, the upper radius corresponds
to $\Re\rho\ge19999/20000$. No zero exclusion in this strip is proved.

**Verdict:** the wider unique-owner allocation has an independently
decaying unallocated remainder. Its natural complete composite companion
does not vanish under the exposed-zero hypotheses. It restores a tapered
prime-product contribution, which remains nonzero even after adding back
the existing reserve. The direct completion test stops at this obstruction.
This does not rule out a future estimate using the retained owner/mask
correction; that correction has not been bounded independently.

## The literal allocation

Write $N=N_j$, $K=K_j$, $L=L_N$, $M=N+1$, and let $A_N$ be the
existing `intermediatePrimes u N`. The integer support is exactly
`tripleBand`: the existing `narrowBand`, including its original masks and
the window $1.95N<\log n\le2.05N$, intersected with squarefree
integers having three prime factors. This covers the exactly-two-reflected-
large sector with threshold $\log p\ge\log n-L$, and also the surviving
balanced three-large triples. No positive triple subfamily is dropped.

The unique owner is the existing `largestPrime n`. The theorem
`owner_mem_intermediate` proves that this owner belongs to $A_N$ on the
actual support. With $a=n/p$, put

$$
I_N=\{k:13N<40k\le27N\},\qquad
w_N(n)=\sum_{k\in I_N}\binom{N+1}{k}
 \left(\frac{\log a}{\log n}\right)^k
 \left(\frac{\log p}{\log n}\right)^{N+1-k}.
$$

The original `boundedShare` is unchanged. Every newly assigned atom keeps
its factor $1-\operatorname{boundedShare}(A_N,N,n)$, full complex phase,
squarefree support, and owner/cofactor coprimality. The exact factorial
atom is

$$
(1-\operatorname{boundedShare})\frac{N+1}{L}
\sum_{k\in I_N}-\mathcal R_L(pa)K_k(s,a)K_{N+1-k}(s,p),
\qquad s=\tfrac32+iy.
$$

`ownerAtom_eq_share`, `ownerCompanion_eq_fibres`, and
`triple_completed_decomposition` prove these are identities of the
actual signed finite carrier, not a replacement of its weights.

## Quantitative gains that passed

All the following are Lean theorems, not floating-point checks.

| Quantity | Checked result | Theorem |
|---|---|---|
| Original completion exponent | `completionExponent u (27/40) (11/8) (27/55) (1+1/262144) ≤ -1/25000` | `completion_rate` |
| Both omitted prime ranges | General completion theorem instantiated through $27N/40$, on its original lower-order domain | `eventually_completion` |
| Owner binomial tails | $1-w_N(n)\le2e^{-N/6500}$ on the actual surviving share interval $[7/20,2/3]$ | `missing_owner_mass`, `owner_share_lower` |
| Unallocated triple carrier | Source-normalized norm at most $2U\,r^N\,\mathrm{MajorantMass}(\sigma)$, where $r=(U/(131071/262144))e^{-1/6500}<1$ | `unallocatedTriples_bound`, `tendsto_unallocatedTriples` |
| Complementary product scale | Actual correlated-order scalar at most $e^{1-N/200000}$ | `wide_product_scalar` |
| Full cofactor-completion error | $\lVert u^{N+1}(W_N+C_N)\rVert\le C_{u,y}(N+1)^2e^{1-N/200000}$, for fixed $\lvert y\rvert>1$ | `exists_wide_completion_bound`, `tendsto_wide_completion` |

The unallocated-triple bound is uniform for arbitrary moving heights.
The last bound pays the shifted cofactor response, saturation boundary,
clipped prime prefix, and repeated-prime diagonal. It does not pay removal
of the ownership or allocation masks. The correlated total order $k+l=N+1$
is essential to the product estimate.

`eventually_wide_weighted_error` also pays the small-prime prefix and the
derivative successor on $N\le4k$, $250k\le169N$. This auxiliary phase
range does not enlarge the actual allocation beyond $27N/40$.

## Where completion puts the source

The completed companion includes all coprime squarefree composite cofactors:

$$
C_N=\frac{N+1}{L}\sum_{k\in I_N}\sum_{p\in A_N}
 \sum_{\substack{a\text{ squarefree composite}\\p\nmid a}}
 -\mathcal R_L(pa)K_k(s,a)K_{N+1-k}(s,p).
$$

The exact completion identity restores

$$
W_N=\sum_{k\in I_N}(N+1)P_k(s)
 \operatorname{taperedMoment}_{A_N,N+1-k}(s,L),
\qquad u^{N+1}(C_N+W_N)\longrightarrow0.
$$

Here $P_k$ is the existing complete factorial prime moment, not a
bounded surrogate. Under the same strictly exposed nontrivial-zero
hypotheses as the original carrier, its weighted phase tends to $-m$,
where $m$ is the positive analytic multiplicity. Independent completion
transfers that phase to the needed finite prime moments. The endpoint
taper stays below one, so `eventually_re_wide_atom` proves a positive
contribution for every order in the proposed band.

The terminal obstruction theorems prove, eventually,

$$
\Re(u^{N+1}C_N)\le-\frac{m^2}{40},\qquad
\Re\bigl(u^{N+1}(C_N+\operatorname{reserve}_N)\bigr)
 \le-\frac{m^2}{5000}.
$$

These are `eventually_re_wideComplete_le` and
`eventually_re_wideComplete_add_reserve_le`.
`not_tendsto_wideComplete_add_reserve` proves nondecay on the actual
dyadic source schedule. No simplicity hypothesis is needed for these
obstructions. They are conditional consequences of the explicitly stated
zero and exposure hypotheses, not assertions that such a zero exists.

## The retained correction and exact scope

Let $E_N$ be `ownerCompletionCorrection`: the complete cofactor sum
minus the finite unique-owner fibres with their original allocation
multiplier. This definition displays the difference inside every order
and prime row. The exact identity is

$$
T_{3,N}=C_N-E_N+U_{3,N},\qquad u^{N+1}U_{3,N}\longrightarrow0.
$$

`narrow_completed_decomposition` embeds this equality in the full actual
narrowed response, retaining the other prime-count classes as a signed
finite sum. No claim $u^{N+1}E_N\to0$ is made. In particular, the theorem
does not identify the uniquely owned companion with the unmasked complete
series. The negative complete contribution cannot be counted as a newly
paid error or as cancellation supplied by the old reserve. Estimating

$$
\text{other prime-count classes}+C_N-E_N
$$

still requires an independent signed arithmetic estimate. The original
Type-II target and the RH/zero-free frontier remain unchanged. The
positive result of this test is the rigorous geometric control of the
unallocated triple mass; the negative result is the explicit nondecaying
completion cost. No historical novelty claim is made.

## Checked sources

- [Concrete rates and literal allocation](../RiemannGaussian/ZetaRieszWideOwnerAudit.lean)
- [Full complementary completion budget](../RiemannGaussian/ZetaRieszWideCompanion.lean)
- [Wide-order signed prime phases](../RiemannGaussian/ZetaRieszWidePhase.lean)
- [Exact carrier decomposition and terminal obstruction](../RiemannGaussian/ZetaRieszWideOwnerObstruction.lean)
