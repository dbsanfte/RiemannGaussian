# Joint cancellation of the unpaid wing and a composite companion

Lean now proves an independent bound for the **original unpaid wing plus
one explicit signed composite companion**. This pays a coupled arithmetic
sum, including all of its completion corrections. It does not yet give a
lower bound for the entire remaining carrier.

Write \(M=N+1\), \(s=3/2+i\gamma\), and retain the original physical length
\(L=L_N\), intermediate prime set \(A_N\), and unpaid order set \(U_N\).
Let

$$
b_k(a)=\frac{(\log a)^k}{k!}a^{-s},\qquad
\mathcal R_L(n)=\sum_{d\mid n}\mu(d)(L-\log d)_+.
$$

The complete composite companion is the literal convergent series

$$
T_N=-\frac{M}{L}\sum_{k\in U_N}\sum_{p\in A_N}
\sum_{\substack{a>1\;\mathrm{squarefree},\ a\;\mathrm{composite}\\p\nmid a}}
\mathcal R_L(pa)\,b_k(a)b_{M-k}(p).
$$

Its phases and signed Riesz coefficients are unchanged. The cofactor sum
includes **all** such composites, rather than only the finite carrier band.
The ordered prime/cofactor incidences in this definition are intentional;
no theorem identifies them with one unweighted contribution per integer.

For every fixed \(|\gamma|>1\), Lean gives a constant \(C_\gamma\ge0\)
such that, for every \(1/2\le u<e^{-2/3}\), eventually

$$
\boxed{\left|u^{N+1}(V_N+T_N)\right|
\le C_\gamma(N+1)^2 e^{-N/64}.}
$$

Here \(V_N\) is exactly `ZetaRieszWingHighOrders.unpaidWing`, with its
original taper, physical primes, and factorial orders. The constant is
common across the radius interval; the starting order may depend on the
radius. The constant is not evaluated or proved uniform in height. No zero,
exposure, simplicity, cancellation, or lower-bound premise is used.

The terminal estimate is
[`exists_unpaidWing_add_compositeWing_bound`](../RiemannGaussian/ZetaRieszJointCofactor.lean).
`hasSum_compositeAtom` proves actual convergence, and
`coupledCoefficient_eq_original` identifies the composite coefficient with
the original carrier coefficient after restoring its logarithmic factor.

## How the complete arithmetic sum is bounded

The prime-insertion identity retains the cutoff difference exactly:

$$
\mathcal R_L(pa)=\mathcal R_L(a)-\mathcal R_{L-\log p}(a),\qquad p\nmid a.
$$

Combining the prime and composite cofactor terms exposes a complete
squarefree Euler response. At Cauchy radius \(3/4\), its marked allowance
retains the mark size:

$$
\operatorname{Budget}_{3/4}(\{p\},d)
\le64\tau(d)d^{-3/4}.
$$

The convergent divisor-square series at exponent \(101/100\) then pays the
entire moving marked prefix with cost \(C T e^{13T/50}\), for
\(T=L-\log p\). The outer prime moment is summable at the same reference
exponent. Source normalization absorbs this cost with geometric saving.

The original wing is recovered through an exact identity, with each
correction bounded:

| Term | Estimate and scope |
| --- | --- |
| Complete shifted squarefree cofactor block | \(C_\gamma M^2e^{-M/64}\); fixed eligible height, uniformly over the radius interval |
| Composite saturation correction \(\mathcal R_L(a)\) | Supported on \(\log a>L\); the whole correction is at most \(CM^2e^{-N/64}\), uniformly in height |
| Clipped prime prefix \((L-\log p-\log a)_+\) | The complete prefix has bound \(CM^2e^{-M/64}\), uniformly in height |
| Repeated-prime correction \(a=p\) | A convergent prime-square mass gives \(CM^2e^{-M/64}\), uniformly in height |
| Unit cofactor | Exactly zero at every original unpaid order |

The proof modules are
[`ZetaRieszCofactorCompletionBound`](../RiemannGaussian/ZetaRieszCofactorCompletionBound.lean),
[`ZetaRieszCofactorBoundary`](../RiemannGaussian/ZetaRieszCofactorBoundary.lean),
[`ZetaRieszCofactorPrimeRepairs`](../RiemannGaussian/ZetaRieszCofactorPrimeRepairs.lean),
and [`ZetaRieszJointCofactor`](../RiemannGaussian/ZetaRieszJointCofactor.lean).

## The remaining lower bound

Keep the exact finite lower-count response \(F_j\) in the already proved
window \(7N_j/4<\log n\le9N_j/4\), with every original mask and count bound.
The new arithmetic remainder is

$$
Q_j=u^{N_j+1}(F_j-T_{N_j}).
$$

Lean proves that this differs from the preceding coupled remainder by a
quantity tending to zero. Under the same exposed-zero hypotheses and
\(1/2<u<e^{-11/16}\), it retains the exact source and positive reserve:

$$
Q_j+u^{N_j+1}V_{N_j}^{+}\longrightarrow-m+m^2c(u),
\qquad \Re(u^{N_j+1}V_{N_j}^{+})\ge15m^2/544
\quad\text{eventually}.
$$

The source theorem is `tendsto_arithmeticRemainder_add_reserve`. The
independent cofinal floor for \(Q_j\) remains open. At this earlier stage,
the sufficient margin for a simple exposed zero is \(\eta<1-c(u)+15/544\).

The [exact allocation follow-up](zeta-riesz-joint-allocation.md) now proves
the prime-incidence comparison, pays the complete companion outside the
finite logarithmic window, removes one more actual signed sector, and pays
the entire correction outside the old arithmetic mask. One retained sum
with multiplier `1-theta` remains, and its total reduction error vanishes
uniformly over the real height axis at each fixed eligible radius. This
smaller finite remainder still needs an independent cofinal floor. The full
reserve is now evaluated, strengthening the usable deficit to more than
`3/40`. The [dominant-prime continuation](zeta-riesz-dominant-sector.md)
then pays the unassigned contribution with a prime carrying at least
`13/20` of `log n`, retaining that same exact source on a smaller support.
Neither the old wing nor the companion is separately asserted to vanish.
No new zero-free region or completed RH contradiction follows from this batch.
