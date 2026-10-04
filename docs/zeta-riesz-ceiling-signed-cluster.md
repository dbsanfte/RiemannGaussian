# Signed nearby-cluster payment of the same ceiling

This slice proves the **unchanged native joinedPhysical ceiling in additional
signed-cluster sectors**. Nearby competing zeros may be present, and their
phases may have both signs. The full all-height ceiling in the original fixed
strip remains open. The simple-zero floor is unchanged.

The proof is
[`ZetaRieszCeilingSignedCluster.lean`](../RiemannGaussian/ZetaRieszCeilingSignedCluster.lean).
Every mode is from the actual canonical zeta divisor with its actual analytic
multiplicity. Complete von Mangoldt arithmetic moments supply the inequality.
No density, thinning or synthetic model is substituted for the prime measure.

## Keep the nearby cluster signed

For a candidate $\rho$, write $u=3/2-\Re\rho$, $y=\Im\rho$ and
$m=\operatorname{analyticZetaZeroMultiplicity}(\rho)$. Let $z$ denote its
existing local zero coordinate. Retain the selected-erased nearby aggregate

$$
Q_n(R)=\sum_{\substack{z\in S\setminus\{-u\}\\|z|\le R}}
m_z\bigl(u(-z^{-1})\bigr)^{n+1}.
$$

`competing_eq_nearby_add_far` splits the existing full competing sum exactly.
Only the exterior $|z|>R$ is norm-paid. `far_norm_bound` proves

$$
|Q_n^{\rm far}(R)|\le(H_y+11)(u/R)^{n+1},
\qquad H_y=\log(|y|+22),
$$

using the multiplicity-weighted mass **once**. The nearby sum remains signed;
no termwise absolute value, positive part, cardinality debit or new carrier
appears in the main quantity.

The independent theorem `multiplicity_add_nearby_re_le` gives

$$
\begin{aligned}
m+\Re Q_n(R)\le{}&(2u)^{n+1}+(H_y+11)(u/R)^{n+1}+u^{n+1}\\
&+160u(H_y+H_0)(n+1)(10u/7)^n
 +(H_y+11)(4u/3)^{n+1}.
\end{aligned}
$$

This holds at every logged order, including zero and one. It imposes no
isolation gap, rightmost hypothesis or small analytic-error assumption.
The exterior payment is geometric; the selected source and nearby signed
family are retained exactly.

## Quantitative sector ceiling

Reuse the checked order-4096 test, with

$$
\frac12<u\le\frac{10001}{20000},\qquad
R=\frac{11}{20},\qquad H_y\le10^{150}.
$$

Its right-hand side is strictly below $9/5$. Therefore, if

$$
\boxed{\Re Q_{4096}(11/20)\ge-1/5,}
$$

then $m<2$, and the positive integer multiplicity is one.
`simple_of_nearby_floor` proves this result. It allows a nonempty nearby
cluster and a genuinely negative signed contribution. It does not assume
that every nearby mode is individually nonnegative.

Under the **original exposed-zero hypothesis**, kept as a separate input,
`eventually_joinedPhysical_ceiling_of_nearby_floor` transfers simplicity
through the existing exact source theorem to the same native carrier:

$$
\Re\!\left(u^{N_j+1}\operatorname{joinedPhysical}(u,y,N_j,K_j)\right)
<\frac{42}{25}\quad\text{eventually}.
$$

The signed-cluster floor is a criterion, not an already proved bound for all
actual clusters. The next geometric theorem provides a sufficient condition
that requires no unknown cancellation estimate.

## Constructive modes have zero cluster cost

For $D=a+i b$, $a>0$, the leaf proves the elementary whole-power bound

$$
\left|\left(\frac aD\right)^k-1\right|\le\frac{k|b|}{a}.
$$

Consequently $k|b|\le a$ implies

$$
\Re\bigl((u/D)^k\bigr)\ge0.
$$

`normalized_power_re_nonneg` proves this for every order. It is obtained
before splitting phases or charging individual multiplicities.
Every genuine zero has $a=3/2-\Re\tau>1/2$. Thus at $k=4097$, the uniform
ordinate cone

$$
\boxed{|\Im\tau-\Im\rho|\le\frac1{8194}}
$$

makes that mode constructive, regardless of its real part. Summing any number
of such genuine competing modes with their actual nonnegative multiplicities
keeps the entire nearby real contribution nonnegative. No local zero-count
bound is needed for this part.

If every nearby competing zero lies in that cone,
`simple_of_small_ordinate_cluster` proves actual simplicity; with the same
explicit height and exposure assumptions,
`eventually_joinedPhysical_ceiling_of_small_ordinate_cluster` pays the native
$42/25$ ceiling. The original empty-cluster isolation sector is included, and
nearby constructive competitors are now also allowed.

## The remaining actual opposing population

`multiple_forces_nearby_counterweight` proves that a surviving multiple
candidate in the stated strip and height range must satisfy

$$
\Re Q_{4096}(11/20)<-1/5.
$$

In particular, `multiple_forces_opposing_cluster` supplies a distinct genuine
zero $\tau$ with

$$
\Re\tau\ge\frac{19}{20},\qquad
\frac1{8194}<|\Im\tau-\Im\rho|<\frac14,
$$

whose **exact** selected-normalized phase at power 4097 has negative real
part. It is not enough for a candidate to have an arbitrary nearby companion.
There must be an opposing nearby phase, and the whole nearby signed aggregate
must exceed the negative budget in magnitude.

This is not a rightward successor, an infinite-chain result or a zero-free
theorem. The finite height restriction remains. At unrestricted heights the
order-4096 error may not be paid; and even within the height range, arbitrary
opposing clusters remain unbounded.

The next global estimate must control this actual opposing signed population
or exploit additional complete-arithmetic/remainder structure. Separate
complete-leg limits, changing the moment order after a finite test, and the
free analytic-remainder model are not substitutes for that estimate.

## Numerical regression and preservation

The optional phase probe uses eighteen **synthetic** denominator rows with
integer multiplicities and one fixed logged power. It demonstrates a mixed
positive/negative two-mode packet whose joined real contribution is

$$
-0.0751269705003256\ldots>-1/5.
$$

The stronger signed-sector criterion accepts this model geometry even though
one component is individually adverse. These are not samples of actual zeros
or primes, and this number is not measured unpaid arithmetic mass.

The frozen root-cloud no-go is retained. Exact character bookkeeping puts its
nearby competing sum within $1.025\cdot10^{-164}$ of $-2$ at power4097, so it
still lies in the **unpaid** sector. No cancelling floating sum is used to
reach that conclusion. This checks that the new theorem has not silently
overridden the preceding obstruction.

The producer and independent 420-bit Arb replay are optional, outside ordinary
CI. The leaf and scoped 14-linter/transitive-axiom check run locally. All prior
positive and negative proof/probe bytes are hash-checked and preserved. There
are no commits, pushes, subagents, root registration, public metadata edits or
wider gates in this slice.
