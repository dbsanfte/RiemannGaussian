# Odd-axis phase recursion: exact shared law, unacquired seed vector

26 October 2026. Bounded paper pass; no implementation, examples, tests, repository edits or Lean. **No faster useful-residue supplier obtained.** The exact finite phase recursion below has certified short-start pivots, but still requires a long seed vector. Its initialized acquisition retains soft sqrt B. This is not a lower bound for another supplier.

Inputs: current projective packet axis-controller.md (including arbitrary-alias transport), the prior string-supplier multisection.md, and the already audited Bostan–Yurkevich geometric-factorial baseline. No new smooth-order or order-coprimality gate is assumed.

## 1. Reduce the ACTUAL odd-axis support to one punctured interval

Use n=k/2, rho=beta^k, u=rho^2 and M=M_B=ceil(B/k)+1. The actual odd phases t=1,3,...,k-1 give r=(t+1)/2 in [1,n]. Their axis exponent is e=t+1-kI=2(r-nI). Consequently h=r-nI, I in [-M,M], tiles exactly once the consecutive integer interval

    A=1-nM <= h <= D=n(M+1).

The original punctured axis product is therefore exactly

    Z_axis=product_(h=A..D,h!=0)(1-u^h).          (1)

It is a scalar equality for this specified axis query, not a completion of a smaller colour family. No phase carry is dropped. The sole literal deletion is h=0. The total length is n(2M+1)=O(B+k), with signed start A. All nonliteral h give nonzero O(log N)-bit beta label 2kh; every located alias has the existing proper-gcd or once-only T_ext route. The smaller-factor stationary witness is h=(1-P)/2; no assertion that an arbitrary located phase equals -P is used.

There is also a zero-safe signed-endpoint simplification. Let Q_s(u)=product_(h=1)^s(1-u^h). Reflection of the negative part gives the NUMERICAL identity

    Z_axis=(-1)^(nM-1) u^[-(nM-1)nM/2]
                      *Q_(nM-1)(u)*Q_D(u).

Since nM-1<D, the smaller prefix divides the larger as a polynomial product. Therefore Z_axis and Q_D have exactly the SAME zero/nonunit predicate at each prime, without asserting the smaller prefix is a unit or dividing its numerical value. A negative hit reflects to a positive h<=D, which is itself an included original odd-axis leaf. This allows the supplier to work on a positive prefix with honest short starts. It is only a constant-size simplification; the unknown order and sqrt B scalar scale remain. Any located positive h supplies its OWN actual phase t=2h-1 mod k through the unique tiled source map.

For each odd m=3^a dividing k, the exact residue dictionary is

    h=(t+1)*2^-1 modulo m.

A useful residue for (1) supplies the licensed kernel b=0 residue, with the short axis cap exactly as in axis-controller. The complete old universal-kernel W interval must not silently replace that cap.

## 2. Execute the shared phase recurrence, including all starts

For residue r modulo m, split [A,D] intersect (r+mZ) at zero before multiplying. Each resulting interval is a supplied geometric factorial. Their lengths differ by at most one before the possible zero split, and their starts are explicitly acquired in soft m. A single residue has old cost soft sqrt((B+k)/m), plus its legal recovery.

Using the positive-prefix predicate reduction above, residue starts can be chosen r=1,...,m with at most two lengths. To expose the proposed SHARED recurrence, first take a common unpunctured length ell and define

    P_r=product_(j=0..ell-1)(1-u^(r+mj)).

Direct cancellation, kept cleared, gives

    (1-u^r)P_(r+m)=(1-u^(r+m*ell))P_r.           (2)

A length ell+1 or a signed finite start changes only its explicitly retained endpoint factor. A puncture changes (2) by the corresponding directly removed literal factors; it must not be implemented as division by 1-u^0. Alternatively use the two direct interval products above, which need no puncture inversion.

For 1<=r<=m<=k, the factor 1-u^r is a certified unit: ord_p(u)=ord_p(rho)>=ord_p(q)>16H, since rho has odd local order and u=rho^2. Thus (2) genuinely advances within ONE residue channel without singular short-start pivots. If the other endpoint is nonunit, it is a legal explicit-label event rather than a divisor to cancel.

But the step in (2) is m, not 1. Its initialized value vector is the m long products P_1,...,P_m (up to the known physical starts), not m known constants. Endpoint factors do not select a useful seed component. The equivalent functional equation

    (1-Z)P(u^m Z)=(1-u^(m*ell)Z)P(Z),
    P(Z)=product_(j=0..ell-1)(1-u^(mj)Z),         (3)

has exactly the same issue when evaluated at Z=u^r. P(0)=1 is not an evaluated nonzero-orbit seed.

The inherited joint monic block algorithm acquires these m seed values, including the at-most-two length groups and literal splits, in

    soft O(m+sqrt(m*(B+k)/m))
       = soft O(m+sqrt(B+k)).                   (4)

This is an initialized upper bound, not an oracle charge hidden in the state. Base-three child splitting is the exact product identity that partitions a channel into its three residue children; it supplies no child value before that child's product is evaluated. Following nonunit children restores the same first-coarse-query cost soft sqrt B, as in the prior multisection audit. It does not become cheap by writing all children in one q-holonomic state.

## 3. Adams/multiplication identities: which index gets changed?

For any finite interval and any auxiliary complete Sth-root phase set, the polynomial identity is

    product_(zeta^S=1) product_h(1-zeta*u^h)
           =product_h(1-u^(S*h)).                (5)

For S a power of two, all nontrivial phase factors are units in the appropriate etale algebra: u has odd local order, and cannot equal a nontrivial 2-power root. Thus simultaneous powering is a certified zero/nonunit-equivalent replacement without acquiring the unit correction numerically. Iterated squaring of the base is cheap.

Equation (5), however, keeps EXACTLY the same h interval and residue-selection problem. Clock dissection instead has the different identity

    product_(h=A..D)(1-u^h)
       =product_(r mod m) product_(h=A..D,h=r modm)(1-u^h),

with the literal omission applied directly. It retains all m channels. Combining the two operations changes the base to u^S in every still-unacquired seed; it does not replace the channel product by a chosen component. The algebraic distinction matters even though both formulas are called multiplication or Adams relations.

For odd S, nontrivial rotated factors are NOT automatically units under the prepared contract. Even an additionally supplied gcd(ord_p(u),m)=1 gate would not identify the inverse of m modulo either hidden order. Such an inverse could rebase the SAME cyclic group, but its values and literal interval mapping are not supplied by coprimality, and full unknown-order cyclic closure cannot be used to shorten the physical query. No such gate is imported here.

## 4. Leading statistics do not initialize these channels for free

Regularize (1) by 1-(1-delta)u^h. Locally the first delta order is the number of nonzero multiples of ord_p(u) in [A,D]. Since that order exceeds 16H, the number is O(1+B/H), but it need not be one. A phase-marked first slice records their residues, exactly as the preceding general finite-weighting packet records hit rows.

The existing univariate reverse-AD/slice algorithm can compute such statistics once an actual product circuit is run, with precision cost multiplying its acquisition. It does not remove the soft sqrt B root test. Reverse differentiation of an endpoint-normalized recurrence merely differentiates the still-unknown P_r seeds. Finite Ward differences similarly transport shifted leading slices and their endpoints, rather than supply their amplitudes.

If a hidden local order d were supplied, counts or selected residue multiples could be computed arithmetically; that is NOT a useful new supplier interface, since q^d-1 (or the corresponding u^d-1) already gives a nonunit and the existing extraction route. The sought missing data is genuinely a useful phase child or equivalent order-free original-leaf statistic, acquired without first evaluating a long seed. Neither (2), (3), nor (5) supplies that datum.

## 5. Primary baseline and scope

[Bostan–Yurkevich, section 2.1, Algorithms 1–2](https://arxiv.org/html/2012.08656#S2.SS1) gives the initialized geometric-factorial baby/giant computation. Their [section 3.4, Theorem 5](https://arxiv.org/html/2012.08656#S3.SS4) explicitly charges growing coefficient degree/rank; a nominal constant-state or shared-index recurrence is not a rank-independent initialization theorem. These sources were checked in the preceding singular-recurrence pass and are PRIOR baseline credit. Equations (1)–(5) here are proved by finite index manipulation, not by importing an infinite quantum-dilogarithm evaluation or a root-of-unity value for actual u.

No supplier cheaper than sqrt B, no uniformly covering small residue palette, and no new complete factoring rate is established. The exact first unpaid operation in this attempted route is evaluation/selection of a useful component of the long seed vector in (2)–(4). This is a scoped failure of that initialized recurrence handoff, not a general lower bound on quantum-dilogarithm, knot or arithmetic algorithms.
