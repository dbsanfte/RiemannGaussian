# A geometric payment for phase alignment across all radial periods

This local slice bounds a new part of the ACTUAL whole signed energy.
It does not introduce a new arithmetic carrier, count-specific allowance
or independent energy hypothesis. The complete one-sided floor remains open.

## The exact paid pair family

Write

\[
 \epsilon_{N,y}=\frac{e^{-N/1000}}{1+|y|},\qquad
 Q_{N,y}=4(\lceil|y|\rceil+1)(N+1).
\]

Two labels belong to the phase band when some integer \(|k|\le Q_{N,y}\)
satisfies

\[
 \left|\log n-\log m-\frac{2\pi k}{y}\right|
 \le\epsilon_{N,y}.
\]

`phaseNear_of_resonance` proves that the finite union contains EVERY
phase period possible on the original finite label range. It has no
prime-count restriction. The log tolerance is exponentially small;
this result does not pay a fixed or polynomially shrinking phase window.

`orbitEnergy` selects these pairs ONLY inside the previously unpaid
`separatedEnergy`. Large common factors, nearby labels and the diagonal
are still paid by the earlier theorems. `separatedEnergy_eq` is the exact
disjoint partition into `orbitEnergy + nonOrbitEnergy`, using the SAME
original adverse cutoff selection, weights and phase. The latter aggregate
remains signed. No adverse selection is repeated after the partition.

## Why different periods have the same sparse capacity

For actual positive integers in a log interval of width \(2\epsilon\),
`log_band_reciprocal` proves

\[
 \sum_{|\log m-a|\le\epsilon}\frac1m
 \le4\epsilon+e^{-l}
 \quad(m\ge e^l,\ 0\le\epsilon\le1/4).
\]

The second term is the retained integer endpoint error. The reciprocal
capacity does not depend on the interval's multiplicative position.
A raw neighbour count would lose that property at distant periods.

`symmetric_reciprocal_capacity` keeps this reciprocal row capacity when
joining the pair weights. On the existing literal window it yields

\[
 \sum_{\text{phase-band pairs}}
 \frac{\tau(n)\tau(m)}{nm}
 \le5C_y(N+1)e^{-N/1000}
       e^{\log X/262144}M(1+1/262144),
 \quad C_y=8(\lceil|y|\rceil+1)+1.
\]

Here \(M\) is the repository's finite divisor-square Dirichlet mass.
This is a sparse-incidence estimate, not an inference of bin orthogonality,
a prime-density completion, or a signed bound on the entire remainder.

## The actual source-normalized energy saving

For all original weights

\[
 w_n=u^{N+1}q_n\,\mathrm{primeWeight}(A,L,y,N,n,1),
 \quad |q_n|\le B,\quad L\ge1,\quad u\le10001/20000,
\]

and the existing endpoint bound \(\log X\le3(N+1)\),
`weighted_orbitEnergy_bound` proves

\[
 |E_{\mathrm{orbit}}|
 \le C_{B,y}(N+1)^4e^{-N/2000},
\]

where exactly

\[
 C_{B,y}=80(10001/20000)^2B^2 C_y
            M(1+1/262144)e^{3/262144}.
\]

The actual squared source growth is included. The corresponding whole-floor
price is at most

\[
 \sqrt{4C_{B,y}}(N+1)^3e^{-N/4000}\longrightarrow0.
\]

The constant depends on the FIXED height and is not numerically evaluated.
This is not a uniform statement for arbitrarily moving heights or an
effective starting-order certificate.

## Applied to the unchanged funded ledger

`eventually_joined_nonOrbit_floor` gives, on the original dyadic schedule,

\[
 \Re[u^{N+1}\mathrm{joinedPhysical}]
 \ge-\sqrt{(129N/200)\max(E_{\mathrm{nonOrbit}},0)}-e_N,
 \qquad e_N\to0.
\]

The SAME supply witness, fixed positive epsilon, tail/growing debit,
all support overlaps and earlier diagonal/shared/near errors remain once.
There is no additional supply credit and no low-order allocation deletion.

The independent bound on `nonOrbitEnergy` is OPEN. For example,
the already checked sufficient budget \(3/[320(N+1)]\) would still give
a floor \(-0.078-o(1)\), stronger than the required \(-0.079-o(1)\).
This slice does not prove that budget or the sign of `nonOrbitEnergy`.
Its exponentially decreasing separation is not fixed-height orthogonality.
Removal of a negative pair family can increase a finite remaining cost;
no universal monotonic improvement is asserted.

## Optional finite diagnostic and validation

`scripts/probe_riesz_phase_orbit_energy.py` keeps the rational radius,
exact integer moving cutoff, actual divisor columns, phase and all selected
counts. At orders4/5 the allocation support is exactly empty. The probe
checks reciprocal capacity and the complete signed partition before any
one-sided cost. Physical/many-bin/dyadic and funding-witness conditions
are not certified; the output is floating and outside ordinary CI.

At these small orders the ORIGINAL exponential near-label strip already
contains every smaller-gcd pair. Its native residual energy is therefore
zero. The nontrivial comparison uses a separately labelled rational
1/1000 distance strip, which is diagnostic ONLY. In all six test cases
its phase-band part is positive and its outside-band part is negative;
two costs strictly decrease and four were already zero. No eventual
outside-band sign or independent arithmetic floor follows.

Focused Lean warnings-as-errors, root import, namespace lint and all-public
transitive axioms are recorded in `riesz-phase-orbit-payment-audit.json`.
No new zero exclusion, whole floor or ceiling is claimed.
