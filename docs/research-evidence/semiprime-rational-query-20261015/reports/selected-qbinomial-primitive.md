# A nearlinear positive primitive for rational pole corrections: selected q-binomial coefficients

2026-10-15. New explicit composite-ring specialization of the classical several-index q-holonomic method. It is a useful sufficient subroutine, NOT a solution of the long target-product query.

## Exact algorithmic statement

Let R=Z/N, q,u supplied units, L>=1 and b=ceil(sqrt(L)). Assume 1-q^a is a unit for every 1<=a<=L. Given any nu public indices k_j in [0,L], the values

    f_(k_j)=u^(k_j) c_(k_j),
    prod_(i<L)(1-Z q^i)=sum_(k=0)^L c_k Z^k,

can be acquired together in soft O(sqrt(L)+nu) ring operations and comparable residue storage, including bit overhead soft O((sqrt(L)+nu)log N) in the normal polynomial-size-index regime. The indices may depend on the actual public N. They are not restricted to a fixed catalog or a geometric progression. Repeated indices are allowed and may simply share the same output; keeping them in the evaluation lists also preserves the stated soft O(sqrt(L)+nu) bound. Indices outside [0,L], if requested under the zero-extension convention, are returned as zero before this algorithm and need no product evaluation.

On the actual source q=gamma^(m²), the retained projected local orders are primes R_P,R_Q>16m² and L<=4m², so q has the same local orders and the stated unit hypothesis holds. This is also available on a certified long route with sufficiently long q orders; it must not be assigned to arbitrary unqualified units q. In the desired regime nu=J=Theta(m), L=Theta(m²), the cost is soft O(m).

## Division-free numerator/denominator streams

The coefficients obey

    (1-q^(k+1))c_(k+1)=(q^L-q^k)c_k, c_0=1.

Define prefix products

    U_k=prod_(i<k)(q^L-q^i),
    V_k=prod_(i<k)(1-q^(i+1)),

so c_k=U_k/V_k for k<=L. All V_k are units by hypothesis. At k=L no problematic numerator endpoint has been used: U_L stops at i=L-1, so q^L-q^i=q^i(q^(L-i)-1) is a unit there as well on the actual branch. The recurrence step to c_(L+1)=0 is not used to acquire c_L. Compute both streams via the following shared prefix-product algorithm; no c_k or collision residual is inverted.

For either degree-one polynomial A(X)=q^L-X or A(X)=1-qX, define

    A_s(X)=prod_(0<=i<s) A(q^i X).

Choose s=b. Build A_b using geometric doubling, degree b, in soft O(b) work. Evaluate it at q^(bt), 0<=t<floor(L/b), by unit-q chirp convolution. Multiplying these block values cumulatively gives every prefix U_(bt) or V_(bt) at cost soft O(b). All q powers and q^L are paid by repeated squaring or sequential generation; no roots of unity or interpolation divisions are needed.

For each selected k_j, start at a_j=b floor(k_j/b), retain the prefix pair there, and represent k_j-a_j in binary. Process bit sizes ell descending from the largest relevant power of two, always ell<b. The block polynomial A_ell has degree ell and can be prebuilt by the same doubling recurrence. At each level evaluate A_ell at the current nu points q^(a_j) using a monic product/remainder tree over R; use the value only when this level's bit is set, then update a_j by ell and multiply the accumulated prefix. Monic polynomial division and remainder trees are valid over arbitrary commutative rings, including repeated evaluation points. The level costs soft O(nu+ell), and the total over O(log b) levels is soft O(nu+b).

This proves the claimed bound for all selected U,V. Batch-invert the nu unit V values with one unit inversion and O(nu) products, then multiply by U and the public powers u^k. An extended-gcd inversion of the combined V is valid under the hypothesis. If that hypothesis is not certified, a proper gcd is a factor and gcd=N is not an inverse; this fallback alone does not establish the claimed general algorithm for arbitrary q.

Every large polynomial operation can use integer Kronecker multiplication, so the algorithm is FFT-root independent over Z/N. For b<=poly(N) the usual logarithmic encoding overhead is absorbed by soft notation. Peak memory can be kept soft O(b+nu), processing refinement levels sequentially. Every supplied discrete index uses O(log(L+1)) bits; q^L and all q^(a_j),u^(k_j) powers cost O((b+nu)log(L+1)) ordinary ring operations by repeated squaring/sequential block generation, absorbed by soft notation. No numerical R_P or R_Q is needed by the algorithm, only the unit/order hypothesis used in its correctness proof. The single combined denominator inversion can use extended gcd; no individual denominator is inverted separately.

## Why this matters for rational certificates

If a valid, composite-safe rational reduction expresses the wanted weighted sum using only O(m) selected coefficient values f_k, known public scalar coefficients, and O(m) ordinary ring operations, then the coefficient-value part of that boundary/pole formula is ALREADY paid soft O(m). It must not be charged as O(m) independent sqrt(L) evaluations: these indices belong to ONE common fixed coefficient recurrence and can share its block construction.

This does not evaluate the row products P_L(z_j). Those are sums of the whole coefficient stream at varying z_j, not selected terms of that stream. Nor does it automatically regularize a rational pole, locate its index, or acquire a derivative/analytic-continuation value. A certificate that requests q-hypergeometric continuation in the index, parameter jets at singular points, or unknown local discrete-log positions needs an additional exact theorem. The positive statement here concerns the explicitly supplied discrete indices and values f_k only.

The complete symbolic certificate construction and its residue coefficients remain unpaid. No small rational certificate reducing the actual Omega(m)-sector remainder to such a bounded correction list was found in this investigation.

## Primary provenance

Bostan–Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*, JSC115 (2023), 96–123:
https://arxiv.org/abs/2012.08656
Section3.4 Theorem6 and its degree-sensitive final paragraph give simultaneous selected terms of one fixed q-holonomic recurrence. Here order and coefficient degree are both ONE, even though L grows. The ring-safe construction above is an explicit specialization, not a blind transfer of a field division/interpolation theorem. The earlier failure to batch changing target recurrences does not apply to this coefficient stream.

This subroutine is compatible with a restriction-stable outer query: public origin/start changes u or the target-weight polynomial, and a requested subinterval length changes L. It pays each permitted invocation separately; it does not infer a fast full weighted-sum program from that compatibility.
