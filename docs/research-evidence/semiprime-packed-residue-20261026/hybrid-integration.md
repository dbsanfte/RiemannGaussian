# A single canonical moment in the acquisition hybrid

26 October 2026. Root integration, independently reviewed by the q-holonomic
and skein agents. This is a paper sufficiency theorem under the existing
prepared-family and restricted-HH contracts. It is not an acquisition
theorem or a completed sixth-exponent bit proof.

## 1. Exact scope and input

Use the original beta-coupled Gauss family, one row per unit j modulo
K=2*3^e, e>=3, and its original finite physical clock. The prepared hard
branch has N=PQ<=K^6, P<Q, P,Q>16H with H=K^2. Put

    n=3^ceil(e/2), D0=3^floor(e/2), n*D0=K/2,
    u_j=[j^2]_n in {0,...,n-1}.

Every good-field hit in a correct bin has j=R mod n. Exactly D0 unit
colours modulo K lift that residue. One hit per row therefore gives
1<=d<=D0, including axes and nonprimitive rows. This is the sharper
multiplicity theorem from the
[six-domain report](../semiprime-six-domain-acquisition-20261026/README.md).
It does not cover a catalogue with several rows per colour.

Fix r in {1,2,3}. Suppose the ACTUAL algebra element

    M_r=Res_delta sum_(j,i) u_j^r/(delta+1-T_j*rho^i)

has been acquired, or a preceding guard has returned a verified factor.
The power is taken AFTER forming canonical integer u_j. At the nonsplit
prime R, possibly the larger factor,

    M_r = c mod R, c=d*u^r, u=[R^2]_n, 1<=u<n.

Then a factor of N can be recovered in soft O(K) bit operations from a
correct-bin input; a wrong-bin input costs the same and may return bounded
failure. Continue over all factor-size bins.

## 2. Recover the bounded integer without knowing R

Set M=D0*n^r=(K/2)n^(r-1). Since n^2<=3K/2,

    0<c<M<=3K^2/4<16H<P,Q.

For r=1, M=K/2. Write the acquired element as c0+c1*tau with canonical
coordinates. Since the good nonsplit reduction is scalar, R divides c1.
A proper gcd(c1,N) factors. A gcd of one rejects only a wrong bin. On
continuation gcd=N and the acquired element is globally scalar.

If 0<=c0<M, then c0=c in a correct bin. Otherwise put b=ceil(sqrt M) and
form the monic polynomial F(X)=product_(v<b)(X-v). Evaluate it at c0-bs
for s=0,...,b-1. These blocks cover the difference c0-c. Product and monic
remainder trees cost soft b, without inverses of point differences.
All padded integers are below b^2<=4M<16H, hence below BOTH primes.

A proper gcd of a block value factors. Inspect at most one saturated
block, containing b leaves. Either a leaf gives a proper factor or a
globally zero difference gives c0=a as canonical integers. Because a,c<R,
their congruence forces a=c in the correct bin. If all blocks are units,
the attempt is a wrong-bin failure. Reject zero and values outside (0,M)
before the next step. Integer recovery costs soft sqrt M<=soft K.

## 3. Recover a palette instead of the unknown count

Factor the recovered SMALL INTEGER c by trial division through sqrt c<=K.
This is paid work on a bounded public integer, not a factorization oracle
for N. Enumerate its divisors v. Retain v only if

    v=u^r, 1<=u<n, 1<=c/v<=D0,

and u is a unit square modulo n. Public Hensel lifting gives its two roots
plus/minus s modulo n. Also include N/s modulo n for each root, and
deduplicate. The true u is retained; the resulting palette contains P mod n
even if R=Q. Its size S is at most 4*tau(c).

Enumeration is acquired in soft K since tau(c)<=2sqrt c. For the sharper
HH cost use the elementary absolute bound

    tau(c)<=C_tau*c^(1/12)<=C_tau*K^(1/6),
    C_tau=324^4096.

Indeed, for primes l>=4096, a+1<=2^a<=l^(a/12). For each smaller prime,
(a+1)l^(-a/12) is below the geometric derivative sum
(1-l^(-1/12))^-2<324: the needed exact inequality is
18^12<2*17^12. Multiplying these estimates proves the bound. The deliberately
loose constant is independent of N and never enters the actual parameter
choice below. No finite exception or unproved divisor-distribution
assumption is being hidden.

## 4. ONE shared restricted-HH call

The inherited [restricted controller](../semiprime-axis-supplier-20261026/parameterized-controller.md)
has cost

    soft O(S*t + sqrt(N)/(n*t)^(3/2) + S + 1).

It is a restriction of
[Harvey–Hittmeir, Proposition 3.3 and Algorithm 4.3](https://arxiv.org/html/2105.11105),
with public lattice and centre construction included. Choose the actual
integer parameters

    A=ceil(cuberoot(K^4)), t=ceil(16*A/n).

Then n*t>=16K^(4/3), so the source's baby bound is
kappa<=K/8+3<K. Also n>=sqrt(K/2) and S=O(K^(1/6)), giving

    S*t<=16*A*S/n+S=O(K).

The integer t is O(K^(5/6)), has O(log N) bits, and satisfies the inherited
height requirements on the native K>=54 range. The giant alphabet, all
centres, lattice starts, modular powers, gcds and localization are paid by
this ONE call on the entire palette. Calling HH separately for every
divisor would not establish the stated bound.

Use alpha=beta^(n^2). Since n^2 divides H, each local alpha order is at
least the already screened order of beta^H, which exceeds 16H and the
baby alphabet. The inherited exact quadratic recovery and safe deletion
of processed global matches therefore apply. Every output factor is
checked; wrong bins or palettes may fail and do not stop the correct bin.
This completes the conditional consumer proof.

## 5. Changes to the hybrid and remaining acquisition

The packed C remains a sound sufficient input, but its count digit is
unnecessary for this consumer. M1 alone is the smallest of the three
displayed integer moment targets; M2 or M3 offer alternatives if another
identity happens to supply them. Canonical weights and the original
multiplicity/provenance theorem remain necessary. An arbitrary nonzero
Lambert amplitude multiplying u is not an integer d*u and cannot be fed
to this decoder without another proof.

Keep three interfaces separate:

1. An acquired whole-bin M_r uses the integer/divisor palette above.
2. One gated singleton ratio can supply u directly, using its existing
   constant-size HH menu; its arbitrary unit cofactor may cancel.
3. A raw-torus collision uses its own nonzero-exponent decoder and need
   not carry either integer colour interface.

The decomposition reports can help acquire any of these, but they currently
complete through the old shared engine. For J=Theta(K), h=O(K^(3/2)),
its bill remains soft(J+b+Jh/b), minimized at soft K^(5/4). This is the
retained route's query cost, not a general factoring record or lower bound.
Endpoint cancellation, a small source matrix, a symbolic gcd or a formal
selected coefficient does not remove that bill by itself.

Prior credit belongs to the side report for packed recovery and the sharper
count, the axis-supplier packet for restricted HH and divisor palettes, and
the even/torus packets for preparation, singleton gating and the value-only
readout. The present change is their explicit combination for c=d*u^r,
independently audited in the two accompanying reviews. Acquisition of any
one M_r in whole-family soft K remains the substantive open step.
