# A partial native tag is sufficient: a complete residue-assisted decoder

24 October 2026. Scratch mathematical report. **The proposed decoder is valid.** Given the smaller factor's residue c=P mod m, for a public divisor m|k with m>=N^(1/12), deterministic interval enumeration plus UNIVARIATE unknown-divisor small roots factors in soft N^(1/4)/m<=soft N^(1/6) bit operations. All dimensions and coefficient sizes are polynomial in log N. There is no fixed N^epsilon loss. This weakens the required acquired readout; it does NOT acquire that residue or improve an overall factoring rate by itself.

## 1. Input, conclusion and primary contract

Let N=PQ for distinct odd primes P<Q, k=Theta(N^(1/6)), and 1<m<=k be public, with gcd(m,N)=1. The native application has m|k and P>=N^(1/3); the decoder below can simply enumerate all smaller-prime dyadic bins and does not need to know its exact size. If gcd(m,N) is proper, return it immediately. Input c is a public integer normalized to [0,m).

There is an explicit deterministic algorithm of soft(1+N^(1/4)/m) bit cost which returns a VERIFIED proper factor whenever c=P mod m, and otherwise returns a factor or bounded failure within the SAME budget. The factor's high interval, local order, factorization, balancedness and a selected lattice root are not advice. Under m<=k the additive1 is harmless asymptotically; m>=N^(1/12) gives the claimed sixth-root decoder budget.

Primary: Alexander May, *New RSA Vulnerabilities Using Lattice Reduction Methods*, dissertation (2003), Section3.2, Theorem6 and its proof:
https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235

It states the unknown-divisor univariate monic small-root theorem, with divisor >=N^beta, root bound (1/2)N^(beta²/delta-epsilon), and runtime polynomial in log N, delta and 1/epsilon. This is not a claim that one-sixth known bits alone imply polynomial-time factoring. For delta=1 choose epsilon=1/n, n=ceil(log2 N). Then N^(-epsilon)>=1/2, so the theorem permits at least a quarter of N^(beta²), at polynomial-logarithmic runtime. An independent exact lattice certificate for the particular constant-fraction bound used below is provided in Section3, avoiding hidden fixed-epsilon or dimension constants.

The result is classical residue-assisted Coppersmith enumeration. Prior native small-root audits reject a SINGLE full-size interval at the original one-sixth tag modulus; they do not reject the PAID interval enumeration here. The known fifth algorithm, original k^(3/2) query and open fast readout acquisition are not reclassified as solved by this backend.

## 2. Enumerate every actual high interval with public integer rounding

Let n=ceil(log2 N). For every b=1,...,floor(n/2), put B=2^b and clip the factor bin to

 B<=p<=min(2B-1,floor(sqrt N)).

Skip an empty bin. These bins cover every odd smaller prime P. Set beta=b/n; since N<=2^n, N^beta<=B. No floating-point logarithm is needed. beta is a public rational and 0<beta<=1/2.

Acquire by exact integer powers and roots

 T_b=floor((N^(b²))^(1/n²)),
 X_b=max(1,floor(T_b/16)).                       (1)

The integer powered before the root has only O(n³) bits; the nth-root degree here is n², and exact comparisons/root algorithms have polynomial(n) bit cost. Write R_b=N^(beta²) as a REAL quantity used only in the proof. Then

 X_b>=R_b/64,
 X_b<=R_b/16 whenever X_b>=2.                    (2)

Indeed floor R_b>=R_b/2 for R_b>=1, and max(1,floor T/16)>=T/32. This also handles small bins without an asymptotic rounding exception.

For this bin enumerate all integers s with c+ms inside its clipped interval:

 s_min=max(0,ceil((B-c)/m)),
 s_max=floor((min(2B-1,floor sqrt N)-c)/m).

Partition them into consecutive blocks starting S0=s_min+v X_b, each containing at most X_b integers. If X_b=1, directly test gcd(c+mS0,N). Otherwise introduce z=s-S0, 0<=z<X_b, and acquire the MONIC linear polynomial

 f(z)=z+A, A=[m^-1(c+mS0)]_N.                    (3)

If the actual smaller factor is in this block and the residue promise is true, f(z0)=0 modulo P, with P>=B>=N^beta. Its unknown integer z0 is genuinely small. A false c supplies no root promise, but does not change any dimension, block count or cost bound.

## 3. An explicit logarithmic-dimension deterministic certificate

For X=X_b>=2 take dimension d=n and multiplicity t=b. Since b<=n/2 and b>=1, both t and d-t are positive. Use the integer polynomial basis

 N^(t-i) f(z)^i,              0<=i<t,
 z^a f(z)^t,                 0<=a<d-t.

Scale coefficient column r by X^r. Its matrix is triangular by degree, with exact determinant

 det Lambda=N^[t(t+1)/2] X^[d(d-1)/2].           (4)

Every basis polynomial vanishes modulo P^t at the promised root z0. Fixed-parameter choices are NOT assumed: d=n grows logarithmically. Basis entries have O(n²) bits because A<N, t,d<=n and X<=N^(1/4). Deterministic LLL with parameter3/4 therefore has polynomial(n) bit cost and returns a nonzero polynomial H with

 |H(z0)|<=sqrt d ||H(zX)||_2
 <=sqrt d 2^[(d-1)/4] (det Lambda)^(1/d).         (5)

The upper bound is STRICTLY below B^t, uniformly here. To see this let a=log2 N<=n, beta=b/n and use X<=N^(beta²)/16. Subtract log2(N^(beta*t)) from the logarithm of (5). With d=n,t=b the result is at most

 (1/2)log2 n+(n-1)/4
          +(1/2)beta(1-beta)a-2(n-1)
 <=(1/2)log2 n-(13/8)n+7/4 <0 for n>=2.          (6)

Thus |H(z0)|<N^(beta*t)<=B^t<=P^t. Since it is divisible by P^t, it is zero as an INTEGER. H is nonzero and degree<d because its scaled lattice vector is nonzero. This is the ordinary univariate small-norm certificate, with no multivariate independence assumption.

One can optionally verify the same strict bound entirely with integers before root extraction:

 d^(2d) 2^[d(d-1)] N^[2t(t+1)] X^[2d(d-1)]
                                      < B^[4td]. (7)

All integers in this test have polynomial(n) bit size. The proof shows it always holds for the stated X>=2 choices. If X=1 the direct candidate gcd already avoids any lattice premise.

Isolate H's integer roots deterministically (e.g. exact univariate root isolation/factorization), retain only 0<=z<X in the actual clipped block, and test gcd(c+m(S0+z),N). The degree and height of H are polynomial(n); so root extraction and all at most d-1 validations cost polynomial(n) bits per block. Only a proper verified gcd is returned. If a false residue or an unpromised interval has no verified factor, continue. This is a total bounded attempt, not a root oracle.

## 4. Charge all bins and blocks: no fixed exponent slack

For each bin there are at most O(1+B/(m X_b)) blocks. Let a=log2 N, delta=n-a in[0,1). Since beta=b/n<=1/2,

 log2(B/R_b)=b-beta² a
            =a beta(1-beta)+delta beta
            <=a/4+1/2.

Consequently B/R_b<=sqrt(2)N^(1/4). Combined with (2), EACH bin uses

 O(1+N^(1/4)/m)

blocks. There are O(log N) bins, each block costs polynomial(log N), and every stored exponent, offset and candidate has O(log N) bits apart from the explicitly polynomial-logarithmic lattice coefficients. Therefore the complete worst-case bit bound is

 soft(1+N^(1/4)/m).                              (8)

The maximum exponent occurs near balanced P; unbalanced bins are included rather than assigned the balanced beta=1/2 theorem incorrectly. Under m>=N^(1/12), (8) is soft N^(1/6). The constant fraction in (1) corresponds to epsilon=O(1/log N), not a fixed positive epsilon or an uncharged N^epsilon enumeration. There is no finite analytic exception or unknown threshold in this decoder: X=1 and small N are actual defined branches.

The correct c ensures that some enumerated block contains z0 and hence a verified proper factor is found. Wrong c runs the same bounded loop, returning a checked factor or failure. The positive candidates tested lie inside a bin clipped at sqrt N, so a candidate cannot equal N; any nontrivial gcd is proper. This decoder uses no beta annihilator, local field or factor-sum fallback.

## 5. The weaker native acquisition contract and complete consumer

Now impose m|k and the existing native paid-prefix promise P>16k², hence m<P. This last inequality makes a label in [0,m) unique at the good P-side field; it is not needed by the stand-alone decoder when c is already supplied as an actual integer residue. At the actual own tag j*=P mod k,

 [j*]_m=P mod m.

Hence choose the known repeated labels w_j=[j]_m instead of the full original tags. The existing weighted product tree acquires a degree-<J interpolating polynomial, or the corresponding direction polynomial, in soft J. A unique-hit weak readout need only supply A,B with A nonzero at the good smaller-nonsplit field and B/A=[j*]_m THERE. It need not identify the full tag or q^I. Repeated labels cause no problem for that ratio. This is a strictly weaker output when m is a proper smaller divisor; the existence of a suitably sized divisor is an EXPLICIT input promise, not asserted for every controlled modulus.

Its bounded validation is concrete. Norm/coordinate-classify A, obtaining a proper factor or a unit on the good branch. Form alpha=B/A=alpha0+alpha1*tau. Since the promised value is in the base field at nonsplit P, gcd(alpha1,N) is proper or N; gcd1 causes bounded failure on a wrong label. In the latter case alpha is globally a base scalar z=alpha0. A monic additive integer-block query of length m locates a residue c in[0,m) in soft sqrt m work, or returns a proper factor/failure. At a saturated scalar leaf z-c=0 modulo N, canonical z and c imply an actual global residue label c, not a nonzero annihilator. Invoke the bounded decoder above. It accepts only verified proper factors, so a wrong orientation/weak output cannot produce a false factor.

For m<=k and m>=N^(1/12), all validation plus (8) costs soft k on EVERY supplied label, with guaranteed success on the correct residue promise. A future bounded weak-readout algorithm may therefore target ONLY this partial tag. Its own acquisition remains open; the current degree-J matrix product still costs soft sqrt(JL). If QRH orientation selection is used to supply the unique-hit label, its earlier explicit conditional/asymptotic scope remains. This unconditional residue DECODER does not remove that acquisition/orientation premise.

## Primary pins and scope

The full May dissertation PDF from the university's /download/pdf/3235 endpoint is cached as sources/may-2003.pdf, SHA256 `a6f8075b93c32a6a687ae83dde2698a98739b069a54c2cb644b75418ffc54332`. Its /3238 endpoint is only the abstract and was NOT used as the theorem source. Section3.2 Theorem6 explicitly charges 1/epsilon; the finite certificate (4)--(7) independently proves the required linear specialization and logarithmic dimensions. The LLL algorithm and univariate integer-root extraction are the established deterministic routines used in that theorem, not heuristic multivariate extraction.

This supplies a complete weaker output/consumer contract, rather than a new factor-residue constructor or overall exponent improvement. No claim that a sixth of the bits alone gives polynomial-time factoring, no small-root theorem on the entire unenumerated interval, and no free high-interval advice is made. No shared/frozen files, finite sample campaign or Lean/backend changes were used.
