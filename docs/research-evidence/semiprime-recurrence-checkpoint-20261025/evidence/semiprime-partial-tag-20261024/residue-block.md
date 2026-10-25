# Coarse native classes: acquired quadratic-phase blocks, unresolved contraction

24 October 2026. Scratch only. Root proposed the cubic-modulus expansion verified here. The positive result is exact soft-k acquisition of quadratic-phase residue blocks, including canonical parity and integer shifts. The executed terminal continuation still costs soft k^(3/2). A coarse-tag Coppersmith completion is a separate contract.

## Inputs and duplicate credit

Authoritative native source: /tmp/semiprime-zero-query-20261024/native-pairing.md SHA256 `06548c974c61d9922a4ec6c2f41ba1c95d7dfcbb92442b3b2e5ceff984cd8016`. Its earlier Hensel observations are credited there. General label partitions/pair directional polynomials already occur in /tmp/semiprime-implicit-gradient-20261024/native-orbit-blocks.md SHA256 `a6ab972dd085669e3c322a5031597fd441821d43945b4fee62e97b3f2a818e15`. The reset primitive is /tmp/semiprime-cofactor-recurrence-20261024/cofactor-contraction.md SHA256 `e4100f7c507a1f3a894b9c9285425b942f086f0080e3f2ef51bd2b0aa7838ee0`. Generalizing a partition gradient is not a new rate.

Let d=2c0 be even, r>=3 an odd public prime coprime to dN, k=d r^3, m=d r^2, H=k^2; m^3=dH. The character conductor divides m. Changed-modulus supply and actual beta,W,q reconstruction/screens are charged to the companion supplier, not inherited from an old k. Assume P,Q>16H, N<=k^6, beta,W odd local orders >16H, beta's two orders coprime, W norm one, pi=beta W, barpi=beta/W, q=pi^H, and q differences through C=16H certified units. Every exponent used below has O(log N) bits. Any gcd(N,2k)>1 is handled first.

A coarse unit class has exactly r unit tags, all the same colour. Retain the FULL canonical minus family. The smaller-nonsplit orientation is conditional, not guaranteed; retain the other colour/old fallback for the unconditional algorithm. Do not import old PLUS fibre bounds to the cube modulus.

The actual repaired data are A in [1,2k), even b=center_k(-(N-Aj^2)/k *j^-1), ell=kb-2Aj, delta=A+ell, and V=pi^ell barpi^(N+A) on minus rows. The public lift Jtilde satisfies A Jtilde^2=N mod H and ell=-2A Jtilde mod H. Original own indices lie in [0,L), L=3H+2.

## 1. Exact parity AP, including the representative

Parity repair is exactly A_j=[N j^-2]_(2k). Indeed b even iff (N-Aj^2)/k is even; j odd and k even preserve this parity. Exactly one of a,a+k has it.

Since m^2 is divisible by 2k, for j_t=j0+mt one has

    A_t=[A0+2m eta*t]_(2k), eta=[-N j0^-3]_r in U(r).

Thus all repaired A in the class are exactly A_h=A_c+2mh, 0<=h<r, for fixed 0<A_c<2m, in an acquired affine permutation of tags. The normalization floor((A0+2m eta*t)/(2k)) has binary successive increments. This AP law also holds at k=d r^2,m=d r; the next quadratic lift uses the stronger cubic modulus.

All permutations and original labels cost O(r) per class, total soft k. There is no H-sized enumeration.

## 2. Initialize the quadratic lift and its exact carry

Take the actual tag with A=A_c, its public J0, and s0=A_c J0 mod H. Then s0 is a unit and s0^2=NA_c mod H. Acquire s0^-1 modulo the public integer H and set

    s(h)=s0+m N s0^-1*h-(m^2/2)N^2 s0^-3*h^2 mod H.

There is no inversion of 2: m^2/2 is an integer. Direct squaring gives s(h)^2=N(A_c+2mh) mod H. The quadratic coefficient cancels, the cubic term is divisible by m^3=dH, and m^4/4 is divisible by H because d is even.

Modulo k,

    j_h=[s(h) A_h^-1]_k=j_base-m s0 A_c^-2*h mod k.

The coefficient after m is a unit modulo r, proving this is exactly the original coarse class. The actual root A_h Jtilde_h agrees with s(h) mod k. Their difference is a multiple of k, whose square vanishes mod H; subtracting squares forces the difference to be 0 or H/2 mod H. Therefore ell_native,h=-2s(h) mod H, including the two-adic ambiguity.

Center the three coefficients of -2s(h) modulo H as ell0,ell1,ell2, and put ellhat(h)=ell0+ell1*h+ell2*h^2. The EXACT integer

    d_h=(ellhat(h)-ell_native,h)/H

is acquired from canonical native data. Globally in the actual composite ring,

    q^d_h V_h=C0 D0^h E0^(h^2),
    C0=pi^ell0 barpi^(N+A_c),
    D0=pi^ell1 barpi^(2m), E0=pi^ell2.

All class starts, phase differences and actual carries cost soft r per class, soft k total. No local equality has replaced a global exponent identity.

## 3. Keep positive indices and original consumers

Since |ell_native|<4.5H, |d_h|<(r^2+r+10)/2. Take B=r^2+r+12, e_h=B+d_h in [0,2B], and

    Vhat_h=q^B C0 D0^h E0^(h^2)=q^e_h V_h,
    Lnew=L+2B.

Own hits map to i_native+e_h. New leaves map back to their KNOWN original index i_native=i-e_h in [-2B,L+2B). This is an overcover, not equality of original masks. For d>=2,r>=3, 2B<H and Lnew<4H, preserving all required q guards.

At the smaller nonsplit prime the original minus norm/angle proof still forces H*i_native=A_h P+Q+ell_native on this range: the same odd coprime order-product >256H^2 margin applies. Its valuation step gives k|(P-j_h), hence one canonical minus row/index. This makes no PLUS-fibre assertion.

A saturated norm leaf uses the predecessor nonsplit/G_beta consumer; it does not imply whole-algebra equality on a split side. Its scalar exponent K=N+delta_native-H*i_native is nonzero because N>256H^2 and |delta_native-H*i_native|<5H^2. For completeness, scalar saturation implies both coprime local beta orders divide K. Their product D_beta divides (P-1)(Q-1)=N+1-P-Q, so it divides S-(P+Q), where S=1+H*i_native-delta_native. Here |S|<5H^2+1, P<=k^3<=H^2 and Q<H^2/16, giving |S-(P+Q)|<7H^2<256H^2<D_beta. Hence S=P+Q exactly. Verify factors explicitly. A wrong-orientation/coarse result takes the verified old fallback; the separate coarse completion is not proved here.

## 4. Execute the coarse-label reset, and charge its block

Let J be the retained minus row count, M=J/r, and acquire by weighted product trees

    F_c(X)=prod_(h<r)(X-Vhat_(c,h)), F=prod_c F_c,
    H0=sum_c F/F_c, H1=sum_c c*(F/F_c).

Cost soft J, degrees J,J-r,at most J-r. Leading(H0)=M is a certified integer unit since M<k<P,Q. At the unique good hit x*, H0(x*) is a local unit and H1(x*)=c*H0(x*).

This reset retains the FULL canonical r rows in every class, including any nonhit aliases. It requires neither interpolation nor a root-separation oracle. Original-root separation does not transfer under the different q shifts e_h. Any later interpolation on the shifted roots must rerun the actual factor-or-separation routine; if it deduplicates, class sizes and all degree claims must be recalculated. At the good hit, the extended-horizon unique-row proof excludes aliases involving that hit, which is exactly what H0(x*) being nonzero requires.

Initialize (Z,A,B)=(1,0,0) and execute, x=q^i,

    Z'=F(x)Z, A'=F(x)A+H0(x)Z, B'=F(x)B+H1(x)Z.

At the unique hit the final ratio B/A is the correct coarse class. This is an actual sufficient conditional readout, not assumed acquired.

For baby length b construct the constant-width polynomial matrix block. Its diagonal has degree Jb; its A entry is

    sum_(t<b) H0(q^t X) prod_(u!=t) F(q^u X).

For dyadic b its leading coefficient at degree Jb-r is exactly

    M*q^(J*b*(b-1)/2)*sum_(t<b)q^(-rt),

which is a unit: the geometric sum factors into 1+q^(-r*2^v), and local component orders are odd. Thus this explicit representation actually retains that degree on every supplied input, not merely generic inputs. This is not an algorithmic lower bound.

Building the block costs soft(Jb); monic multipoint evaluation and numerical block multiplication cost soft(Jb+Lnew/b). Construct any final short block explicitly. No hit values are inverted. The completed cost is soft(Jb+Lnew/b+J), optimized to soft sqrt(J Lnew)=soft k^(3/2) when J~k. Classwise queries would cost soft((J/r)*sqrt(r Lnew)), worse. The r-degree saving in an off-diagonal does not acquire the diagonal starts.

## 5. Exact remaining operation

The acquired class sequence has second multiplicative difference E0^2, but consecutive ratio D0 E0^(2h+1). D0 contains barpi^(2m). The finite q-product recurrence transports a fixed q shift, not this changing mixed-base ratio. No identification with guarded short q powers has been proved or used.

The initialized even/odd class-polynomial recursion is

    F_r(X;C,D,E)=F_ceil(r/2)(X;C,D^2,E^4)
                *F_floor(r/2)(X;CDE,D^2E^4,E^4).

It acquires the degree-r class polynomial in soft r, already paid above. Applied to a long scalar query it retains BOTH child queries: a terminal scalar state has not closed. The remaining specific primitive is a shared zero-safe contraction over these supplied quadratic-phase classes and bounded seed indices, with coarse-label output only. All O(k) starts and O(r^2) index corrections are supplied now. No generic recurrence impossibility, full-query gain, or unproved coarse decoder is claimed.

Ledger: changed-modulus/seed supply separate and required; class permutations/lifts/carries/starts soft k; actual rows/class gradients soft k; executed terminal continuation soft k^(3/2); original bounded labels and old fallback retained. No repository edits or experiments.
