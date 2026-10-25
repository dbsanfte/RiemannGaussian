# Complete signed hyperbola catalogue and exact root-coset product tiling

24 October 2026. Scratch constructive primitive. The acquired object is the COMPLETE nonzero-product divisor catalogue |ab|<k, with every modular phase root, plus the four necessary axis vectors. Its row count/acquisition is soft k. An integer ellipse filter preserves the old cover and bounds EVERY retained leaf. Full modular-root cosets then contract exactly to single-start longer q-products. The paid completion remains soft k^(5/4); this is NOT a query exponent advance or a new global fifth-bound theorem.

## 1. Existing input, including the single-prime conductor

Use the integrated positive theorem /tmp/semiprime-arithmetic-query-reuse-20261024/signed-two-weight-query.md SHA256 `b36e44e9d5e2c897caac87d6ad6339548fd9d438bd21352bd50971ff236efc93`, independent review `16b648c2556ae7b72864901a6a213672d18bce575a9c73114d15c1bf48c67eec`. Its all-bin localization and direct integer-quadratic consumer are retained. The actual setup is independently pinned in symmetric-supplier-audit.md in that packet, SHA256 `e31daf2b017109cd844bda3b5814cac84bd000ac223a7571efe13c615ff1ac62`.

In particular the existing D0 choice already has at most ONE odd prime conductor factor: when N=3 mod4 take D0=-4; when N=1 mod4 factor the acquired small Jacobi-minus witness and select a prime ell with Jacobi(ell,N)=-1. Take D0=-ell,-4ell or-8 as specified there. This does not alter setup or introduce a new least-prime premise. For odd ell, reciprocity and N=1 mod4 give (N/ell)=-1, an acquired nonresidue. If ell=2 or ell=3, use the explicit small-prime cases below.

The factored modulus is k=2c0*3^e at sixth-root scale, c0=|D0|, e>=3, H=k^2. If N=3 mod4, k=8*3^e, so only2,3 occur. If ell=2, k=16*3^e. If ell=3 its power MERGES with the existing3 part; it is not treated as a distinct CRT prime. Generally the distinct prime set S of k has size at most3 and lies in {2,3,ell}.

The actual prefix/setup returns a factor or N=P Q<=k^6, P,Q>16H, k>16, beta/W odd k-rough local orders>16H, pi=beta W, barpi=beta/W, q=pi^H, with the actual short q screen through16H. At the unknown nonsplit factor R (possibly larger), ord_R(pi)>256H^2 and pi^R=barpi. One unconditional D0 and ALL factor-size bins suffice; no QRH orientation or unique-hit input is used.

## 2. Complete pairs, axis content and the per-bin filter

For each integer1<=n<k enumerate its divisors, acquiring all ordered signed pairs with |ab|=n: (d,n/d),(-d,-n/d),(d,-n/d),(-d,n/d) over d|n. They are4*tau(n) pairs. A sieve and divisor generation cost soft k overall. Store K=ab, a,b, their signs and content gcd(|a|,|b|). Do NOT divide out that content or discard it because it shares a factor with k.

For zero product retain only (a,b)=(+k,0),(-k,0),(0,+k),(0,-k). These are exactly the possible axis vectors from the old shortest-vector constructor: a zero coordinate forces the other to be a multiple of k, and any multiple with magnitude>k is longer than the lattice's axis vector. The full zero-product set is infinite and is NOT claimed to be listed.

For each public dyadic factor bin B0<=R<2B0, retain a pair iff the acquired integer test

    (a B0^2)^2+(b N)^2 <= 2k B0^2 N                 (1)

passes. This mask depends only on a,b, NOT on the phase root, so it retains complete root cosets.

Every old Gauss witness passes(1): its squared norm is at most(2/sqrt3)kB0^2N. Furthermore that norm gives |ab|<=k/sqrt3<k whenever ab!=0, so the complete catalogue contains it. This credits the old Gauss family; the new catalogue removes any need to choose its vector per tag.

In the correct bin EVERY retained pair, not just a witness, satisfies

    |a|R+|b|(N/R) <= sqrt5*norm(aB0^2,bN)/B0
                  <=sqrt10*sqrt(kN)<4sqrt(kN).    (2)

Without(1), arbitrarily added divisor rows would not have the old all-leaf recovery guarantee. Bins are processed separately; wrong-bin rows are not merged into an unchecked aggregate.

## 3. Acquire ALL phase roots, including ramified prime powers

For each signed K!=0 acquire every integer phase0<=lambda<H with

    lambda^2=4KN modH.                            (3)

No inverse of a,b,2 or a content gcd is used. Write H=prod_(p in S)p^(2e_p), and t_p=v_p(4KN)=v_p(4K), using gcd(N,H)=1. If t_p<2e_p is odd there are no roots. If t_p>=2e_p, the local root set is x=0 modp^e_p, one coset of length p^e_p. Otherwise t_p=2v<2e_p; divide by p^(2v), find the UNIT roots y modulo p^(2e_p-2v), and obtain

    x=p^v*y modp^(2e_p-v).

Each unit-root branch is a coset modulo p^(2e_p-v), containing p^v roots modulo p^(2e_p). Odd primes have at most2 unit branches. Prime2 has at most4 (with the usual fewer branches at exponent1 or2). This explicitly handles the extra factor4, odd valuations and the zero discriminant cases; no bounded-valuation hypothesis is used.

For p=3, test roots modulo3 and lift unit roots by their invertible derivative. For p=2, lift the unit equation bit by bit, keeping at most4 branches after the initial exponents; zero valuations have already been separated. For the possible odd ell>=5, N modell is the known quadratic nonresidue above. Tonelli--Shanks is therefore INITIALIZED (only the2-part of ell-1 is needed, found by division), followed by unit-derivative Hensel lifting. These operations are polynomial(log N) per K/branch and do not factor N or seek an uncharged nonresidue. All modulus factors are public.

CRT uses each DISTINCT prime once. The resulting root set is partitioned into at most16 disjoint global cosets

    lambda=lambda0+(H/g_K)*t, 0<=t<g_K,
    0<=lambda0<H/g_K,
    g_K=prod_(p in S)p^min(floor(t_p/2),e_p).      (4)

If a local no-root case occurs, there is no global coset. Formula(4) also holds when ell=3 merges with that prime; there are then fewer branches. Bases lambda0 are acquired by explicit CRT and every literal phase in[0,H) is included exactly once.

For the four axes K=0, (3) is lambda^2=0 modk^2, hence EXACTLY lambda=k*t,0<=t<k. This is one coset with g=k. Its4k phase rows are fully paid.

## 4. Prove the entire catalogue has soft-k size and acquisition

Let r(K) be the root count in(3). Write |K|=u*v, where every prime of u lies in S and gcd(v,prod S)=1. The factor4 contributes at most one extra2 to g_K, so

    r(K)<=16g_K<=32sqrt(u).

For X>=1, sum_(v<=X)tau(v)<=X(1+log X). Consequently

    sum_(1<=n<k)tau(n)[r(n)+r(-n)]
      =O(k log k * sum_(u S-smooth)tau(u)/sqrt(u))
      <=O(k log k * prod_(p in S)(1-p^(-1/2))^(-2))
      =O(k log k).                              (5)

The last constant is uniform: at most3 distinct primes occur and the largest product is bounded by using2,3,5. This includes arbitrary3-adic degeneracy, all2-adic branches and ell=3 merging. No erroneous constant root-count-per-K bound is used. Multiplying by the two sign choices for each signed K and including the4k axes leaves soft k rows.

Sieve factorization/divisors, all modular-root tests and CRT bases cost soft k; explicitly writing every phase row costs the bound(5). Acquire its content/divisor/coset label, lambda, and actual unit

    V_lambda=pi^lambda*barpi^(a+bN).

All have O(log N)-bit exponents/representations; expansion inside a coset can use a power walk. The complete catalogue is acquired ONCE and is then filtered by(1) in each separate bin. No factor, local order or masked coefficient value is advice.

## 5. Coverage, uncentered carries and EVERY retained leaf

For the old Gauss witness, f(j)=0 modH and f'(j)=0 modk imply

    ell^2-4abN=f'(j)^2-4a*f(j)=0 modH.

Thus its pair and phase are in the new catalogue. At ab=0 shortestness gives one of the four axes already included. All Gauss witnesses pass(1). Replacing centered ell by lambda=[ell]_H changes it by0 orH, hence changes the old integer index by0 or1, not by an unknown carry.

Use the same public Dceil=ceil sqrt(kN), M=ceil(4Dceil/H)+2 and h=2M+1 as the positive query. Directly, the own index with0<=lambda<H satisfies

    |(aR+b(N/R)+lambda)/H|<4sqrt(kN)/H+1<M.

Thus the signed index interval[-M,M] covers it despite the uncentering, and h<16H remains certified. Acquire T_lambda=q^M V_lambda, so its nonnegative seed index s maps to original i=s-M.

At the nonsplit field R, FOR EVERY retained row V_lambda=pi^(aR+b(N/R)+lambda). Therefore a saturated norm leaf in the correct bin makes ord_R(pi)>256H^2 divide

    K_leaf=aR+b(N/R)+lambda-H*i.

By(2), lambda<H and |i|<=M,

    |K_leaf|<8sqrt(kN)+4H+4<3H^2<256H^2 (k>16).

It is zero as an INTEGER. The actual proper factor R is consequently an integer root of

    aX^2+(lambda-H*i)X+bN.

Use the prior exact quadratic/root-divisibility validator, including a=0 and b=0. The polynomial is nonzero because a,b are not both zero. Coefficient contents or additional roots not attached to a unit tag do not invalidate this argument. Thus the extra catalogue is a SAFE OVERCOVER, not a claim that every modular phase was an old tag. Positive/negative K, nonprimitive pairs and axes all have the same correct-bin all-leaf proof.

Each bin is queried/localized/decoded separately. Wrong bins return verified factors or bounded failure; the correct bin necessarily succeeds. No arbitrary auxiliary norm consumer or smaller-prime bound is used.

## 6. Exact root-coset product tiling, with its units and labels

For one retained pair and one coset(4), write g=g_K, delta=H/g and

    u_g=pi^delta, u_g^g=q,
    V_t=V0*u_g^t, V0=pi^lambda0*barpi^(a+bN), 0<=t<g,
    Y=q^(-M)*V0^(-1).

These are actual acquired units. With P_n(X;v)=prod_(i<n)(1-v^i X), the finite product is EXACTLY

    prod_(t<g) P_h((q^M V_t)^(-1);q)
       =P_(gh)(Y*u_g^(-g+1);u_g).               (6)

Indeed the exponents g*s-t, 0<=s<h,0<=t<g, fill the consecutive interval[-g+1,g(h-1)] once each. No partial coset, divisor label, tail or carry was deleted; the ellipse mask retains complete cosets.

For the shifted actual difference product, including ALL signs/units,

    prod_(t<g,s<h)(q^M V_t-q^s)
      =(q^M V0)^(gh)*u_g^(h*g*(g-1)/2)
           *P_(gh)(Y*u_g^(-g+1);u_g).           (7)

There is NO minus sign: each difference is target times(1-seed/target). For the original signed differences V_t-q^(s-M), multiply(7) by q^(-Mgh), giving prefactor V0^(gh)*u_g^(h*g*(g-1)/2). Every displayed prefactor is a supplied unit with O(log N)-bit exponent, acquired in soft1 per coset. No collision product is inverted.

Localization after tiling retains every original leaf. For a merged position j=0,...,gh-1 put n=j-g+1, s=ceil(n/g), t=g*s-n. Then0<=s<h,0<=t<g and n=g*s-t. Recover lambda=lambda0+delta*t and original i=s-M. The merged factor differs by an actual known unit from the corresponding original difference, so a saturated norm leaf invokes precisely the correct-bin quadratic proof above. This also covers the axes g=k.

## 7. Actual acquisition and completion cost

The possible g divide k, with at most prod_(p|k)(e_p+1)=polylog N types. For each type let C_g be the number of RETAINED pair/root cosets in the current bin. Equations(4)--(5) give

    sum_g C_g*g=soft k.

All cosets with that g have the SAME acquired base u_g and merged length gh. Evaluate P_(gh)(X;u_g) at their C_g actual starts from(6), using the existing baby-product/monic-MPE algorithm with d=min(gh,ceil sqrt(C_g*gh)). It pays every full-block argument and the one clipped final polynomial, at cost soft(C_g+sqrt(C_g*g*h)). This algorithm only multiplies polynomials and divides by MONIC evaluation-tree moduli. It requires neither target separation nor unit differences for the new base u_g. In particular gh can exceed16H; the old q screen is NOT asserted to screen all these longer u_g intervals.

Sum the groups, including all unit prefactors in(7). Cauchy--Schwarz and the polylogarithmic number of types give

    sum_g soft(C_g+sqrt(C_g*g*h))
      =soft(k+sqrt(k*h))=soft k^(5/4).

If the norm is saturated, localize first among these g groups, then among their full coset lists, and finally within ONE merged index interval. Each stage uses the same initialized query at no larger size, so only logarithmic overhead is added. There is no query for an arbitrary broken mask of a partial root coset. More simply, for merged position j use s=floor(j/g), t=g-1-(j modg); this is the same inverse map as Section6 and returns the genuine original leaf. Keep bins separate, as in the positive theorem.

The exact new acquired object is a tag-free complete signed divisor/root catalogue, its safe integer ellipse masks, and root-coset contractions whose starts, units, prefactors and recovery labels are fully supplied. All nonprimitive content and ramified root multiplicities are retained. The same softly linear acquisition supports every bin, but it does not acquire all long products in soft k.

The remaining specific operation is the simultaneous shifted product over divisor labels (a,b), with varying starts V0=pi^lambda0*barpi^(a+bN), even after grouping by K and g. Tiling alone preserves the total row-times-horizon mass; no lower bound on another implicit evaluator is inferred. The proved completion remains the existing soft k^(5/4) fixed-sixth-scale algorithm, slower than the known global fifth bound and short of soft k. No numerical campaign, backend theorem or shared/frozen source edit was used.
