# Native clock phases: a paid parity selector and its higher-bit boundary

Scope: paper derivation on the prepared pure modulus K=2·3^e, H=K², with odd factors R,S, RS=N. No new implementation, order oracle, or asymptotic sixth-rate claim. The shortened-clock consumer is the frozen scalar-acceleration/coupled-section.md; the weighted lattice coverage argument is inherited from the weighted Gauss construction.

## 1. Exact phase criterion

Write a row as (a,c), avoiding confusion with the desired dyadic modulus b. Put f(X)=aX²+ell X+cN. For a stationary support colour r modulo K, choose its canonical phase ell, so H divides f(r) and K divides f'(r). Define the actual integers A=f(r)/H and C=f'(r)/K. If R=r+Ks is an actual factor and i is its signed clock index, then

    i = (a s²+C s+A)/(r+Ks).

This identity follows from f(R)=HRi. For dyadic b, r+Ks is odd and invertible modulo b. The phase equals a fixed k for EVERY integer s if and only if

    b | 2a,   b | a+C-kK,   b | A-kr.                 (1)

Indeed the numerator after subtracting k(r+Ks) is a quadratic integer-valued polynomial; its values at 0 and 1 and its second finite difference are sufficient and necessary. The only candidate is k=A/r modulo b. All divisions defining A,C are exact integer divisions; the only modular inverse here is the certified odd r.

Multiplying the middle expression by r and using KA=f(r)/K gives the useful equivalent test

    b | 2a,
    cN ≡ a r(r+K) (mod Kb).                         (2)

More explicitly, r(C-kK)≡(a r²-cN)/K modulo b; stationarity makes the displayed quotient integral. Thus no division by K in a dyadic residue ring has been assumed.

This is a full-fibre criterion, not a claim that every lift is an integer divisor of N. Restricting to actual factors could yield additional selectors.

## 2. Positive amended coverage: one public bit

For each unit colour r modulo K use the lattice

    Lambda'_r = {(a,c): a r(r+K) ≡ cN (mod 2K)}.     (3)

Its covolume is 2K: the coefficient of c is a unit modulo 2K. The condition is well defined on r modulo K. By the Chinese remainder theorem, (3) is exactly the old stationary congruence modulo K together with

    a+cN ≡ 0 (mod 4).                              (4)

Here r(r+K)≡3 modulo 4 and the odd part of 2K is 3^e. Thus a weighted Gauss shortest vector in this lattice provides coverage for every actual factor colour, with the old weighted Hermite bound enlarged by sqrt(2). This is a change of the covered family, not a filter that discards half of an existing witness bank.

For ANY row satisfying (4), canonical ell satisfies ell≡-(a+cN)r≡0 modulo 4. At an actual hit,

    ell+aR+cS = H i.

Odd R satisfies R^{-1}≡R modulo 8, hence S≡NR modulo 8. Since a+cN is divisible by 4, (a+cN)R≡a+cN modulo 8. Also H≡4 modulo 8. Consequently

    i ≡ (ell+a+cN)/4 (mod 2).                       (5)

The quotient is an integer. Crucially (5) is independent of the colour within a row's support. In normalized indices t=i+M0, the known phase is

    r_row = M0+(ell+a+cN)/4 mod 2.

If T=q^{M0}y, the retained leaves are exactly

    1-(T q^{-r_row})(q²)^{-s},
    0≤s≤floor((h-1-r_row)/2).

There are two possible lengths, differing by one, but a single common base q². No nonunit leaf is divided out. In a correct bin every actual good hit is retained. No knowledge of either local order is needed, and q² retains the old odd local orders.

## 3. Acquisition and guard accounting

Weighted Gauss reduction in (3) costs polylogarithmic bit work per colour. Enumerating the full enlarged ellipse, if needed for the support-partition construction, still costs soft O(K): its semiaxis product is (4/sqrt(3))K; content-g pair counts remain O(K/g²), colour incidences O(g), and summation over the native 2·3^v contents converges. Integer labels retain O(log N) bits. Canonical phases and the integer quotient in (5) are acquired directly.

The new weighted squared-norm bound is (4/sqrt(3))KN, rather than (2/sqrt(3))KN. Thus the old physical index horizon grows by sqrt(2), up to rounding. Each retained row then has half that enlarged horizon. At the level of row-clock mass the net gain is a constant about 1/sqrt(2), not a power of K. The old variable-window engine can process the two retained-length groups. Its bound remains soft O(K+sqrt(sum h_row)).

Do not silently import the old strict |ac|<K or coefficient ≤K assertions: the enlarged ellipse only gives |ac|≤2K/sqrt(3), with corresponding constant coefficient bounds. The usual provenance argument still has the same asymptotic margin in the prepared branch, because the row, phase, and clock bounds change only by fixed constants while the local order bound is >256H² and factors exceed16H. A complete archived family should state those constants and retain the original finite guard branch. This note proves the coverage lattice and phase selector; it does not claim a newly audited unique-support partition for the enlarged ellipse.

Literal-zero deletion and mixed-relation localization use the unchanged actual-label decoders. Once-only extraction costs soft N^(31/192), bounded by soft K; it is not merely polylogarithmic because labels are short. Wrong bins still require bounded validation, and all-bin scheduling should acquire cheap metadata first.

## 4. Why the same full-fibre trick does not give sqrt(K) bits for free

For b=2^t≥2, (2) forces a=(b/2)a' and c=(b/2)c'. To see the second divisibility, stationarity modulo Kb and the odd units r(r+K),N imply that c has the same necessary 2-adic divisibility as a. After cancelling b/2, the remaining congruence is

    c'N ≡ a' r(r+K) (mod 2K).                      (6)

Thus every row with a full-fibre constant phase modulo b is (b/2) times a parity-lattice row. Scaling a row scales its canonical physical index range by b/2, up to a canonical integer carry, while thinning by b removes only that same factor. Rebuilding a shorter-vector lattice cannot remove this forced scalar content within criterion (1). This is a scoped statement about constant phase on all lifts, not an exclusion of factor-only masks, compressed joint processing, or a new arithmetic restriction on s.

The positive output is therefore a genuinely acquired, coverage-preserving one-bit selector for an amended native family. It supplies a constant improvement and an exact initialized q² query. The missing sixth-rate input remains a substantially stronger actual-factor phase restriction, or a collective algorithm processing many phases without paying their separate shortened queries.
