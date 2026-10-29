# Full native family: character masks plus the familiar axis wheel

26 October 2026. Verdict: the proposed integration is valid. A single primorial modulus supports quadratic-residue masks on nonaxis rows and coprimality masks on axes, with all CRT starts charged. It produces a complete coverage-safe filtered query whose axis contribution has the familiar square-root log-log wheel factor. The exponent remains 5/4, and this is not a new wheel technique, factoring record, or soft-k solution.

## 1. One acquired modulus and two row masks

Let L be the largest product of consecutive primes starting with 5 that is at most k^(1/4), and let p_* be its largest prime. Construct these primes by an ordinary sieve and check gcd(ell,N) for each. A proper gcd already factors; on the prepared hard branch all are much smaller than P,Q anyway. Then gcd(k,L)=1, log L=Theta(log k), p_*=Theta(log k), and

    w=phi(L)/L=Theta(1/loglog k).

Small finite k is handled by the inherited fallback. Prime generation, L, phi(L), CRT inverses and residue tables cost polynomial(log N).

For every nonaxis original label use the exact conic mask from conic-character-filter.md:

    f_j(I)=H I²-2lambda I+(lambda²-4abN)/H;
    retain I iff f_j(I) is square or zero modulo every ell|L.

For an axis pair use the following explicit, different mask. Keep original signed labels before any half-center fold; alternatively transport this metadata back from the fold.

## 2. Exact horizontal/vertical and opposite transport

Write a horizontal axis as (a,b)=(epsilon*k,0), epsilon in {+1,-1}, and lambda=t*k with 0<=t<k. At physical index I its factor-prime candidate is

    P_*(I)=epsilon*(kI-t).                              (1)

Indeed HI=aR+lambda implies R=P_*(I). Retain exactly those I for which gcd(P_*(I),L)=1. Any actual covered prime R is greater than 16H and therefore greater than every ell|L, so it passes.

The vertical swap (0,epsilon*k,t*k) receives EXACTLY the same mask (1), interpreted through its virtual horizontal partner. At the old common swap witness, the horizontal row hits at one prime and the vertical row hits at the other, but their physical value is the same epsilon*k*R. Independently treating the vertical row as a candidate for the *other* factor would lose the shared-mask argument. No actual missing partner row needs to be reintroduced: the virtual formula uses only epsilon,t,k. The actual coverage pair survives the documented pruning.

For lambda>0, opposite labels transport

    epsilon->-epsilon, t->k-t, I->1-I.

The candidate is unchanged:

    (-epsilon)*[k(1-I)-(k-t)]
       =epsilon*(kI-t).

For lambda=0 the transport is epsilon->-epsilon, I->-I and again preserves (1). The already paid lambda=0 removal may be retained. Thus uncentered signs, swaps and opposites are all exact. For the negative-only clock I=-i simply substitute -i in (1) and in the nonaxis conic; CRT cardinalities are unchanged.

## 3. Complete mask acquisition, including axes

For each auxiliary prime explicitly tabulate the allowed I residues, then expand their CRT product. Let A_j be the final number of allowed residues modulo L and rho_j=A_j/L. The axis affine map I->epsilon(kI-t) is bijective modulo L, so every axis row has exactly A_j=phi(L) and rho_j=w. There are at most 4k original axis phase rows; deletions only lower this count.

For nonaxes the exact per-prime count is (ell+chi_ell(abN))/2 when ell does not divide ab, and ell when it does. The complete native divisor/root count proves

    sum_(nonaxis j) rho_j
      <=C k log k *2^-t
          *prod_(ell|L)(1+1/ell)(1+2/ell),              (2)

where t=omega(L). The proof in conic-character-filter.md applies unchanged: sum over D|L and use the acquired catalogue bound O(k log k*tau(D)/D) for D|ab. No independent-character or random-input assumption is used.

For these first t primes the Euler product in (2) is O((log p_*)³). Also t=(1/4+o(1))*log k/loglog k. Hence the nonaxis sum is o(k*w), even with its explicit log k root-count factor. Combined with the axes,

    sum_(all j) rho_j=O(k*w),
    sum_j A_j=O(k*L*w).                                (3)

All masks are actually expanded. Per-prime scans cost soft(k); CRT list generation costs soft(sum A_j), including every axis residue and every degenerate nonaxis prime. The same common L is used by every row, so the AP product base is uniformly q^L.

## 4. Paid filtered product and recovery

Intersect each residue in each acquired mask with that original row's requested clock interval, using exact floor/ceiling. If each interval has length at most O(m), the number of AP descriptors is at most O(kLw), and the retained support size is at most

    S' <=sum_j[h_j rho_j+A_j]=O(k*(m+L)*w).             (4)

The A_j term pays clipped boundaries and avoids assuming residue equidistribution in short intervals. The monic variable-window evaluator at common base q^L acquires all scalar products in

    soft(k + kLw + sqrt(k*(m+L)*w)).                    (5)

It does not need inverses of collision factors or scalar q-factorials, nor a new local-order screen for q^L. Each selected AP factor maps to an original row and physical index I=r+Ls; the original exponent E-HI remains the licensed recovery label.

The masks are fixed as m grows, so the FILTERED prefix product has an exact monotone zero predicate. Every old actual swap witness passes either its common nonaxis conic mask or its common axis mask, yielding the full-zero endpoint at the known complete horizon. First-zero search therefore gives a nonunit newly introduced factor, and the original signed row scan/global-annihilator consumer finishes as before.

It is unnecessary, and generally false, to claim equality of filtered and original prefix zero predicates at every intermediate m: the sieve may delete accidental original collisions that are not physical factor witnesses. What is proved is retained witness coverage, a zero endpoint, monotonicity of the filtered product, and original-leaf recovery. Those are the sufficient consumer properties.

At m=Theta(k^(3/2)) and L<=k^(1/4), (5)'s dominant square-root scale is

    k^(5/4)/sqrt(loglog k),                            (6)

with the same polylogarithmic multiplication/MPE overhead as the initialized executor. The start term kLw is smaller by a square-root log-log factor at this choice. Soft-O suppresses these slowly varying factors, so the conclusion is still soft(k^(5/4)); no fixed-power exponent saving or optimized bit-log record is asserted.

## 5. Literature credit and status

The primorial/wheel square-root log-log effect is familiar. Primary references: Andrew Sutherland, *Order Computations in Generic Groups*, https://math.mit.edu/~drew/sutherland-phd.pdf, Algorithms 4.1/4.2 and Proposition 4.2 (primorial steps); David Harvey and Markus Hittmeir, *Deterministic methods for finding elements of large multiplicative order*, https://arxiv.org/abs/2601.11131, whose abstract recalls the same familiar D^(1/2)/(loglog D)^(1/2) scale and credits Sutherland's order-computation optimization. These are context/credit, not a claim that their group-order algorithm directly evaluates this filtered knot product.

The operation established here is the exact integration into the native masked product, especially the virtual-horizontal transport of the axis mask and the full charged CRT expansion. It closes the earlier axis *coverage bookkeeping* loophole without a baseline-cost small-factor prepass. Axes still dominate the final asymptotic scale, reducing the strong nonaxis subpower saving to the familiar wheel factor for the whole family. The desired soft-k primitive remains unproved.

No source report or repository file was edited, and no numerical campaign is used.
