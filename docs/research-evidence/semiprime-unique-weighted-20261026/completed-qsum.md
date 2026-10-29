# Repeated rows, one moment, and a regular coefficient-rectangle completion

26 October 2026. Scratch paper execution, no repository edits or numerical tests. The one-moment consumer extends to soft-K repeated-row catalogues by public batching. A different regular completion below has fully acquired soft-K inputs and native coverage/provenance. Its executed q-sum still costs the retained soft K^(5/4). Completion and fixed-pair chirp contraction have old credit; dropping the count is the newer interface, not a new catalogue theorem by itself.

## 1. Repetition does not invalidate M1

Assume EVERY hit in a correct bin of a supplied completed table retains j=R modulo n=3^ceil(e/2), with the original beta-coupled exact-integer provenance, and total rows J=soft K. Partition the actual row list publicly into batches of at most K rows. Within one batch

 M1=Res_delta sum_(rows,t) [j²]_n/(delta+1-T_j rho^t)

has good value c=d*u, where 0<=d<=K and u=[R²]_n. A nonempty batch has 0<c<K*n<4H<R; all its modular-integer recovery, trial factorization, divisor-palette and ONE shared restricted-HH call cost soft K by the frozen moment consumer. Its padding is below 4K*n<16H for K>=54. Empty good batches have good residue zero: norm/coordinate classification factors or certifies global zero and skips them; it must not run divisor factorization on zero. At least one correct-bin batch is nonempty. There are only polylogarithmically many batches and bins. This avoids an asymptotic total-J count guard.

No singleton promise or unique colour per row is used. Canonical integer weights, all-hit common tags, and constant clock amplitudes ARE used. Arbitrary Lambert amplitudes and raw-torus aliases are not covered. Older pair consumers already permitted lawful completions; the change is that no count output is needed now.

## 2. Construct a regular support completion, not only colour lifts of selected pairs

Fix a public bin B<=R<2B and the ACTUAL original lattice (K B²,0),(s_j B²,N). Original shortest coefficients satisfy |a|,|b|<=K, |ab|<=K/sqrt(3). Let

 A_B=min(K, floor(sqrt(4KN/B²))),
 B_B=min(K, floor(sqrt(4K B²/N))).

Compute these exactly by integer square roots of the corresponding integer quotients. FLOOR, not ceiling, is important: near very unbalanced bins an added unit coefficient outside this cap can already destroy the short horizon. Either cap may be zero.

For each dyadic A=1,2,4,...<=K include the four signed coefficient rectangles

 A<=|a|<min(2A,K+1),   1<=|b|<=floor(K/(sqrt(3)*A)),
 |a|<=A_B, |b|<=B_B.                                    (1)

The last b bound is exactly computable as floor(sqrt(floor(K²/(3A²)))). Add ONLY horizontal axes (+/-K,0) when K<=A_B and vertical axes (0,+/-K) when K<=B_B. Do not add every axis at every bin without this filter.

For every resulting pair enumerate EVERY unit j modulo K satisfying a*j²=b*N modulo K, and attach its canonical stationary phase

 ell_j=[-a*j-b*N*j^-1]_H centered in [-H/2,H/2), H=K².    (2)

All inverses in (2) are modulo known H; all row metadata are retained. The actual normalized root is T_j=q^M*pi^ell_j*barpi^(a+bN). This is a different regular coefficient SUPPORT completion: it contains eligible coefficient pairs not selected by any shortest-vector routine. Completing fixed acquired pairs and their chirps remains prior credit.

### Coverage and clock

Every original Gauss witness is included. Its coordinate bounds are at most sqrt(2/sqrt3)*sqrt(KN)/B and sqrt(2/sqrt3)*sqrt K*B/sqrt N, both below the caps before floors. An integer below those real caps is still admitted by the floored 2-times caps. Its dyadic rectangle contains its |a| and its |b| bound follows from |ab|<=K/sqrt3. Axis shortest vectors are precisely the four primitive axes and pass their respective cap.

EVERY added row, not merely a witness, satisfies in the correct bin

 |a|R+|b|N/R<6sqrt(KN).                              (3)

Choose Dceil=ceil(sqrt(KN)), M=ceil(6Dceil/H)+2 and h=2M+1. Thus h<=12K^(3/2)+9<16H for native K>=54. The own-colour physical index is inside [-M,M]. At ANY hit the integer

 L_hit=aR+b(N/R)+ell_j-H*i

has absolute value below 12sqrt(KN)+(7/2)H+O(1)<3H² for K>=54, and the prepared pi order exceeds 256H². Therefore the hit is an EXACT integer zero, not an arbitrary modular alias. This proves the provenance needed for M1 on the completed support.

### The same coarse tag survives the slightly larger product cutoff

All nonaxis rows in (1) obey |ab|<2K/sqrt3. Let v=v3(gcd(a,K))=v3(gcd(b,K)). Then 3^(2v)<=|ab|<(4/sqrt3)*3^e. If e=2t the right factor is <9*3^(2t), and if e=2t+1 it is <9*3^(2t) as well (4sqrt3<9). Hence v<=floor(e/2). The valuation proof in pure-weighted-common-tag §4 gives K/g |R-j from exact integer provenance, so the SAME n=3^ceil(e/2) divides R-j. The retained primitive axes carry the full K tag by their explicit stationary formulas. Thus every hit of this regular completion shares the required tag; repeated phases/rows cause only positive multiplicity.

### Actual acquisition count

Enumerate the coefficient rectangles in O(K log K) integer iterations (they are disjoint in |a|). For a candidate pair compute g, reject incompatible unit valuations, and solve j0²=N*(b/g)*(a/g)^-1 modulo K/g using known 2/3-power Hensel arithmetic. Enumerate its at most O(g) lifts, filtering unit j. The number of pairs divisible by g is O((K/g²)log K), since |ab|<2K/sqrt3. Thus total coloured incidences are

 O(K log K sum_(g|K)1/g)=soft K.

Axes add O(K), not O(K²). This is the existing explicit incidence-enumeration argument, applied to (1); there is no scan of every colour against every coefficient pair. All actual roots, phases, powers and weights cost soft K. Repeated rows need not be removed for M1, although literal duplicates can be combined with positive integer multiplicities.

## 3. Execute the additive q-sum on this support

Fix j and j^-1 modulo H. The unwrapped character factors are

 X_j=barpi*pi^-j,   Y_j=barpi^N*pi^(-N*j^-1).

Define the exact known integer carry

 c_j(a,b)=(ell_j+a*j+b*N*j^-1)/H.

Then globally T_j=q^(M+c_j(a,b))*X_j^a*Y_j^b. The required one-moment coefficient is the residue of the explicitly finite sum

 sum_j [j²]_n sum_((a,b) in (1), a*j²=bN mod K)
     sum_(i=0)^(h-1)
   1/(1+delta-X_j^a*Y_j^b*q^(M+c_j(a,b)-i)),           (4)

with the filtered axes added. This is a true finite Lambert/Appell-type sum over stationary lattice rectangles, with all carries retained. No special-function name makes (4) acquired.

A promising literal geometric summation would hold b,j fixed and write a=s_j*b+K*t. But each signed dyadic a interval in (1) has width <K and lies in [1,K] or [-K,-1]; hence it contains AT MOST ONE such t. This particular regular completion supplies no long fixed-b geometric coefficient string to sum. Across b the allowed a is a modular sawtooth, and c_j(a,b) is another explicit floor carry; changing it into an uncarried two-generator character changes the clock interval to a row-dependent interval shifted by c_j. That carry can be large, so the four endpoint gates used for bounded colour-lift chirps do NOT erase it. Equation (4) retains those moving finite boundaries.

Thus the tested elementary geometric/q-digamma summation has the SAME actual sparse row input, not a newly initialized long q-hypergeometric progression. This is a precise failed specialization of this completion, not a claim that (4) has no better joint summation algorithm.

## 4. One scalar and the already paid chirp contraction

There is a useful simplification of marks. On any fixed coefficient pair, g as above and m=K/g, all compatible colours satisfy

 j²=N*(b/g)*(a/g)^-1 modulo m.

Because n|m, their CANONICAL squared tag u_(a,b) is constant across EVERY colour lift of that pair. It is computed in the PUBLIC residue ring modulo n before embedding in B. Hence M1 may be attached once to each fixed-pair branch, with the known phase multiplicity. No count output or per-lift tag interpolation is needed.

The existing [quadratic-lifts §4](../semiprime-fused-readout-20261026/quadratic-lifts.md) already completes branches and contracts quadratic colour lifts to O(log g) consecutive GP strings. In fact g²<K still holds here: for g=2^alpha*3^v dividing K, the first possible value of g²/K above one is at least 3/2, excluded by g²<=|ab|<2K/sqrt3. Thus the old cubic truncation and parity adjustment apply with their stated hypotheses. Maximum square-stratum length is at most D0, so the new horizon satisfies D0*h<16H (use D0<=sqrt(K/2) and h<=12K^(3/2)+9 at K>=54). Thus its per-string one-hit flag and endpoint gates remain legal. Added nonaxis row labels still have |a|<=K and b!=0, so the inherited nonzero-label endpoint proof is unchanged.

For the public at-most-K-row consumer batches, pack WHOLE fixed-coefficient colour completions, never an arbitrary subset of a chirp. Each nonaxis pair contributes at most 2g<=2sqrt K<K rows; greedy packing yields only O(J/K+1) batches, since every nonfinal batch has at least K-2sqrt K rows. Pack original axis incidences separately as needed. This preserves every complete square stratum. Acquire ALL string values using the old batched engine, classify them, and sum known multiplicity times u_(a,b) times their flags. The completed M1 is acquired, with empty strings contributing exactly zero and no Hasse-depth search. Summing the geometric content/stratum costs gives

 soft(K+sqrt(Kh))=soft K^(5/4).

The g=1 sector has length-one phase strata and still Theta(K) coefficient incidences at clock h. Dropping the second count output changes mark bookkeeping and permits the divisor-palette consumer, but does not reduce this engine's dominant number of starts or clock length. This is an executed cost of the known algorithm, not a lower bound on primitive summation.

## Outcome and provenance

A regular dyadic-rectangle completion is now explicitly constructed, with paid soft-K enumeration, all-semiprime coverage, the SAME coarse factor tag, safe axes/carries, and a one-scalar consumer by public batches. It is not credited as the first lawful completion. The completed q-sum (4) remains a joint finite-boundary acquisition target; the tested coefficient-line summation produces no long progression, and the old chirp contraction still completes it at K^(5/4). A new scalar summation of (4), preserving its canonical character carries, is the precise remaining opportunity.
