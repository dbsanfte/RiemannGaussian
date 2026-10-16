# Input-dependent convex factor-box refinement: precise limit of geometric pruning

2026-10-15. No new nearlinear acquisition algorithm found. This note isolates a concrete geometric-relaxation contract; it is not a bound against divisibility-aware lattice algorithms or implicit long products.

## Prior work checked first

The journal's known-residue/content audit (around lines 9005--9040) already corrects the unscaled reducible polynomial and derives the cleared height test N<B^4; sixth-scale substitution N=B^6 fails that proposed test. It explicitly does not establish a general lattice lower bound.

The full-Euclid obstruction already covers actual N-dependent rectangle/stationary/cancellation centers with soft-linear windows. The journal around 21175--21255 explicitly leaves stronger full-N carry-correlated selection unpaid (the D11 packet-energy estimate). It also explains why dropping a +1 from lattice-point counts fails even with one genuinely prime factor. A generic lattice-density claim would therefore be a rediscovery of a known invalid shortcut.

## A concrete adaptive geometric route that cannot prune enough

Consider the following restricted route. For each tag j it retains possible real smaller factors t in the full balanced box

P_lo=sqrt(N/2), P_hi=sqrt(N).

It propagates only the exact real factor-sum range

f_j(t)=(a_j t+N/t+ell_j)/m^2

through an arbitrary adaptive subdivision of that box. It can discard a t-cell only if the real factor box is empty there or its image has no possible original index. It has no arithmetic test that t divides N, no additional lattice congruence beyond the original tag, and no separately acquired residual certificate. If it eventually tests original integer index residuals individually, or materializes a list containing every integer in the image ranges, its total index work is Omega(m^3) on every balanced input at the literal sixth scale. Merely refining these real boxes cannot reduce that projection.

Here is the full elementary bound. Assume m and N^(1/6) are within fixed constants, as on the retained actual supply. For each a the congruence a j^2=N modulo prime m has at most two tags. Therefore at most m/4+O(1) tags have 1<=a_j<m/8. At least a fixed positive fraction of the m-1 tags have a_j>=m/8.

For t in [sqrt(N/2),sqrt(N)], one has 1<=N/t^2<=2. Thus for a_j>=m/8 and m sufficiently large,

f_j'(t)=(a_j-N/t^2)/m^2 >=a_j/(2m^2)>=1/(16m).

The factor-box width is (1-1/sqrt(2))*sqrt(N)=Theta(m^3), so its image is one interval of width Omega(m^2). Any exact covering by refined image intervals must still contain that interval; its union contains Omega(m^2) integer indices. Summing over Omega(m) such tags gives Omega(m^3) DISTINCT LABELED tag/index pairs. This does not infer a large polynomial degree from roots over a composite ring.

These real image indices lie inside the full canonical index scale, rather than being an artifact far outside the allowed search. Since ell_j is between -3m^2-a_j and m^2-a_j, t<=sqrt(N)<=m^3, and N/t<=sqrt(2N)<=sqrt(2)m^3,

f_j(t)<=m^2+sqrt(2)m+1<2m^2+2

for m sufficiently large. Also a_j t+N/t>=N/t>=sqrt(N)=Theta(m^3), so f_j(t)>=Theta(m)-4>0. Thus clipping to [0,2m^2+2) does not remove these images eventually.

Even retaining the residue-class relaxation t=j+mx does not create sparse gaps between rounded candidate ranges. Consecutive admissible real-grid points have

f_j(t+m)-f_j(t)=a_j/m-N/[m t(t+m)].

For the stated large slopes this is positive and strictly less than a_j/m<1 throughout the balanced box. Their floor values therefore have no missing integers between their endpoint floors. Exact integrality of f_j(t), or the requirement N/t be an integer, is a genuinely additional arithmetic filter and is not supplied by convexity.

## What this does and does not settle

An adaptive subdivision with a NEW cheap arithmetic rejection test might remove almost all relaxed candidates. The preceding argument supplies no bound on such a test and does not exclude it. Likewise a polynomial representation can cover the whole image without enumerating Omega(m^3) residuals; its acquisition is exactly the still-unpaid long-query problem. Thus this is a rigorous obstruction only to claiming that convex factor-box subdivision alone makes a direct atomic-index enumerator nearlinear.

The source's exact identity already gives the right low digit and full index, but neighboring tags do not provide simultaneous integer-index witnesses for the same unknown prime: the quotient-row integer-index theorem applies at j=p mod m. Treating every other tag's real range as another integer relation is an unjustified promotion of the relaxation.

No new complete scalar acquisition, shared higher-digit factorization, or actual-source small-root theorem was obtained in this investigation. A useful positive target would be an arithmetic rejection/correlation theorem that acts on these real cells using the actual full-N lifts and proves a whole-family soft O(m) surviving-work bound. The prior packet-energy gate illustrates why that theorem cannot be replaced by carry bijectivity or heuristic lattice density.
