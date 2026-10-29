# Primitive native coverage: signed cancellation and rational slope test

26 October 2026. Scratch only. Updated result: no reduction of native whole-family acquisition to soft(k) is proved. Harvey–Hittmeir Proposition 3.3 gives a lawful alternate source and the exact acquisition/clock tradeoff below. The subsequent [event-count.md](event-count.md) now rules out the proposed literal full continuous-tag coalescence target at polynomial bin fineness: it needs Omega(kr/log k) descriptors. A narrower cover proved only for actual semiprime factor points remains open. Sections 5–6 preserve the chronological candidate and its analysis, with that outcome explicitly qualified.

Read the latest repository native-contraction.md requested by the parent, the authoritative scalar-catalogue.md and swap-erratum.md, and the prior variable-windows.md. Content d|k, root-coset tiling, opposite folding, and variable-tail acquisition are credited prior work, not novelty here.

## 1. Exact requirement for a shorter physical witness interval

For the actual unknown factors P,Q and a native row, put

    T=aP+bQ,       D=aP-bQ.

The physical stationary condition is k|D. It is equivalent to

    aP²=bN mod k.

Then lambda=[-T]_(k²) is a stored conic root because T²-4abN=D²=0 mod k², and I=(T+lambda)/k² is an integer. This supplies the actual collision beta^(a+bN+lambda)=q^I mod P. Arbitrary good rational approximants to P/Q do not supply k|D.

For positive a,b, the familiar exact identity is

    T-2sqrt(abN)=D²/[T+2sqrt(abN)].                       (1)

For opposite signs the signed T can be small, but no positive stationary lower endpoint exists. These two possibilities must be analyzed separately; replacing |a|P+|b|Q by |T| without a new witness theorem is not valid.

If a positive stationary approximant with small gap were acquired/proved, one could center its row at the public integer

    c=floor([2sqrt(abN)+lambda]/H), H=k².

Then 0<=I-c<1+[T-2sqrt(abN)]/H. All floors are computable by integer square-root and rational comparisons. For its uncentered opposite row E'=H-E, assign c'=1-c; the centered target beta^E q^-c and its opposite are exact inverses. For lambda=0 use c'=-c. Thus row-dependent centering need not break the algebraic fold or its nonzero-exponent consumer. This is a lawful transport of known centers, not a coverage improvement by itself.

Public exact-zero deletion for any proposed new centered interval must test E=H(c+i) on that actual interval. A genuine collision survives this deletion whenever the new interval is shorter than both local q orders, by the same nonzero-Fermat-exponent argument as the old catalogue. Original integer labels must be retained for the saturated extractor.

## 2. Ordinary Lehman/continued-fraction coverage misses the congruence

Primary source: David Harvey, *An exponent one-fifth algorithm for deterministic integer factorisation*, https://arxiv.org/pdf/2010.05450, Lemma 3.3 and its proof. For N=pq and p>=sqrt(N/r), it gives positive a,b with ab<=r and

    0<=aq+bp-2sqrt(abN)<sqrt(N)/(4r sqrt(ab)).             (2)

The proof uses a rational approximation and the exact squared-difference identity (1). The original source is R. Sherman Lehman, *Factoring large integers* (1974), theorem in Section 2, DOI https://doi.org/10.1090/S0025-5718-1974-0340163-2. Its Farey-type dissection covers all factor ratios in the stated range, not just favorable experimental semiprimes.

At r~k and N~k^6, (2) appears to give exceptionally short H-normalized windows. But it does not prove k|(aq-bp). Setting lambda=[-aq-bp]_H would then generally fail lambda²=4abN mod H. Choosing one of the native conic roots instead does not repair this: it supplies the needed residue only for an approximant already satisfying the stationary congruence. Therefore (2) cannot be inserted into the existing native clock as a paid short-witness theorem.

Scaling a,b by k forces the congruence but changes the coefficient-product budget from r to k²r and introduces k phase lifts. It is not a subfamily of |ab|<k and does not preserve the soft-k acquisition count. Likewise lowering the clock conductor needs explicit new phase lifts/congruence checks before using H again.

## 3. The actual congruence-restricted theorem and its cost

Primary source: Harvey–Hittmeir, *A log-log speedup for exponent one-fifth deterministic integer factorisation*, https://arxiv.org/pdf/2105.11105, Proposition 3.3, equations (3.3),(3.4), and Algorithm 4.3. Given a public residue sigma mod m and factor interval [B,(1+1/r)B), it constructs a,b in polynomial(log N) time such that, for the factor in that residue/interval,

    |aQ+bP-(aN/B+bB)| <= 4sqrt(Nm)/r^(3/2),
    aQ+bP = aN/sigma+b sigma mod m².                    (3)

The proof uses a *sheared* rank-two lattice with determinant N*m*r*B². Its construction is exact and deterministic; it does not assume favorable continued fractions of the hidden factor.

At m=k and r>=1, q=beta^(k²) is exactly the original clock. Publicly center each row using (aN/B+bB)/H and the known stationary residue. Equation (3) yields a window of length

    L=O(1+sqrt(N)/(kr)^(3/2)).                           (4)

There are soft(k*r) residue/interval descriptors. Acquiring a single stationary phase per descriptor already pays those soft(k*r) starts; arbitrary extra conic roots are not required for this alternate coverage family. The resulting rows may have |ab| larger than k, so this is an alternate initialized source, not a claimed subset of the old hyperbola catalogue.

The single phase is explicit: for the canonical integer sigma in [1,k], compute its inverse modulo H=k², set tau=aN sigma^-1+b sigma modulo H, and take lambda=[-tau]_H. An inverse computed only modulo k cannot be reused as an inverse modulo H. No enumeration of the k lifts of sigma is needed: replacing sigma by sigma+kt changes tau modulo H by kt(b-aN sigma^-2)=0 modulo H, using the stationary congruence modulo k. Also tau²-4abN=(aN sigma^-1-b sigma)²=0 modulo H. Thus this source gives one lawful conic phase, independently of the lift of the factor residue.

For each descriptor add its swapped coefficient row with the *same* lambda and transport the *same* public integer center c=floor[(aN/B+bB+lambda)/H] to both. In the project's exponent convention E_(u,v)=u+vN+lambda, the physical value T=aQ+bP satisfies

    E_(b,a)-(T+lambda)=(P-1)(aQ-b),
    E_(a,b)-(T+lambda)=(Q-1)(bP-a).

Hence at the true descriptor a P-local hit on row (b,a) and a Q-local hit on row (a,b) share the same centered index I-c, where I=(T+lambda)/H. This differs from Section 1's coefficient orientation and is why explicit swapped labels are retained. Independently recentering the swapped row from its coefficient-oriented approximation would lose the shared-index proof. The full-zero endpoint is preserved at constant descriptor overhead. Opposites may also be added with the compatible transported centers from Section 1; they are unnecessary solely for this endpoint.

For the tested range 1<=r<=k^(1/3), and public bins starting B>=16k² on the prepared hard branch, the inequalities in the source proof give |a|<=2sqrt(kr), |b|<=4sqrt(Nkr)/B. These are below both factors for sufficiently large k since N<=k^6. Hence the witness Fermat exponents are nonzero exactly as in the old catalogue (aQ-b cannot vanish unless the pair is zero). Public exact-integer deletion therefore preserves the true descriptor rows; the licensed polylog-bit annihilator consumer remains applicable. Finite remaining k can be handled by the inherited finite fallback. These qualifications make the alternate source safe; they do not improve its acquisition count.

More precisely both aQ-b and bP-a are nonzero, including axes, by these coefficient bounds and (a,b)!=(0,0). If a witness row were deleted by E_(u,v)=H(c+i0) inside its actual centered interval, the corresponding local hit would force q^(i0-(I-c))=1. The interval diameter is below both certified local q orders, forcing i0=I-c and contradicting its nonzero Fermat integer. All exponents have O(log N) bits. The licensed consumer accepts arbitrary nonzero polynomial-bit global annihilators under the prepared odd local-order bounds; it does not require the old |a|,|b|<=k bounds. No later prime-modulus-specific query contract or unit root-separation promise is imported.

The existing monic variable-window product construction then gives

    soft(R+sqrt(RL)),   R=soft(k*r).                     (5)

For N~k^6 this is, ignoring ceilings/logarithms,

    soft(k*r + k^(5/4)/r^(1/4)).                         (6)

Taking r~k^(1/3) would shorten the clock to L=O(k), but acquisition rises to soft(k^(4/3)), beyond the goal. Optimizing (6) gives r~k^(1/5) and soft(k^(6/5))=soft(N^(1/5)), the familiar one-fifth scale. At soft-k acquisition (r at most polylogarithmic), (4) remains soft(k^(3/2)). This is a cost conclusion about this actual constructor, not a lower bound on another approach.

More generally replacing m by a divisor of k and compensating with r so that m*r~k leaves the right side of (4) at the same scale. The smaller-conductor clock beta^(m²) is known and has adequate order because m²|H, but it is not the old q without accounting for the additional lift data. This variant does not create an exponent saving.

## 4. What pure signed cancellation would have to add

In the balanced regime P,Q~sqrt(N), use real coordinates A=aP,B=bQ. The congruence lattice has determinant kN in these coordinates. The candidate region

    |AB|<kN,       |A+B|<=T

has area O(T sqrt(kN)+T²) when T<<sqrt(kN): at small A+B, the product constraint forces |A-B|=O(sqrt(kN)). A direct convex-body area guarantee therefore naturally reaches T~sqrt(kN), exactly the old scale. To get T=O(kH)=O(k³) when N~k^6, one needs information about this *particular semiprime lattice*, not merely its determinant. This area calculation does not prove the desired smaller region is empty for any actual semiprime.

For positive a,b, replacing the signed strip by the near-stationary gap region from (1) similarly requires a congruence-restricted approximant with unusually small transverse D. Neither the current Gauss theorem nor ordinary rational approximation proves that extra bound uniformly. Small rational slopes or torus-knot slope labels do not by themselves impose k|D; the modular and real approximation constraints must be met simultaneously.

## 5. Chronological coalescence candidate, now excluded for the full product domain

The candidate tested here was to avoid paying every descriptor in the actual theorem (3). Fix each public residue sigma. As B traverses the narrow bins, the underlying congruence lattice is fixed while its sheared metric changes. A continued-fraction/reduced-basis event algorithm could try to acquire only distinct vectors (a,b), their valid B-ranges, and the union of their clock intervals. The literal version requiring coverage of all residue/real-scale pairs is now excluded by event-count.md; it is no longer an unqualified promising full-cover target.

The required lemma is precise: construct, without knowing P or Q, a collection of original-labeled centered intervals that covers the guaranteed stationary witness for every factor, with

    number of acquired row descriptors = soft(k),
    total interval width S = soft(k²).                  (7)

The prior variable-windows constructor would then evaluate their exact product in soft(J+sqrt(S))=soft(k), including unequal residual tails and recovery. Compatible centering of opposite rows can preserve a folded representation, but the lemma must also preserve a two-prime/full-zero endpoint if the interface requested is zero-only. A one-prime-only cover would support the nonunit consumer instead and cannot silently replace that zero endpoint premise.

Including the swapped descriptor rows described in Section 3 is an explicit way to preserve that endpoint at constant overhead, provided coalescence retains both original labels and their common physical-index window. Merely selecting an arbitrary equivalent short lattice vector for each prime would not suffice without this common-index bookkeeping.

Why this is substantive: equal lattice vectors in neighboring bins can be reused, but their *centers* vary. Merging their windows can restore the long support even when the vector list shrinks. Therefore merely bounding the number of continued-fraction basis changes does not prove (7). The target is a bound on the acquired union of integer clock intervals, with every center and tail retained. It is a genuine arithmetic acquisition problem rather than another formal q-product transform.

The cited primary theorem only gives the tradeoff (6). Subsequent work in event-count.md proves that (7)'s descriptor target cannot hold for the literal full unit-tag × balanced-continuous-scale domain when r=k^epsilon. Its exact bound is R=Omega(kr/log k), even before total interval width is charged. A selection theorem restricted to the actual semiprime factor points is not covered by that premise and remains a possible narrower direction. No finite numerical campaign is used as evidence, and no generic q-hypergeometric identity supplies the missing arithmetic coverage theorem.

## 6. Further event analysis: a quantitative limitation of simple vector reuse

There is a sharper exact calculation behind the center-union warning. Use the positive stationary case of HH Proposition 3.3, fixing one coefficient vector a,b>0 and one residue tag. Put

    A=sqrt(abN), B*=sqrt(aN/b), z=log(B/B*),
    U(B)=aN/B+bB=2A cosh(z).

The source's transverse admissibility condition is

    |aN/B-bB|=2A|sinh(z)|<=D0,
    D0=2sqrt(Nk/r).

Hence its full admissible B range has log half-width

    zmax=asinh[D0/(2A)].                                (8)

Across this same range, the public center U(B) varies by the exact amount

    DeltaU=sqrt(4A²+D0²)-2A
           =D0²/[sqrt(4A²+D0²)+2A].                    (9)

The second HH amplitude inequality can also be enforced; restricting to A a fixed sufficiently small constant times sqrt(Nkr) keeps it valid throughout the ranges considered below. Thus this is an actual admissibility calculation, not an arbitrary hypothetical metric.

Parameterize A=Theta(sqrt(Nkr)/s), with 1<=s<=sqrt(r) and r tending to infinity. Then (8),(9) give

    zmax=Theta(s/r),
    number of geometric 1/r-bins served=Theta(s),
    DeltaU=Theta[sqrt(Nk)*s/r^(3/2)].                    (10)

The single-bin error radius supplied by HH is E0=4sqrt(Nk)/r^(3/2). Therefore its H-normalized width is L=Theta(1+E0/H), whereas merging the entire valid range for this repeated vector requires an interval of width Theta(1+s*E0/H). In our tested parameter range E0/H>=Theta(k), so integer roundoff does not dominate.

This calculation gives the concrete tradeoff: reuse over Theta(s) bins lowers the descriptor count by that factor, but the changing centers enlarge its clock interval by the same factor. The fully merged interval is not replaceable by one width-L interval with the same guaranteed support. Moreover |dU/dlog B|<=D0 on the range, so consecutive bin centers differ by O(D0/r)=O(E0); their supplied error windows overlap up to constants. Keeping a union of intervals rather than its hull therefore does not create a power saving for this full-range construction.

Two important cases are s=1, where full-scale vectors have ab=Theta(kr) and persist for only O(1) bins, and s=sqrt(r), where native-scale ab=Theta(k) vectors persist for Theta(sqrt(r)) bins but incur Theta(sqrt(r)) times the single-bin width. Thus merely listing distinct positive stationary vectors/events cannot prove the desired total-width bound: the exact metric simultaneously controls event persistence and center drift.

This is a sharp analysis of the simple repeat-vector coalescence rule, not a claim that all actual semiprimes force the worst pattern or that a more selective valid covering family is impossible. A genuine advance must either exploit overlap *between different* coefficient vectors, provide a much smaller certified error than E0 across each event range, or prove a covering selection that avoids the width-persistence balance (10). The existing variable-window executor already pays the resulting exact union once such a selection is supplied.

### Final scope update after independent review

The phase-lift precision, orientation, common-center transport and coefficient-consumer qualifications above incorporate coverage-review.md. The exact measure proof in [event-count.md](event-count.md) supersedes any suggestion that literal full-domain event enumeration might achieve soft-k descriptors at polynomial r. It establishes k<=C1 delta²+C2 delta sqrt(R tau(k)), with delta=C sqrt(k/r), and hence the stated descriptor lower bound. This is a constructor bound for an independently quantified residue/scale product domain. It does not refute an acquired cover required only to hit the two factor points linked by PQ=N, or an implicit contraction avoiding individual descriptor acquisition. No factoring lower bound or improved factoring exponent is claimed.
