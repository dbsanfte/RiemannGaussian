# Independent review of completed-source.md: ellipse and one-moment source

26 October 2026. Paper-only source review, no repository edits or experiments. **PASS** for the complete ellipse construction, explicit linear count, marked contraction, and retained acquisition cost. The ellipse gives cleaner constants than the separate rectangle experiment; both are valid constructions, and neither proves a faster query.

## 1. Enumeration, all contents and exact count

The coefficient semiaxes obey AB=2K/sqrt3. When both integer bounding ranges are nonempty, A,B>=1 and A+B<=2AB, so constructing their bounding rectangle takes O(K) work even in wrong bins. If a semiaxis is below one, no nonaxis pair is enumerated; there is no huge thin-axis scan. The irrational bound can be tested by 3(a²B0^4+b²N²)²<=4K²B0^4N². All nonaxis points satisfy |ab|<=K/sqrt3 and therefore |a|,|b|<K.

For each exact content g, at most 4AB/g² signed coefficient pairs are present. Unit roots of the divided conic modulo K/g have at most two branches; each has at most g lifts, with parity filtering reducing the number when g is even. Thus <=2g is valid for both parity cases. g=K is impossible for nonaxis points since it would give |ab|>=K². Summing gives

 J_nonaxis<=8AB sum_(g|K)1/g <12sqrt3 K<21K.

The sum is exactly less than (1+1/2)/(1-1/3)=9/4 for pure K. Adding only the four primitive axes that pass the SAME ellipse test contributes at most 4phi(K)=4K/3, so J_completed<23K. Including arbitrary axis multiples or all axes in every bin would invalidate this construction; the source correctly does neither.

Coverage and every-hit provenance follow from the SAME weighted ellipse inequality as the original Gauss proof. The added points therefore retain the original h, nonzero labelled endpoint decoder, and common n tag, rather than using an unproved raw-torus alias promise.

## 2. Marks, multiplicities, finite source and consumer

For nonaxis content g, a/g and b/g are units modulo n, and n divides K/g. Every compatible colour therefore has exactly the public CANONICAL mark [N(b/g)/(a/g)]_n. It must be reduced as an integer modulo n BEFORE native embedding. The report makes that distinction. Axes use their actual colour marks separately.

The marked concatenation (6) is exact before delta or epsilon specialization because the mark is constant on the fixed coefficient pair. The unwrapped exponent reindexing is bijective; multiplicity mu is an integer weight, not an emitted list. Canonical carry replacement is residue equivalence after certified endpoint UNIT gates, not unconditional scalar equality. The old chirp/stratum theorem and its prior credit are retained. At each compressed string the inherited short-order guard gives at most one hit per component; consequently all-string value classification plus mu*u weighting computes the ACTUAL M1, even with repeated original rows. A single aggregate zero bit would not compute it; the report correctly acquires all string values.

The whole-bin integer c=d*u satisfies c<23Kn. Native e>=3 gives n<=K/6, hence M=23Kn<=23H/6<4H. The blocked decoder's padded b²<=4M<16H<P,Q is safe; b=ceil(sqrt M)<2K at K>=54. Trial factorization through sqrt c<2K costs soft K. The divisor palette has S<=4tau(c)=O(K^(1/6)) with an absolute fixed divisor-bound constant, and ONE shared restricted-HH call fits soft K with the already guarded parameter choice. Either nonsplit factor can be R; complements include the smaller factor. Wrong-bin candidate failures must continue, as stated.

No finite-size batching or additional roughening gate is required for this particular J<23K ellipse. Those are valid alternatives for a less sharply counted completion, but the explicit count supersedes them here.

## 3. Primitive-fibre normalization and its limit

Section 6 is correct. For g=1 every hit has j=R modulo K, and EVERY completed row of that own colour has its physical index inside the window. Its public fibre count m_j is therefore the hit count if that fibre is nonempty. m_j<21K<P,Q certifies its scalar inverse. This can normalize the primitive residue without a clock cofactor, but does not guarantee a primitive witness.

For higher content write j=R+(K/g)t and z=(aR-bS)/K. The exact phase difference is

 aR+bS+ell_j = -(K²/g)*t*(z+(a/g)t)/j mod H.

Thus the extra-hit condition g | t(z+(a/g)t) has the correct sign and coefficient. The integer z exists from the stationary congruence and R being a unit. It is not publicly acquired, so public nonprimitive fibre size is not its actual hit count.

A further scope distinction matters when comparing to original singleton blocks: this completed primitive fibre may contain multiple good hits. Its public normalization is lawful for CONSTANT clock amplitudes. It does not automatically make arbitrary Lambert amplitudes cancellation-safe as in the original one-row-per-colour primitive bank.

## 4. Direct pair-weighted trace opportunity and actual cost

The direct marked source is genuinely simpler to acquire than a formal high-rank tensor: use the pair constant u_(a,b), known multiplicity mu, and ONE logarithmic derivative per compressed GP string. All the input coefficients, including the regulator/epsilon dependence, are supplied. What remains is its selected pole or equivalently its flag at a native root. The old engine executes those flags at soft(K+sqrt(Kh)); the g=1 bank has L=1 and still O(K) starts. Dropping the count output does not eliminate that bank or shorten its clock in this executed algorithm.

One might try to fuse coefficient pairs before singular evaluation using the mark N(b/g)/(a/g). In the native algebra that unreduced expression is zero; only its public canonical residue is a legal mark. Thus ordinary rational coefficient-line summation cannot replace the source weight by that native quotient. The constant pair mark DOES allow the complete chirp concatenation already performed, but supplies no additional proved joint phase/collision contraction. This is a concrete source-initialization distinction, not a complexity lower bound or exclusion of other weighted-trace methods.

All branch guards and startup costs are explicit. No substantive correction required; the whole-bin consumer can replace the batch presentation in integration for this ellipse. The regular rectangle construction remains a separate scoped experiment, with its own longer horizon and batching ledger.
