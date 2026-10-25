# Independent review of fixed-modulus density accounting

22 October2026. Reviewed fixed-modulus-density.md together with pell-count.md. Verdict: PASS for the FIXED public admissible modulus m and the displayed canonical-row consumer. It is not a counterexample to the actual paid preparation algorithm, a least-prime/adaptive selector, or a universal factoring endpoint.

The requested two-tag wording repair is now present: each occurring a has exactly two tags and every a has at most two. This is the correct statement for a=N j^(−2) modm, whose values range over one square coset.

## Branch accounting

Canonical dependence on N modm³ is correct provided the canonical a,b are the specified residue-based deterministic choices. Increasing N by m³t changes c_row by mt, hence fixes Delta modm, kappa, ell and v. Thus each pair's norm functions are affine in the same higher digit. There are O(m³) residue classes, O(m) rows and O(m²) pairs per residue, yielding O(m⁵) residue/pair descriptors.

Initial gcd: for each fixed residue,row, |v|<=2m³ and P>=alpha m³ imply at most floor(2/alpha) possible cofactors h in |v|=Ph, hence O_alpha(1) candidate prime P. Since m does not divide P, Q is fixed modulo m³; a fixed interval of width O(m³) contains O_beta(1) such Q. This proves O(m⁴) initial-gcd inputs. The equation v²=m³z modulo squarefree N proves identical divisibility by each prime, hence gcd(v,N)=gcd(z,N); no extra z branch is missing. Balanced prime lower bounds eliminate m|N and a-sharing factors for sufficiently large m. Since |v|<N, saturation is impossible. z=0 would make gcd(v,N)=N and so is also impossible on this box after the native bounds.

Singleton: W²=m³z=v²−4aN forces a<=1/c from |v|<=2m³ and N>=c m⁶. Thus only O_c(1) multipliers, each at most two tags, matter per residue. Unit v modulo the odd prime m has exactly two square roots ±v modulo m³. The interval0<=W<=2m³ contains O(1) representatives of each, and every W determines one rational candidate N, at most one integer input. Total O_c(m³) follows, including unhelpful or inadmissible candidates. A prime P of N has odd valuation in4aN because a<m<P, so W=0 is indeed impossible. The singleton characterization uses m³z square, equivalently mz square; no positive z-square case is silently substituted.

Pair degeneracy: C=a_i z_j−a_j z_i is constant on the residue class. Expanding (2a_jz_i+C)²−4a_i a_jY² gives C² whenever Y²=z_i z_j. The first coordinate changes injectively with N because a_i,a_j>0, so the bounded Pell count does bound the number of N. For C=0, the rational ratios z_i/z_j=a_i/a_j=v_i²/v_j² hold. On the unit-screened branch every displayed modular denominator is invertible. Thus the two normalized roots are globally ± each other and the pair cannot be actionable. This includes unequal a, and no C=0 infinite family is incorrectly counted by the nonzero-norm lemma.

For C!=0, both square and nonsquare coefficients are handled uniformly by pell-count.md. Its maximal-order ideal argument gives tau(C²) times O(logm) possible solutions and needs no primitive-solution condition, fixed discriminant, computed class group or fundamental unit. Imprimitive ideals and ramification are included. The square-coefficient divisor factorization also includes all integer signs. Since |C|=O(m⁴), the uniform bound is m^{o(1)}, not an asserted fixed polylog bound. Summing over O(m⁵) descriptors yields m^{5+o(1)} candidate inputs; the initial gcd and singleton terms are smaller. Duplicate discoveries only overcount, which is legitimate.

## Prime-box denominator

Choose fixed0<alpha<beta<1 with alpha²>c, possible for any fixed c<1. Primes P,Q in[alpha m³,beta m³] then produce N∈[c m⁶,m⁶]. The prime number theorem gives Theta(m³/logm) primes there. Taking unordered distinct pairs gives Theta(m⁶/log²m) distinct semiprime products by unique factorization; diagonal pairs are negligible. For large m this box automatically satisfies P,Q>16m². The ratio of the counted success bound to this denominator is m^(−1+o(1)) log²m→0. Thus “most” is valid for THIS fixed-modulus box and THIS complete singleton/pair consumer, including its initial scalar gcd successes.

The opening general alpha,beta,c describe a family whose box may be empty or unsuitable; the denominator conclusion appropriately chooses a suitable box, rather than asserting every such parameter choice has that many inputs. The proof does not need PNT in varying arithmetic progressions: residue classes are used only for a success upper bound, while PNT counts the whole fixed interval.

## Strict scope and pending preparation addendum

The result supplies a uniform scarcity statement for the canonical norm consumer at one fixed admissible m. It does not show that N lies in the actual least-prime-selector bin(previousprime^6,m^6], and cannot be transferred to that much thinner interval without a separate argument. Nor does it control a paid adaptive menu, higher dependencies, or a new shared-H evaluator.

The actual gamma/preparation contract is not established by the elementary prime-box denominator above. In particular the proof does not show that the real paid preparation would reach this norm consumer, rather than factor beforehand. Any proposed positive-proportion restriction to P,Q=3mod4 with coprime half-orders requires its own complete counting argument and still must be connected explicitly to the full supplied-gamma contract. This review leaves that addendum CONDITIONAL and makes no counterexample claim against the paid preparation success branch.

Only this scratch review was written. No earlier report, repository file, implementation, finite example or build was changed.


## Independent review of the separate prepared-order addendum

Reviewed prepared-order-density-addendum.md after it was separated from the main report. Verdict: PASS. The previously conditional base-existence extension is now proved, with the following exact scope.

Let M=m³ and use the stated fixed separated positive intervals. PNT in the fixed progression3mod4 gives A_i asymptotic to interval_length*M/(2logM). Their product counts distinct semiprime products injectively because the intervals are disjoint. For any fixed odd prime r, conditional on3mod4, the extra condition1modr selects one of r−1 reduced classes modulo4r, by CRT. Thus its pair fraction tends to1/(r−1)². Finitely many r<=T can be summed with an o(1) error for fixed T. The upper bound sum_(odd primes)1/(r−1)²<=pi²/24 is correct and strictly below1.

For T<r<=sqrt M, apply Brun--Titchmarsh to pi(beta_i M;r,1), ignoring the interval lower endpoint and the mod4 constraint for an upper bound. For sufficiently large M, log(beta_i M/r)>=one-third logM uniformly throughout this range; r−1>=r/2. Hence the stated bound C_i M/(r logM) has constants independent of r,M,T, depending only on beta_i. Summing squared counts over integer r>T gives at most C M²/(T log²M). Dividing by A_1 A_2 only changes this fixed constant. Choose T sufficiently large using that constant and the positive margin1−pi²/24, THEN take M sufficiently large for the finite-modulus PNT errors and main-count asymptotics. This order avoids a growing-modulus PNT assumption.

For r>sqrt M the integer-candidate bound is O(M/r+1), uniform in the fixed intervals. Its squared sum through O(M) is O(M^(3/2)+MlogM+M): the three terms come from M² sum r^(−2), M sum r^(−1), and sum1. It is o(M²/log²M). Extending the sum from primes to all integers is a valid upper bound and requires no distribution theorem. Together with the small-prime fraction and intermediate tail this leaves a positive proportion of coprime odd half-orders.

Both prime coordinates being3mod4 makes (P−1)/2,(Q−1)/2 odd. No common odd prime divisor means their gcd is1. Fixed positive lower endpoints give each half-order>16m² eventually, since m³/m²=m→infinity. Local generators of those cyclic subgroups exist, and CRT combines them into a unit gamma with precisely those odd coprime local orders. This is mathematical existence only: the proof uses hidden P,Q to describe the witness and does NOT acquire it publicly or charge factoring/generator construction as free.

The norm-success upper bound remains m^(5+o(1)), since restricting the ambient prime family cannot enlarge its successful subset. The prepared-order existence family still has Omega(m⁶/log²m) products, so its unsuccessful proportion tends to1. The addendum correctly says this defeats only the specified fixed-modulus norm screen: a real preparation branch may already factor those inputs, an acquired gamma could have additional properties, and the literal least-prime selector or adaptive modulus family is not addressed. The old conditional paragraph above is superseded only for EXISTENCE of a base with the displayed odd/coprime-order contract, not for public preparation behavior.

The cited Lenstra--Pomerance Section11 primary formulation supplies exactly the required fixed-q PNT and uniform Brun--Titchmarsh inequality; no stronger uniform asymptotic is needed. No archived files were modified during this review.


## Final q-order refinement

Independently inspected the addendum's new final refinement. PASS. Since m=M^(1/3), Brun--Titchmarsh with modulus m and x=beta_i M has phi(m)=m−1 and log(x/m)=(2/3)log M+O(1). Thus P=1modm primes in either fixed coordinate interval number O(M/(m log M)), with constants depending only on the interval. Multiplying by the other coordinate's O(M/log M) primes and taking the two-coordinate union removes O(M²/(m log²M))=o(M²/log²M) pairs. Ignoring the mod4 and half-order-coprimality filters only enlarges this removal bound, so the previously retained positive proportion survives.

For the remaining primes, m odd and P,Q not1modm imply m divides neither A=(P−1)/2 nor B=(Q−1)/2. Hence gcd(m²,A)=gcd(m²,B)=1. Local gamma generators of orders A,B consequently give ord_P(gamma^(m²))=A and ord_Q(gamma^(m²))=B, both odd, coprime and greater than16m². CRT and coprimality also give ord_N(gamma)=lcm(A,B)=AB>256m⁴. This discharges the extra q-order promise by existence of the same proof-side base; it supplies no public acquisition, actual-preparation failure, literal selected-modulus claim, or adaptive-menu conclusion. The norm-success upper bound is unchanged under the additional restriction. Earlier archived files remain untouched.
