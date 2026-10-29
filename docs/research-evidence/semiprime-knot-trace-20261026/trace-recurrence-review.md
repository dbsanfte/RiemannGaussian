# Independent review: common trace and coloured incidence recurrence

26 October2026. Read `trace-recurrence.md`, its current Farey companion, and the inherited native/swap contracts. The output-sensitive incidence acquisition, fixed-centre uniqueness, actual expanded-degree example, and carry-aware matrix recurrence pass. This establishes acquired structure and coverage, not a whole-query scalar algorithm. No numerical tests or repository edits.

## Incidence enumeration is genuinely soft k

For nonaxis a,b put g=gcd(a,b,k), n=k/g. If a unit j solves aj²=bN modk, division by g gives (a/g)j²=(b/g)N modn. For every prime dividing n, at least one of a/g,b/g is a unit by definition of g. Equality and j,N units then force BOTH to be units. Hence the algorithm's rejection test is necessary, not an unjustified cancellation. Once they are units, the square congruence modulo n is equivalent to the original one.

Since n divides2·3^e, there are at most two unit square roots modulo n (one in the trivial/parity cases). The derivative lift at3 is invertible and the parity/3-parts combine by elementary CRT. Each root has g candidate lifts modulo k; filtering unit j does not invalidate the O(g) work bound. The pair count for coefficients divisible by g is O((k/g²)logk), so summing g times that count over g|k gives O(klogk sum_(g|k)1/g)=soft k. This bounds rejected lifts as well as retained outputs. The O(klogk) signed-product enumeration and all polylogarithmic arithmetic fit the same bound. The n=1 convention is harmless; axes are separately enumerated with4phi(k) incidences.

Every actual stationary witness is represented by j=P modk and its canonical lambda_j. Swap maps j to N j^-1 modk and preserves the phase, as checked by taking that lift modulo H and its inverse jN^-1. Thus this coloured subset has the stated all-semiprime coverage; enumerating colours is not a selected-colour oracle. Literal duplicate rows may be merged only while keeping all incidence/decoder metadata. Existing public deletion and unit-certified pruning retain their original survival proof.

## Fixed-centre uniqueness and the expanded degree

For equal(s,lambda), the root congruence gives S=H/4 dividing ab−a'b'. Its magnitude is<2k<S on k>16, so the integer products coincide. Equal sum and product determine the same unordered integer pair, including signed/axis cases. Different integer centre labels s(N+1)/2+lambda cannot agree because a unit change in s exceeds the entire lambda width. This is integer-label uniqueness; local beta-powered aliasing is correctly left to factor-aware separation tests.

The b=1 subfamily with k/2<=a<k, a odd, aN=1mod3 has Theta(k) choices. Its unit square congruences have actual native roots; d=a−1 has magnitude Omega(k). Diagonal and axis deletion do not affect these rows, and swap/opposite identification changes counts only by constants. Thus their formal common-Z product has degree Omega(k²), with a unit leading coefficient at any supplied unit t: each NONDEGENERATE factor contributes −t u_j times the monic D_|d|.

Precision: the blanket degree statement should explicitly restrict to d!=0, as the actual paid nondegenerate pair interface does. A d=0 factor is independent of Z and equals(t−u)², which need not be a unit merely because t is a unit. It can be omitted after the old unit-certified diagonal prepass, or its value can be tested/handled separately. This qualification does not change the genuine Omega(k²) nondegenerate subfamily calculation. The bound concerns expansion in formal Z with centres fixed, not arbitrary implicit use of the acquired scalar Z.

## Matrix algebra, tau signs and finite boundary

Here tau=floor(mu_j/H), whereas Farey's tau is defined by lambda=L+H*tau and has the opposite sign. Each report is internally consistent when kept separate. The two diagonal entries of Mtilde are the unwrapped original and same-lambda swap exponents. Since lambda=mu−Htau, M=q^(-tau)Mtilde, exactly as printed.

For the sum, tau_(v+w)=tau_v+tau_w+c_+, and for the difference tau_(v−w)=tau_v−tau_w+c_-. These identities give both printed matrix products. Applying the integral2-by2 determinant-weighted trace identity yields equation(3) with the stated det(M(w)) and q^c_- coefficient. The unwrapped line recurrence follows by Cayley–Hamilton, including negative indices when its unit determinant is used. The stated coefficients/seeds are acquired from two short-bit lattice-basis matrices per colour, so the total input is genuinely soft k.

Small prose correction: recovering the native trace FROM Ttilde multiplies by q^(-tau_n), not q^(+tau_n). The displayed matrix formula and shifted-comparison equation(5) already have the correct signs. Equation(5) shows why dropping carries changes the physical interval.

The support counterexample2(a,1) correctly leaves |ab|<k. A known out-of-band character remains an acquired algebraic value, but is not an original query leaf. The report correctly refuses to assign additive trace zeros, new boundary comparisons or shifted endpoints an original annihilator decoder without a new proof. A selected index/colour would have a paid old consumer, but computing its trace is not selection.

## Conclusion

The common-trace sharing and the stronger coloured incidence/recurrence are valid initialized interfaces. The family retains actual coverage, with output work charged rather than a k-by-k table. Fixed centres do not furnish long colour strings, formal expansion has the stated actual growing degree, and the finite hyperbolic/clock boundary stays explicit. The two small sign/diagonal qualifications above suffice; no full-query or sixth-exponent advance follows from the current recurrence.

Integration note: the nondegenerate-factor restriction and the q^(-tau_n) recovery sign have been incorporated into the report.
