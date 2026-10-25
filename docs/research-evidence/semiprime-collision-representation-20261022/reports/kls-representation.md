# Constructive source representation search: an exact positive Jacobi kernel

22 October 2026. New scratch construction; earlier packets unchanged. No examples, backend or claim of a completed near-linear query. Two candidates were pursued: a convex rounding carrier and an exact labelled positive kernel. The latter gives a proved restriction-stable representation and a concrete additive contraction target, with its cost still explicit.

## Candidate 1: convex row-lattice rounding, resolved limitation

For one actual tag j, write P=j+mh. Its row equation gives I*P=a h²+b h+c, equivalently m²I=aP+N/P+ellrow. The real function of P is convex for P>0. Its EPIGRAPH is therefore a public convex relaxation, and one can place a log-concave measure on an explicitly bounded portion. However the exact factor candidates are on the boundary aP+N/P+ellrow=m²I and also satisfy integer congruences. A continuous density assigns zero mass to that exact curve. Rounding an epigraph point to (h,I) does not preserve the boundary identity. A narrow neighborhood bounded on BOTH sides by the graph is not justified as convex by epigraph convexity. In particular uniform covariance or a dimension-free Poincare estimate proves no lower bound for rounding into the two true divisor cells.

This resolves this specific naive relaxation: no source-preserving rounding argument was obtained from its convexity. It is not a theorem excluding another convex lift. Rather than assuming a rare-boundary mass bound, the second candidate encodes the useful local collision exactly.

## Candidate 2: public character features with exact nonnegative same-leaf energy

Assume the project input N=P Q is odd squarefree with distinct primes. Let chi(x)=Jacobi(x,N), including chi=0 at nonunits. This is PUBLIC and computed in polylog N work for a supplied integer x. For any scalar residue a define the public real vector

    psi_a(t)=chi(t+a), t in Z/N,
    Phi_a(t,u)=psi_a(t)*psi_a(u), (t,u) in (Z/N)^2.

No hidden local Legendre symbol or zero projector is an input. The complete correlation is exactly

    K(a,b)=sum_(t modN)chi(t+a)chi(t+b)=c_N(a-b),

where the last notation is only a description of the proved value. Proof: CRT separates the sum. At an odd prime p the sum is p-1 if a=b modp, and -1 otherwise. The latter identity follows by counting solutions of z²=(t+a)(t+b): after an invertible affine change when a!=b it is the elementary quadratic-character sum of x²-1. Thus no supplied factor is used by the definition or computation oracle for the features; P,Q occur only in the proof.

Consequently

    <Phi_a,Phi_b>=K(a,b)^2.

Define the INTEGER leaf energy W(a,b)=K(a,b)^2-1. Its exact cases are

    0                         if gcd(a-b,N)=1,
    (P-1)^2-1                 if a=b modP but not modQ,
    (Q-1)^2-1                 if a=b modQ but not modP,
    ((P-1)(Q-1))^2-1         if a=b modN.

Every energy is NONNEGATIVE and it is positive iff the original scalar difference is a nonunit. In particular a local P-only hit is retained; this is not merely a representation of global equality. The tensor square removes the sign cancellation in the first Jacobi correlation. No conjugate component, norm or mixed-leaf inference is needed.

For actual scalar target/seed sets Y and S, with labels retained and multiplicities allowed, the exact aggregate is

    E(Y,S)=sum_(a in Y,b in S)W(a,b)
          =<sum_a Phi_a, sum_b Phi_b>-|Y|*|S|.       (1)

It is a nonnegative integer, zero iff EVERY original scalar leaf is a unit. This is an exact representation of the desired collision support, not only an applicability hypothesis. Whole native coverage implies E>0 unless a preceding branch already factors. Its bit length is O(log N+log(|Y||S|))=O(log N) in the retained polynomial-size regime.

The same formula works for supplied complete pair groups, original unmasked intervals, arbitrary supplied target restrictions and seed subintervals. Additivity and nonnegativity give exact one-path localization: if E(parent)>0, one child must be positive; evaluate a child and select it if positive, otherwise the other. Binary pair localization, then the two original row descents, reaches a genuine scalar leaf. Compute its gcd; proper factors finish, saturation uses the original certified nonzero gamma exponent and decoder. Thus representation and recovery are proved, including the saturated branch. It is not an acquired QUERY until (1)'s contraction is computed cheaply.

## What is actually paid and what is not

The feature family has a short public oracle: any entry chi(t+a)chi(u+a) is acquired in polylog N. The original native Y descriptions, geometric seeds and all label/carry metadata remain soft m inputs. But a short entry oracle is not evaluation of the aggregate. Materializing Phi has N² coordinates, and even a single sampled pair (t,u) asks for the seed-side sum

    B_S(t,u)=sum_(b in S)chi(t+b)chi(u+b),

with |S|~m² geometric scalars. Its naive evaluation costs m² Jacobi calls; it is NOT assumed a soft-m primitive. The target-side sum costs O(J), but this does not pay B_S.

An exact alternate expression requiring only two PUBLIC shift parameters is

    E=N²*E_(uniform t,u)[A_Y(t,u) B_S(t,u)]-|Y||S|,
    A_Y=sum_(a in Y)chi(t+a)chi(u+a).              (2)

Equation (2) is a conditional intermediate bridge: a near-linear, certified computation of this PARTICULAR complete bilinear character average would solve the query with the proved positive localization interface. It is additive rather than the old multiplicative H product and its source positivity is already established. It cannot be treated as paid merely because it has two parameters.

Crude sampling does not provide the required guarantee. A single balanced P-only leaf contributes only about N^-1 to E/N², while complete character averages have cancellation before the tensor square. KLS does not turn that small expected signal into inverse-polylog event mass. Furthermore any certified approximation to E must have absolute error below1/2 to recover it by rounding; estimating the NORMALIZED expectation in (2) therefore requires absolute error below1/(2N²), unless a stronger support-gap theorem and properly scaled decision threshold are used. No such cheap estimator or concentration bound was proved here.

A standard Gaussian measure on the feature space is indeed an explicit isotropic log-concave carrier: linear functions with coefficient vectors Phi have the stated covariance. But its KLS/Poincare bound is already dimension-free independently of the new paper. Evaluating those linear functions requires the same unacquired feature contractions, and covariance identities do not give collision mass. Invoking that Gaussian as a free oracle would hide the query, so this is NOT the claimed all-input representation satisfying all three computational conditions.

## Exact shared budget and next contraction

The paper's direct-sum/same-family principle is realized algebraically here: each native leaf has its own nonnegative W and the aggregate is additive with no loss. Every restriction uses the SAME feature family and the budget is EXACT, not a separate existential low-loss family at each level. What is absent is the paper-inspired compression of that budget into a paid scalar contraction.

A useful next lemma would evaluate (2), or a rigorously positive low-dimensional substitute with identical zero support, in soft O(|Y|+sqrt(|S|)) bit work for the actual native geometric S, uniformly under complete-pair restrictions. It may use the public Jacobi oracle and original gamma but not unknown factors, hidden zero projectors, supplied eigenvectors, or unacquired normalizers. Any approximation must retain the integer gap and charge precision. This is a concrete new additive-character query with a proved source/recovery bridge, not a list of unspecified positivity assumptions.

Result: the naive convex carrier fails its explicit rounding-source step, so the investigation changed candidate. The second candidate DOES provide an exact public positive same-leaf representation and valid localization, but its complete character contraction remains unpaid. No near-linear collision query or new factoring exponent is claimed. Residue agent's algebraic-orbit construction is complementary; no assumption from it was used as a free oracle here.

## Further constructive contraction: exact geometric boundary update

Write S_L={q^i:0<=i<L} with its index labels. The seed feature sum obeys an acquired O(1) update along a simultaneous scalar orbit:

    B_L(qt,qu)=B_L(t,u)
      +chi(t+q^-1)chi(u+q^-1)
      -chi(t+q^(L-1))chi(u+q^(L-1)).             (3)

Proof: factor q from both Jacobi arguments and use chi(q)^2=1, since q is a unit. Reindex i to i-1; no complete-period or hidden-order assumption is used. This is an exact additive boundary budget for the NEW positive-kernel representation, with all native geometric carries retained. It applies to arbitrary supplied t,u, including nonunit arguments, because Jacobi multiplicativity remains valid there. For a supplied length-T simultaneous q-orbit, one startup value B_L(t,u) and O(T) public Jacobi products acquire all T sliding sums. There is no repeated length-L cost after the startup.

A direct-sum orbit of these values therefore has a genuine telescoping mechanism; it is not signed cancellation asserted to preserve a collision. The representation's final energy remains the proved nonnegative scalar (1). The complete t,u contraction, however, must still supply initial B_L for every needed orbit and its target-side weighting. The action on all pairs has many orbits and neither their startup values nor their aggregation are paid by (3). On the diagonal t=u, B_L(t,t)=L minus the number of nonunit t+q^i. Thus that especially tempting startup is ALREADY a scalar collision count, not an automatically known value. The paid scalar q-factorial supplies a PRODUCT/Jacobi parity of these terms, not their sum; those outputs cannot be substituted.

## Witness amplification gives a public decision gap

The earlier exact rounding-to-an-integer requirement is stronger than necessary for detection. On the retained P,Q>16m² branch, every positive leaf W is at least

    G0=256m^4-32m²,

because P(P-2),Q(Q-2)>G0. Consequently E is either0 or at least G0, regardless of balance. A certified approximation E_tilde with absolute error<G0/4 gives a correct zero/nonzero decision by threshold G0/2. The same gap holds under every target or interval restriction containing any collision, so approximate scalar GROUP queries with this certified error would suffice for deterministic binary localization. There is no need to recover E to accuracy1/2 unless its exact integer value is sought.

For balanced factors one useful local leaf contributes order N, versus the all-unit baseline |Y||S| of order m³. This is real signal amplification, but its computational value depends on estimating the raw complete character contraction. Under uniform independent t,u the expected signal is E/N², only about1/N for one balanced local leaf. A sampled product A_Y B_S may have absolute size |Y||S|, and each seed sample still contains a long Jacobi sum. No variance/control-variate theorem delivering error G0/4 in total softm has been proved. Equation (3) is a possible amortized tool for such a theorem; it does not supply one by itself.

The full kernel also admits the exact nonnegative decomposition

    W(a,b)=P(P-2)1_(a=b modP)
           +Q(Q-2)1_(a=b modQ)
           +P(P-2)Q(Q-2)1_(a=b modN).

This proves positive semidefiniteness and identifies the same-leaf source weights, but P,Q and their equality projectors are PROOF objects, not production inputs. In particular the positive identity-component weight does not justify a paid small-dimensional exact feature map. The public Jacobi definition, explicit boundary update and certified decision gap are the actual acquired/symbolic constructions established here.
