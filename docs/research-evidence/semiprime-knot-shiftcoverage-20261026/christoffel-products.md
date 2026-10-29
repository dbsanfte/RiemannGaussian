# Christoffel/Beatty products: a paid first Euclidean split

26 October2026. Fresh bounded primary-source probe and finite derivation. Executed an exact quotient-block split for the specified product and charged its scalar initialization. Christoffel word compression and short rational generating functions are genuinely available, but the inspected theorems do not give its scalar product at polylogarithmic cost per colour. No root-of-unity assumption on native U,V is made. No repository edits or numerical campaign.

## 1. Exact product and a completed scalar algorithm

Take1<=theta<k with gcd(theta,k)=1, and supplied unit U,V,z. Set

    W=U*V^theta, C=V^(-k),
    P_theta(z;U,V)=product_(a=0)^(k−1)
                (1−z W^a C^floor(a*theta/k)).        (1)

This is exactly the requested modular-residue product. Group by r=floor(a*theta/k). For0<=r<theta put

    A_r=ceil(r*k/theta),
    L_r=ceil((r+1)*k/theta)−A_r,
    x_r=z W^A_r C^r.

Then the initialized finite identity is

    P_theta=product_(r=0)^(theta−1)(x_r;W)_(L_r).    (2)

Every L_r is h or h+1, h=floor(k/theta). Group their acquired starts by these two lengths. Apply the INHERITED joint geometric-product backend separately to each group: with J_g starts and length h_g it costs soft(J_g+sqrt(J_g*h_g)), using actual baby polynomials and monic multipoint trees. Since sum_g J_g*h_g=k, the total is soft(theta+sqrt k). Integer ceilings, powers and all starts are included. No1−W^n inverse or collision value is used: kernel factors are built by multiplication and evaluation divisors are monic. Thus it works without a native-order guard for W, including W=1, C=1 and repeated starts. This pays a scalar completion of the first quotient, but it is a use of the OLD backend rather than a new fast algorithm. Materializing full degree-h kernels also gives the weaker alternative soft(h+theta); it is not the claimed best completion.

The exact reindexing by b=a*theta modk also gives

    P_theta(z;U,V)=P_(theta^-1 modk)(z;V,U).         (3)

A second exact identity is the CLEARED reflection

    (1−z V^k) P_(k−theta)(z;U,V)
       =(1−z) P_theta(z V^k;U,V^-1).               (4)

Its boundary factors may be nonunits or zero, so equation(4) must not be used by numerical division. There is, however, an OPERATIONAL division-free reflection: compute the theta'=k−theta product with parameters z'=z V^k, U'=U,V'=V^-1, OMIT its a=0 factor, and multiply1−z. For every a>=1, the transformed factor equals the original factor exactly. In the quotient-block algorithm only the first block changes: its start moves from a=0 to a=1 and its length decreases by1, with an empty block skipped. Thus reflection is fully usable at zeros, without normalizer inversion. Combining this with(3) gives per-colour cost soft(min{theta,k−theta,theta^-1 modk,k−(theta^-1 modk)}+sqrt k), by the inherited backend. Formula(4) is just its cleared boundary ledger.

## 2. What Christoffel compression proves—and what it leaves

Primary source: Berstel–Lauve–Reutenauer–Saliola, *Combinatorics on Words: Christoffel Words and Repetitions in Words*, author draft https://webpages.math.luc.edu/~lauve/papers/wordsbook.pdf, Chapters3 and7; published https://doi.org/10.1090/crmm/027. Standard factorization and continued fractions give recursively concatenated/powered words for coprime rational slopes. Their coprime-word hypotheses apply to the mechanical word with theta ones and k−theta zeros here (the Christoffel path slope is theta/(k−theta), rather than confusing its path length with theta/k). They describe the word and its evaluation under an ACTUAL fixed-dimensional monoid morphism; they do not assert a fast value for a product of all prefix monomials.

For this product a correct transfer acts on functions of z:

    T_c f(z)=(1−z) f(cz),

where each letter c is W or WC according to the increment of the Beatty floor. A concatenated block is represented by an endpoint multiplier c_block AND its entire scalar prefix-product function f_block(z). Repeating a block n times requires product_(t<n) f_block(c_block^t z). This is the new geometric-orbit product, not ordinary powering of the single scalar f_block(z).

Already a constant-letter run has

    T_W^n 1=(z;W)_n,

with its usual initialized soft sqrt n scalar algorithm. A continued-fraction word with a huge quotient can therefore be short while its required run normalization is an actual finite Pochhammer. This tests this particular transfer interface; it is not a lower bound excluding another representation. A productive future theorem would evaluate the recursively changing run normalizations jointly with paid starts, rather than merely binary-power a formal operator.

The first quotient algorithm(2) materializes theta block starts. Its degree-h kernel is shared, so the cost above is better than theta independent factorial calls; this is the concrete split tested here, completed by the old backend. Across all native colours theta=j²/N modk has phi(k)/2=k/6 distinct values, each from two colours. Summing theta starts in this explicit implementation is quadratic scale. Even choosing the cheapest of theta,k−theta,theta^-1,k−theta^-1 before materialization does not make this one-level constructor soft k: at most4x distinct slopes have that minimum<=x, so a linear-size slope family still has a quadratic sum of these minima. This is only a cost bound for MATERIALIZED first-quotient starts, not for a recursive/compressed evaluator or a coverage-preserving colour subset.

## 3. Short rational generating functions: an exact but different scalar

Barvinok–Woods, *Short rational generating functions for lattice point problems*, https://arxiv.org/pdf/math/0211146, Theorem1.7, gives polynomial-time short rational SUM descriptions for integer-point projections of rational polytopes in FIXED dimension. The graph b=a theta−k r,0<=a,b<k, is such a fixed-dimensional integer set with O(logk)-bit input. Hence the additive character sum

    R_theta(U,V)=sum_(a=0)^(k−1)U^a V^(a theta modk)

has that legitimate short rational representation. It is not the product(1).

The precise bridge would be the formal characteristic-zero identity

    log P_theta(z)=−sum_(n>=1) z^n R_theta(U^n,V^n)/n. (5)

To recover the full degree-k polynomial this requests precision k and k power sums. At native N all1..k are units because P,Q>16H, so the small integer denominators themselves are not the issue. But the short rational representation's monomial denominators can vanish after specialization; cancellations must be performed formally or by a proved confluent algorithm. No such denominator is declared a unit from a generic generating-function theorem. More fundamentally, computing only a few formal coefficients does not acquire its value at a supplied unit z; its omitted z-tail is not nilpotent. The source's counting/specialization algorithms do not state a polylog scalar multiplicative readout for(1).

Equation(5) is therefore a precise possible future interface, not an algorithm claimed here. Truncating at k and explicitly acquiring all power sums/coefficient outputs has at least the degree-k output scale in that implementation, per colour. No infinite analytic product or formal logarithm is evaluated at a native collision.

## 4. Native specializations and coverage conditions

The stated native inputs have known short integer exponents

    U=beta^(1−j), V=beta^[N(1−j^-1)],

with canonical1<=j<k and inverse1<=j^-1<H. The colour j=1 has U=V=1 and P=(1−z)^k, genuinely cheap. For j!=1, V^k has a NONZERO known exponent kN(1−j^-1). A proper gcd of V^k−1 factors N; a saturated equality gives that short global beta-annihilator and the licensed extractor. Thus in soft k across the supplied colours one may factor or certify V^k−1 unit for every nontrivial colour. A root-of-unity collapse C=1 cannot silently be assumed on their continued branch. This is an elementary applicability check, not a query improvement.

The product in the question includes all modular graph points0<=a<k. Actual native admission additionally requires the signed |ab|<k cutoff (or specified axes) and canonical lambda carry; the unwrapped monomial U^a V^b differs from beta^E by q to that row's acquired carry. Thus even a fast evaluator for(1) would need an additional finite-mask/boundary theorem to yield the full native physical query. Conversely the a=0 term is1−z, which is a known unit for the actual nonzero guarded q-clock phases but a tautological zero at z=1; it must be treated with its actual physical start.

No theorem above removes these original carry/window obligations or proves fewer colours cover every semiprime. Source word identities and(2)–(4) are finite and valid over the modular ring; their scalar costs and boundary factors remain as explicitly charged.

## Result

The executed mechanism is the exact two-length quotient-block split(2), with inherited-backend cost soft(min{theta,k−theta,theta^-1,k−theta^-1}+sqrt k) and operational division-free inversion/reflection; this is not a new algorithmic advance. The fresh primary theorems provide compressed Christoffel WORDS and additive rational GENERATING FUNCTIONS, not the missing multiplicative scalar theorem. Recursive Euclidean batching of the run normalizations, with all starts and physical masks retained, is a specific future lead. A polylog-per-colour product, joint soft-k zero oracle or factoring exponent gain is not established.


## Balanced full-box coverage connection (conditional geometric scope)

The parent supplied a useful alternative coverage interpretation; it does not initialize its scalar product. At the true colour j=P modk, all k vectors a=0,...,k−1, b=[a theta]_k are stationary. Their CANONICAL phases give integer indices in

    0<=I<((k−1)(P+Q))/H+1.

If all k indices are distinct, a nearest gap has magnitude at most (P+Q)/H+1/(k−1); duplicate indices give gap0. In the constant-balance range P+Q=O(sqrtN), this is O(k) since sqrtN<=k³. Differences have |A|,|B|<k and B!=0 because theta permutes residues. The two stationary equations imply the exact nonliteral gap

    E_2−E_1−H*(I_2−I_1)=(P−1)(B Q−A)!=0.

Thus an acquired full-box pair comparison at the appropriate short shift would have a valid proper-gcd or short global-annihilator consumer, even though its difference vector need not meet the old |AB|<k mask. This follows from the general short-label extractor, not from pretending the difference is an original bounded-hyperbola row.

There are still k nodes per colour, hence quadratic acquisition across all colours if materialized. Moreover(1) uses UNWRAPPED character phases: the actual canonical-phase full-box polynomial has the row-dependent q-carries from the coloured recurrence packet. Its index gap is O(k) only in the stated balanced range, not uniformly over every prepared unbalanced semiprime. A compressed Christoffel evaluator retaining those carries could therefore connect to a real new short-shift cover, but neither the word theorem nor the paid first split(2) proves such an evaluator or a guaranteed all-semiprime target bound.
