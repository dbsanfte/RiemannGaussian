# Independent review: retained Gaussian lift character and one-step phase killing

2026-10-22. Verdict: **PASS for the stated algebra**, with the global-versus-local character distinction below. This review assumes N=P Q with DISTINCT ODD primes and S_N the Gaussian quartic Jacobi symbol with denominator the FULL rational ideal (N). No factoring-rate, character-surjectivity, or local-fourth-power conclusion is inferred. No searches, code, tests or repository changes were used.

Reviewed against the definitions supplied by the independent algebraic-symbol agent in `algebraic_symbols/cross-twist-symbols.md` and `algebraic_symbols/corrected-cross-order-root.md`.

## 1. Ring and lift existence, including split primes

Let R=(Z/NZ)[i], bar conjugation, and G={z: z bar z=1}. Since N is odd, this is an etale algebra. Locally R_p is either F_(p²) or F_p x F_p; it is REDUCED in both cases. Conjugation is Frobenius in the inert case and exchanges the two components in the split case. Elements of G are units.

For z in G, alpha=1+z satisfies bar alpha=alpha/z. If its norm is a unit, z=alpha/bar alpha. At an odd prime p, norm(alpha)=0 implies alpha²/z=0, hence alpha=0 in the reduced algebra, hence z=-1. This remains true in the split case: the relation bar alpha=alpha/z prevents only one component from vanishing.

Therefore the proposed public procedure is correct:

- gcd(Norm(1+z),N)=1: use alpha=1+z;
- a proper gcd: return a proper factor;
- gcd=N: z=-1 in BOTH local algebras, hence z=-1 modulo N by squarefreeness; use alpha=i, since i/bar i=-1.

The distinct-odd-prime hypothesis matters. Over a nonreduced repeated-prime quotient the inference alpha²=0=>alpha=0 can fail.

### Additional total public lift lemma

One may also avoid exceptional branches by trying exactly

 alpha_t=(1+z)+t i(1-z), t=0,1,2.

Every candidate satisfies bar alpha_t=alpha_t/z. At each local odd prime, norm zero again means alpha_t=0. Two distinct t in {0,1,2} cannot both be bad: their difference is (t-u)i(1-z), and t-u is a local unit, so both bad would imply z=1, whereas then alpha_t=2!=0. Thus each of P,Q excludes at most one of the three candidates. At least one has globally unit norm, recognized with at most three public gcds. Proper gcds may of course be returned as factors instead. This is a total N-only lift selector for G under the same semiprime hypothesis.

## 2. Lift independence and the rational-unit symbol

If alpha and beta are two unit lifts of z, then r=beta/alpha satisfies r=bar r. As 2 is invertible, the conjugation-fixed subring is exactly Z/NZ, so r is a rational unit. The full rational-ideal Gaussian quartic symbol is trivial on every such unit:

 S_N(r)=1.

Locally at p=1 mod4, the two conjugate Gaussian-prime contributions cancel on rational inputs. At inert p=3 mod4, the exponent (p²-1)/4 is a multiple of p-1, so the symbol of a rational unit is 1. Multiplication over P,Q proves the statement.

Consequently tau(z)=S_N(alpha) is independent of the chosen unit lift. The product of two lifts is a lift of the product, so tau:G->GLOBAL mu4 is a homomorphism.

## 3. Local contribution formula

Put epsilon_p=(-1/p), d_p=p-epsilon_p (always divisible by4). Let tau_p denote the p-CONTRIBUTION, interpreted as a global Gaussian phase via the injective embedding of {1,i,-1,-i} in R_p. Then

 tau_p(z)=z_p^(epsilon_p d_p/4).

Split p: write alpha=(x,y), z=(x/y,y/x). The conjugate-prime symbol phases multiply to z^((p-1)/4), with opposite component exponents as required by norm1.

Inert p: bar alpha=alpha^p and z=alpha^(1-p). Thus

 alpha^((p²-1)/4)=z^(-(p+1)/4).

This checks the sign epsilon_p=-1. Both formulas give local norm-one fourth roots, exactly the images of the four global phases.

**Notation caution:** tau(z)=tau_P(z) tau_Q(z) is a PRODUCT OF PHASE CONTRIBUTIONS. Reduction of the global tau(z) at P is not tau_P(z) alone: it includes the Q contribution too. The displayed local contribution formula must not be interpreted as a CRT componentwise definition of tau.

## 4. Global mu4 formula

Let sigma=epsilon_P epsilon_Q=Jacobi(-1,N), k=(N-sigma)/4. Since N=sigma mod4, k is an integer computable from N alone.

Let x=epsilon_P P, y=epsilon_Q Q. Both x,y=1 mod4. The sum of local phase exponents on i is

 c=(x+y-2)/4.

Since xy=sigma N,

 sigma k-c=(x-1)(y-1)/4=0 mod4.

Hence tau(i)=i^(sigma k), and homomorphy gives

 tau(omega)=omega^(sigma k)

for every GLOBAL omega in mu4. The lift 1+i of i has unit norm2, so tau(i)=S_N(1+i) is also valid directly. No local phase choice or hidden factor is supplied to the algorithm.

There are 16 CRT combinations in G[4], not only four. The formula just proved concerns the diagonal/global four phases. Those four are distinct for every odd N, and their pairwise differences are units (norm2 or4), so no accidental global-phase collision is being used.

## 5. The corrected map

Define

 F(z)=z^k tau(z)^(-sigma).

Every global phase has norm1, so F maps G to G and is a homomorphism. As tau(z)^4=1,

 F(z)^4=z^(4k)=z^(N-sigma).

Writing w=tau(z) in global mu4,

 tau(F(z))=w^k tau(w)^(-sigma)
           =w^k w^(-sigma²k)=1.

Thus the character is killed in one step, and

 F(F(z))=F(z)^k,
 F^t(z)=F(z)^(k^(t-1)) for t>=1.

There is no need that k be odd, invertible modulo an unknown order, or that tau be surjective. Also F(omega)=1 for every GLOBAL omega in mu4, so F(omega z)=F(z).

For odd-order z, tau(z)=1 because a homomorphic image of odd order in a group of exponent4 is trivial. Thus F(z)=z^k on the already prepared odd-order subgroup; the retained-lift character does not create a fresh colour there.

## 6. Scope of the killed phase

The conclusion tau(F(z))=1 is the GLOBAL product-character statement. It does NOT assert tau_P(F(z))=tau_Q(F(z))=1 individually. Opposite local phases may cancel. In particular membership in ker(tau) is not equivalent to being a fourth power in G, and the map must not be described as killing all independent local fourth-root phases. Likewise its behavior does not imply that a public colour distinguishes the hidden local factors.

The original 1+z lift algorithm is factor-or-value total under the semiprime hypothesis. The three-candidate lift gives a total value selector if desired. Computing S_N remains the inherited public Gaussian-symbol operation. All additional lift checks and phase operations have constant or polylogarithmic arithmetic cost. No long collision product or annihilator has been acquired by these identities.

## Final verdict

The retained lift, rational-unit quotient, split/inert sign, global phase law, fourth-power identity, killed global character, odd-order triviality and iteration formula are consistent. The result corrects the earlier direct-norm-one-symbol collapse by evaluating the symbol on a lift; it is an algebraic phase/root operation, not a guaranteed factoring-rate improvement.
