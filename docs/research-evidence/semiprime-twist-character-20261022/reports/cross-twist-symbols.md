# Algorithmic algebraic characters and cross-twist cancellation

22 October 2026. Exact paper-level derivations and a deterministic Gaussian-symbol implementation are supplied. No universal annihilator or sixth-root factoring algorithm is obtained. In particular, the extra phase of a nonrational numerator is retained below rather than discarded by replacing every symbol with its norm Jacobi value.

## 1. The actual Gaussian character at each hidden prime

Let F=Q(i), α=a+bi, gcd(a²+b²,N)=1, and N=P Q odd squarefree. Define S_n(α)=(α/(n))_4, the quartic Jacobi symbol with the full rational ideal (n) as denominator. Its values are the four *global* roots μ4={1,i,−1,−i}. Put

    e_p=(-1/p), d_p=p−e_p, z_p=α/barα mod p.

Here z_p is in the norm-one subgroup of the quadratic étale algebra F_p[i], including its split version. Always 4 divides d_p. The exact local formula is

    S_p(α)=z_p^(e_p*d_p/4).                         (1)

If p=1 mod4, choose t²=−1 modp. The two Gaussian prime factors of (p) evaluate α at a+bt and a−bt; interpreting both symbols in the same μ4 gives the quartic character of their ratio. This proves (1) with exponent (p−1)/4.

If p=3 mod4, (p) is inert with residue field F_(p²). Its defining symbol is α^((p²−1)/4). Since barα=α^p and z=α^(1−p), this equals z^(−(p+1)/4). Thus (1) covers both local torus signs without a hidden choice of embedding.

Consequently

    S_N(α)=S_P(α)*S_Q(α),
    S_p(α)^2=(a²+b²/p),
    S_N(α)^2=Jacobi(a²+b²,N).                       (2)

The quartic phase is an actual extra bit beyond the single value on the right of (2). For example, for α=−1+2i, N=21 and69 both have Jacobi(5,N)=1, but S_N(α)=1 and−1 respectively. This is an exact phase distinction, not a factoring success claim.

## 2. A fully paid algorithm and the reciprocity formula

Check gcd(a²+b²,N) first: a proper gcd factors; a zero norm modulo both primes does not license a symbol query on a unit and is skipped or handled by its existing exact factor test. For unit inputs, compute S_N(α) by Gaussian Euclidean descent with quartic reciprocity and the (1+i),i supplements. The accompanying check_formulas.py contains an actual exact implementation. Gaussian remainders reduce positive norm by at least a factor two, with coordinates bounded by the input bit size B=O(log N+log(2+|a|+|b|)). Straight integer arithmetic gives a conservative O(B³) bit bound. Thus soft-O(m) explicitly generated O(log N)-bit numerators cost soft O(m) in total; all input reading and every symbol query are charged.

Let σ=Jacobi(−1,N), λ=σN, so λ=1 mod4 is a primary Gaussian integer. For an odd primary α, Gaussian reciprocity specializes to

    S_N(α)=(λ/α)_4.                                 (3)

The reciprocity correction is 1 because λ is rational and λ−1 is divisible by4. For general α=(1+i)^v i^k α0 with α0 primary,

    S_N(α)=i^[v(λ−1)/4] * Jacobi(2,N)^k * (λ/α0)_4. (4)

All arguments on the right are public. In particular, for fixed α this is a Dirichlet character of rational N, with a sufficient explicit period 16*Norm(α0). The additional phase is therefore a product character of P,Q and follows from N modulo an acquired public modulus; it is not a selected hidden local phase. This is an exact reciprocity identification, not a lower bound for algorithms using such characters adaptively.

## 3. Explicit cross-parameter cancellation, retaining the extra phase

Use the existing Cayley numerator α_a=a+i. Assume a(a²+1) is a unit modulo N, checking its gcd first. Rational inverse parameters are represented modulo N; multiplying a numerator by a rational unit has quartic symbol1. Set s=S_N(a+i) and j2=Jacobi(2,N). Direct Gaussian identities give

| Parameter | Public quartic phase |
| --- | --- |
| a | s |
| −a | s^(−1) |
| 1/a | j2*s^(−1) |
| −1/a | j2*s |

These hold locally at each P and Q too, replacing j2 by (2/p). They therefore include every hidden split/nonsplit sign branch. They use only α_(-a)=−barα_a and α_(1/a)=i*barα_a/a.

Any signed product over this four-point orbit is exactly

    j2^F*s^E,
    E=c_a−c_(-a)−c_(1/a)+c_(-1/a),
    F=c_(1/a)+c_(-1/a).

If E is odd, the extra quartic phase survives; it is exactly the original s or its inverse times explicit quadratic colours. If E is even, (2) reduces the expression to Jacobi(a²+1,N) and j2. Examples are

    s(a)*s(−a)=1,
    s(a)*s(1/a)=j2,
    s(a)/s(−a)=Jacobi(a²+1,N).

Thus this actual twist/reciprocal orbit admits cancellation, but does not yield a second independent equation isolating one prime's torus character. Four queries cost polynomial in log N; equivalently one quartic query and two ordinary Jacobi values reconstruct the entire orbit.

The same phenomenon is explicit on a norm-one point z=α/barα itself:

    S_N(z)=S_N(α)^2=Jacobi(Norm α,N).                (5)

One must query a non-norm-one numerator α to retain s, rather than assume the extra phase exists on z.

## 4. Cancelling a known norm square

A proposed controlled-norm coupling can force both hidden quadratic norm signs to +1, but its cost is loss of the quartic bit. If α=a+bi and Norm α=c² is a known rational square, put β=a+c+bi. The exact identity

    β²=2(a+c)α,  Norm β=2c(a+c)

gives, whenever its rational denominator is a unit,

    S_N(α)=Jacobi(2c(a+c),N).                       (6)

A proper gcd in a+c already factors. If gcd(a+c,N)=N while c is a unit, then b=0 modulo N and α is a rational numerator modulo N, with symbol1. This covers the exceptional denominator case, rather than silently dividing through it.

For two Gaussian numerators A,B, any coupling whose norm ratio Norm A/Norm B is a known rational square can be treated by applying (6) to A*barB after clearing rational denominators. Cancelling only the *public Jacobi values* is weaker: it says the two hidden norm signs agree, leaving both the (+,+) and (−,−) branches. A retained phase −1 then still permits local pairs (1,−1),(−1,1),(i,i),(−i,−i). No branch has been identified merely from that cancellation.

## 5. Full octic inputs and all rational-prime branches

Let K=Q(ζ8), α in Z[ζ8], coprime to N, and T_N(α)=(α/(N))_8, computable by Joye's fixed-field octic algorithm. For a hidden odd prime p put f=ord_8(p): f=1 for p=1 mod8 and f=2 otherwise. Choose a primitive eighth root z in F_(p^f). Representatives for the Frobenius orbits of j in {1,3,5,7} may be chosen as follows:

| p mod8 | f | Orbit representatives |
| --- | --- | --- |
| 1 | 1 | 1,3,5,7 |
| 3 | 2 | 1,5 |
| 5 | 2 | 1,3 |
| 7 | 2 | 1,3 |

For each representative j define h_j modulo8 by

    α(z^j)^((p^f−1)/8)=z^(j*h_j).

Then the exact local value is T_p(α)=ζ8^(sum_j h_j), and T_N=T_P*T_Q. This is a proof-only formula for the hidden local values; production symbol evaluation uses no hidden p or finite-field embedding.

Let σ_j act by ζ8→ζ8^j, let η=α*σ5α=Norm_(K/Q(i))(α), and let r=Norm_(K/Q)(α). Galois equivariance and norm compatibility give the cross-twist identities

    T_N(σ_jα)=T_N(α)^j,
    T_N(α)^2=S_N(η),
    T_N(α)^4=Jacobi(r,N).                           (7)

The second equality explicitly retains an extra Gaussian quartic phase, not just its quadratic square.

For T=T_N(α), the actual relative-torus quotient couplings are

| Coupling | Retained phase |
| --- | --- |
| α/σ3α | T^(−2)=S_N(η)^(−1) |
| α/σ5α | T^(−4)=Jacobi(r,N) |
| α/σ7α | T^(−6)=S_N(η) |

The full four-conjugate product has symbol T^(1+3+5+7)=1. An arbitrary weighted Galois-orbit product has symbol T^(sum_j j*c_j): odd total exponent retains the original octic phase, even exponent reduces to the Gaussian/quadratic phases in (7). In particular a cross-twist norm-one quotient can retain a quartic phase, but this is the already computable symbol of the explicit relative norm η, still a product across P,Q.

For Gaussian numerators α in Q(i), the octic symbol in K gives no further bit:

    T_N(α)=S_N(α)^(−1).                             (8)

To verify (8) prime ideal by prime ideal over F=Q(i): if its norm n=1 mod8, the two split lifts contribute U*U^5=(U²)^3, the inverse quartic symbol. If n=5 mod8, the inert lift has exponent (n²−1)/8=((n−1)/4)*((n+1)/2), where (n+1)/2=3 mod4, again the inverse quartic symbol. These exhaust odd Gaussian prime-ideal norms.

## 6. Octic reciprocity also exposes the public residue datum

For a primary octic numerator α0, Joye's reciprocity theorem with the same rational primary λ=σN specializes to

    T_N(α0)=(λ/α0)_8.                              (9)

Indeed Norm_K(λ)=N^4, so (N^4−1)/8 is even, and the relative cross terms d(λ),f(λ) vanish. If α=(1+ζ8)^v ζ8^k ε^l α0 with ε=1+sqrt2, its rational-denominator supplements are

    T_N(ζ8)=ζ8^((N²−1)/4),
    T_N(ε)=1,
    T_N(1+ζ8)=ζ8^((N²−1)/8).

Thus a sufficient explicit rational period for fixed α is 64*Norm_K(α0). This gives actual computable, nontrivial higher phases, with no substitution of Hittmeir's rational CRS oracle. The Gaussian implementation above has a complete conservative bit charge. For full octic inputs, the primary fixed-field algorithm is available; no new universal recovery claim here relies on an unaudited sharp bit bound for its norm-Euclidean implementation. All Galois-orbit values can in any event be recovered from a single such symbol query and fixed-degree relative norms; they are not free independent queries.

## 7. The exact missing datum after these cancellations

The computed S_N or T_N is one global root of unity equal to a product of hidden local roots. It is not the CRT-valued tuple of those roots. Multiplicative norm/Galois couplings above either retain that same phase or reduce it to an explicitly paid lower symbol; none computes an asymmetric local quarter-power.

For example (1) would supply CRT values z_p^(e_p d_p/4) if the unknown p-dependent exponents were available. Computing that CRT-valued element is a different operation from returning its product in μ4. When its local values differ, comparison against μ4 constants by gcd would factor. No algorithm producing it in soft O(m), or a guaranteed useful native-row character count in that time, was obtained here. Several unrelated/adaptive numerators could still be useful; these calculations are not a generic lower bound excluding them. The absent constructive step is a universal choice and arithmetic use that converts the retained product phase into a short nonzero annihilator or the covered long-query factor signal.

## Validation and primary pins

check_formulas.py compares Gaussian Euclidean symbols with their defining split/inert local symbols and (1) on 1120 cases; verifies 1012 reciprocal-parameter cases; checks 92 full octic cases, Galois equivariance, the relative-norm identity and every p mod8 branch. These are sign/convention regression checks for the proved identities, not empirical evidence of universal factoring coverage.

Primary references:

- Bach--Sandlund, On Euclidean Methods for Cubic and Quartic Jacobi Symbols, arXiv:1807.07719v1, Section7 and equations17--20; https://arxiv.org/html/1807.07719v1 ; saved PDF SHA256 2f8942dde3c54580a39e442e51781d688dee1169d7e0722bd7077e5768d3c3cb.
- Weilert, Fast Computation of the Biquadratic Residue Symbol, JNT96(2002),133--151; https://doi.org/10.1006/jnth.2002.2783 . Its fast Gaussian algorithm is available; the conservative implemented descent charge suffices here.
- Joye, Fast Computation of the Octic Residue Symbol, Theorem1, relative norm formulas and Algorithm1; https://marcjoye.github.io/papers/Joy22octic.pdf ; saved PDF SHA256 392342a2fc22098e22b793a23189405362c04e3be33925c7fcfe8a6c83842314.

Only /tmp/semiprime-character-acquisition-20261022/algebraic_symbols/ was written. No repository changes, builds, commits, or subagents.
