# Corrected cross-order fourth root: exact map and iteration

22 October 2026. This validates the proposed coupling as an efficiently computable canonical root choice, then derives its exact iteration. It does not claim a universal short annihilator.

## 1. Local cross-order cancellation is exact

Work in the norm-one torus of (Z/NZ)[i], N=P Q odd distinct primes, with a Gaussian unit lift z=α/barα. Put

    ep=(-1/P), eq=(-1/Q), σ=ep*eq=Jacobi(−1,N),
    A=P−ep, B=Q−eq, E=N−σ, k=E/4,
    s_P=S_P(α), s_Q=S_Q(α), s=S_N(α)=s_P*s_Q.

Both A and B are divisible by4, and

    E=AB+eq*A+ep*B.

The proved local symbol formula is s_P=z_P^(ep*A/4), with its Q counterpart. Define the completely public corrected root

    C=F(z)=z^k*s^(−σ).                              (1)

Reducing the exponent modulo A and B gives exactly

    C_P=z_P^(ep*B/4)*s_Q^(−σ),
    C_Q=z_Q^(eq*A/4)*s_P^(−σ).                       (2)

Thus the own local quarter-phase does cancel, leaving the opposite quarter-power corrected by the opposite local phase. No hidden exponent occurs in the production formula (1).

Since s is a fourth root of unity, a global identity follows immediately:

    C^4=z^E.                                         (3)

The coupling really does compute a particular fourth root of the old projected point.

## 2. The useful stronger invariant: the next correction is exactly 1

For any norm-one point w with a Gaussian unit lift w=β/barβ, define

    τ(w)=S_N(β).

This is independent of the lift: two such unit lifts differ by a conjugation-fixed rational unit, whose Gaussian quartic symbol with rational denominator N is1. Every local norm-one point has a unit lift: use 1+w unless w=−1, then use i. CRT combines these local lifts into a global unit lift as a proof of existence. It is multiplicative, using the product of two lifts for the product point. Thus τ is a homomorphism from the norm-one group to the *global* μ4.

Here is the paid deterministic lift algorithm, with w=x+yi represented modulo N and Norm(w)=1 modulo N:

1. Compute h=2+2x modulo N and g=gcd(h,N). This h is Norm(1+w), since Norm(w)=1.
2. If 1<g<N, return that factor.
3. If g=1, set β=(1+x)+yi, compute its Gaussian quartic symbol S_N(β), and return it as τ(w).
4. If g=N, verify/derive w=−1 modulo N, set β=i, and return S_N(i)=Jacobi(2,N).

The last branch is valid even in the split local algebra. For a hidden odd prime p with −1 split, write w=(t,t^(−1)); then Norm(1+w)=(1+t)(1+t^(−1))=0 forces t=−1, hence w=−1 in both components. In the inert quadratic field, a zero norm forces 1+w=0. Equivalently, in either étale case Norm(w)=1 and trace(w)=−2 imply (w+1)²=0, and reducedness forces w+1=0. CRT now gives w=−1 globally when g=N. Thus no arbitrary split-algebra zero-norm inference is being used.

For g=1, (1+w)/(1+barw)=w by direct multiplication and Norm(w)=1. The exceptional lift i also satisfies i/bari=−1. Every inversion is of a checked unit; alternatively the symbol routine uses integer Gaussian representatives without modular division. With O(log N)-bit coordinates, one gcd, the lift, and the implemented Gaussian Euclidean symbol cost O((log N)^3) bit work conservatively. No factor, order, prime-ideal orientation, or local character is an input.

For global roots ω in μ4, Gaussian supplements give

    τ(i)=S_N(1+i)=i^((σN−1)/4)=i^(σk),
    τ(ω)=ω^(σk).                                    (4)

Applying the homomorphism to (1) now yields a stronger fact than merely S_N(C)=1:

    τ(C)=τ(z)^k * τ(τ(z))^(−σ)
        =s^k * (s^(σk))^(−σ)=1.                    (5)

In particular, when 1+C is a unit, its quartic symbol is exactly1, not an undetermined ±1. A denominator exception either factors N or is the explicitly handled global point−1. Moreover F(ω)=1 for all global ω in μ4.

The ordinary quartic symbol of the corrected point also equals1. Indeed S_N(z)=s² and S_N(i)=Jacobi(2,N)=(-1)^k, so S_N(C)=1. Equation(5) is stronger because τ(C) is the character of a Cayley lift of C.

## 3. Odd preparation and exact iteration

Since τ is a homomorphism into μ4, it is identically1 on every odd-order input: τ(w)^r=1 for an odd order r, while τ(w)^4=1. In particular, when both local orders are odd, the global order is odd and τ(w)=1. The retained lift phase can therefore be nontrivial before odd preparation, or on new nonlinear arguments whose order is not known odd; it supplies no phase on the already odd prepared point itself. Computing S_N(1+w) does retain τ rather than only τ², but on an odd-order w this retained value is exactly1.

Because τ(C)=1 and τ is multiplicative,

    F(C)=C^k,
    F^t(z)=C^(k^(t−1))  for every t>=1.              (6)

Therefore

    [F^t(z)]^4=z^(E*k^(t−1)),
    [F^t(z)]^(4^t)=z^(E^t).                         (7)

There is only one nontrivial quartic correction. Repeating the same corrected-root construction supplies no new phase sequence: after the first step it is ordinary powering by the public k. This conclusion is specific to this exact map and character, not to every possible adaptive use of algebraic symbols.

On an odd local subgroup of original order r, global μ4 corrections have no odd component, so the odd local order after t iterations is exactly

    r/gcd(r,k^t)=r/gcd(r,E^t).                        (8)

This is precisely the odd order under ordinary repeated E-projection. The coupled root can change the 2-primary choice; it does not shorten a surviving odd rough period beyond that existing powering. If a divisor of r is coprime to E, it persists under every literal iteration.

If a comparison of F^t(z) against a fourth root of unity produces a local collision, (7) implies that the ordinary point z^(E*k^(t−1)) is already1 at that prime. Conversely an ordinary identity can have several 2-primary root choices. The correction may organize such choices, but no new guaranteed odd-order collapse has been proved.

## 4. Full cost and exact missing step

For O(log N)-bit Gaussian input coordinates, acquiring s uses the implemented quartic Euclidean descent with conservative O((log N)^3) bit cost. Computing k, one modular power, inversions and gcds is polynomial in log N. A lift τ(w) is acquired at the same cost or returns a proper factor. Running t=polylog(N) iterations, including all denominator checks, remains polynomial in log N. An annihilator exponent E*k^(t−1), if certified by a local/global collision, has O(t log N) explicit bits. It is an annihilator of the starting torus element z; no claim identifies it with an annihilator of an unrelated scalar gamma.

All four ep,eq sign combinations are retained. No local symbol, hidden cardinality, or CRT decomposition is used by (1). No random search or higher rational-residuosity oracle is required.

What remains absent is a coverage theorem forcing a useful collision/annihilator for every input from this map, or a different paid use of the retained quartic character that lowers the native long-query cost. The exact formula(8) shows why the literal iteration does not itself supply that theorem. It does not rule out a different cross-twist operation or information extracted from unrelated numerators.

## 5. Checks and source pins

check_corrected_root.py checks the corrected root, τ(F(z))=1, and four iterations on548 unit input cases across (++),(+−),(−+),(−−). It uses defining local symbols only as private identity checks; the production map uses the public Gaussian symbol. The earlier check_formulas.py covers the local formula and symbol conventions. These are regression checks, not empirical evidence of universal factoring.

The only external input for (4) is the Gaussian quartic reciprocity/supplement convention in Bach--Sandlund, arXiv:1807.07719v1, Section7, equations17--20:
https://arxiv.org/html/1807.07719v1
Saved PDF SHA256 2f8942dde3c54580a39e442e51781d688dee1169d7e0722bd7077e5768d3c3cb.

The derivations use the local formula already proved in cross-twist-symbols.md. No new analytic assumption, repository change, build, commit, or subagent.
