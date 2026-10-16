# Input-dependent phase normalization and cyclic q-dilogarithm reciprocity

2026-10-15. Classical algebra and freshly inspected primary literature. No shared source edits or builds. No nearlinear long-product evaluator was obtained.

## Outcome

There is a source-specific exact obstruction to a tempting CYCLIC endpoint evaluator: on the actual retained family, every target lies precisely on the singular full-orbit locus of the cyclic quantum dilogarithm. No invertible cyclic primitive with the desired first-order product recurrence exists there, even if the local order were supplied. This is different from the earlier rational-function telescoping obstruction: it concerns arbitrary functions on the actual finite orbit and follows from its forced zero factor.

This does not exclude noncyclic interval functions, regularized singular limits, extra divisors, implicit scalar algorithms or arbitrary input-dependent sampling. A regularized construction would need a new exact evaluation and collision-preserving localization theorem.

## Exact public identities that survive over Z/N

Write d=m², q=gamma^d and E_j=N+delta_j. Let E_j=d h_j+r_j be ordinary integer Euclidean division with 0<=r_j<d. Then for any signed start s and length L,

    prod_(i=s to s+L-1)(gamma^E_j-q^i)
      =q^(h_j L) prod_(k=s-h_j to s-h_j+L-1)(gamma^r_j-q^k).       (1)

All factors removed are known units. The identity holds without dividing by any residual. The public metadata r_j,h_j and the unit phase can be acquired in soft O(m) total work with polynomial logarithms for the actual m-1 seed list. BUT the interval length is unchanged and its new start s-h_j is generally of order N/m²~m^4, so this is not a short-boundary product acquisition. Testing a known zero of the new progression at a different index does not preserve the original valid interval.

The standard finite reversal is also ring-safe:

    (z;q)_L=(-z)^L q^(L(L-1)/2) (z^(-1)q^(1-L);q)_L.             (2)

It uses inverses only of known units z,q. It preserves exactly L factors and reverses their order; it does not shorten the valid interval. The literal target exponent becomes d(L-1)-E_j, retaining the large common N contribution with opposite sign.

A division-free residue-class identity is

    (z;gamma)_(dL)=prod_(r=0 to d-1)(z gamma^r;gamma^d)_L.         (3)

It interchanges a complete d-by-L rectangle with one long progression, not the actual sparse m-1 target set. Using it on the source would require a proved sparse-complement/cancellation identity and its paid nonunit denominators; enumerating d=m² classes does not meet the whole-family soft O(m) clock. This observation is a charge for this explicit completion contract, not a scalar lower bound.

## A cyclic monodromy obstruction on the ACTUAL family

Fix one hidden field F_P on the retained majority supply. Gamma has exact prime local order R=R_P>16m². Since R is prime and R>m, q=gamma^(m²) has the SAME order R and generates the same subgroup as gamma. For every actual supplied exponent E_j,

    z_j=gamma^(-E_j) is in <q>, so z_j^R=1.

Consequently, exactly over the field,

    prod_(k=0 to R-1)(1-z_j q^k)=1-z_j^R=0.                     (4)

Here q is primitive of order R and the characteristic P does not divide R because R divides P-1.

Proposition. There is no function W from this cyclic orbit to the nonzero field elements satisfying

    W(qz)=(1-z)W(z)

at every orbit point. More generally, no nonzero scalar c and nowhere-zero W can satisfy W(qz)=c(1-z)W(z).

Proof. Multiply all R recurrence ratios. Their left side telescopes to 1, whereas the right side is c^R(1-z^R)=0. Equivalently, iterating the recurrence gives W(z)=0 for every starting point. The contradiction is purely algebraic and persists in any extension field.

For a general off-orbit parameter z with z^R!=1, a normalized cyclic primitive would require a scalar c with

    c^R(1-z^R)=1.                                               (5)

This requires both invertibility of 1-z^R and an appropriate R-th root. At the actual source points 1-z^R=0, so even granting arbitrary root extraction and the hidden period cannot make (5) true. Since this failure occurs after reduction in each hidden field, a composite-ring construction whose W and normalization are units cannot avoid it.

This obstruction is not evaded by publicly shifting E_j by multiples of d: it just moves z_j within the SAME singular orbit. Euclidean division of E_j by d and reciprocal reversal also keep all targets in <gamma>=<q>. It therefore applies to the input-dependent carries in (1), not merely a fixed catalog of indices.

The actual query interval has L~m²<R. Its product need not vanish in either field on every individual row; the complete orbit always does. The obstruction only rejects a globally invertible CYCLIC primitive. A function defined on a noncyclic path can accumulate the interval product, but acquiring that function is the original long-product problem.

## Primary literature check, including 2026 papers

Tsukasa Ishibashi, *Cyclic Quantum Teichmüller Theory*, Communications in Mathematical Physics 407, article 173, published July 9, 2026:
https://link.springer.com/article/10.1007/s00220-026-05604-6
Primary PDF saved as ishibashi-2026.pdf, extracted text beside it.

Section 2 assumes a KNOWN primitive root of an odd KNOWN order. Lemma 2.1 supplies the full-orbit product identity. Definition 2.3 and equation (2.2) use a punctured Fermat curve and fractional powers; choosing their branches and generic parameters is explicit. Its inversion relation Theorem 2.9 uses a normalized complete-orbit product equal to one. Matching its linear factor with 1-zq^k would instead give the source product (4), equal to zero. Thus the standard nonsingular normalized identity cannot be specialized directly to these source factors. Neither a composite-ring algorithm nor its bit clock is stated there.

Gene S. Kopp, *The Shintani–Faddeev modular cocycle: Stark units from q-Pochhammer ratios*, arXiv:2411.06763v3, May 3, 2025:
https://arxiv.org/abs/2411.06763
Primary PDF saved as kopp-2025.pdf. The inspected introduction and cocycle definitions concern complex meromorphic modular transformations and real quadratic special values. They do not give a finite modular-residue evaluator or an algorithm interchanging the known integer d=m² with an unknown order in Z/N. A lift from a finite-field unit to a complex number would not preserve the desired residue arithmetic automatically.

Arash Arabi Ardehali and Hjalmar Rosengren, *A New Product Formula for (z;q)_infinity, with Applications to Asymptotics*, published September 19, 2026:
https://link.springer.com/article/10.1007/s00365-026-09783-2
The primary main identity is equation (2), for Re(beta)>0 with q=exp(-beta), and uses an infinite gamma product, dilogarithm and chosen complex branches. Its asymptotic goal is q approaching 1. The stated domain and infinite analytic objects do not provide an exact finite-ring substitution or a guaranteed modular bit-cost shortcut.

*Real quadratic fields and finite quantum dilogarithms I*, arXiv:2609.21892, September 2026:
https://arxiv.org/abs/2609.21892
Primary PDF saved as fqd-2026.pdf. Theorems 1–2 concern algebraicity and an explicit system over cyclotomic coefficient rings; they are not an efficient algorithm to acquire the required long finite product at unknown-order composite-ring inputs. An algebraic characterization alone does not supply the right root or a nearlinear evaluator.

## Why ordinary exponent Euclid is not the missing modular reciprocity

The public extended Euclidean algorithm can relate d and E_j as INTEGERS; identity (1) is a legitimate example. To represent gamma^E_j as q^t within the actual cyclic group requires d*t=E_j mod R, however, not d*t=E_j over the integers. R is hidden. The source gamma itself is supplied, so this is not a claim that extracting a d-th root of q is hard; that root is already known. The missing datum is an index t in the q cycle with the correct interval placement. Even if supplied, the singular cyclic-primitive obstruction above remains.

In particular, the public tag j=1 satisfies E_1=0 mod m², giving an exact public global zero at i=E_1/m²~m^4. This lies outside the native O(m²) coverage rectangle on the large inputs. Bringing this zero to a new origin by (1) changes the interval's start by the same amount. It does not bring the original valid interval's collisions to a small boundary for free.

## Remaining positive target

A useful reciprocity algorithm would have to supply an exact composite-safe identity on the ORIGINAL finite intervals, with all singular factors localized and their proper-factor/saturation recovery paid, plus a whole-family soft O(m) evaluation clock. Noncyclic or singularly regularized special functions are not ruled out; neither are direct input-dependent sampling identities. The inspected cyclic and modular q-gamma literature does not yet provide that theorem.
