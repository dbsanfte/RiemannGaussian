# Cross-tuple Hecke, signed tail, and physical-window tests

Local research checkpoint, 2026-10-19. This follows the
[full central payment](arithmetic-operator-auxiliary-order-central.md) and
the [Siegel interpolation review](siegel-interpolation-review.md).
The imported strict `Re(s)>7/8` endpoint is unchanged.

The common lesson remains the one exposed by the interpolation determinant:
the integer object, its weights and its zero response must survive together.
This pass tests three possible ways around the preceding source/physical
mask obstructions, and checks a more specific literature input for the
remaining square-numerator sector.

## A physical-window projector also kills the original source coefficient

[QuasiRHPhysicalWindowSourceAudit](../scripts/QuasiRHPhysicalWindowSourceAudit.lean)
allows an arbitrary finite complex linear combination of the actual two
physical Schwartz windows. Its exact factor on the theta hyperplane is

\[
F(z)=\sum_i c_i\,
\mathcal M(\widehat W_{0,i}^{\rm radial})(z)
\mathcal M(W_{1,i})(7/6-z).
\]

Lean proves that this function is analytic on `Re(z)>0`. At the source
intersection `(w,z)=(1,1/6)`, the original principal double-residue constant
of the code is exactly

\[
F(1/6)\,\frac{\operatorname{Res}(L_{\rm principal})^2}{6}.
\]

If the code vanishes pointwise on the actual theta line
`z=17/50+it`, even just on `-H<t<H` for any `H>0`, the identity theorem
forces this source constant to vanish. This closes the proposed exact
window-projector shortcut while retaining the original normalizer.

It does **not** rule out an integrated arithmetic cancellation, quantitative
smallness on a moving spectral range, or a different source carried by
single-residue/exterior terms of a newly coded principal pool. Those terms
would need their own complete accounting. No theta component is assigned
the original source merely from this analytic fact.

## The cross-tuple Hecke partner exists, but does not cancel the leading term

The earlier fixed-tuple `j=1`/`j=3` audit had disjoint numerator windows.
The new paper-level calculation keeps the original slots and finds a real
exception: for a split auxiliary prime `l`, a slot carrying its conjugate
`r=conj(l)` has the same norm without dividing the numerator.

Moving that slot from unselected to selected and simultaneously reindexing
the squarefree spectral ideal gives the local map

\[
(U,m,I,J)\longmapsto
(U\setminus\{i\},\,l^2m,\,rI,\,J),
\qquad r\nmid mI.
\]

Here `v_l(m)=6t+1`, the image has valuation `6t+3`, and both conjugate
primes lie outside the current fixed exclusions. Both the numerator cutoff
and the original Gaussian argument then match.
Repeated slot primes, the selected divisibility mask and every cube power
of `J` remain explicit. The full coefficient ratio has modulus
`q^(-1/2)`, where `q=N(l)`, on each scalar branch of the original finite
raw-section/ray expansion. Its unit phase and subset sign remain explicit;
different branches need not share that phase. This is not a scalar ratio
of the assembled residue vector. The inverse map costs `q^(1/2)`. The sum
of one matched scalar pair has modulus at least `(1-q^(-1/2))` times its
first term. No lower bound for the whole tuple sum is inferred.

There are genuine coverage failures. If `r|I`, adjoining it breaks
squarefreeness and cannot be repaired by the local cube exponent. More
decisively, the original slot norms are at most a fixed multiple of
`Z^(1/6)`, whereas a prime numerator in the physical window has norm at
least a fixed multiple of `Z^(1/2)`. Such prime-core indices have no
conjugate slot to supply this pairing eventually.

These are exact weight/support calculations, with the raw sextic residue
relation retained as a paper-level input. They do not assert that every
uncovered coefficient is nonzero or that an isolated core carries a zero
source. They close this local rescue, not all possible collective transfers.

## Signed integral tails meet a primitive-root source problem

[ArithmeticOperatorSignedIntegralSourceAudit](../scripts/ArithmeticOperatorSignedIntegralSourceAudit.lean)
proves a finite identity for the actual cyclotomic tail. For prime
`M+1<p<=2M+1`,

\[
\exists d\in[M+1,2M]:\quad
p\mid\Phi_d(b),\quad p\nmid d
\quad\Longleftrightarrow\quad
b\text{ is a primitive root modulo }p.
\]

Any adaptive row mask is retained exactly at `d=p-1`. No retained tail
prime exists through `p<=M+1`. The finite joined identity permits arbitrary
complex prime weights; it assumes no density theorem.

Apply this to an actual integral quotient
`C_(2M)/(C_M * selected denominator)`. The previous paper-level primitive
debt bound reduces its full phased packet to its positive primitive parents,
with error `O_b(M^(2/3) log M)`. All positive parents lie above `M`, so the
packet is source-small through physical cutoff `X<=M+1` for every row-source
exponent greater than `2/3`. This loses the desired source.

For fixed `1<kappa<2`, physical cutoff `X=M^kappa` permits a surviving tail,
but only its first prime layer. Its total source is an order-selected prime
sum, not the ordinary Chebyshev source. The first annulus is exactly the
primitive-root selection above; for square bases it is empty. Integrality
does not force the remaining positive row mask to be a prefix: the actual
integer `Phi_21(2)/Phi_3(2)=337` allows arbitrary further high positive rows.

No total zero response for the unsaturated tail is proved. This does not
assert that proving that response would imply Artin's conjecture, or that
the response cannot exist: it identifies the actual missing arithmetic
statement before further estimates are attempted.

## The closest global square identity remains an unproved input

The literature preflight examines the sextic-square Rankin–Selberg
convolution of [Chinta–Friedberg–Hoffstein](https://chinta.ccny.cuny.edu/publ/patterson.pdf),
the [Friedberg–Ginzburg descent](https://arxiv.org/abs/1403.3930v3),
and the explicit sextic computations of
[Bröker–Hoffstein](https://arxiv.org/abs/1312.0568v1). The relevant
number-field convolution is conjectural. The descent comparison is not an
identification of the actual native finite-section theta coefficient;
bad-place sections and phases cannot be suppressed.

A sufficiently uniform version would be genuinely useful. An energy bound
of size `Q^(1/3+epsilon)` for the actual fixed vector, including its fixed
bad numerator multipliers, all finite unit classes and sixth powers, would
give the conditional native square-ideal cost

\[
Q^{1/6}Y^{-1/3}=Z^{-1/48+\text{small positive costs}}.
\]

The actual unselected length cancels in this expression. The remaining
native square character is still `chi_I(a)^2` with the coprimality mask
`((a),J)=1`, the mark `D|I*J^3` and the original norm profile. This calculation
supplies a precise missing
coefficient bound, not a proof of it. Prime and other odd-core sectors also
remain outside its scope. No new source allocation follows.

## Validation and remaining frontier

Two isolated strict Lean leaves pass warning-as-error compilation, 15
namespace linters each and all-local standard-axiom audits. Their 37 local
declarations include 33 theorem declarations and generated helpers. Root
independently reran the signed-tail leaf and all 18,451 exact regression
checks. The physical-window theorem received an independent native-source
review. Including the cross-tuple and square-normalization probes, root
reran 400,176 exact checks. They do not certify automorphic residue identities.

The complete native central estimate from the preceding checkpoint is
preserved. The protected source remains in
`normalizedProbe - normalizedF_all`. The actual prescribed signed physical
theta correlation on the unknown prime/square cores remains unpaid.
Neither local transfers, exact window deletion nor a conjectural scalar
square identity supplies that estimate.

See the [frozen evidence manifest](arithmetic-operator-cross-tuple-tail-window-gates.json).
Work remains local: no broad CI, root/public registration, commit or push.
Eight Tier-1 families have been visited; none is marked exhausted.
