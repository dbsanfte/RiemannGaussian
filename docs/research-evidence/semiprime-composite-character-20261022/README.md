# Composite colours and original-base character aggregates

22 October 2026. This continuation removes the auxiliary-prime supply
gap for the acquired Gauss aggregates and extends the exact quadratic
colour catalogue to composite row moduli. It also normalizes the
aggregates to the original prepared scalar base. The constructions have
classical proofs and independently reviewed reference implementations.
They do **not** acquire the long collision query or establish the
whole-input sixth-rate factoring bound.

The previous [weighted-aggregate packet](../semiprime-character-aggregate-20261022/README.md)
required an affordable prime ell congruent to 1 modulo a prescribed prime
m. The new selector chooses ell first. This is an explicit amendment to
the modulus selector; prime-field theorems and old selector-specific
claims are not transferred automatically.

## Public parameters are acquired at the required scale

Set u=ceil(N^(1/6)). Sieve successive doubled intervals to find the first
prime ell>2u with ell=3 modulo 4, and put m=(ell-1)/2. Then m is odd,
m>=u and ell=2m+1. A fixed-progression prime bound gives ell=O(u), so the
entire sieve costs soft O(u). No prime-in-a-growing-progression or
Sophie Germain prime hypothesis is needed.

For an effective bound, Bennett, Martin, O'Bryant and Rechnitzer,
[Theorem 1.2 and equations (1.10)-(1.11)](https://personal.math.ubc.ca/~gerg/papers/downloads/EBPAP.pdf),
give |theta(x;4,3)-x/2|<x/(160 log x) for x>=8*10^9. Subtracting the
bounds at x and 2x proves a prime in (x,2x]; taking x=2u gives ell<=4u
for u>=4*10^9. The fixed remaining range has an effective absolute
constant. The algorithm stops at the first actual prime, without sieving
to that threshold routinely. The cached primary PDF and its theorem
were independently inspected; its fingerprint is in source-pins.json.

Factor the public m and screen N against each distinct prime divisor of
m and against ell separately. For composite semiprime N every nonunit
screen gives a proper factor, including cases where a combined product
gcd would equal N. Otherwise all subsequent scalar inverses exist.
Factoring ell-1, primitive-root candidate testing and enumerating its
character table cost soft O(ell). This is public enumeration, not a
hidden-prime discrete logarithm. See the [supply proof](reports/composite-gauss-supply.md).

## Composite colours retain the original source

Use only unit tags j modulo m and the original canonical integer rows

    a=N*j^(-2) mod m, 1<=a<m,
    b=centered_m(((a*j^2-N)/m)*j^(-1)),
    c=(N+j*m*b-j^2*a)/m^2,
    ellrow=m*b-2*a*j, E=N+a+ellrow.

The exact quotient identity uses only unit tags. At the true tag
j=P mod m, with N=P*Q and P<=Q,

    m^2*I=a*P+Q+ellrow,
    E-m^2*I=(P-1)*(Q-a).

After the retained small-factor prefix, P,Q>16m^2. Since N<=m^6,
P<=m^3 and Q<m^4/16; hence

    13<I<(17/16)*m^2+3<4m^2.

This covers all retained factor ratios. The existing scalar recovery
contract remains applicable: E>=N-3m^2 and N>256m^4 give a positive
exponent gap even for the translated boundary indices i<L+m,
L<=4m^2. Raising gamma to m^2 need not preserve its local orders; the
inherited soft-O(m) small-order screen handles that explicitly.
Prepared gamma and its decoder are inherited interfaces, not new
end-to-end implementations in this packet. See the
[source audit](reports/composite-modulus-source.md).

For Delta=b^2-4*a*c and kappa=-Delta/(4*a*j) modulo m, the exact mask is

    I mod m in kappa+(4*a*j)^(-1)*Squares(Z/m).

Zero and all nonunit squares are included. Factor m into odd prime
powers p^e. Each unit squareclass is specified by its Legendre signs at
the distinct p; a single Jacobi sign is insufficient. For each colour
choose a unit representative w and form R_colour=w*Squares(Z/m).
Although there are 2^omega(m) colours, the combined explicit output has
size

    T=sum_colour |R_colour|
     =product_(p^e || m) 2*|Squares(Z/p^e)|
     <=product_(p^e || m)(p^e+1)
     <=m*(1+log m).

The [catalogue proof](reports/composite-colour-catalog.md) gives an actual
algorithm: mark local square images, construct their two unit multiples,
and combine coloured entries by CRT. Intermediate work is proportional
to the final output, including shared zeros. This avoids enumerating
every global residue separately for every colour. All row assignments
cost soft O(m+J), J=phi(m).

The earlier translation proof works for any ordered residue subset.
Consequently all palette trees together have total degree soft O(m)
per depth, and all requested boundary values cost soft O(m+J). What
remains is the same kind of long product, now indexed by colour:

    H_colour(X)=product_(r in R_colour, 0<=n<K)(X-q^(r+m*n)),
    q=gamma^(m^2), L=m*K+t.

Its assigned values have not been acquired at the desired cost. The
[independent integration review](reviews/composite-integration-review.md)
checks both the source extension and the complete catalogue charge.

## Normalization removes the auxiliary amplitudes

Let g_a be the proof-side Gauss sums, bar=rho_(-1) invert the character
variable while fixing the additive root, and choose the public t with
t^2=gamma. Such t can be prepared by the previously reviewed power-of-two
rebasing of the original odd-order scalar; no root-extraction oracle is
introduced. Put h_a=t*g_a/g_(-a). Then

    h_a*bar(h_a)=gamma

on every character component, including the trivial one. In the packed
degree-m algebra acquire U=-C_m=g_1^m and D=E0+(1-E0)*ell, where E0 is the
trivial-character projector. The normalized quantities are

    V=h_1^m=t^m*U^2*D^(-m),  q_h=V^m.

For unit antipodal tags the integer weights agree and
ellrow_j+ellrow_(-j)=-m^2*s_j, s_j in {0,1,2}. The corrected normalized
targets retain the true whole-local-algebra source. Their pair and whole
products are exactly

    T_j*T_(-j)=gamma^(N+a_j)*q_h^(-s_j),
    product_unit_j T_j=gamma^(A+N*h)*q_h^(-S),
    A=sum_pairs a_j, S=sum_pairs s_j, h=phi(m)/2.

Three shared vectors q_h^(-s), plus O(m) scalar descriptors, acquire
every pair product without expanding every pair vector. The complete
product is one acquired vector. For normalized quotients
A_j=t^(j-1)*C_j/bar(C_j), the entire weighted aggregate is

    product_unit_j A_j^a_j=(V/gamma)^A.

These are actual soft-O(m) computations with the new supplied parameters.
The explicit inverse formula also handles intermediate nonunit exponents:
if E_E projects onto characters made trivial by exponent E and
D_E=E_E+(1-E_E)*ell, then

    C_E^(-1)=bar(C_E)*D_E*D^(-E).

No generic polynomial inversion is needed. Proper-divisor characters of
composite m and E=0 are retained. See the
[normalization proof and algorithms](reviews/gamma-normalization-review.md)
and the [independent formula review](reviews/normalized-formula-independent-review.md).

## The remaining collision information

The normalized source has the original scalar norm:

    T_j*bar(T_j)=gamma^E_j,
    q_h*bar(q_h)=gamma^(m^2).

For a single leaf z=q_h^i, f=T_j-z and
G=gamma^E_j-gamma^(m^2*i), the exact identity gives

    G=bar(T_j)*f+z*bar(f),
    (f,bar(f))=(f,G).

Thus a certified same-leaf paired collision, or a whole-local-algebra
leaf collision, recovers an original scalar collision and its existing
factor/annihilator route. An isolated character-component hit is
insufficient. Nor can zeros from different leaves be combined: even a
product which is zero in every component can have its zeros distributed
over different factors. The same-leaf support still needs an acquisition
and localization algorithm.

The acquired unit products do not supply the mixed traces in
(T-z)*(bar(T)-bar(z)), products of differences, or the long H values.
For original scalar antipodal rows the degree-two difference polynomials
and their group product are already affordable; their resultant with H
is still unpaid. The [scalar-pair investigation](reports/paired-scalar-differences.md)
and [Gauss deformation investigation](reports/difference-gauss-deformation.md)
record these precise remaining contractions. They are not general lower
bounds. The earlier [normalization exploration](reports/gamma-normalized-gauss.md)
is preserved verbatim; its auxiliary-supply and generic-inverse caveats
are superseded by the reviewed constructions above.

## Implementation and validation

The reference files acquire public metadata and the stated unit
aggregates. They do not certify semiprimality, prepare the scalar's
orders, implement boundary multipoint evaluation, or evaluate H.

| Reference | Acquired output | Validation |
| --- | --- | --- |
| [composite_colours.py](implementation/composite_colours.py) | Prime selector, unit rows, explicit CRT palettes | Five exact algebra/control test groups |
| [composite_gauss_aggregate.py](implementation/composite_gauss_aggregate.py) | Whole Gauss aggregate and three-vector pair representation | Direct joint Gauss-sum oracle, including proper-divisor characters |
| [gamma_normalized_aggregate.py](implementation/gamma_normalized_aggregate.py) | Original-gamma aggregates and explicit C_E inverses | Direct normalized Gauss oracle and unit/exception controls |

Run from this packet's implementation directory, supplying the absolute
repository root for the frozen PackedGauss dependency:

```sh
python3 -m unittest -v test_composite_colours.py
python3 test_composite_gauss_aggregate.py --repo-root /path/to/riemann/formal
python3 test_gamma_normalized_aggregate.py --repo-root /path/to/riemann/formal
```

Implementation notes and independent reviews are beside the code.
Tests use known small split fields only as independent arithmetic
oracles. They are not family-coverage evidence or runtime certificates.
The theoretical bit charges assume fast integer/polynomial arithmetic;
no bound for the Python interpreter is certified. The archived reports
are verbatim, with fingerprints and source paths in archive-provenance.json.
Validation and preservation checks are in validation.json.

The auxiliary supply, composite catalogue and normalized unit aggregates
are now paid constructions. Restriction-stable acquisition of useful
collision information, the full factoring bit proof and Lean composition
remain open. No improved worst-case factoring exponent is claimed.
