# Fast-prefix attempts after the half-center reduction

26 October 2026. This packet continues the full deterministic all-semiprime
sixth-exponent objective from the [one-sided query](../semiprime-knot-prefix-20261025/README.md).
No fast prefix algorithm is established here. The current complete query
still costs soft O(k^(5/4)); the desired soft O(k) acquisition and complete
executable/Lean bit-complexity proof remain open.

## Constructive changes

**A smaller public arithmetic family.** A shortest virtual Gauss witness
has content d=gcd(|a|,|b|) dividing the known k. Otherwise one can divide
out a prime while preserving its lattice congruence and strictly shorten
the vector. Filtering to d|k is therefore coverage preserving for every
allowed semiprime, without knowing the factor residue or witness. The
filter respects swap and opposite labels. Exact content descent groups
the d phase lifts at base beta^d, retaining the known carry and all labels.
The primitive-content family and axes remain large, so the acquired query
bound is unchanged. See [native-contraction.md](native-contraction.md)
and its [independent review](native-review.md).

**An exact symmetric-power determinant.** For the smaller knot polynomial
K and eta^2=q, define

    A_m=eta^(m+2) Sym^(m-1)(diag(eta,eta^-1)).

Its eigenvalues are precisely eta^3,eta^5,...,eta^(2m+1). If V is the
acquired 2L Seifert matrix, then

    det(V tensor I_m - V^T tensor A_m)
       =eta^[L*m*(m+2)] prod_(i=1)^m K(eta^(2i+1)).

The prefactor is a cheap known unit. This gives a short operator descriptor
for the exact query, while its expansion still has rank m and O(Lm)
entries. The [surgery construction](surgery-construction.md) tests binary
tensorization and an infection along a commutator; neither yet accelerates
the scalar determinant.

**A repaired nonabelian infection pattern.** The unlink pattern in the
first infection attempt had a vanishing background invariant. A fixed
T(2,4) two-component torus-link pattern repairs this. With generators a,c
and relator a c^2 a^-1 c^-2, the chosen odd-weight representation has
C^2=-I. Its Fox derivatives include 2I, while C-I is invertible. The
background torsion is the explicit unit 2^m. The commutator axis has
eigenvalues eta^w for w=+/-3,+/-5,...,+/-(2m+1), so the reciprocal knot
contribution is the square of the desired prefix product. Squaring
preserves zero modulo the actual squarefree N.

The [pattern calculation](unit-pattern-infection.md) distinguishes the
proved base acyclicity from the infected determinant at collision points.
The explicit normalized matrix satisfies det Z_m=2^m P_m^2 over the
composite ring, including at zeros. Its identification with satellite
torsion is proved on the generic based-field locus. Reduction of a
specified raw infection Fox minor to this matrix at singular composite-
ring inputs is still unproved; it is not needed for the direct determinant
identity. A zero determinant is not called a value of acyclic torsion. The
[independent review](unit-pattern-review.md) separates these scopes. This
fixes the background-zero problem but does not compute the remaining
representation norm cheaply.

## Specific shortcut tests

The [structured recurrence](recurrence.md) is fully initialized and
division free: B_0=H and B_(n+1)=(C-a_(n+1)I)B_n, where C is the companion
of the folded native polynomial, H its unimodular symmetric divided-
difference matrix, and a_n=q^-n+q^(n+1). Its determinant is the prefix
norm up to a unit. A proposed constant-channel boundary compression
fails exactly: H has rank L for every monic degree-L input. The naive
clock Loewner determinant is always a unit even at a collision. Small
displacement representations and determinant-only algorithms remain open;
these calculations are not a general algorithmic lower bound.

The native-content report also constructs a valid cubic Fourier/Bloch
operation over the rank-two auxiliary root-of-unity algebra. Its exact
Cauchy kernel retains the boundary factor 1-q. Conjugation does not
shorten the resulting root-coset product, and the native stationary-phase
projector is a linear operation rather than an acquired multiplicative
norm. The arithmetic q is never identified with the auxiliary cubic root.

## What the next algorithm must supply

The smaller family, one-sided clock, and unit-normalized knot/link
representations preserve the original goal. The missing operation is
still an exact zero or nonunit decision for the long prefix at cost
soft O(J+sqrt(m)), including every boundary/generator and all finite-ring
branches. A short binary representation, constant topology, or constant
displacement rank does not establish that acquisition cost.

The useful next target in the infection formulation is a fast contraction
of the odd-weight norm, exploiting the actual native arithmetic. The
primitive content-1 block must be handled; smooth-content fusion alone
does not remove it. No additional example coverage or backend proof batch
is counted as closing this gap.

## Evidence

The boundary [reference check](check_boundary.py) and its
[captured result](boundary-validation.txt) check the displayed companion,
symmetry and boundary-column identities over composite rings. The [unit-pattern symbolic check](check_unit_pattern.py) and its
[result](unit-pattern-validation.txt) verify Laurent-polynomial Fox signs
and three small Seifert block identities. The proofs and independent
reviews, rather than those finite checks, support the uniform statements. Sources and theorem scopes are given in each report.
Only local reports and small validation artifacts are bundled; external
fulltexts remain scratch-only.

See [review.json](review.json) and [manifest.json](manifest.json). Earlier
research packets and journal/guide prefixes are preserved. No Lean/public
assets, commit or push; concurrent engineering work is unchanged.
