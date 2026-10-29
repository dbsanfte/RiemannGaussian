# Three-adic stationary colour lifting: exact phases and a complete filtered query

26 October 2026. Derived finite identities; no experiments, repository changes, or improved exponent claim. The authoritative trace packet's stationary-colour enumeration and coverage are prerequisites. This investigation executes the three-child contraction and an index-image filter. The latter is a complete algorithm, but its paid bound is still soft O(J+sqrt(Jm)).

## 1. Exactly which children exist?

Write K=2*3^r, H=K², r>=1, with N coprime to6. A parent unit colour j, 0<j<K, is stationary for(a,b) when aj²=bN modulo K. Put the known INTEGER D=(aj²-bN)/K. At the next scale the colours are j_t=j+Kt, t=0,1,2, and

    aj_t²=bN mod3K  iff  D+2aj*t=0 mod3.                 (1)

If 3 does not divide a, exactly ONE child is stationary. If 3 divides a, stationarity also forces 3|b; there are all three children when 3|D and none otherwise. Thus the primitive unit-a branch is a partition of rows, not a three-factor norm for each row. All tests and child indices cost polylogarithmic integer work per parent incidence.

Here is the exact canonical phase, including the bottom level K=6. Set F(x)=ax+bN/x, compute j inverse modulo9H, choose the resulting integer representative F_0 of F(j), and let lambda=[-F_0]_H. Define

    L_0=[(-F_0-lambda)/H]_9,
    sigma_t=[t(D+aj*t)/(j*(j+Kt))]_9,
    L_t=[L_0-sigma_t]_9.

All denominators in sigma are units modulo9. The exact rational difference

    F(j+Kt)-F(j)=H*t(D+aj*t)/(j*(j+Kt))                 (2)

proves that the child phase is lambda_t=lambda+H*L_t, in [0,9H), whenever that child is stationary. This computation chooses inverse precision BEFORE the integer quotient; replacing F_0 by a congruent representative modulo9H changes nothing. For r>=2, sigma_t=D*j^-2*t+a*j^-1*t² modulo9. The denominator in(2) must be retained at r=1.

When all three children exist, write a=3a_1,D=3D_1. For every r>=1,

    sigma_t=3*(D_1*j^-2*t+a_1*j^-1*t²) mod9.           (3)

If the quadratic coefficient vanishes modulo3 but the linear one does not, the phases form one complete coset {ell,ell+3,ell+6}. If both vanish they coincide. If the quadratic coefficient is nonzero there are TWO phase values, one repeated. These assertions follow by evaluating the degree-two polynomial over F_3, or completing its square. Three stationary children need not mean three distinct roots.

## 2. Execute the actual geometric product

Let q=beta^H, x=beta^(a+bN+lambda). A child clock has base q^9. Exactly,

    product_(i=1..m)(beta^(a+bN+lambda_t)-q^(-9i))
      =q^(m*L_t) product_(i=1..m)(x-q^(-(9i+L_t))).     (4)

The prefactor is a known unit. Equation(4) explicitly uses the NEGATIVE clock: its signed parent index is I=-9i-L_t. For the positive-clock convention the corresponding identity is beta^E_child-q^(9i)=q^L_t*(x-q^(9i-L_t)), so the signed parent index is I=9i-L_t. These conventions must not be mixed. In the complete-coset case the three strings interlace to ONE q^-3 string of length3m, with indices 9+ell+3j, 0<=j<3m. They do not form a parent q^-1 string of length m. Clock mass has not disappeared. Coincident phases can be deduplicated for zero predicates, but their numerical multiplicities cannot be silently discarded.

On the unit-a branch only one child exists, so this interlacing is unavailable. Moreover the native child cutoff |ab|<3K introduces a new band K<=|ab|<3K, including Theta(K) primitive rows with b=1. Reusing only the old cutoff is not a coverage theorem. Formula(4) identifies the precise moving clock windows a recursive contraction must acquire; it supplies no uncharged endpoint replacement.

## 3. A complete known index mask, with all divisions paid

There is nevertheless a useful exact filter. Fix the FINAL native K=k and H=k². For an actual factor P in colour j write P=j+Kt, Q=N/P. Then

    I=(aP+bQ+lambda)/H

is the original integer collision index. Define the integer

    n_0=(aj²+bN+lambda*j)/H.

It is integral by the defining phase congruence. For any R=3^s dividing K, compute

    gamma=n_0/j modR, delta=D/j² modR, alpha=a/j modR.

The integer quotient in n_0 is performed before reduction or inversion. The exact localized-rational identity

    I=n_0/j+t(D+aj*t)/(j*(j+Kt))

then proves

    I=gamma+delta*t+alpha*t² modR.                    (5)

This is an exact identity for the actual factor, with no unknown-order reduction. All inverses concern the known 3-power R, not Z/N. Choose R=K/2 to obtain the strongest mask justified by(5).

For alpha a unit, complete the square: the image is kappa+alpha*Squares(R), kappa=gamma-delta²/(4alpha). The exact disjoint description is

    Squares(3^s)={0} union
      union_(0<=2v<s){x:x=3^(2v) mod3^(2v+1)}.         (6)

A unit is a square modulo every 3-power precisely when it is1 modulo3, by the invertible derivative of its square root. Thus(6), and its shifted/scaled image, have O(log K) arithmetic-progression pieces. Their density tends3/8; successive colour levels are not independent half-density filters. In particular the unit-square branch remains an entire progression modulo3 at every higher precision.

Prior-credit clarification, independently checked during integration: for a unit row, put c=(lambda²-4abN)/H. The intrinsic integer conic identity gives ((aP-bQ)/K)²=H*I²-2*lambda*I+c. Modulo R the first term vanishes, while (aP-bQ)/K=D/j+2*a*t is a bijective affine coordinate. Thus the EXACT image is c/(2*lambda)-(2*lambda)^-1*Squares(R). It equals the displayed colour mask: kappa=c/(2*lambda) and alpha/[-(2*lambda)^-1]=(2*a)² modulo R. This is the old intrinsic conic-square condition at this known 3-power, not extra information obtained by adding a colour tag. Its coefficients can be acquired directly from the row. The new discussion pays the complete progression-grouped query and exact child carries; it does not claim a new independent sieve condition.

Nonunit alpha requires no exclusion. Set v=min(v_3(alpha),v_3(delta),s). If v=s the image is {gamma}. Otherwise divide both coefficients by3^v and work modulo3^(s-v). If the new alpha is a unit use the square description. If it is nonunit the new delta is a unit, and the polynomial has unit derivative everywhere: it is a bijection modulo each 3-power by unique Hensel lifting. Its original image is simply I=gamma modulo3^v. Hence EVERY coloured incidence has an explicitly acquired O(log K)-piece image. The four axes illustrate the scope: for (a,b)=(+-K,0) or (0,+-K), alpha=0 moduloR and delta is a unit; their image is ALL indices moduloR. This filter does not shorten their clocks.

These are derived identities. The quadratic-image/palette idea and root-coset interlacing have prior credit in the existing arithmetic palette work; the specific new calculation here is the canonical child law(1)-(4) and its complete query accounting. No independent new literature theorem is invoked.

## 4. Full algorithm, coverage, decoding, and cost

Use the trace packet's output-sensitive soft-K enumeration of all stationary-colour incidences, including axes and inherited public deletions/pruning. Its total size J_col is soft O(K); it does not scan all K colours for each row. Compute(5)-(6) and their nonunit variants for every incidence, keeping the original label and colour metadata. This costs soft O(J_col), produces soft O(J_col) progression pieces, with total O(J_col log K) pieces. A single row can have many colour tags (axes can have Theta(K)); only the TOTAL incidence bound is used, not a per-row polylogarithmic multiplicity bound.

For each stride d=3^v<=R group pieces by their residue modulo d. Intersect each progression with the ORIGINAL signed index window [-M,M], or with the requested prefix of it. Each nonempty group has a common geometric clock of base q^d and length at most h/d+1, where h=2M+1. Build its monic polynomial of the original x roots and apply the existing division-free geometric-product query. Empty intersections are skipped. This is an executable deterministic scalar query; it makes no assumption that q^d has a cheaply known order. Repeated local roots do not invalidate monic polynomial remainder/product algorithms. This grouping uses one COMMON original window or prefix, so starts and lengths agree within each stride/residue group. Row-specific windows would require separately paid segmentation or a variable-window engine; padding to a common envelope is not licensed.

Coverage is componentwise: the correct physical factor colour is enumerated; its true I lies in its computed image by(5); its retained original row and original window index are therefore tested. The old guaranteed physical witnesses for both local factors remain present, so their aggregate retains the old full-window zero guarantee. Conversely every retained test is an OLD row at an OLD index. Original integer-zero row deletion ensures its label E-HI is nonzero; proper gcds yield factors and saturated short-label leaves use the inherited extractor. Nothing treats a new additive cancellation as an original annihilator. The same predicate can be prefix-localized, retaining the original integer index as its leaf label.

Let J_d be the total row degree for one stride, at most 2*J_col after literal duplicate pieces are removed (a last square-image piece and the singleton can share the final stride). There are at most d residue groups. Their cost is

    soft O(J_d + sum_groups sqrt(J_group*(h/d+1)))
      <=soft O(J_d+sqrt(J_d*(h+d))).                  (7)

Since d<=R<=K and h is Theta(K^(3/2)) on the long query, summing the O(log K) stride levels gives

    soft O(J_col+sqrt(J_col*h)),                      (8)

the existing bound, not soft O(J_col+sqrt h). For shorter h, skip or truncate masks and use the old engine where advantageous. The cost claim does not assert that the worst-case bound(7) is a lower bound for this actual catalogue, nor that no different scalar algorithm can exploit correlations.

The remaining specific opportunity is a proved collective contraction over the varying residue centres kappa and original roots, or an actual complete-cover theorem concentrating those centres enough to improve(7). Merely iterating three-colour lifting supplies neither: generic primitive rows choose only one child, and the exact image filter has dense progression pieces. No whole-query improvement is obtained by this executed construction.

## 5. Higher-precision critical-point option: not charged as a solution

For unit a,b with the chosen stationary square-root branch, one can instead lift the critical point p_*²=bN/a in Z_3 and use F(p)-F(p_*)=a(p-p_*)²/p. This can describe an index image at precision beyond R|K after acquiring sufficient inverse/root precision and handling the constant divided by H exactly. It does not make the image sparse: an analytic square-coordinate change retains the shifted-square structure. The finite mask algorithm and bound above need none of that additional interface; no higher-precision hypothesis or acquisition is hidden in(5).

## Inputs and credit

Authoritative prerequisites: repository packet semiprime-knot-trace-20261026, especially trace-recurrence.md sections3-5 (stationary colours, soft-K incidence enumeration, canonical carries), and its README/farey-query.md for current coverage and query scope. Prior Frohman-Gelca/Chebyshev pair identities are already credited there; they are not a new contraction in this report. All new equations above follow by exact rational algebra and elementary unit-derivative lifting over the known powers of3. No claim about an arbitrary algorithm's complexity or a semiprime-specific lower bound is made.
