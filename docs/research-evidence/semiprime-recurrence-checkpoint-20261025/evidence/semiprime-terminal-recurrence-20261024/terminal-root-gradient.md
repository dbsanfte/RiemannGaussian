# Root-gradient support and uniform fixed-degree restrictions

24 October 2026. Scratch addendum; no repository or frozen-report changes. This simplifies the recovery in `terminal-literature.md` (SHA256 `49c90f496dcfaf1f4cc2e69e746950c9e3b597257ca94d21056c76ad7547ed06`). The observations below were supplied by root and checked here. They acquire no new endpoint circuit and improve no current whole-query bound.

## Leading root gradient directly selects a hit row

Keep the original report's generic independent-coefficient circuit contract, fixed unit seeds x_i=q^(u+i), monic F=product_j(X-Y_j), and unit-separated original roots. After E=0 modulo N, its adaptive Hasse procedure either returns a proper factor from unequal local hit counts, or acquires a common count h>=1 and the UNIT coefficient a_h=[z^h]E(F+z). Let

    D_k(z)=partial E/partial f_k at F+z,
    B_k=[z^(h-1)]D_k(z), 0<=k<J.

The original proof gives B_k=a_h*sum_(local hit nodes)x_i^k in each field. Instead of Newton identities, convert this vector to root derivatives while holding z fixed. Write

    g_j(z)=partial/partial Y_j E(F+z),
    G_j=[z^(h-1)]g_j(z).

The factors of F+z are NOT being treated as Y_j+z: Y_j are the roots of the unperturbed F, and only its constant coefficient receives z. Since

    partial F(X)/partial Y_j=-product_(a!=j)(X-Y_a),

at a hit node x_i=Y_j this derivative equals -F'(Y_j); at any OTHER original root it is zero. Deleting a hit factor from product_i(F(x_i)+z) leaves leading coefficient a_h at degree h-1; deleting a nonhit leaves degree h. Therefore, in BOTH local fields,

    G_j=-a_h*F'(Y_j)*1_(Y_j is a local hit).       (1)

All multiplier factors in (1) are units: a_h was certified, and F'(Y_j) is a product of guarded original-root differences. There is no division at a hit and no integer division from Newton identities.

The entire G vector is actually acquired in soft J additional work. For F_rev(T)=T^J F(1/T) and B(T)=sum_(k<J)B_k*T^k, compute

    V_rev=-B*F_rev mod T^J,
    V(X)=X^(J-1)*V_rev(1/X),

then evaluate V at all Y_j by monic MPE. The convolution/duality proof in the original report gives V(Y_j)=G_j; equivalently reverse the root-product tree. This map uses only monic arithmetic.

Scan gcd(G_j,N) individually. A proper gcd factors N. In its absence, the two local hit-row sets agree: every hit coefficient is a unit, every nonhit coefficient is zero globally. Since h>=1, select a unit G_j and invoke the paid ORIGINAL one-row locator. Different local seed indices in that same row are handled by that locator. Only actual original leaves use its saturated decoder. This works also at h=J and needs neither a derivative in the fixed monic leading coefficient nor an explicit hit polynomial. The h=0/unit-E and initial proper-gcd cases remain as in the original report.

Adaptive doubling and one reverse truncated-ring pass still cost soft(C*(h+1)+J+sqrt L), with h=min(h_P,h_Q)<=J. The simplification removes Newton reconstruction and its small-integer inversions; it does NOT remove the jet precision multiplier.

## A stronger uniform circuit contract removes that multiplier by old bisection

The h cost is not fundamental for every generic scalar algorithm. Suppose a fixed-degree-J circuit is UNIFORMLY valid on all monic inputs used below, and is division free or divides only by certified public q-units. More generally every actual denominator on every query must be proved unit uniformly on this query class. A single input's valid formal trace is insufficient: a padded polynomial may take different branches or make another denominator nonunit.

For a row subset S, zero-padding

    F_S(X)*X^(J-|S|)

preserves the zero/unit mask on the unit seeds, while keeping degree J. Thus under a genuinely unrestricted monic-input contract one fixed-degree circuit supports balanced row bisection. This is the older restriction recovery route, now implemented through fixed-degree padding. Zero-padding is INVALID for a contract requiring F(0) unit or pairwise unit-separated roots.

For those root/constant conditions, acquire safe distinct dummies instead. On interval start u use d_s=q^(u-s), 1<=s<=3J. Their powers cost soft J. MPE the ACTUAL original F there and gcd each value with N. Proper gcd returns a factor. Otherwise every value is a unit or zero modulo N; discard the latter points. There are at most J discarded points by the degree-J root bound in either field. A discarded point may match DIFFERENT original roots across P and Q: it is not declared one globally equal original row. At least 2J certified good points remain; choose J.

The dummies are unit-separated from one another and the seeds because their exponent gaps are positive and at most L+3J<16H in the retained source window. Unit F(d_s) certifies separation from EACH original root, since its factor product is a unit. Their individual seed differences are therefore certified units. No long product of dummy evaluations is numerically acquired or divided out: its UNIT status suffices for the mask.

Use F_S times the first J-|S| dummy factors. The padded polynomial has unit constant coefficient and pairwise unit-separated roots, and its endpoint mask equals that of the original restricted rows. Acquire actual coefficients by monic product trees, soft J per bisection level. The stronger circuit contract must still cover ALL other denominators on these padded inputs; the root conditions alone do not imply it.

Balanced row bisection uses O(log J) endpoint calls and soft(J log J) coefficient/dummy work. A known-nonunit parent has a nonunit child; proper gcds terminate, otherwise saturated children continue. A selected original row uses its existing soft sqrt L locator. Total recovery is soft(C+J+sqrt L), without an h multiplier, conditional on that UNIFORM endpoint circuit. A zero-mask oracle supporting these same uniform queries also suffices without differentiation.

Thus pointwise differentiable traces yield the actual-h gradient interface; stronger uniform circuits yield old restriction recovery at unchanged scalar scale. Native-only formulas, known-covered-root constants and unverified padded branches meet neither contract automatically. No fast circuit or all-input acquisition theorem is supplied here.
