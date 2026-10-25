# Scalar endpoint circuits: reverse gradients and adaptive Hasse support recovery

24 October 2026. Scratch only; no repository changes, numerical examples or backend work. Root redirected this report from the parallel Toda audit to the Baur–Strassen recovery interface. The result is a fully specified transformation of an ACTUAL differentiable scalar endpoint circuit, not an acquired new fast endpoint circuit. First gradients recover an original witness whenever the smaller local hit count is one. An adaptive Hasse lift handles every multiplicity at cost soft(C*h), with h<=J; that factor is charged. No new whole-query exponent or generic lower bound is claimed.

Read journal lines 39678–39990 and `/tmp/semiprime-tensor-norm-20261024/scalar-resultant-algorithms.md`. The old scalar-only/zero-support interfaces, q-holonomic sqrt(JL) theorem, formal q-hook normalization and native masks are not repeated as new results. This report retains the FULL covered source E_L(F), not a selected small target family.

## 1. Exact circuit contract and primary sources

Let R=Z/N, N=PQ distinct odd primes, x_i=q^(u+i), 0<=i<L, with all required short q-differences units. Let

    F(X)=X^J+sum_(k=0)^(J-1) f_k X^k=product_j(X-Y_j),
    E(F)=product_(i<L) F(x_i),
    P_L(X)=product_(i<L)(X-x_i).

The original Y_j are explicit and pairwise unit-separated after the inherited guards; J<P,Q. q,u,L and all source labels are held FIXED during differentiation. Assume an actually supplied straight-line circuit computes E as a polynomial/rational identity in INDEPENDENT f_0,...,f_(J-1), with total arithmetic size C and all its evaluated denominators certified units. A division-free circuit, or one dividing only by public q-units, meets this contract even at E=0. This is stronger than a black-box unit-mask oracle or a program valid only on the native one-parameter beta family. The old blocked endpoint constructor supplies such a circuit at its existing cost; no smaller circuit is supplied by this report.

Walter Baur and Volker Strassen, *The complexity of partial derivatives*, TCS 22 (1983), 317–330, [primary paper](https://web.vu.lt/mif/s.jukna/tropical/Baur-Strassen.pdf), DOI [10.1016/0304-3975(83)90110-X](https://doi.org/10.1016/0304-3975(83)90110-X), proves a constant-factor derivative bound in its field/nonscalar-complexity model. Its resultant corollary explicitly uses derivatives of a product of polynomial values. The paper's lower bounds for independent generic roots are not imported as native lower bounds here. The composite-ring implementation below is proved directly by local reverse rules, rather than misquoting the field statement as an arbitrary-ring theorem. Cache `sources/baur-strassen-1983.pdf`, SHA256 `828e8c9eb30af0089c48b1a5bcac3990bc0e21d3b68d4e343490b0fdaa38ecae`.

Alin Bostan, Grégoire Lecerf and Éric Schost, *Tellegen's principle into practice*, ISSAC 2003, 37–44, [primary author PDF](https://mathexp.eu/bostan/publications/BoLeSc03.pdf), DOI [10.1145/860854.860870](https://doi.org/10.1145/860854.860870), gives explicit transposes of multiplication, remaindering, evaluation and interpolation over a commutative ring. Its linear-program transformation preserves arithmetic scale and includes precomputation distinctions. It does not evaluate an unacquired nonlinear endpoint merely by transposition. Here the short gradient-to-root map can alternatively be implemented by one explicit convolution, proved below. Cache `sources/bostan-lecerf-schost-2003.pdf`, SHA256 `c179b22688abc2ccf2deadc1fb5398ef9916e49f10688edc7a2a4b20a412e269`.

## 2. Reverse propagation is legal at actual zeros

Store the primal tape, seed the output adjoint with one, and reverse each gate. For z=a+b distribute its adjoint to both inputs. For z=a*b add b*adj(z) to adj(a) and a*adj(z) to adj(b). For z=a^(-1), add -z²*adj(z) to adj(a); z is already acquired and a is a certified unit. These rules use only ring arithmetic and those same unit inverses. In particular they NEVER divide by E, F(x_i), or an unverified pivot.

Thus all D_k=partial E/partial f_k cost O(C+J) total arithmetic, including explicit zero output slots and tape storage. Integer/modular bit overhead is the same as for the supplied circuit. A data-dependent unit guard can be frozen on a branch only when it supplies a rational identity in a formal neighborhood and its denominator remains a unit there. A branch “coverage says E=0, return zero” supplies no such identity in independent coefficients. A gcd/factor outcome already finishes factoring but is not a differentiable E gate.

If one only has a ternary Jacobi/Boolean zero oracle, Baur–Strassen does not apply. Likewise differentiating the native beta parameter yields a chain-rule sum, with q often varying too; it does not expose J independent root directions. Cutting the computation after coefficient acquisition is valid only if the remaining circuit genuinely accepts those independent inputs. Native relations must not be silently retained while their parameters are differentiated independently.

## 3. Exact first-gradient statistic and single-hit recovery

Direct polynomial differentiation gives the division-free identity

    D_k=sum_(i<L) x_i^k * product_(v!=i) F(x_v).    (1)

Proof-side let h_p be the number of grid nodes at which F vanishes modulo p. Distinct nodes and deg F=J give 0<=h_p<=min(J,L).

If h_p=1, with unique node x_*, then

    D_k = C_p*x_*^k modulo p,
    C_p=product_(v!=*)F(x_v) !=0.

If h_p>=2, every first derivative D_k vanishes modulo p. This describes support lost by first differentiation exactly; it is not a claim that native coverage has h_p=1.

For direct row recovery compose the scalar circuit with the already acquired monic root-product tree and reverse it as well. Equivalently compute all root derivatives g_j=partial E/partial Y_j in soft J additional work. Since E=(-1)^(JL)*product_j P_L(Y_j),

    g_j=(-1)^(JL)*P_L'(Y_j)*product_(a!=j)P_L(Y_a). (2)

At a field with exactly one hit, exactly ONE g_j is nonzero, at the original hit row: the q-separation makes P_L' at that hit nonzero, and all other row values are nonzero. At a field with two or more hits, every g_j is zero.

Actual controller: first compute gcd(E,N). A proper result factors; a unit result means no hit. On E=0 modulo N, acquire the root gradient and gcd EACH g_j with N. If one field has exactly one hit and the other has more, a proper gcd is obtained. If both have one but their row labels differ, a proper gcd is likewise obtained. Otherwise their one common row has unit g_j and is now identified publicly. The original one-row geometric locator costs soft sqrt L, with its original row/interval labels and saturated-leaf decoder. No auxiliary derivative value is itself fed to that decoder.

Therefore an actual scalar C-size circuit gives complete original-witness recovery on min(h_P,h_Q)=1 at total soft(C+J+sqrt L), without endpoint inverses. If J=1 this original one-row query already handles the whole task directly.

## 4. What the gradient gives modulo F, rather than a free P_L remainder

The coefficient gradient can be converted to the root-gradient interpolant without inversions. Put

    F_rev(T)=T^J F(1/T),
    D(T)=sum_(k=0)^(J-1) D_k*T^k,
    V_rev(T)= -D(T)*F_rev(T) mod T^J,
    V(X)=X^(J-1)*V_rev(1/X).                       (3)

This uses one truncated product and reversal, soft J over R. If lambda_F(Q) denotes the X^(J-1) coefficient of Q mod F, then

    sum_(k>=0) lambda_F(X^k V)*T^k=V_rev(T)/F_rev(T).

Since F_rev(0)=1, this is a lawful formal identity over R; matching its first J terms gives lambda_F(X^k V)=-D_k. With the unit-separated supplied roots, the usual Lagrange coefficient identity gives lambda_F(Q)=sum_j Q(Y_j)/F'(Y_j). Comparing with the root chain rule proves V(Y_j)=g_j. The algorithm (3) itself does not divide by F' or any hit value; ordinary monic MPE obtains all g_j in soft J.

On a UNIT-E branch only, this same V satisfies

    V=E * (P_L' / P_L) mod F.                     (4)

Thus the gradient naturally acquires a SCALED LOGARITHMIC-DERIVATIVE remainder. At zeros, (3) remains the valid polynomial/cofactor statistic, while the quotient notation (4) is not used. It is not P_L mod F. No reconstruction of that long remainder from (3) alone has been proved, and the q-shift relations needed to integrate it retain the earlier transport/endpoint charges. The consequence is a precise recovery interface, not a claim that scalar E automatically yields every long grid value at unchanged cost.

## 5. Adaptive Hasse lift: all hit counts with actual-h cost

Multiple hits can be handled while retaining every original row and seed. Work with the formal perturbation F+z and the SAME circuit. Every denominator unit at z=0 has a unique inverse in R[z]/z^t, so the lift is lawful with fast truncated-ring arithmetic. No value F(x_i) is inverted. Let

    A(z)=E(F+z)=product_i(F(x_i)+z)=sum_a a_a*z^a.

Modulo each p its valuation is EXACTLY h_p: the leading coefficient is the product of all nonzero F(x_i), with coefficient one from each zero factor. Hence it is nonzero. There is no cancellation premise here.

Handle a_0=E first as above. If it is a unit, return unit mask; if proper gcd, factor. Otherwise it is zero globally and both local counts are positive. Acquire A modulo z^2,z^4,..., stopping once some acquired coefficient has nonunit gcd behavior other than global zero; cap precision at min(J,L)+1. Scan coefficients in increasing order. Let h=min(h_P,h_Q) be the first index not zero modulo N.

- If gcd(a_h,N) is proper, the local counts differ and this gcd factors N.
- Otherwise a_h is a unit and h_P=h_Q=h. Counts are now common and acquired. h<=min(J,L).

Precision doubling is an actual attempt to avoid a uniform J multiplier: the sum of requested precisions is O(h+1), so the primal lifts cost soft(C*(h+1)+J), not C*J unless h is that large. Zero coefficients are compared as residues, not divided out. Run reverse differentiation ONCE at the final precision to obtain D_k(z)=partial E/partial f_k evaluated at F+z, modulo z^h. This has the same soft(C*h+J) bound. Gradient output slots and coefficient extraction are included; no J separate forward directional passes are needed.

Set

    B_k=[z^(h-1)] D_k(z).

Equation (1), now over the truncated ring, proves

    B_k = a_h * sum_(hit nodes x_i) x_i^k           (5)

in BOTH local fields. Indeed deleting a hit factor leaves valuation h-1 and the nonzero-factor product a_h; deleting a nonhit factor leaves valuation h and contributes nothing at that coefficient. Alternatively (5) is the derivative of the leading term of E(F+zR) with respect to the independent coefficients of R, at R=1. This derivation uses Hasse coefficients and has no factorial division.

Invert the certified UNIT a_h once. If h<J, take k=1,...,h in (5), available among the monic coefficient gradients, and use Newton identities to acquire the monic polynomial

    H_hit(X)=product_(hit nodes x_i)(X-x_i).

All divisions 1,...,h are units since h<=J<P,Q. Fast Newton/power-series conversion costs soft J. If h=J, take H_hit=F directly: degree J and exactly J distinct hit nodes force this equality locally. This avoids requesting a derivative with respect to the fixed monic leading coefficient. h=0 was already handled; empty L or J gives the direct unit case.

Evaluate H_hit at the ORIGINAL Y_j by monic MPE, cost soft J, and gcd each value with N. Local hit-row sets differ -> some proper gcd factors. If no proper gcd occurs, all zero evaluations are global, and at least one exists because h>=1. Select one such original row and run the original one-row locator, cost soft sqrt L. Local indices may differ across the two fields; this is precisely what the inherited row locator handles. Only an actual saturated ORIGINAL leaf invokes its bounded decoder.

This is a complete initialized support-recovery algorithm GIVEN the stated circuit, with total

    soft(C*(h+1)+J+sqrt L), h=min(h_P,h_Q)<=J,     (6)

or an earlier proper factor. Its scalar computation is entirely in public rings. It neither receives a hidden hit count nor assumes one small enough for the desired bound.

## 6. Sparse-jet test and the remaining multiplicity requirement

The adaptive doubling above is a substantive improvement over blindly requesting J jets: bounded h costs only a constant multiple of the hypothetical C-size endpoint acquisition. It also stops immediately on a coefficient gcd separating unequal local multiplicities. In particular the entire first-gradient controller is the h=1 case, with no long jet construction.

A sparse-leading-term implementation was tested symbolically as a further shortcut. Multiplication adds valuations, but addition needs actual coefficients when two valuations coincide; exact cancellation can raise the order. A general scalar endpoint circuit can contain such additive mixed gates, including the already tested Schur updates. Knowing only its output valuation h does not bound the necessary intermediate sparse supports or provide their coefficients. In the fully factored canonical expression A=product_i(F(x_i)+z), leading terms are easy AFTER all L factor constants have been supplied, but acquiring that length-L list already costs soft(L+J). Calling that a sparse-jet oracle would reinsert the missing endpoint work. No soft(C+J) all-h circuit transform is acquired here.

The safe implemented model therefore uses truncated-ring arithmetic and explicitly charges (6). Native q-order>16m² means an individual row has at most one grid hit, and row separation means a node hits at most one row. It does NOT by itself imply a constant TOTAL number of hit rows. The remaining sufficient requirement for uniform soft(J+sqrt L) recovery from a similarly fast scalar circuit is a proved bounded/soft-constant h, a paid isolation/restriction mechanism, or a new way to acquire the needed leading Hasse statistics without the h multiplier. None is supplied by first-order autodifferentiation alone.

## 7. Restrictions, actual instantiation and outcome

For a public interval starting at u and a row subset, acquire its ACTUAL F coefficients from the retained product tree and use that circuit instance with its actual J,L. The same proof applies unchanged, with h bounded by the restricted degree/horizon. Differentiating q or beta instead is not substituted for those independent coefficients. Logarithmic row bisection with a restriction-stable scalar oracle is the older complete recovery route; its calls still need their own paid endpoint circuits.

Instantiating this report with the existing generic monic blocking circuit gives C=soft(J+sqrt(JL)). The h=1 recovery adds only soft(J+sqrt L); for larger h a controller can retain the old complete restriction/bisection algorithm instead of paying the more expensive jet route. Thus every branch has a previously paid complete fallback, and no current guaranteed query bound improves. If a future genuinely generic scalar C=soft(J+sqrt L) circuit is constructed, this report makes its single-hit recovery essentially free and quantifies exactly the extra multiplicity cost for the full covered source.

Delivered: primary derivative/transposition contracts, a composite-safe first-gradient recovery algorithm, the precise scaled-logarithmic remainder it acquires, and an adaptive all-hit Hasse algorithm with actual-h cost and original-leaf recovery. No small-family coverage premise, derivative through a Jacobi oracle, division by a nonunit, free long norm, new endpoint circuit or whole-input factoring exponent is asserted.
