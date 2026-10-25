# Independent review of conductor-m³ quadratic colour

22 October 2026. Reviewed `higher_conductor/native-quadratic-colour.md`. The displayed signs, full nested Frobenius action, quadratic image and Hensel stabilization are correct. The retained colour is a public admissibility palette, not the unknown true index. A small constructive polynomial interface is available, described below; the long masked query remains unacquired.

## Wild Gauss formula and full Frobenius

In the decomposition v(1+mt), put t=t0+ms. The specified character contributes zeta_(m²)^t0 * zeta_m^(s-t0²/2), while the additive character contributes zeta_(m³)^v * zeta_(m²)^(v t0) * zeta_m^(v s). Summing over s forces v+1=0 modm. Its Teichmueller representative is exactly -1, so the zeta_(m²) factors cancel and

    tau(chi)=m zeta_(m³)^(-1) sum_t zeta_m^(-t²/2).

The negative quadratic sign is correct. The quadratic Gauss sum G satisfies G²=epsilon*m independently of its nonzero quadratic coefficient. For A=mG, full P-Frobenius sends A to Legendre(P,m) A modulo P and zeta_(m³) to its Pth power. Its inverse has the same sign on A. Consequently the report's scalar amplitude A^(ell+a+N) Legendre(j,m)^(a+N) and root exponent -ell-aP-NP^(-1) are correct. Independent automorphisms on the nested roots have not been assumed.

Here the Gauss-source amplitude A is NOT automatically the original prepared scalar gamma. Its own order/recovery contract would need separate proof. The report correctly avoids that problem by passing to u0=gamma*zeta_(m³)^(-1); only this latter branch directly preserves the original prepared scalar source.

## Native arithmetic, source preservation and recovery

From m²c-jm b+j²a=N, ell=mb-2aj and P=j+mh, direct expansion gives

    P*(aP+N/P+ell)=m²(ah²+bh+c).

Thus IP=ah²+bh+c and I=(ah²+bh+c)/j modm. This proves both the reported third-digit cancellation and the signs in

    (b+2ah)²=Delta+4ajI, Delta=b²-4ac.

For u0, the public candidate family T_(j,h)=gamma^E zeta_m^(-f_j(h)), q0=gamma^(m²)zeta_m^(-1), contains the original own collision at the ACTUAL h and I. It is not correct to select one h publicly without another theorem. If a selected extension-ring leaf is nonunit in even one local component, raising the corresponding equality to the mth power gives the scalar annihilator

    gamma^[m(E-m²I)]=1 modulo that prime.

This uses no choice of a local primitive root. The inherited nonzero integer-gap guard is still required; multiplying by m preserves nonzeroness and adds O(log m) exponent bits. This implication supplies recovery AFTER a leaf is located, not acquisition of the nonunit leaf or a free extension-ring locator. A saturated scalar annihilator remains subject to the inherited decoder premises.

## Exact image and the two common palettes

Completing the square gives

    f_j(h)=kappa_j+lambda_j(h+b/(2a))²,
    kappa_j=-Delta/(4aj), lambda_j=a/j.

Since aj²=N modm, Legendre(lambda_j,m)=Legendre(Nj,m). Let S_+={0} union nonzero quadratic residues and S_-={0} union nonsquares. Then EXACTLY

    R_j=kappa_j+S_(Legendre(Nj,m)).

Both have size (m+1)/2. The h translation does not affect the image, and multiplication by a square/nonsquare only chooses between these two sets. A public residue table and the J pairs (kappa_j,sign_j) therefore give O(m+J) descriptors for every mask; an m-by-m Boolean table is unnecessary. This is a useful exact normalization, but it does not select the true I or evaluate the associated masked product.

There is a stronger, paid small POLYNOMIAL interface if useful downstream. Let g denote the standard quadratic Gauss element, g²=epsilon*m, and retain it formally in R[g]/(g²-epsilon*m), without extracting a square root modulo N. Define

    K_eta(Z)=product_(r in S_eta)(Z-zeta_m^r), eta=±1.

Their coefficients lie in this quadratic subalgebra. For 1≤k≤(m+1)/2<m, their power sums are exactly

    p_k=(1+eta*Legendre(k,m)*g)/2.

The standard finite character sum proves this formula; it retains the orientation of g as the standard Gauss sum. Native prepared local orders >16m² imply P,Q>m, so 1,...,(m+1)/2 are units modulo N. Construct both K_eta by fast Newton identities / truncated-series exponential in soft O(m) fixed-rank-ring work and soft O(m log N) bits up to logarithms. The Legendre table, coefficient output and unit divisions are charged. This uses formal quadratic algebra, not a supplied scalar square root.

For a complete constructive proof, put D=(m+1)/2 and compute

    E_eta(T)=exp[-sum_(k=1)^D p_k T^k/k] mod T^(D+1),
    K_eta(Z)=Z^D E_eta(1/Z).

The formal product identity E_eta(T)=product_(r in S_eta)(1-zeta_m^r T) proves correctness through degree D, hence recovers the whole degree-D polynomial. It follows by logarithmic differentiation or Newton identities and is an identity of truncated formal series, with no analytic convergence assumption. Every division is by 2 or an integer at most D, a certified unit. Those inverses can be batch-built with one factorial inverse and O(m) scalar products. Standard Newton iteration for formal logarithm/exponential uses soft O(D) operations in the fixed rank-two coefficient ring when these denominators are units; multiplication is cyclic/integer-packed polynomial multiplication, so no field hypothesis is required. The two signs share the Legendre table and denominator preparation. This explicitly constructs all O(m) quadratic coefficients, and the extension map g→sum_r Legendre(r,m)zeta_m^r identifies them with the asserted root polynomials. No choice of a local sign or scalar square root is used by the algorithm.

These zeta-mask polynomials must also be distinguished from the scalar root polynomial product_(r in S_eta)(Z-q^r). The latter is independently acquired in soft O(m) by generating q^r for r<m and a monic product tree, but its coefficients do not generally obey the displayed quadratic-Gauss power-sum formula. Neither polynomial's short acquisition supplies the product over the remaining length-about-m quotient-index orbit.

These are two explicit degree-(m+1)/2 root polynomials, beyond a mere predicate description. They still do not evaluate the original long orbit. For a row's negative phase, the h-product has degree m, since the centre has one preimage and every other image has two. In particular it is a phase-translated K_(epsilon*eta)^2 with the centre factor removed. Row-dependent phase translations generally return to the full zeta_m algebra. Materializing J such degree-m polynomials has quadratic output; storing the two K polynomials plus J scalings/translations is compact, but a cheap product/norm query on that compact family is another algorithmic requirement.

A polynomial encoding S_eta over the AUXILIARY field F_m, such as Z*(Z^((m-1)/2)-eta), also gives the correct membership predicate. It must not be evaluated modulo N as though its auxiliary roots were the original collision residues: m is a unit modulo N. The quadratic Gauss-root polynomials above are a different, source-compatible cyclotomic construction.

## Hensel statement and precise limit

The exact relation with I gives a h²+(b-mI)h+(c-jI)=0. Since 2a is a unit at m, solvability modulo m^t is equivalent to the discriminant D(I)=(b-mI)²-4a(c-jI) being a square there. Modulo m this is the nonconstant affine expression Delta+4ajI. For each of its (m-1)/2 NONZERO-square classes, every integer lift I has a nonzero square root modulo m, and Hensel lifts either root to every higher power. The one zero-discriminant class may thin further. The reported surviving fraction is therefore correct for this quadratic solvability predicate.

This statement concerns the residue predicate, not existence of a prime P of the required size, the actual h of N, or every native interval condition. Those requirements are not inferred from Hensel solvability. Conversely the report uses the predicate as a necessary public superset retaining the true index, which is valid.

No substantive correction to the report's algebra is required. Recommended clarifications: explicitly separate the Gauss amplitude's order from prepared gamma, retain the nonzero-gap recovery guard, and state that the two common palettes and even their paid degree-O(m) root polynomials have not acquired the masked long norm or its restriction-stable locator.

Finally, an extension norm being nonunit means some local component is nonunit; a saturated norm does not mean the element vanishes in every component or identify a leaf. For a SELECTED source-compatible leaf, any such component suffices for the scalar mth-power annihilator above. Acquiring the norm itself, restricting it to a child interval/row subset, and selecting that leaf still require charged algorithms. This distinction remains necessary even when a quadratic subalgebra makes an individual coefficient norm inexpensive.

## Additional review: two-common-products boundary construction

Read `higher_conductor/two-common-products.md`. Its interval reduction and paid boundary method are correct. For S=kappa+r, original index i=S+mn gives lower endpoint n=-1 exactly when S>=m, and otherwise n=0. Its upper endpoint is K when S<t, K-1 when t<=S<m+t, and K-2 when S>=m+t. These are exactly the stated A/B/C corrections. Multiplying the remaining D_j factors contributes q^(kappa D_j), so the displayed polynomial identity, including its scaling, is correct.

For K>=1 denominator removal roots correspond to original auxiliary indices in [L,L+m-2], outside the covered native interval. The explicit nonzero exponent-ledger check is therefore essential; the note supplies it rather than assuming every saturated denominator zero is useful. For K=0 the proposed symbolic cancellation leaves precisely S in [m,m+t) or S<t, so no illegal inverse is used. Prefix/suffix decomposition requests O(1) nodes per tree depth per row; batched monic multipoint evaluation has total degree O(m) and O(J) point requests at that depth. Hence its soft O(m+J) cost is justified, with native O(log N)-bit descriptors and modular powers. A single selected nonunit boundary tree can also be descended within this budget.

The product identity H_+H_-=F_(mK)*product_(n<K)(X-q^(mn)) is exact because only residue zero is duplicated. The second factor costs soft O(K+J), which is soft O(m+J) in the stated native L~m² regime. The two degree-about-L/2 common H polynomials remain unacquired. Thus this is a genuine paid translation-and-boundary reduction to TWO common long products, stronger than merely listing O(m) mask descriptors, while it still supplies no faster evaluator for the remaining weighted products.
