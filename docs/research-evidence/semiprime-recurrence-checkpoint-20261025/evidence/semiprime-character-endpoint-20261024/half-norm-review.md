# Independent half-norm cancellation review

24 October 2026. Reviewed exact current bytes of /tmp/semiprime-character-endpoint-20261024/half-norm-cancellation.md.

SHA-256: `b0185cb2ab94f4224ebe3133dabe0a1cb5179f87ecfe22907f72160b93118889`.

Verdict: **PASS. No required fixes.** Read-only final audit; no source changes, examples, backend work or further research claim.

## Coherent roots and exact scalar half

The scalar opening correctly requires an ALREADY odd-local-order beta0 and sets the working beta=beta0². Squaring preserves these odd orders and the original local/global collision conditions, so x_j=beta0^(N+delta_j) and y_i=beta0^(Hi) are coherent odd-order roots. Their plus factors are units because their ratios lie in the same odd-order subgroup. An arbitrary supplied square root would not suffice, and the final text explicitly excludes that shortcut. Original beta coverage and bounded recovery margins survive the controlled replacement.

For the period construction the raw and guarded branches are correctly distinguished. R is supplied by the paid surviving period controller, not extracted as a root of an arbitrary W. Setting W=R² preserves the odd local orders, their coprimality and the certified H-power orders. These are additional period guards, not consequences of original beta's order.

If R^K=a+tau*b, then R^K-R^-K=2*tau*b and Norm(R^K)=1. Thus Norm(W^K-1)=-4D*b² exactly. Norm(u_i²)=1 removes the seed unit from Y_j-q^i, giving equation (1) with exponent JL and no missing prefactor. Hhalf is an explicit scalar expression from coherent group powers; the report never extracts it by taking a modular square root of an acquired norm.

## Real coordinates and all removed normalizers are paid units

For a norm-one local element z of odd order, Re(z)=0 would imply z²=-1 and hence order four. This contradiction is valid in the entire local quadratic algebra, including its split case. Therefore each A_j and a_i is a nonzero scalar in both hidden fields, hence a unit modulo N. No imaginary coordinate or difference value is inverted.

The formula Im(r_j*bar(u_i))=B_j*a_i-A_j*b_i=A_j*a_i*(c_j-c_i) checks. With r=R^H and q=r²,

    product_i a_i=2^-L*r^[-L(L-1)/2]*product_i(1+q^i)

follows directly by a_i=(r^i+r^-i)/2. Its right side is indeed scalar; its algebra prefactors and signs are correct. The degree-one plus product is acquired by ordinary fixed-rank geometric blocking in soft sqrt L. Each factor is a unit by odd order, and the target real-coordinate products/inverses are soft J. Therefore the full Uhalf and every normalizer removed in equations (2),(3) cost soft(J+sqrt L), including values rather than mere unit promises. A shifted seed interval adds only the known starting power and uses the same constructor at its actual length.

## Terminal polynomial is exactly a unit multiple of degree-J F_W

The Cayley formula c_i=(q^i-1)/(tau*(q^i+1)) is correct. Its denominators are units, and conjugation fixes the result. At a target the same formula gives

    tau*c_j-1=-2/(Y_j+1),
    tau*c_j+1=2Y_j/(Y_j+1).

Consequently L_j(X)=(-2/(Y_j+1))*(X-Y_j), exactly as stated. Every Y_j+1 is a unit, so their product multiplier is an ACQUIRED unit. G therefore has exact degree J and unit leading coefficient even at target hits; no top-coefficient cancellation or hidden degree-halving occurs.

The factor tau*(q^i+1) in L_j(q^i)=tau*(q^i+1)*(c_j-c_i) yields the prefactors of equation (3) with the displayed signs and powers. Building G is soft J. Acquiring its long terminal product uses a degree-Jb coefficient block and L/b explicit giant starts, costing soft(Jb+L/b+J), optimized at soft(J+sqrt(JL)). The report does not replace this terminal acquisition by the cheaper normalizer computation.

## Jacobi zero convention and discriminant check

For squarefree odd N, Jacobi(z²,N) is one precisely for a unit z and zero otherwise. Applying this to equation (1), with Hhalf a unit exactly when V is, gives the exact phase Jacobi(-D,N)^(JL) multiplied by the absorbing unit indicator. The scalar factor 4 is a unit square. This includes all nonunit cases correctly; removing an even exponent from a symbol without retaining its zero support would change the desired function.

The discriminant identity is also exact: Disc(F P_L)=Disc(F)*Disc(P_L)*Res(F,P_L)², and the report's E orientation agrees with Res(F,P_L)=product_j P_L(Y_j). Same-side separation makes both internal discriminants units, while cross collisions remain in E². Since these are split monic root polynomials, their discriminants are Vandermonde squares; the combined Jacobi output is exactly the unit/nonunit mask, not a known unit on collision restrictions. Acquiring Disc(F) by derivative MPE and the known sign is soft J; Disc(P_L)'s numeric weighted q-product is correctly not assigned free acquisition. Its support normalization can be omitted using the already proved unit property.

## Restrictions and distinct recovery contracts

All identities hold for supplied row subsets and shifted seed subintervals, with their actual labels and endpoint powers retained. Plus/real normalizers stay units. Monic MPE does not invert cross differences, and a saturated aggregate descends by the same paid restrictions at the old clock.

At a scalar half-product leaf, the unit Cayley identity implies an ACTUAL global period-row collision when saturated; there is no split-component orientation ambiguity. The report invokes the signed period sum/difference decoder only after the paid surviving-point/order guards, and explicitly retains the unresolved preparation branch. It does not apply an original scalar beta decoder to W for free. In the separate original scalar discriminant experiment, saturated original beta leaves instead use their own original decoder. These are the correct, separate recovery contracts.

## Final assessment

The half and its normalizers are constructively acquired, and the zero convention/recovery are sound. The final polynomial is exactly a unit times the original degree-J torus target polynomial, so the completed query remains soft m^(3/2) at the native scale. The reviewed bytes claim no smaller covered endpoint, no new factoring exponent, and no lower bound on other half/discriminant/character algorithms. PASS.
