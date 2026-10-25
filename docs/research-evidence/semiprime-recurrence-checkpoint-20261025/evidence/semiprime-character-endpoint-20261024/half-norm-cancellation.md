# Half-norm cancellation test: exact scalar half, unchanged terminal degree

2026-10-24. Scratch only; no repository edits, examples or backend work. This executes one half-norm attempt: remove the known-unit normalizers and take the scalar half of a norm-one chord square, then derive and acquire its terminal polynomial. The half exists with paid data and preserves zero support on every restriction. Its terminal polynomial is exactly a known-unit multiple of the original degree-J torus target polynomial. Thus it does NOT reduce degree times horizon, and no new whole-query exponent is obtained.

## Prior boundary read before the attempt

- character-aggregate/reciprocity-observable.md, SHA256 19a87256dcf5ef9be65534e8a7b9a70f519bd424a06e89ded06b581292d50517: a ternary symbol with its ZERO convention is sufficient, while a unit-only phase and a known root-level zero do not locate a row.
- /tmp/semiprime-dyadic-shared-20261022/source-retaining-functional.md, SHA256 a07d811cebca3e4d9ff2e830e0a861c1430ba3ae6c7a370de575046e231ddbf0: the exact reciprocal defect (V-1)^2/V and its source boundary were already proved.
- /tmp/semiprime-gauss-period-20261024/period-query-attempt.md, SHA256 b876429f4ca01b324e5dec74d62a27706664942c023a5eb97487252df6152cb9, and period-recovery.md, SHA256 bb8fd816c969e00061192201e88c97d0d8e0ed0993dced370f1e7ea670408e3d: constant antipodal folding, common-power dyadic identities and the guarded torus decoder are already known. They are not credited as a new acceleration here.

Also read the native multiplier closure and acquired Gauss weighted aggregate reports: exact target products or low-digit inverse-tag maps are not products of target-minus-seed factors. The tested construction below retains the full difference query rather than substituting those unit aggregates.

## 1. What can safely be removed from the original scalar query

For the original scalar beta source, let Y_j=beta^(N+delta_j), q=beta^H and

    E=product_(j,i)(Y_j-q^i), H=m^2, 0<=i<L.

Every public row/seed restriction retains the same setup. The targets and seeds lie in a common odd-order subgroup locally. Choose beta0 itself to be an already prepared ODD-LOCAL-ORDER base and replace the working beta by its known public square beta0^2; this preserves the odd local orders, every local collision and the native decoder margins. The coherent roots x_j=beta0^(N+delta_j), y_i=beta0^(H*i) then lie in odd-order subgroups too. An arbitrary known square root of an odd-order beta need not have odd order and is NOT sufficient for the following unit claim. With this explicit odd-order-root construction,

    x_j^2-y_i^2=(x_j-y_i)(x_j+y_i).

The plus factor is a certified unit: a ratio in an odd-order group cannot equal -1. Returning to the known roots preserves every local equality and order, so it preserves native coverage and the original bounded decoder. However it retains J targets and the SAME L indices. This is an exact zero-safe removal of a unit cofactor, not a shorter query. Repeated public dyadic powering/undoing has the same property.

One cannot similarly delete a square factor of an unknown/nonunit difference. If d is nonunit then d^2 is nonunit at exactly the same local primes; deleting d^2 would delete the source. The scalar half attempt below computes a concrete square root expression from known group data, rather than dividing a target square away.

## 2. Acquired coherent half in the GUARDED period torus

Use B=calR[tau]/(tau^2-D), calR=Z/N, with 2,D units, conjugation bar and Norm(z)=z bar z. Assume the PAID survivor branch of period-recovery.md returned a norm-one point R0 with coprime odd local orders >16H and the corresponding q-order guard. This assumption does not hold on its unresolved separator-kernel branch, and does not follow merely from the original scalar beta order.

Set R=R0 and W=R^2. This is an ACQUIRED coherent square root, not a hidden root extraction. Squaring preserves the already odd local orders, including the q-order guard, and every own equality. The same signed period decoder remains applicable to the W rows because its order margin is unchanged. No original-beta decoder is transferred to W.

For a native torus exponent E_j=ell_j+chi(j)(N+a_j), acquire

    r_j=R^E_j=A_j+tau B_j,
    Y_j=W^E_j=r_j^2,
    u_i=R^(Hi)=a_i+tau b_i,
    q=W^H,  q^i=u_i^2.

All r_j (two coordinates each) are acquired in soft J by signed powering. We do not acquire all L seed vectors. All r_j,u_i have odd local order. Their real coordinates A_j,a_i are certified SCALAR units: if Re(z)=0 for a norm-one z, then z^2=-1, which would force an order divisible by four, impossible for these odd-order points. This argument applies to the full local quadratic algebra, including the split case. Target real-coordinate inverses cost soft J; no imaginary coordinate or hit value is inverted.

For K=E_j-Hi, write R^K=a+tau b. Then

    W^K-1=R^K(R^K-R^-K),
    Norm(W^K-1)=-4D b^2.

Therefore the scalar Hhalf=product_(j,i) Im(R^(E_j-Hi)) satisfies EXACTLY

    product_(j,i) Norm(Y_j-q^i)=(-4D)^(JL) Hhalf^2.  (1)

The square Hhalf^2 contains all collision zeros. It is not divided away. Equation (1) defines a true scalar half from acquired group inputs; its long product remains to be computed.

## 3. Unit normalizers of that half are actually acquired

Set acquired scalar targets c_j=B_j/A_j. Write c_i=b_i/a_i for the implicit seed sequence. Direct multiplication gives

    Im(R^(E_j-Hi))=B_j*a_i-A_j*b_i
                 =A_j*a_i*(c_j-c_i).

Thus

    Hhalf=Uhalf*V,
    Uhalf=(product_j A_j^L)*(product_i a_i^J),
    V=product_(j,i)(c_j-c_i).                       (2)

Uhalf is a certified unit. Its target part costs soft J. Its seed part is also actually paid, without listing L vectors. Put r=R^H, r^2=q. Then

    product_(i=0)^(L-1) a_i
      =2^-L*r^(-L(L-1)/2)*product_(i=0)^(L-1)(1+q^i).

The last product is one degree-one geometric product in the fixed-rank algebra B: build its common length-b baby polynomial, evaluate at the L/b actual giant starts by monic MPE, include the tail, and choose b near sqrt L. It costs soft sqrt L. Each factor is a unit because q has odd local order; the resulting scalar value and its inverse are lawful. The known powers cost polylogarithmic work. Thus ALL normalizers removed in (2) cost soft(J+sqrt L), including unit certificates and their values.

The procedure is not using the norm product (1) to extract a modular square root. It constructs the half expression and its cheap normalizers directly. Taking a square root of a supplied squared residue would be a different operation and could not be assumed over unfactored N.

## 4. Actual terminal polynomial: the apparent half returns the original degree J

The implicit scalar seed has the exact Cayley form

    c_i=(q^i-1)/(tau*(q^i+1)).

All displayed denominators are units, and this expression is fixed by conjugation. For each acquired c_j build the LINEAR polynomial over B

    L_j(X)=(tau*c_j-1)X+(tau*c_j+1),
    G(X)=product_j L_j(X), degree J.

At X=q^i,

    L_j(q^i)=tau*(q^i+1)*(c_j-c_i).

Hence

    V=tau^(-JL)*product_i(q^i+1)^(-J)
             *product_(i=0)^(L-1)G(q^i).          (3)

The prefactors have already been acquired in soft(J+sqrt L). G is genuinely acquired from J linear factors by a product tree in soft J rank-two work.

But since c_j=(Y_j-1)/(tau*(Y_j+1)), one obtains the STRONGER exact identity

    L_j(X)=(-2/(Y_j+1))*(X-Y_j),
    G(X)=[product_j -2/(Y_j+1)]*F_W(X),
    F_W(X)=product_j(X-Y_j).                       (4)

Each Y_j+1 is a certified unit by odd local order. Therefore G has degree exactly J with unit leading coefficient. The square-half operation has returned precisely the original torus polynomial up to an acquired unit. It does not halve its degree or shorten the seed horizon.

The completed initialized evaluator for (3) builds product_(r<b)G(q^r X) of degree Jb, evaluates it at L/b actual giant starts, and pays the tail. Its cost is

    soft(Jb+L/b+J), minimized at soft(J+sqrt(JL)).

At J~m,L~m^2 this remains soft m^1.5. This is an actual scalar output V and can be recovered without a dense matrix, but it is just a unit rescaling of the already available query. The old constant antipodal target fold is not being counted as progress; equations (1)-(4) do not even require that pairing.

## 5. Jacobi-square phase: the zero case is the WHOLE missing mask

For any scalar z modulo squarefree odd N, Jacobi_N(z^2)=1 if z is a unit and 0 otherwise. Equations (1)-(2) therefore give the exact ternary symbol

    Jacobi_N(product Norm(Y_j-q^i))
      =Jacobi_N(-D)^(JL) * 1_(V is a unit).        (5)

The phase is cheap, but the indicator is NOT removed by the square. Its zero output is exactly the desired collision support. Replacing the left side by its known unit phase on every restriction returns the wrong answer whenever that restriction contains a collision. Computing (5) with the correct absorbing zero convention is a potential smaller OUTPUT contract, not an acquired algorithm here.

Likewise the covered unrestricted product is known nonunit, so its symbol zero is known already. That does not identify a successful row or seed child. A usable half-norm/Jacobi routine must retain (5) on each paid row/interval restriction; unit-only reciprocity identities are insufficient. This is the same zero-symbol boundary emphasized in the prior reciprocity report, now checked on the actual half expression.

## 6. Scalar discriminant cross-check: no cancellation of a target square

Return to the ORIGINAL scalar source and P_L(X)=product_i(X-q^i). Its internal discriminant and Disc(F) are units by the same-side separation certificates. The integral identity is

    Disc(F P_L)=Disc(F)*Disc(P_L)*Res(F,P_L)^2,
    Res(F,P_L)=product_(j,i)(Y_j-q^i)=E.           (6)

Thus removing the two certified-unit normalizers leaves E^2, which has exactly the original nonunit support. It does not leave a known unit. In particular the fact that a split squarefree polynomial has square discriminant does not decide whether this combined polynomial is squarefree: a cross collision makes its discriminant zero modulo the corresponding prime. The exact Jacobi output is 1 on the fully unit case and 0 when a collision occurs (all internal Vandermonde squares are units), which is the same unacquired Boolean query.

Disc(F) is actually acquired in soft J via derivative MPE at its supplied, unit-separated roots, with the known discriminant sign. Disc(P_L) has the certified-unit weighted q-factorial formula, but its numeric value is NOT taken as free; direct acquisition costs soft L. For support arguments its value can be omitted using only its proved unit status. The combined implicit degree-(L+J) polynomial/discriminant still has not been acquired at soft(J+sqrt L). Its cross square is precisely the target, not a factor licensed for cancellation. This is a diagnostic identity, not a second proposed fast algorithm.

## 7. Restriction safety and recovery

Equations (1)-(5) hold on any supplied row subset and seed subinterval, with the actual native index shift retained. All target/seed normalizers remain units. The one degree-one seed product starts at the corresponding q^a and costs soft sqrt(length); the linear target polynomial is rebuilt for the restricted rows. No original nonunit difference, imaginary coordinate, square of a hit value or collision-sensitive pivot is inverted.

The acquired scalar product V is nonunit at a hidden prime EXACTLY when a corresponding original torus row hits there, since all factors between (1)-(4) are units and a scalar square vanishes in a field only when its base does. Proper gcds factor. Saturated products can be localized by these paid restrictions at the existing soft sqrt(JL) clock. At a saturated LEAF, the invertible Cayley transform gives an actual global period-row collision. The signed sum/difference decoder is then used ONLY under the already acquired survivor/order guards of period-recovery.md. No original scalar beta decoder is assigned to the period representation for free.

For the discriminant test (6), a saturated original scalar leaf instead uses the original beta decoder. The two recovery contracts are kept distinct.

## Outcome

The tested half norm has an exact acquired scalarization, cheap certified-unit normalizers and a complete restriction/recovery contract on the guarded period branch. Its actual terminal polynomial equals an acquired unit times F_W, so the degree-times-horizon interaction is unchanged. The Jacobi-square shortcut retains an unpaid exact zero/unit mask, and the scalar discriminant identity retains E^2 rather than canceling it.

No new smaller covered norm or half-norm acceleration is obtained. The positive algebra above is a paid test of that concrete cancellation idea, not a claim that every square/discriminant or character method has the same cost. A new construction must change the actual terminal acquisition while preserving the absorbing zero and its original leaf witness.
