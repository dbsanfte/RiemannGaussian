# Independent review of the cyclic quantum-torus audit

26 October2026. Read `quantum-torus.md` and the primary Kashaev/Ishibashi sources, including Ishibashi's16October2026 correction. The finite algebra, paid screen, central-character separation and scoped cost claims pass. No numerical tests or repository edits.

## Cyclic determinant, signs and phases

For Ue_r=a zeta^r e_r and the forward wrap-c shift V, UV=zeta VU holds also at the wrapped basis vector. In det(G(U)−V), the full-cycle permutation contributes −c: its sign (−1)^(ell−1) times the ell negative shift entries gives (−1)^(2ell−1). Therefore det=product_r G(a zeta^r)−c, with exactly the printed sign. Taking G=1−X gives1−a^ell−c.

For F=product_j(X−v_j), each cyclic factor contributes (−1)^ell(v_j^ell−a^ell), hence the sign (−1)^(ell J) in equation(2) is correct. Since ell is odd, det U=a^ell zeta^[ell(ell−1)/2]=a^ell. The reciprocal Laurent normalization is consequently c_0^ell a^(−ell L), as stated. All these are genuine integral finite identities after adjoining zeta; they retain zeros and require no matrix-dilogarithm branch convention.

The soft-J scalar readout presumes that the central values a^ell,c and native v_j are actually acquired base-ring scalars, as in the intended arithmetic specialization. If arbitrary unrelated extension-coordinate inputs a,c were allowed, their acquisition would have to be charged; the report already warns against J full cyclotomic vectors. It would be useful to make the base-ring central-input convention explicit in Section2.

## Order screen and at-most-one-point statement

The original scalar q-orders are odd and coprime; powering by ell preserves coprimality. The arbitrary-unit separator applied to q^ell through16H therefore either factors, returns exact common order1, or certifies both orders>16H. In the common-order1 branch, ell is a nonzero short GLOBAL annihilator of the OLD q with its supplied high odd orders. The licensed extractor applies. No assumption that the powered q itself still has high order is needed in that branch.

On the continued branch, z_i^ell−z_j^ell=eta^ell q^(ell*j)((q^ell)^(i−j)−1) is a unit whenever0<|i−j|<m<16H. Thus one auxiliary ell-cycle can contain at most one physical clock point per local component, independently of split factorization of the cyclotomic algebra. The two conic lifts differ by eta and have distinct ellth central characters as well; rho has the same odd order as q since rho⁴=q.

This proves precisely the failure of covering the ENTIRE geometric clock by one standard cyclic block. It does not disprove a specially selected polylogarithmic family covering one guaranteed native witness. The report correctly preserves that distinction.

## Actual-q boundary and cost

For D=diag(1,q,...,q^(r−1)), the interior commutator DC−qCD vanishes and the wrap entry is c(1−q^r), with the printed row/column orientation. It is a unit under the short-order guard. The periodic finite-dilogarithm recurrence clears to (xq;q)_r g_r=y^r g_0. Imposing an invertible periodic g_0 genuinely requires the missing block scalar as y^r. A nonunit block scalar cannot have a unit root; removing this normalization would remove original zeros.

The degree-r q-factorial at J*m/r actual starts has the charged soft(r+Jm/r+J) completion, including final tails and without collision inverses. Taking r=Theta(k) costs about m; optimizing over unrestricted admissible r gives the old bound. The latter optimizer is about k^1.25, so it should be read as returning to the ordinary algorithm, not preserving the earlier intended rank-O(k) architecture. No hidden faster normalization is claimed.

## Weil/cutoff and source hypotheses

The conductor-S Gaussian matrix factors into two invertible diagonals and a permuted Fourier matrix, so its rank is S; inverse Fourier scaling by S is legal since3 is a unit. The cutoff commutator formula has the correct sign. A nonempty proper cyclic mask necessarily has a boundary coefficient+/-1. The full b=1 low-a mask is proper by the unit-square-image count, and nonempty after standard pruning using a=7 when N=1mod3 or a=5 when N=2mod3. State that assignment explicitly if desired; these choices are nondegenerate, lie inside |ab|<k, and have abN=1mod3.

Kashaev's primitive odd-root cyclic modules and Fermat constraint match the source role claimed. Ishibashi's original paper uses an auxiliary root of unity; its new correction requires additional lifting data and allows an extra root-of-unity phase, with strict lifts on its specified regular locus. Those are complex/coefficient-space statements, not an algorithm constructing arbitrary modular lifts. The report does not import such an algorithm. Its directly proved determinant/boundary identities avoid that issue, and valid auxiliary phase units do not make native block normalizers units.

## Decoder and conclusion

A proper scalar gcd always factors. A saturated powered-root difference needs the stated known nonzero exponent label; multiplication by ell preserves its short bitwidth. Additive determinant shifts, arbitrary cutoff minors and auxiliary spectral zeros have no automatic original-gap decoder. These restrictions are correctly maintained. Subject to the small input-convention clarifications above, the report requires no mathematical correction and establishes no full-query speedup.
