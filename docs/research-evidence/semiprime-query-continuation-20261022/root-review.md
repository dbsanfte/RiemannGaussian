# Root integration review

2026-10-22. This is a classical proof review, not a Lean check or an
implementation benchmark. The checkpoint claims no new whole-family
acquisition bound.

1. The weighted lattice has determinant m because gcd(Nj,m)=1. With
   coordinates K/T and (A-KN/P0^2)/(m/T), its determinant is one. Fixed
   dimensional Gauss reduction therefore gives the stated absolute
   constant bounds. At the interior parameter scales, neither A nor K
   can vanish: the defining congruence would force the other nonzero
   coordinate to have absolute value at least m. Boundary constants
   require the stated finite handling; no asymptotic claim relies on
   a zero leading coefficient.

2. The congruence for B and definition of C0 give
   g(h)/P=(AP+KQ+Bm-2Aj)/m^2. Subtracting the value at P0 uses the exact
   remainder KN*x^2/(P0^2*(P0+x)), so the displayed window bound does
   not rely on a truncated Taylor approximation. Centering subtracts
   an acquired integer multiple of mx+j, shifting the quotient by a
   known integer. The balanced-case window count is charged explicitly.
   It is not extended to all unbalanced inputs without a further ledger.

3. The giant exponent simplifies to KN+Bm+A(1-2j). For a true witness,
   its difference from m^2*sigma is divisible by P-1. Thus a full-N
   match and a short candidate interval force sigma'=sigma by the
   local order of q. The recovery quadratic has nonzero leading A.
   A fixed-degree extension uses
   m^d*g((Z-j)/m)-sigma*m^d*Z^s and tests the zero-polynomial exception.
   For dyadic m, odd local orders are unchanged by powering by m^d.
   Giant exponent size is absent from this recovery proof. An unrelated
   full-N hit must not discard a true witness from another interval;
   target reuse retains the interval labels and diameter checks.

4. In the original scalar query, x_j/q^i has odd order at each prime,
   so it cannot be -1. Squaring therefore multiplies by units and keeps
   precisely the same local hits, including under restriction. It keeps
   the same J and L. Every coefficient of the geometric seed polynomial
   is a unit by the q-binomial formula and the retained q-order bound.
   No zero coefficient tail is available in this particular repair.

5. The Cauchy clearing identity is a polynomial identity: the cleared
   columns are the degree-(J-1) Lagrange numerator basis. Their evaluation
   determinant equals the within-target Vandermonde times the
   within-seed Vandermonde, up to sign. This verifies the loss of cross
   collision support without assuming any cross-factor inverse. The
   negative conclusion concerns that exact proposed replacement only.

6. The higher-degree lattice determinant and its known trivial
   sublattice have the stated exponents. Successive-minimum bounds do
   not turn the projected quotient-lattice mean into a small integer
   lift. The report does not prove that a better source-specific lift
   is impossible, or that all higher-degree methods fail.

7. Root and the independent reviewer checked the order/root algorithms.
   Their product-tree exponent-bit sums include setup, all node powers,
   gcds, and output. The rough-subgroup inverse-exponent proof of root
   separation has replaced the earlier informal exponent cancellation.
   These are inherited paid constructions. Their early scratch wording
   suggesting a new acquisition advance was corrected before archival.
   Their retained branch still supplies neither a numerical order nor
   a distinguishing full-field torsion invariant.

The root checked all eleven reports before archival. The review is
limited to the displayed arguments and the explicitly inherited setup,
detector, and extractor contracts; it does not independently reprove
the external analytic inputs. Validation of hashes and links confirms
artifact integrity, not a new factoring algorithm.
