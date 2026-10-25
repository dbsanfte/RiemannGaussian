# Independent review: finite q-difference endpoint literature

24 October 2026. **PASS.** The requested citation-only page-range correction is verified in the final frozen source. No mathematical correction was required.

Source examined: /tmp/semiprime-casoratian-endpoint-20261024/literature.md SHA256 `49b298182ed180517cdd5582f4276b280939ea52619aeb4138e07eeccaa92ae8`.

Primary caches independently read and hashed:

- sources/abramov-1999.pdf SHA256 `af8f32f0a8325c86992a47f058efa8f2a2a73c91742fd2e64582aefbf666c0e0`: introduction, printed pp2–4, denominator discussion, Sections2–3 and Theorem2.
- sources/ardehali-rosengren-2026.pdf SHA256 `74d803e5140ee566c76ad4186f2a6ea4cd4c398c5fbfe02a6fb855fc541e15b8`: p2, equation(2), branch/convergence discussion and gamma-product interpretation.

## Executed native recurrence

The inverse-point convention is correct: Y_h=Vhat_h^-1 and P_L(Y)=prod_(i<L)(1-q^iY). Original zero labels and q shifts are retained. A(X)=prod_h(1-D^h E^(h^2)X) is acquired in soft r per class; no native mixed-base factor is replaced by q.

The exact finite identity A(X)Z(qX)=A(q^L X)Z(X) follows by endpoint cancellation in each finite factor, without divisions through hits. Since every factor's linear coefficient is a unit, Z has exact degree rL with unit leading coefficient even at repeated roots. Comparing degree terms over the stated characteristic-zero non-root-of-unity field gives n=rL.

Coefficient comparison gives exactly

    (q^n-1)z_n=sum_(1<=t<=min(r,n))
                 a_t*(q^(Lt)-q^(n-t))*z_(n-t), z0=1.

Computing s coefficients literally takes O(rs) arithmetic operations and the stated unit denominators for 1<=n<s. Full reconstruction costs O(r^2L) per class, O(JrL) overall, and the dense division-free alternative costs soft(rL) per class, soft(JL) overall. The native denominator guard ends at16H and need not cover rL; the source explicitly refuses to run unguarded inversion or import characteristic-zero normalized-solution uniqueness. Thus no actual composite-ring division has been smuggled in through the formal field solver.

The separate degree-r baby/giant evaluation cost soft(r+sqrt(rL)) per class, and total soft(J+J sqrt(L/r)), are correct. The joint degree-J algorithm restores soft(J+sqrt(JL)) and uses monic products/MPE, preserving zero-safe execution and the original restriction/consumer contract. The report does not mistake a coefficient germ or field degree bound for an acquired native scalar endpoint.

## Primary contracts

Abramov's actual source assumes a computable characteristic-zero field and q nonzero/not a root of unity. Its explicit q-suitable assumption requires an algorithm finding all nonnegative integers n for which a supplied polynomial vanishes at q^n. The source is a rational-solution/degree-and-denominator algorithm, not a nearlinear native scalar endpoint theorem. Theorem2 bounds degrees using the indicial equation, after which polynomial coefficients may be found by undetermined coefficients/linear algebra. The report correctly preserves both the field restriction and the power-root operation, while not claiming that every possible rational solver must implement that exact strategy. Native norm/coordinate pivot classification does not establish the absent field theorem or supply its geometric search.

The sole requested correction was bibliographic: the q-suitable definition is on printed/PDF p4, whereas the original sentence grouped it with assumptions on pp2–3. The author corrected this to introduction pp2–4; the final bytes above have been verified. This changes no algebra, cost or applicability conclusion.

Ardehali–Rosengren equation(2) is an analytic infinite product of dressed reciprocal gamma functions indexed by all integers. The source explicitly requires Re(beta)>0, excludes y in2pi*i*Z, and fixes branches. It proves absolute convergence, not a finite modular truncation rule. Forming the finite quotient replaces gamma arguments by integer shifts L; the gamma recurrence introduces L finite linear factors, while the analytic infinite-index cancellation and prefactors remain. No exact finite-ring circuit or certified modular tail deletion is provided. The report's conclusion is correctly scoped to this candidate, not a claim that analytic identities can never yield arithmetic algorithms.

No source or shared documents were edited by this reviewer; no numerical experiments or preservation validation were performed.
