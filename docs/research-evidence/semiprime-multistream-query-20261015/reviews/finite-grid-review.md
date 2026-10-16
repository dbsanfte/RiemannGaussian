# Independent review: finite-grid defects, residues and selected jets

2026-10-15. Verdict: PASS on the final frozen bytes below. The interpolation-existence wording clarification was incorporated; no substantive algebraic correction was found. No repository edits or new query algorithm are asserted.

## Base reviewed artifact and sources

Full base report finite_grid/report.md SHA256 0adbee78fe8ff2d8a2edbd1c776bc16d6b64095b63f7348f80755959d1f51f9f, 9,324 bytes. A final pin after the requested wording clarification will be appended, preserving this base history.

Independently validated the report and all FOUR manifest source entries by both SHA256 and byte count. All passed, including the selected-coefficient primitive, actual row-density theorem, density-source pin table and final rational trace report. No external characteristic-zero theorem is needed for the new identities.

## Finite-value compatibility

The recurrence makes f_k b_k+f_(k+1)a_(k+1)=0. All required pivots are units. The first L triangular equations uniquely determine p_0,...,p_(L-1), with the displayed partial-sum formula. The final residual is exactly S/f_L; its sign is correct. The map from E-values to this defect is surjective because f_L is a unit, so the cokernel is precisely one free R coordinate.

The intended interpolation claim is an EXISTENCE/forced-values statement: the interpolant of the uniquely solved first-L values satisfies the final equation iff S=0. A completely arbitrary chosen polynomial need not satisfy the first equations merely because S=0. That wording precision was sent to the root; the next paragraph's actual-node interpolation already supports the intended result.

Unit point differences and monic interpolation are legitimate on the actual source. In fact the generic parameter-unit hypotheses already imply 1-gamma^r is a unit for r<=L, since 1-q^r=(1-gamma^r)(1+...+gamma^((d-1)r)). Explicit interpolation still has L entries; the report does not claim an arithmetic lower bound for implicit representations.

## Moving-grid identity and residue signs

In (A), the recurrence for F_k(alpha) cancels all interior terms. The first surviving term is (1-alpha^d)p(alpha/gamma), and the last is +u q^L(alpha^d-1)F_L(alpha)p(alpha gamma^L). Both signs and powers are correct. All denominator series have unit constant term; no division by F_k is required.

At x=gamma^-1 the substitution x=alpha/gamma gives principal term gamma*Res/(alpha-1). Multiplication by 1-alpha^d contributes -d, so the first residue term is -d gamma Res. At x=gamma^L the principal term is gamma^(-L)Res/(alpha-1); the other boundary coefficient contributes +d u q^L f_L, giving exactly +d u gamma^((d-1)L)f_L Res. Thus equation (B) is correctly scaled.

Regularity of T(p) at the sampled points licenses the left-side limit even when interior poles of p cancel in the operator. The report confines (B) to at-most-simple boundary poles and explicitly requires higher jets/finite-part accounting for more complicated poles. No pole contribution is silently dropped.

Boundary poles are a GENUINE escape from the finite-VALUE matrix, not disproved by the earlier rational-identity theorem. On the actual source, for example, p_0(x)=r/(x-gamma^-1) has a canceled boundary pole and gives weighted query -d gamma r. Choosing r=-S/(d gamma) leaves a compatible residual E-T(p_0) on the grid, which can be supplied by a polynomial interpolant. This proves existence of such finite-grid objects for arbitrary prescribed grid data; it also exposes that this direct construction already uses S. A faster way to acquire the residue or the interpolant is not ruled out. Equality only on this grid is not exact equality T(p)=E in K(x), so no contradiction with the previous trace criterion occurs.

## Top deformation

The first L pivots are units in R[[epsilon]], while the final pivot is -u q^L epsilon, a unit times epsilon in R((epsilon)). Therefore the triangular solution has the stated regular first entries and at most a simple final pole. Interior cancellation gives sum f_k(epsilon)E_k=-u q^L epsilon f_L(epsilon)p_L(epsilon). Taking the leading coefficient gives [epsilon^-1]p_L=-S/(u q^L f_L), with the correct negative sign.

The pole coefficient is nonzero in each hidden field for the actual formal independent weights because S has nonzero unit-row coefficients. Its identification is a conservation/payload statement. The report does not infer that a finite part can never encode useful related information, or that another regularization cannot compute the coefficient cheaply.

## Selected jets and full cost

The shared selected-prefix algorithm remains valid over the truncated ring R[epsilon]/epsilon^(h+1). Block construction and monic multipoint remainders do not need coefficient-field or node-difference inverses. Repeated indices/points are allowed. Only the selected V_k are inverted, and unit constant term is precisely the truncated-ring unit condition. A batch inverse needs one base-ring extended gcd plus truncated-series inversion; proper nonunit gcd and gcd=N are correctly distinguished.

Both F_k(1+epsilon) and the top-deformed f_k(epsilon) fit the stated four-parameter linear-factor product form. The parameter construction includes (1+epsilon)^d at O(log(d+1)) truncated multiplications. Multiplying by the coefficient-ring cost gives the claimed soft O((h+1)(sqrt L+nu)log N) bit cost, plus supplied-parameter construction and the specified powering overhead. Sequential refinement and ordinary polynomial encoding give the stated soft residue storage. There is no uncharged length-L moment list or a separate sqrt L computation for every selected index.

For polylogarithmic h and nu=O(m), the selected-jet primitive is indeed softly linear in m. It does not acquire the weighted residue coefficients, locate unknown poles/indices, or construct a complete endpoint formula. The final defect, boundary combination and deformation Laurent coefficient all equal the missing S up to known units; identifying them does not itself evaluate them.

## Scope conclusion

The report properly leaves finite-grid interpolation, regularization, several streams, weighted combinations and direct norm methods open. It closes only the proposals that ignore the compatibility defect or discard an unpaid singular contribution. Neither a general scalar lower bound nor a fast actual query follows. No further mathematical correction requested beyond the existence wording clarification.

## Final frozen bytes after the wording clarification

Re-read the corrected existence statement and revalidated all final manifest hashes and byte counts. Final finite_grid/report.md SHA256 b9362413654b889c5a74d947f7c216ad6194ca57fad463cac14d09e5ded4a84b, 9,446 bytes. Final manifest SHA256 070448c898f080e879a3b783901417357810ac703ba40841074d3ecdc190b510. PASS applies to these final bytes; the original base pin above remains historical provenance. No outstanding correction requested.
