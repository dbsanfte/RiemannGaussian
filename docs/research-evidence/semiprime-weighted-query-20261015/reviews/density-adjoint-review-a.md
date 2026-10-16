# Independent final review: actual full-row density and finite adjoint sectors

2026-10-15. Verdict: **PASS**. Reviewed the complete exact report `/tmp/semiprime-weighted-query-20261015/source/actual-row-density-adjoint-obstruction.md` (8,621 bytes), SHA-256 `723472c4e1dba27e23f490fbab953d240c032d65ffc7e79e87e98962f35939e9`. Source-pin file SHA-256 `566dca1bf09f8fddf130caaeb8639658995d02552fc185898a976ac4fcfcd46c`; all ten source hashes independently recomputed and MATCH. No report or repository file edited.

## New count

The local multiplier budget is uniform across the entire box, all tags and all i<4m²: Q varies by m², delta by 4m² and m²i by O(m⁴), so k lies in a common interval of O(m⁴/R_P+1)=O(M^1.969) integers. R_P is fixed with P, so no uncharged order/cofactor multiplicity occurs.

For fixed k the low-digit equation a_j(j²-2Pj+P)=PkR_P is correct. At a nonexceptional false tag it fixes a_j, hence Q modulo m. The two hit indices may differ; subtraction gives Delta Q+m Delta b=m²Delta i, so the index term disappears modulo m². Combined with the exact full-lift congruence this gives the unit-coefficient uniqueness (1-P I_j)Delta Q=0 modulo m². The half-open box therefore contains at most one Q per false j,a_j,k. The at-most-two exceptional quadratic roots are false because P(1-P) is a unit modulo m, and granting all slopes costs O(m). The own tag fixes one slope and grants O(m) Q in one residue class, without falsely applying the false-tag inverse. Thus O(m) incidences per k is correct.

Summing O(M³) possible P, O(M^2.969) incidences per box and the O(K_*M) box telescope gives O(K_*M^6.969). There is no additional index, tag, cofactor or second menu factor. Counted hits may overcount row incidences, which only strengthens the upper bound; the stated R>4m² also guarantees a unique i per local row if needed.

Markov deletion at M^.997 hits in any candidate/field costs O(K_*M^5.972)=O(M^5.992). On survivors each field has fewer than that threshold at every candidate, so the union of bad rows across the two fields is below 2M^.997=o(m). Thus m-o(m) COMPLETE original row products are units modulo squarefree N, simultaneously for every prefix length up to 4m². Counting the maximum interval legitimately provides all smaller lengths without another union factor. This remains compatible with existing full-query coverage because at least one exceptional hit can remain. All quantities are input/incidence counts, not runtime.

The cited older M^6.969 journal arguments count centered/pure q=1 TARGET-TARGET pair collisions and then distinct/simple target support. I read those specific preceding passages (around the original 28984 and 29172 locations): they do not already give this full first-current target-versus-geometric-prefix row-hit event. No exhaustive historical novelty claim is inferred.

## Finite-ring functional

The q-binomial coefficient equation is division-free and the finite extension by zero is valid for all integer indices: k=-1 is killed by 1-q^0, k=L by q^L-q^L, and the remaining exterior positions have zero supported values. Multiplication by u^k gives equation (6) exactly. No c_k, q-factorial denominator or collision factor is inverted.

For the stated adjoint, finite reindexing gives coefficient [(1-q^(k+1))f_(k+1)-u(q^L-q^k)f_k] on p(gamma^k), exactly zero by (6). The k=-1 and k=L terms are essential and are correctly accounted for. Gamma is a unit, so all Laurent evaluations are defined. Consequently Lambda annihilates the whole finite-Laurent adjoint image over Z/N, including zero divisors.

The identity u gamma^(3d-delta_j)=gamma^(-N-delta_j) is exact, so Lambda(x^e_j)=P_L(z_j). Any nonzero row value, in particular a unit value, certifies a nonzero monomial cokernel class. This is a direct actual-ring argument and does not transplant symbolic nonsummability from characteristic zero.

## Sectors and formal weights

Equation (8) is correct and preserves the exponent class modulo d. Decomposing a finite Laurent polynomial into these classes therefore decomposes the operator image and cokernel as direct sums, even though the coefficient gamma has finite numerical order. The formal variable x is not identified with gamma. The source equation c j²+2Nj-N=0 is nonzero over F_m and gives at most two tags per low digit, hence per d-sector. The unit rows thus occupy Omega(m) sectors. Independent formal weights cannot cancel their nonzero coefficient classes; extending this R-linear operator coefficientwise to the polynomial weight ring is valid.

Optional strengthening, not needed for the report: each unit-valued sector actually contains a free R direct summand. The descended functional has Lambda([x^e])=a unit, so r->r a^(-1)[x^e] is a section onto R. This is only an existence statement: neither Lambda nor the row value/inverse has been acquired cheaply.

## Scope

The endpoint-only FINITE-LAURENT certificate route is excluded, but Omega(m) surviving sectors still fit a softly linear state budget. The report correctly does not infer a computational lower bound, failure of rational singular certificates or other operators, or absence of a new joint implicit evaluator. Source prime-order/menu supply and all frozen observation losses are inherited and independently pinned; no new prime-distribution input or Lean result is claimed.

No blocking algebraic, counting, boundary, quantifier or cost-scope issue found.
