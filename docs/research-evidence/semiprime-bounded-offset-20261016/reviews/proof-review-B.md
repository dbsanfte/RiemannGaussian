# Independent final-byte review B: four recurrence reports and integration

2026-10-16. Verdict: PASS, no corrections requested. This independently reviews the four q-agent-authored reports below and the root-authored README/journal. I authored constant-recurrence-obstruction.md, so I do not count this as an independent review of that fifth proof.

## Exact reviewed bytes

- uniform-recurrence-barrier.md: 7000 bytes, SHA256 `22d22246cce49eb933e831a93651aa467bfdcf2f8a6c38f974b47dbecc9eda8a`.
- chirped-stream-degree.md: 3677 bytes, SHA256 `61d007c9cef02d35e3da5860c7c00f99ce577c19cea5ac62b894bac0e65f40f9`.
- general-q-recurrence.md: 5582 bytes, SHA256 `36070d66b167ac8b15fb2e05402e4a3a2c43b32dd0fc081df06e85dfa15b552f`.
- q-stream-obstruction.md: 4919 bytes, SHA256 `012c8ca2d71100b5edd40bbe247fde5dbb0942462e0efbfdc819786b5dc64f8d`.
- README.md: 4373 bytes, SHA256 `a40fcebac26a43853739b0569de2205f190656ef46bfac2e257a1ae2ade45489`.
- journal-entry.md: 4347 bytes, SHA256 `e216273c567212b622cfd94ca1c79b104423dfaec87f474ab0d5ae9d3496aad9`.
- source-pins.json: 2299 bytes, SHA256 `8bdcb404f3129f32586c6db2970d98b898bc2efc1d296c679b8e7cc5e0d01cd9`.

All seven durable prerequisite files were independently rehashed against source-pins.json; all match. For its three gzip entries, compressed bytes and decompressed bytes/hashes were both verified. This revalidates the primary PDF pin, not a fresh claim to have reviewed the entire Bostan--Yurkevich paper. The old short-exponent mechanism and journal G15 passage were inspected for attribution and scope; the main four proofs below are self-contained algebra/counts using their stated inherited source promises.

## 1. Paid uniform alias screen

The setup premise is the new beta with odd coprime local orders>16m², hence exact global order>256m⁴, together with certified q=beta^(m²) local orders>16m². This is a paid factor-or-interface result under its explicit numerical hypotheses, not a free substitution for the original base2.

The degree-2m monic polynomial with roots beta^t, 0<|t|<=m, is acquired from O(m) known-unit powers. Evaluating it at m q-points is ordinary monic multipoint evaluation; no point differences need inverses. Each gcd-one row implies every leaf is a unit. A saturated row can contain different P-only and Q-only zero leaves, so product saturation alone would be insufficient; the report correctly localizes through the product tree. Every putative globally zero leaf would give the nonzero annihilator ds−t with absolute value at most m³+m, smaller than the actual global order. Therefore localization must find a proper factor, and cannot terminate in an unresolved saturated leaf.

Product/remainder trees, O(m) row gcds, and one Horner-localization path with geometrically decreasing degrees all fit soft O(m) bit work at logN=Theta(logm). No m-by-2m residue array or list of all leaf inverses is charged as free output. On survival the semantic unit certificate excludes all signed mixed aliases; axis aliases are separately excluded by the certified g/q orders. Composite orders and possible gcd(m,order)>1 are handled correctly.

Clearing the finite ratios gives coefficient degree<=D+r. When r+D<=m, the frequency array has at most (r+1)(D+r+1)<=(m+1)² distinct bases. The available L−r+1 equations are at least this many for m>=3. Fieldwise Vandermonde independence then forces every coefficient polynomial to vanish. No prime-order/majority deletion premise is imported into this uniform factor-or-certified-branch conclusion.

## 2. Exact first-order g-stream degree

The coefficient identity from (1−t)F(qt)=(1−q^L t)F(t) has the stated sign and denominator. The chirp contributes exactly g^(−k), yielding numerator degree d and denominator X(1−g^d X^d) of degree d+1. The order hypotheses make every required finite-segment value and denominator nonzero.

Any proposed degree<=d description gives a cross-multiplied polynomial of degree<=2d+1 vanishing at L=2d+2 distinct g-nodes, hence an exact polynomial identity. The displayed numerator is coprime to the degree-(d+1) denominator: X is excluded by the nonzero constant, and the other common divisor would divide 1−q^(L+1), which is nonzero. Thus that denominator must divide V, contradicting its degree. This proves the minimum d+1, not merely the degree of a chosen formula. The argument is characteristic-safe. The geometric rescaling and integer-binomial Bluestein identity are also exact. The theorem applies both to the old prime-order source and the new certified g/q interface, as separately stated.

## 3. Original-family general q-recurrence count

The signed hyperbolic catalog |st|<=m has O(m logm) entries. Every m²s−t is nonzero: equality would imply |st|=m²s²>m. Its size O(M³) permits only O(1) prime divisors above cM^2.031. Each gives O(M^.969) possible factors through P=1+vR and O(M³) unrestricted partners. Summing ALL O(M) comparable moduli yields soft O(M^5.969) exceptions. This is precisely the inherited elementary short-exponent divisor-count mechanism, newly applied to this frequency catalog; no prime-distribution theorem or per-input-menu/global-menu substitution is introduced.

Under r(D+r)<=m, every mixed alias difference lies in that catalog, while axis cases are excluded by prime-order source properties. Clearing denominators has degree D+r, with no vanishing finite denominator or lost endpoint. The number of frequencies is at most 2m+2r<=4m and fits the finite segment eventually. The Vandermonde conclusion is valid with fully advised coefficients and zero individual coefficient polynomials. Positive r is explicit, avoiding an unconstrained order-zero degree loophole. This theorem stays on the ORIGINAL qualified prime-local-order family; it does not silently replace it by the arbitrary-odd-order beta output.

## 4. First-order q-stream inverse bound

Cross multiplication produces the two base families gq^u and q^v, with u,v<=r+1. Within-family distinctness follows from the order bound, and a cross equality is exactly d(v−u)=1 modulo R. The least-absolute-inverse condition excludes it. If r<d and r<rho−1, there are 2r+4<=L consecutive equations, so Vandermonde forces both multiplied polynomials to vanish, contradicting a valid denominator. Hence r>=min(d,rho−1).

The catalog m²s−1, |s|<=m, is nonzero; its count and large-prime divisor/cofactor bounds give the stated O(M^5.969) original-input loss. On survivors rho>m, implying the claimed r>=m. This smaller supporting result expressly retains prime-order source hypotheses and credits the old count. It is not an unconditional substitution for a uniform composite-order base or a statement about higher-order recurrences.

## Integration, novelty and remaining scope

The README and journal accurately separate the old original-family deletion theorem from the new paid uniform factor-or-alias-certificate theorem. They retain balanced distinct odd inputs, m=Theta(N^(1/6)), N<=m⁶ and P+Q<=3m³ when invoking the fixed-target paid setup. They distinguish local-order hypotheses, arbitrary advised recurrence coefficients, fieldwise conclusions and unchanged original controller coverage.

The G15 passage near journal28743 concerns U_n=product_(i<n)F(theta^i) for a fixed polynomial F, using leading-degree separation. It is a different sequence and not the present chirped coefficient theorem. The integration credits this precedent, the old static exponent count, and classical monic product/remainder trees. It neither claims the degree-sensitive q-holonomic upper bound is a lower bound nor calls the square-alias screen a new generic primitive.

The exact r+D<=m and order<=m thresholds are preserved. Order2m, larger nearlinear recurrence order, other bases, multivariate/sparse representations, selected convolution, implicit sharing and scalar norms remain open. Computing the smaller alias query is not computing the irregular m-by-m² collision query. The generic query clock remains soft O(m^(3/2)); no acquired soft O(m) whole-query algorithm, operation lower bound, automatic controller transfer, native edit or Lean theorem is claimed. The packet's preservation baseline is a separate packaging-integrity obligation, not checked by this mathematical/integration review. No frozen source or report was mutated and no build was run.
