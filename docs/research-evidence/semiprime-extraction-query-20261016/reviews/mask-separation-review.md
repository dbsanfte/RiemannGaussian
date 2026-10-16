# Independent review B: actual mask/channel separation rank

2026-10-16. Verdict: PASS. The coefficientwise scope is essential and is retained throughout.

Reviewed `/tmp/semiprime-extraction-20261016/mask-separation-review.md`, SHA-256 `2077495ac4885bd7251e05b3a7828f096ff3e2879b13ee815fab8f09bbc42a22`. All FIVE frozen prerequisite hashes listed at its end were independently recomputed and match. No original report or repository file was changed; no build was run.

## Projection and actual rank

Cartier/Fourier projection of A(t,Y)E_B(t), with Y=t^B during the projection, gives

    z_j^s G_s(y_j) = E_B(z_j) A(z_j,y_j)/B.

Only the trivial dyadic phase survives because the mask vanishes at every other phase. Dividing by the supplied unit z_j^s proves the displayed formula. Polynomial or Laurent coefficients in Y can be evaluated at the unit y_j, so no hidden algorithmic inverse at arbitrary Y is granted. The splitting extension is proof-side, not an acquired representation.

On any selected k rows where A(z_j,y_j) is nonzero, the evaluation matrix is a nonzero diagonal times a rectangular Vandermonde at z_j^(-1), and has rank min(k,B) over that field. On k<=B rows with A values unit modulo N, its first k columns have exactly the displayed unit Vandermonde determinant. The inverse-node differences are units because z_i-z_j and both nodes are units. This gives a genuine composite-ring unit minor, not an invalid global-distinctness root count or an ambiguous rank assertion over a zero-divisor ring.

Any coefficientwise separable family factors this evaluation matrix through r columns. The unit minor precludes r<k over R by the universal Cauchy--Binet identity; the corresponding field rank gives r>=min(k,B) without the stronger common-unit premise. Input-dependent scalar constants do not change the factorization argument.

For A=F, the inherited actual unit-row theorem leaves Omega(m) distinct unit nodes after at-most-two-fold offset deduplication. B=Theta(m) therefore yields an actual Omega(m) constant-linear span of the N_s polynomials. Dividing all channels by their common nonzero polynomial H preserves constant-linear independence over each field, since multiplication by H is injective. This is a span theorem, not an operation or coefficient-acquisition lower bound.

## Carry-corrected scalar weights

The zero channel has weights w_0=e_0 and w_s=Y e_(B-s) for s>0. At y_j=z_j^B these evaluate to kappa_j z_j^s. Omitting the factor Y would be wrong; the report includes it. Thus initial-column minors of the actual weight vector have unit Vandermonde determinants, giving its precise coefficientwise separation bound min(B,J).

For a scalar combination sum_r beta_r(Y)N_r(Y), grouping the two cases r>=s and r<s gives exactly the stated carry-corrected weight formula. At y_j both cases become kappa_j z_j^s times b_j=sum_r beta_r(y_j)z_j^(-r). Hence S(y_j)=kappa_j F(z_j)b_j. Fieldwise support preservation forces b_j nonzero only where F(z_j) is nonzero in that field; it need not be a unit at a row that already collides there. At the Omega(m) rows unit in BOTH fields, b_j must be a unit modulo N, so the same unit-minor bound applies. The report correctly distinguishes this necessary condition from the stronger sufficient all-node unit condition.

## Exact excluded route

A paid C action does acquire the full polynomial sum_s alpha_s F_s(Y), since its output is precisely that polynomial's complete-block coefficient vector. If a contraction is required to be an identity of linear functionals in the F_s, then r such actions combined as sum_l p_l(Y)K_l(Y) must represent the canonical weight vector coefficientwise. The actual separation theorem excludes a polylogarithmic r for that contract, even with freely supplied high-degree p_l.

The actual q-binomial F_s are not independent formal inputs. Polynomial/q-recurrence syzygies can change the weight vector without changing the scalar output; this report explicitly leaves that escape open. It also leaves shared multi-action algorithms, nonseparable bilinear computations, direct gcd/norm/factor acquisition and compressed implicit channel operators open. No Omega(m) call count or Omega(m^2) running-time lower bound for all actual programs follows.

The result is therefore a substantive actual-source obstruction to exact separable mask compression, alongside an actual channel-span theorem. It does not close the acquisition problem or imply a general scalar lower bound.
