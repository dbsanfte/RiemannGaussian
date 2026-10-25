# Independent mathematical review: native small-root congruences

24 October 2026. Reviewer: root, independent of the source author.

PASS for final `native-lattice.md`, SHA256
`0967581b19be8e9b5a929a9c09d2aec27f9be9e1d5a9383682bf26976d271769`.
The earlier source incorrectly called g total degree three. This was a substantive theorem-selection error; the author corrected it before this review. No all-algorithm lattice lower bound is certified.

## Arithmetic and primitive heights

Expanding (j+kx)(q0+ky)-N and dividing by k gives the displayed primitive f. Its coefficient j is coprime to k, so the first content removal is exact. Its constant term is of size N/k on the prepared branch. The scaled mixed term and linear terms give the stated height Theta(N/k), for bounds chosen comparable to S/k and N/(Sk). Consequently the delta-one Coppersmith sufficient condition indeed needs k>N^(1/4) at exponent scale.

Substitution y=kI-a x-s0 gives coefficients k(j+kx), -ka, -kb and -k c_j. The exact divisibilities defining s0,c_j follow from the acquired tag congruences. At x=-j/k the positive quadratic a x²+b x+c_j equals N/k², so the linear I coefficient does not divide it; primitivity and irreducibility follow. The substituted g has degree two in x, degree one in I, and TOTAL DEGREE TWO. Its height and box product are respectively Theta((N+aS²)/k²) and Theta((N+aS²)/k³). Even the stronger total-degree-two certificate XY< const sqrt(W) fails by a factor of order at least sqrt(N)/k². The weaker separate-degree bound also fails. None of these inequalities rules out specially favorable lattice vectors.

The relation y=-a x-s0 mod k is exactly the reduction of the already known product equation modulo k² after dividing its first content. It supplies no second independently acquired prime residue. This is an exact redundancy statement about this equation, not a general information-theoretic bound.

## Unknown-divisor lattice

The first t basis degrees are 0 through t-1, with leading coefficients N^(t-i); the remaining s degrees are t through t+s-1, monic. Column scaling supplies X^(d(d-1)/2), hence the stated determinant. Every basis row vanishes modulo P^t at the desired root, including the N-powered rows since P divides N. Cauchy--Schwarz gives the displayed sqrt(d) norm certificate. A resulting nonzero univariate integer polynomial admits deterministic candidate isolation; checking gcds supplies the final certification.

The finite-dimensional exponent estimate is valid: completing the square in t gives

    [2 beta t d-t(t+1)]/[d(d-1)]
      <= (beta d-1/2)^2/[d(d-1)] < beta²

for d>=2 and beta in [1/3,1/2]. The omitted LLL and sqrt(d) penalties only tighten this necessary condition. The desired native coordinate has exponent beta-1/6, exceeding beta² uniformly on this interval. This excludes the displayed determinant certificate for the full boxes, not all short-vector behavior or another lattice design.

## Primary contract and scope checks

Independently inspected the cached Coppersmith first-page raster: it states the separate-degree delta weighted-height bound XY<D^(2/(3delta)). Independently read the Howgrave-Graham thesis text around Theorem 5.1.1: its total-degree delta bound is (XY)^delta<const D, confirming the corrected degree-two invocation. The thesis also supplies the small-norm integer-vanishing setting; the exact unknown-divisor specialization above is proved in the source rather than borrowed from a full-modulus statement.

The report does not use multivariate algebraic independence as an established fact. Its Jochemsz--May citation is a warning against assuming the extraction premise, not a positive lemma needed by this audit. Direct primary PDF retrieval during this review returned an error, so no independent new PDF-content verification for that citation is claimed.

All conclusions are theorem-application or certificate limits. No finite numerical campaign, source modification, Lean check, shared-file edit, new factoring rate, or completed one-sixth proof is claimed by this review.
