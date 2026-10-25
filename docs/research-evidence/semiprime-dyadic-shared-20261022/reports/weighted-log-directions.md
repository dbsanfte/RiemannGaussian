# All-output directions after the paid tangent norm

This continues the actual shared-contraction attempt. The shifted denominator and ONE fixed spatial numerator are now acquired near-linearly by `sheared-norm-constructor.md`, independently checked in `sparse-norm-constructor-review.md` and `tangent-transposition-review.md`. This report does not claim the weighted all-shift logarithm is acquired.

## Exact weighted-log target

Put u=b^-1 mod m and Q_k(z)=Norm_A(1−z R X^(uk)). The formal logarithm is well-defined through z^(m−1), since all 1,...,m−1 are units on retained inputs. Then

 sum_(a>=1) H_a z^a/a = −(1/m) sum_k B_k log Q_k(z).       (1)

The coefficient ring can remain Z/NZ; no real/analytic logarithm is used. Actual computation would use log derivatives and one formal integration, with all denominators checked/proved units.

For a primitive order-m spatial component, Q_(k+m/2)(z)=Q_k(−z), so pairing k,k+m/2 yields

 B_k log Q_k(z)+B_(k+d) log Q_k(−z)
 = (B_k+B_(k+d))/2 *log(Q_k(z)Q_k(−z))
   +(B_k−B_(k+d))/2 *log(Q_k(z)/Q_k(−z)), d=m/2.        (2)

The odd output prefix depends ONLY on the coefficient differences B_k−B_(k+d). Thus the initial all-output direction is genuinely reduced by half without evaluating each output. The spatial trace of this folded state is exactly the rational-kernel contraction (9) of `additive-contraction.md`.

## What transposition DOES pay

For ONE fixed shift s, linearized sparse Graeffe is a linear arithmetic circuit in the supplied spatial U. Its transpose is therefore paid in the same soft-linear bound. This acquires fixed-base power composition/projection contractions, including arbitrary monomial shifts of the rational base.

But k in (1) is a SUPPORT POSITION, not the coefficient of one linear perturbation U of a common F. Q_k is the norm of a different base polynomial g−z f X^(uk). Differentiating Norm(F+epsilon U) gives a sum of U evaluated at the roots divided by ONE fixed F. It does not give sum_k B_k log Norm(g−z f X^(uk)). Replacing the latter by log Norm(g−z f*sum_k B_k X^(uk)) introduces mixed products B_i B_j in every moment beyond the first and computes different quantities.

Thus the tangent algorithm's linearity cannot be transposed in the discrete exponent k without a new representation. A direct-product algebra with one orthogonal idempotent per k represents the expression exactly, but has rank m before its existing spatial rank is counted; it is not a near-linear scalar implementation. This is the cost of that embedding, not a general lower bound.

## Explicit affine-state update, and the point requiring shared arithmetic

For

 C=CT_X sum_k B_k X^(alpha*k) F(z X^(beta*k),X),

pairing k,k+d multiplies the second coefficient by (−1)^alpha and replaces the kernel argument by (−1)^beta times its first argument. If beta is odd and output parity sigma is selected, the folded coefficient is

 B'_k=B_k+(−1)^(alpha+sigma)B_(k+d),
 alpha'=alpha+beta*sigma, beta'=2beta,

with half output precision after reindexing. This is an exact shared update of coefficient lists; their total length over the two sigma branches stays equal to the parent length.

The spatial X↔−X fold has two cases. If alpha' is even, one can keep all k and replace alpha' by alpha'/2 and beta' by beta'/2 in the lower-rank cyclic variable. If alpha' is odd, splitting k=2l+epsilon selects different spatial parity numerators. Each branch carries a known prefactor and a kernel shift z→z Y^(beta'*epsilon/2); its new beta is beta' rather than beta'/2. This creates even beta states as well as odd beta states. In an even beta state, coefficient pairing does NOT select/reduce output parity automatically. Its integer output range and high bands remain.

The scalar B-list bookkeeping is small: each split is sums/differences or a partition of existing lists. However the kernels attached to these lists are NOT equal. The sparse norm/tangent constructor would pay them if the corresponding U directions, shifts, and precisions had a bounded TOTAL input/support measure. I did not establish that measure for all descendants. Counting only the scalar B-list lengths is insufficient because it does not count their attached spatial modulations and kernel powers; counting a full dense rectangle is also unjustified because the acquired sheared sparsity removes that penalty. The unresolved task is exactly the shared update of the attached affine numerator directions.

## Special B=W^N: identities retained in the attempted update

The input B can be acquired in soft O(m) by binary cyclic exponentiation. Its relative norm is another Nth power in the rational family; this supplies the multiplicative tower but not its additive coordinates. Its coefficient-list sums/differences in (2) are actual projections of that same acquired Nth power, rather than arbitrary or independently supplied arrays.

Neither the norm identity nor formal differentiation justifies a short ordinary recurrence for these projected coefficient lists. In characteristic N the unreduced derivative of W^N is zero, but differentiating its cyclic representative is invalid without the wrap contribution. The exact special-power doubling correction T_(2a−m*kappa)=T_a²/rho_(a/b)(D_2^N)*R^(−m*kappa) remains available; it does not turn all projected directions into one common U.

A further universal symmetry is present: every monomial-shift base U_k=R X^(uk) satisfies U_k*bar(U_k)=gamma. Therefore its full characteristic norm is reciprocal under the common gamma involution, and its power traces can be expressed through Dickson polynomials in U_k+gamma/U_k. This halves conjugate information but still leaves the k-dependent trace coordinate. It does not identify different k kernels or supply the moving numerator.

## Native carried row and long seed index do not fit for free

The actual row is Z_j=W^ell_j (rho_j W)^a_j rho_(j^-1)(W^N), and the seed is W^(m²i). The current H_a contraction is one specially aligned power piece. The integer ell_j is not merely an affine residue exponent in a_j; it includes the exact centered-row carry. Absorbing W^ell_j into the kernel requires a row-dependent POWER, not just the coefficient-index modulation X^(alpha k). Likewise varying i introduces a family of bases/powers indexed through the full covered long interval; it is not a fixed scalar z coefficient already contained in (1).

For one actual difference, its relative norm equals Norm(Z_j)−W^(m²i)*Tr_relative(Z_j)+W^(2m²i) only when the seed is fixed by that relative involution; in general use the full two-coordinate product and retain both seed conjugates. The original bar-involution scalar norm is a separate pairing. No component norm hit may be promoted to an original same-leaf scalar annihilator without that pairing. Consequently even a solved all-a H_a primitive would need a proved integration step for ell_j, the geometric seed interval, and localization; those costs are not inferred from its unit moments.

## Result of this pass

Actual acquired ingredients are the deterministic sparse shifted norm, fixed spatial numerator propagation, and its transpose. Equations (1)–(2) and the affine update above give the exact all-output recursion inputs. I did not close the total attached-numerator support/precision ledger, nor integrate native ell/seed factors. The precise next simplification would express the folded Nth-power directions as shared tangent inputs of total soft-O(m) size while preserving their affine kernel shifts. No assertion that this is impossible is made, and no factoring-rate claim is added.
