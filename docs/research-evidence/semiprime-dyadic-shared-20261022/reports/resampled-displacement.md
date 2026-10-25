# Resampled rational-power displacement: explicit recurrence and shared-state target

Let m=2^k, u=N^-1 mod m, R=t(1+gamma X)/(X(X+gamma)), and C[a,l]=CT_X[X^l R^a] in the original cyclic algebra. For odd a define M[a,k]=C[a,u*a*k], so the requested vector is H=M B. All l and k indices below are modulo m, while a is the actual integer power. The derivation keeps cyclic aliases.

## A real constant-width recurrence before resampling

The rational identity X(X+gamma)R=t(1+gamma X) gives

 C[a+1,l+2]+gamma*C[a+1,l+1]
 =t*C[a,l]+t*gamma*C[a,l+1].

To stay on odd rows, square this identity:

 C[a+2,l+4]+2gamma*C[a+2,l+3]+gamma^2*C[a+2,l+2]
 =t^2*(C[a,l]+2gamma*C[a,l+1]+gamma^2*C[a,l+2]).       (1)

This is an exact width-five relation, with all denominators already accounted for in the prepared unit R. It applies to arbitrary supplied weights after summing against them. No derivative of a cyclic residue is used.

## The exact resampled operators

For an odd a put v_a=(u*a)^-1 modulo m and d_a=(a+2)*a^-1 modulo m. Choosing l=u*(a+2)*k in (1) gives

 M[a+2,k+4v_(a+2)] + 2gamma*M[a+2,k+3v_(a+2)]
   +gamma^2*M[a+2,k+2v_(a+2)]
 =t^2*(M[a,d_a*k]+2gamma*M[a,d_a*k+v_a]
                         +gamma^2*M[a,d_a*k+2v_a]).     (2)

Thus the recurrence survives the resampling, but its shifts and dilation depend on the row a. These are explicit affine permutations of the coefficient index, so they can each be applied to one length-m vector in O(m). The recurrence is not an ordinary constant-shift Toeplitz displacement. Calling it low displacement rank without specifying these row-dependent operators would omit the main operation.

After contraction with B, each term on the left is the same row functional applied to a translated B, and each term on the right is the preceding row functional applied to a dilated-and-translated B. Explicitly, for a row vector f(k),

 sum_k B_k f(k+c)=sum_j B_(j-c) f(j),
 sum_k B_k f(d*k+c)=sum_j B_(d^-1*(j-c)) f(j).

Hence (2) supplies an exact recurrence for H only together with these transformed weight directions. It is a candidate skew-affine state, not a closed scalar recurrence for the original H.

## A concrete shared-state candidate

Suppose an acquired B belongs to a publicly supplied subspace V of dimension r, invariant under ALL translations and odd dilations used in (2), and the relevant affine operators on V are supplied at total soft O(m*r) cost. Then one may track the r weighted row projections together; (2) is a width-five coupled recurrence in that state. To turn this into an actual fast solver one must still specify its row startup/boundary data and solve the cyclic left-side shift polynomial with its unit/factor guards. The scalar rational denominator is unit in the original algebra, but its resampled actions and the state boundary conditions must not be presumed invertible without that argument.

For example a single additive Fourier character is invariant under translations but odd dilations permute its frequency; a full dilation orbit may have size comparable to m. A multiplicative-character direction is invariant under dilations but translations mix such directions. Thus neither one transform basis alone proves a small r. These are exact action statements, not a lower bound against another compressed representation.

The special acquired B=W^N has a short exponentiation circuit, but I have not proved a polylogarithmic-dimensional invariant space for its coefficient vector under these affine actions. The naive orbit under translations already permits up to m independent directions. This does not rule out a faster contraction exploiting its particular source; it means the stated short circuit is not yet the required state invariant.

## Binomial diagnostic

For the diagnostic R=1+X, the cyclic coefficient matrix is C[a,l]=binom(a,n) where n is the canonical residue -l modulo m when 0<=a<m (and the value is zero if n>a). Thus M multiplies B by a binomial kernel followed by the row-dependent multiplicative resampling n=-u*a*k modulo m. The ordinary Pascal transform is fast before this resampling. Pascal recurrence couples rows by n->n-1; after resampling it produces precisely affine permutations of k with row-dependent inverse a and dilation (a+1)/a, where defined. Restricting to odd rows uses the squared Pascal recurrence and the same always-invertible (a+2)/a as (2).

Consequently this diagnostic yields the same concrete computational task: apply a Pascal/rational-power transform with a different input permutation for each row. Composing one ordinary fast Pascal transform with one FFT does not implement it. A successful butterfly factorization would need an explicit recursive sharing rule for those affine input directions, with total coefficient size and cost bounded across the dyadic levels. I did not derive such a rule.

## Current constructive endpoint

Equation (2) is a constant-width skew-affine displacement identity valid for the actual rational R, including cyclic wrap. It provides a precise possible algorithm interface: a shared solver for its affine weight directions with supplied original B and O(m) startup data. The known fixed-weight tangent constructor supplies one weight direction's all-row projection; the new identity explains exactly how varying directions enter and what a shared recurrence would have to combine.

I did not obtain a near-linear all-family multiplication or a closed butterfly state. No numerical rank campaign, generic impossibility claim, or factorization-rate theorem is asserted. The original native ell_j and long seed index remain separate source obligations even if this power-piece transform is solved.
