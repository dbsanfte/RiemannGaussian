# Actual mask separation rank: exact theorem and limits

2026-10-16. Independent derivation/review of the proposed rank obstruction. PASS with the essential coefficientwise scope below. No frozen report or repository file was changed. This is not an arithmetic-operation lower bound or a proof against all polylogarithmically many block actions on the actual q-binomial input.

## Setup and projection identity

Use the actual deduplicated unit nodes z_j. In either hidden field they lie in one odd-order subgroup; dyadic B>=2 is coprime to the characteristic and to that group order. Distinct nodes and their B-th powers y_j=z_j^B remain distinct. Their pairwise differences are units modulo N, using the actual offset-span/local-order promise.

Let D(t)=prod_j(1-t/z_j), D_B(Y)=prod_j(1-Y/z_j^B), and E_B(t)=D_B(t^B)/D(t). Put kappa_j=E_B(z_j)/B, a unit modulo N. The mask is zero at every nontrivial dyadic phase omega^a z_j, while E_B(z_j) is a unit; these are the frozen actual mask facts.

Allow any A(t,Y), polynomial in t with polynomial or Laurent-polynomial coefficients in Y. Reduce

 A(t,Y)E_B(t) mod(t^B-Y)=sum_(s=0)^(B-1)t^s G_s(Y).

At Y=y_j, apply dyadic Fourier projection in an algebraic closure of either hidden field. Only the phase t=z_j survives the mask, giving the exact formula

 G_s(y_j)=kappa_j A(z_j,y_j) z_j^(-s).             (1)

The extension is proof-side only. Evaluating polynomial/Laurent identities at the unit y_j is legitimate modulo N as well. No arbitrary Y is inverted by an algorithm here.

## Actual field rank and composite unit minor

Suppose A(z_j,y_j) is nonzero at k distinct supplied nodes in one hidden field. The evaluation matrix (G_s(y_j))_(j,s) is a row-scaled Vandermonde on z_j^(-1), so its rank is min(k,B).

If A(z_j,y_j) is a UNIT modulo N at k nodes and k<=B, the minor using columns s=0,...,k-1 has determinant

 [prod_j kappa_j A(z_j,y_j)]
   *prod_(i<j)(z_j^(-1)-z_i^(-1)),

which is a unit modulo N. Thus the conclusion has a direct composite-ring certificate, not only an ambiguous rank notion over a ring with zero divisors.

Consequently a coefficientwise separable representation

 G_s(Y)=sum_(ell=1)^r alpha_(ell,s) p_ell(Y),       (2)

where alpha_(ell,s) are scalar constants and p_ell are arbitrary polynomial/Laurent functions regular at the sampled nodes, requires r>=min(k,B) over the field. Under the unit-minor premise it requires r>=k over Z/N as well: evaluation factors the unit-minor matrix through r columns, and Cauchy--Binet makes its determinant zero if r<k. Scalars may depend on all actual input data; their being input-dependent constants does not change this rank argument.

In particular A=F=P_L gives G_s=N_s. The retained m-o(m) unit rows, even after at-most-two-fold public offset deduplication, supply k=Omega(m) unit nodes. For B=Theta(m), the ACTUAL channel polynomials have constant-linear span dimension Omega(m). Their small common factor does not make their polynomial-vector family lie in a polylogarithmic-dimensional constant span. Factoring out H does not reduce that span dimension over a field, because multiplication by a nonzero H is injective. This does not prohibit acquiring H directly.

## The exact N_0 contraction and its carry

Write F(t)=sum_(s<B)t^s F_s(t^B), E_B(t)=sum_(s<B)t^s e_s(t^B). The zero Cartier channel is

 N_0(Y)=F_0(Y)e_0(Y)
        +Y sum_(s=1)^(B-1)F_s(Y)e_(B-s)(Y).

Thus its coefficientwise weights on the F_s are

 w_0=e_0,  w_s=Y e_(B-s) for s>0.

The carry factor Y is essential. Formula (1) for A=1 gives e_s(y_j)=kappa_j z_j^(-s), hence

 w_s(y_j)=kappa_j z_j^s, 0<=s<B.                  (3)

Every k-by-k initial-column evaluation minor at k<=B actual distinct nodes is a unit Vandermonde minor. Therefore the exact canonical weight vector w has separable rank at least min(B,J). No generic-degree or transcendental-source argument is used.

For a more general scalar combination S(Y)=sum_(r<B) beta_r(Y)N_r(Y), polynomial or Laurent beta are allowed at the unit nodes. Its canonical weights on F_s are

 w_s(Y)=sum_(r>=s)beta_r(Y)e_(r-s)(Y)
       +Y sum_(r<s)beta_r(Y)e_(B+r-s)(Y).

Evaluating the carry-corrected formula gives

 w_s(y_j)=kappa_j z_j^s b_j,
 b_j=sum_(r<B)beta_r(y_j)z_j^(-r),
 S(y_j)=kappa_j F(z_j)b_j.                       (4)

If this scalar combination preserves the fieldwise zero/nonzero status of F on all rows, then at each UNIT original row b_j must be nonzero in each field, hence a unit modulo N. Nothing is required of b_j at a row already zero in the relevant field. Requiring b_j to be a unit at ALL nodes is a convenient sufficient condition for complete support preservation, but is not necessary on collision rows. On the Omega(m) actual unit rows, the same rank/unit-minor bound applies to these canonical weights.

## Precisely what operator implementation is excluded

The paid block operator computes the complete polynomial K_ell(Y)=sum_s alpha_(ell,s)F_s(Y) for any scalar coefficient vector alpha_ell. A proposed COEFFICIENTWISE implementation of the contraction as

 sum_(ell=1)^r p_ell(Y) K_ell(Y)

must represent its formal linear-functional weight vector as sum_ell p_ell(Y)alpha_ell. Equations (3)--(4) rule out r=polylog(m) for these exact canonical masks when it retains the actual unit rows. This holds even if polynomial p_ell have large degree or are supplied for free: it is a separation-rank statement, not a degree/cost inference.

The word coefficientwise is indispensable. The F_s are fixed, highly constrained q-binomial polynomials, not independent formal inputs. There may be nonzero vectors v_s(Y) with sum_s v_s(Y)F_s(Y)=0. A different weight vector could give the same actual output by such q-recurrence/polynomial syzygies without being coefficientwise equal to w. The present rank theorem does NOT exclude that route, paid sharing among many actions, other structured bilinear algorithms, or direct common-gcd/norm/factor computations. It does NOT prove that any actual program needs Omega(m) calls or Omega(m^2) work. A formal-input coefficient identity is the extra contract needed for that call-count interpretation.

Thus the proposed obstruction is sound for exact separable mask compression and for low constant-span compression of all channels, and remains narrow enough to preserve the actual positive acquisition problem.

## Exact frozen prerequisites checked

- Block-query bundle manifest: SHA256 562b3b54859243e9b0cddf2f1878d6b9f563b5189c1f0642f29967dc61214b8a.
- reports/block-transform.md: SHA256 825aaaa7d10637eddcf38a7b8e8f2241a70984c4b94c506372e922b845b2fe70.
- reports/decimation.md: SHA256 65a5c827a64b5c035d3d0a7bed445c6970910f9f92749309878d1e1520e5c4fd.
- reports/common-channel-collision-locator.md: SHA256 6dfc707ebe2896d7eb2ff78b6324d4df78b3db7ca6bc6a3e67e7b4adf4c737ff.
- Inherited actual-row-density proof: SHA256 723472c4e1dba27e23f490fbab953d240c032d65ffc7e79e87e98962f35939e9.

The projection and rank arguments here are self-contained. No new external primary theorem, build, numerical test or implementation is claimed.
