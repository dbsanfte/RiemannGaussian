# Independent review: acquired Schur boundary operator

26 October 2026. Read the complete root report, checked the elementary
bounds, finite determinant cancellation and inverse-action algorithm.
No tests, source edits or repository changes.

**PASS, with the stated coverage and normalization scope retained.**
The O(r^2)=soft k inverse action is genuinely initialized; it is not a
free dense inverse or an invocation of generic cubic elimination.

- Put x=sqrt(N/k)>16k^(3/2). From the actual integer definitions,
  D0<=2kx, V<3sqrt k and
  T<=x/(8k^2)+1+3sqrt k. These imply W<3x for the stated k>=6,
  and C>=x^2/2>W+V+1. Hence A=C-W-1>r=V. In particular all
  original positive-block and U-boundary exponents are positive;
  the only literal incidence in the original signed rectangle is
  b=h=0. This bound does not assume balanced factors.

- The unbalanced partition and principal specialization match every
  cross-block factor exactly. The cleared identity is D*J=diag(Z_i)U,
  not J=diag(Z_i)U when D may be a nonunit. Formal cancellation
  proves the specialized Laurent-polynomial determinant identity
  `det U=q^eta V_r(q^C) product_(t=1)^(r-1)(1-q^(s+t))^t`
  in every ring. The r=2 sign and monomial are correct.

- Its unit screen requires only C*d and s+t for 1<=d,t<r.
  Their labels are positive short integers, so every nonunit gate
  has the proper-gcd or nonzero beta-annihilator consumer and one
  terminating T_ext. Neither a full prefix through n-1 nor unit D
  is needed to acquire or invert U.

- Interpolation at x_i=q^(A+C(r-i)) is legal: their differences are
  monomial units times 1-q^(Cd), precisely the screened factors.
  Degree-<r interpolation and evaluation at q^t each cost O(r^2).
  Evaluation at q^t itself needs no inverse; the original short
  guard additionally certifies their differences if used.

- At q^t the left product of P_j contains a factor 1-q^0 exactly
  for j<r-t. For j=r-t its remaining factors are exactly
  `(product_(a=1)^t(1-q^a)) *
   (product_(a=s+t+1)^(s+r-1)(1-q^a))`.
  The first group is short-guarded; the second is a subset of the
  explicit s+1,...,s+r-1 gate. Thus each descending pivot is a
  certified unit. At t=0 one recovers c_r first, and at t=r-1 one
  recovers c_1 last. This verifies the triangular orientation.

- All P_j(q^t) can indeed be acquired in O(r) per t using prefix/
  suffix products of two O(r)-factor lists, retaining literal zeros
  and using no ratio through a zero. Back substitution totals O(r^2),
  and the full inverse matrix is never materialized.

- The report correctly distinguishes the paid U inverse action from
  the unacquired cleared matrix K=D*J. The identity
  K*U^(-1)=diag(Z_i) exposes the missing original row products;
  it does not acquire K. No Schur denominator inversion is licensed.

The A0 warning is essential and correctly included: its optional
soft sqrt W readout is not uniformly soft k, and Z alone has not
been promoted to an unconditional covered target. The boundary gate
may itself terminate with a valid factor, but its unit result supplies
no independent useful-collision coverage.

Separately corrected my companion cyclic-reciprocity Section 2:
2k-powering equivalence is conditional on a PAID order-coprimality
certificate, not assumed on this scalar branch. Without it there is
only automatic forward hit preservation; a powered overcover can
still use its own nonzero short beta labels, but does not have the
same original prefix bits. No correction to the root boundary
operator report is required.
