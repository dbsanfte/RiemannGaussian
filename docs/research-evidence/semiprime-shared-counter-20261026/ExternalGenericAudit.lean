import OAI.Algorithms.SubexponentialSAT.GlobalPolynomial
import OAI.Algorithms.SubexponentialSAT.Separation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets

-- External baseline only: this audits reusable algebra, not the new counter's
-- complete implementation, complexity theorem, or published SAT endpoint.
#print axioms OAI.Algorithms.SubexponentialSAT.GlobalPolynomial.eval_zero_interpolatedGlobalPolynomial
#print axioms OAI.Algorithms.SubexponentialSAT.GlobalPolynomial.natDegree_compose_le
#print axioms OAI.Algorithms.SubexponentialSAT.Separation.weighted_separation_equiv
#print axioms OAI.Algorithms.SubexponentialSAT.Separation.coset_row_group_separation
#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.integer_kernel_of_rational_span
#print axioms OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.killsIntegerKernel_of_rational_span
