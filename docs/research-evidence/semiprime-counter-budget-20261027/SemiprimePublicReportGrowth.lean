/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeReportPolynomialGrowth
import RiemannGaussian.SemiprimeScheduledScalarBudget

/-! # Fixed monomial envelopes for actual public controller resources
These algebraic growth witnesses concern the concrete report expressions.
Their eventual rate application and primitive execution model remain separate.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimePublicReportGrowth
open SemiprimeReportPolynomialGrowth

/-- The actual controller polynomial has fixed coefficient and exponent. -/
theorem controller_monomial : ∃ C k : ℕ, ∀ S,
    SemiprimePublicReportPolynomial.controllerEnvelope S≤C*(S+1)^k := by
  change Bound SemiprimePublicReportPolynomial.controllerEnvelope
  have hc : Bound SemiprimePublicReportPolynomial.countEnvelope := setup_native_monomial
  unfold SemiprimePublicReportPolynomial.controllerEnvelope
  apply mul_bound
  · exact add_bound identity_bound (constant_bound 1)
  · exact add_bound
      (add_bound
        (add_bound (add_bound hc identity_bound)
          (mul_bound (constant_bound 3) (pow_bound (add_bound identity_bound (constant_bound 1)) 2)))
        identity_bound)
      (constant_bound 19)

/-- The actual scheduled scalar envelope has fixed coefficient and exponent. -/
theorem scalar_monomial : ∃ C k : ℕ, ∀ n,
    SemiprimeScheduledScalarBudget.scalarEnvelope n≤C*(n+1)^k := by
  change Bound SemiprimeScheduledScalarBudget.scalarEnvelope
  unfold SemiprimeScheduledScalarBudget.scalarEnvelope
    SemiprimePublicBudgetDimensions.entryEnvelope SemiprimePublicBudgetDimensions.scopeEnvelope
    SemiprimePublicBudgetDimensions.decoderEnvelope
  boundArithmetic

end RiemannGaussian.SemiprimePublicReportGrowth
