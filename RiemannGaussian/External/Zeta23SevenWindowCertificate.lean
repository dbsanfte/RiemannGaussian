/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.External.Zeta23SevenWindowTarget
import RiemannGaussian.MontgomeryTaylorBoxCertificate

/-!
# From a checked finite box certificate to literal zeta zero counts

The numerical input is now an executable certificate with continuous
soundness. A proved range table, proved anchor catalogue and accepted box
cover would imply the exact 67.31 percent endpoint. The full accepted cover
is still outstanding; this implication is not an achieved zero certificate.
-/

namespace RiemannGaussian.Zeta23InverseSampling
noncomputable section

/-- The complete checker-to-count implication: no unspecified analytic
floor remains once the finite certificate data have all passed their checks. -/
theorem simpleCritical_6731_of_checked_box_certificate
    {table : MontgomeryTaylorRangeTable.Table} {l r : ℚ}
    (htable : MontgomeryTaylorRangeTable.Valid table l r)
    (anchors : ℕ → Option MontgomeryTaylorAnchorBounds.Anchor)
    (hanchors : ∀ i a, anchors i = some a → MontgomeryTaylorAnchorBounds.Valid a)
    (tree : CertifiedBoxCover.Tree (Fin 6) MontgomeryTaylorBoxCertificate.Leaf)
    (hcheck : CertifiedBoxCover.check
      (MontgomeryTaylorBoxCertificate.leafCheck table l r anchors) tree
      MontgomeryTaylorBoxCertificate.rootBox = true) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6731 : ℝ) / 10000 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) :=
  simpleCritical_6731_of_compact_model_floor
    (MontgomeryTaylorBoxCertificate.compact_floor_of_check htable anchors hanchors tree hcheck)

end
end RiemannGaussian.Zeta23InverseSampling
