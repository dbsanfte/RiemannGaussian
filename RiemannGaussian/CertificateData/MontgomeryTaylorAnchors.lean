/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertificateData.MontgomeryTaylorAnchors00
import RiemannGaussian.CertificateData.MontgomeryTaylorAnchors01
import RiemannGaussian.CertificateData.MontgomeryTaylorAnchors02
import RiemannGaussian.CertificateData.MontgomeryTaylorAnchors03
import RiemannGaussian.CertificateData.MontgomeryTaylorAnchors04
import RiemannGaussian.CertificateData.MontgomeryTaylorAnchors05
import RiemannGaussian.CertificateData.MontgomeryTaylorAnchors06
import RiemannGaussian.CertificateData.MontgomeryTaylorAnchors07

/-!
# The complete certified anchor catalogue

All stored objective and gradient enclosures have passed Lean's kernel.
This catalogue supports a future exhaustive box certificate; it does not
by itself establish the proposed zeta zero-count improvement.
-/

namespace RiemannGaussian.MontgomeryTaylorAnchorBounds.CertificateData

/-- The complete catalogue in short indexed blocks. -/
def blocks : List (List Anchor) :=
  Group00.blocks ++ Group01.blocks ++ Group02.blocks ++ Group03.blocks ++ Group04.blocks ++ Group05.blocks ++ Group06.blocks ++ Group07.blocks

/-- Every available anchor has a proved real value and gradient enclosure. -/
theorem blocks_valid : ∀ block ∈ blocks, ∀ a ∈ block, Valid a := by
  intro block hb
  simp only [blocks, List.mem_append, or_assoc] at hb
  rcases hb with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact Group00.blocks_valid block h0
  · exact Group01.blocks_valid block h1
  · exact Group02.blocks_valid block h2
  · exact Group03.blocks_valid block h3
  · exact Group04.blocks_valid block h4
  · exact Group05.blocks_valid block h5
  · exact Group06.blocks_valid block h6
  · exact Group07.blocks_valid block h7

/-- The optional lookup used by the exhaustive checker. -/
def lookup (i : ℕ) : Option Anchor := catalogueLookup blocks i

/-- A successful catalogue lookup returns a fully certified anchor. -/
theorem lookup_valid (i : ℕ) (a : Anchor) (h : lookup i = some a) : Valid a :=
  catalogueLookup_valid blocks blocks_valid h

end RiemannGaussian.MontgomeryTaylorAnchorBounds.CertificateData
