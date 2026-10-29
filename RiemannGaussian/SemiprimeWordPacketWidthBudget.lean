/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWordPacketWidth
import RiemannGaussian.SemiprimeNativeInputBits
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Fixed-polynomial growth of the actual packet width frontend
Traversal cardinalities may occur polynomially in widths. No full truth table,
2^Y width, caller clock premise or primitive-machine conclusion is introduced.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeWordPacketWidthBudget
open SemiprimeWordPacketWidth SemiprimeNativeGroupBitsHeight SemiprimeNativeGroupBits
open SemiprimeReportPolynomialGrowth

/-- Original factor exponent grows monotonically in original scalar dimensions. -/
theorem factorExponent_mono {b R s b' R' s' : ℕ}
    (hb : b ≤ b') (hR : R ≤ R') (hs : s ≤ s') : factorExponent b R s ≤ factorExponent b' R' s' := by
  unfold factorExponent SemiprimeNativeLocalBits.portExponent
  gcongr

/-- Actual common group-height exponent grows monotonically in original dimensions. -/
theorem exponent_mono {b R F s b' R' F' s' : ℕ}
    (hb : b ≤ b') (hR : R ≤ R') (hF : F ≤ F') (hs : s ≤ s') :
    exponent b R F s ≤ exponent b' R' F' s' := by
  unfold exponent factorExponent SemiprimeNativeLocalBits.portExponent
  gcongr

/-- Actual physical group width is monotone in the same dimensions. -/
theorem groupWidth_mono {b R F s b' R' F' s' : ℕ}
    (hb : b ≤ b') (hR : R ≤ R') (hF : F ≤ F') (hs : s ≤ s') :
    groupWidth b R F s ≤ groupWidth b' R' F' s' := by
  unfold groupWidth factorExponent SemiprimeNativeLocalBits.publicWidth
    SemiprimeNativeLocalBits.portExponent SemiprimeCorrectedPortBits.portWidth SemiprimeLocalBitsBounds.bufferWidth
  gcongr

/-- Actual runtime packet widths are monotone; the common resources are explicit. -/
theorem packetWidth_mono {b R n F s J r headCap Y Cq b' R' n' F' s' J' r' headCap' Y' Cq' : ℕ}
    (hb : b ≤ b') (hR : R ≤ R') (hn : n ≤ n') (hF : F ≤ F') (hs : s ≤ s')
    (hJ : J ≤ J') (hr : r ≤ r') (hh : headCap ≤ headCap') (hY : Y ≤ Y') (hCq : Cq ≤ Cq') :
    packetWidth b R n F s J r headCap Y Cq ≤ packetWidth b' R' n' F' s' J' r' headCap' Y' Cq' := by
  unfold packetWidth productExponent exponent groupWidth factorExponent
    SemiprimeNativeLocalBits.publicWidth SemiprimeNativeLocalBits.portExponent
    SemiprimeCorrectedPortBits.portWidth SemiprimeLocalBitsBounds.bufferWidth
  gcongr

/-- Diagonal fixed polynomial in a shared bound on all actual runtime resources. -/
def envelope (S : ℕ) : ℕ := packetWidth S S S S S S S S S S

/-- No resource hidden in the width escapes the shared bound. -/
theorem packetWidth_le_envelope (b R n F s J r headCap Y Cq S : ℕ)
    (hb : b ≤ S) (hR : R ≤ S) (hn : n ≤ S) (hF : F ≤ S) (hs : s ≤ S)
    (hJ : J ≤ S) (hr : r ≤ S) (hh : headCap ≤ S) (hY : Y ≤ S) (hCq : Cq ≤ S) :
    packetWidth b R n F s J r headCap Y Cq ≤ envelope S :=
  packetWidth_mono hb hR hn hF hs hJ hr hh hY hCq

/-- Concrete width envelope has fixed monomial witnesses, independent of the input. -/
theorem envelope_monomial : ∃ C k : ℕ, ∀ S,envelope S ≤ C*(S+1)^k := by
  change Bound envelope
  unfold envelope packetWidth productExponent exponent groupWidth factorExponent
    SemiprimeNativeLocalBits.publicWidth SemiprimeNativeLocalBits.portExponent
    SemiprimeCorrectedPortBits.portWidth SemiprimeLocalBitsBounds.bufferWidth
  boundArithmetic

/-- Original source input bits need a polynomial resource, not the false bound b ≤ S. -/
def sourceEnvelope (S : ℕ) : ℕ :=
  packetWidth (SemiprimeNativeInputBits.polynomial S S S S S) S S S S S S S S S

/-- The ACTUAL source-derived input width is covered from original dimensions. -/
theorem source_width_le_envelope (n B Q R J F s r headCap Y Cq S : ℕ)
    (hn : n ≤ S) (hB : B ≤ S) (hQ : Q ≤ S) (hR : R ≤ S) (hJ : J ≤ S)
    (hF : F ≤ S) (hs : s ≤ S) (hr : r ≤ S) (hh : headCap ≤ S) (hY : Y ≤ S) (hCq : Cq ≤ S) :
    packetWidth (SemiprimeNativeInputBits.inputBits n B Q R J) R n F s J r headCap Y Cq ≤ 
      sourceEnvelope S := by
  have hb : SemiprimeNativeInputBits.inputBits n B Q R J ≤ SemiprimeNativeInputBits.polynomial S S S S S := by
    apply (SemiprimeNativeInputBits.inputBits_le_polynomial n B Q R J).trans
    unfold SemiprimeNativeInputBits.polynomial
    gcongr
  exact packetWidth_mono hb hR hn hF hs hJ hr hh hY hCq

/-- The source-specialized ACTUAL width also has fixed monomial growth. -/
theorem source_envelope_monomial : ∃ C k : ℕ, ∀ S,sourceEnvelope S ≤ C*(S+1)^k := by
  change Bound sourceEnvelope
  unfold sourceEnvelope SemiprimeNativeInputBits.polynomial packetWidth productExponent exponent
    groupWidth factorExponent SemiprimeNativeLocalBits.publicWidth SemiprimeNativeLocalBits.portExponent
    SemiprimeCorrectedPortBits.portWidth SemiprimeLocalBitsBounds.bufferWidth
  boundArithmetic

end RiemannGaussian.SemiprimeWordPacketWidthBudget
