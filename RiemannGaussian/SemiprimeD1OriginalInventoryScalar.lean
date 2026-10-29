/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OriginalScalarResources
import RiemannGaussian.SemiprimeD1TensorTapeLeafBudget
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Full literal inventory and tape-leaf cost at the original scalar
All literal truth-table payload is retained as an additional 2^delta factor.
The tape leaf's concrete polynomial, including whole serialization/read work,
has a fixed monomial envelope with that factor present. No native/tape clock
equality or complete machine simulation is inferred.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1OriginalInventoryScalar
open SemiprimeD1PackingReady SemiprimeD1OriginalStateResources
open SemiprimeD1OriginalEnvelopeRate SemiprimeD1OriginalScalarResources
open SemiprimeReportPolynomialGrowth

/-- The actual stored-table cofactor after replacing scalar dimensions only. -/
def inventoryPolynomial (S : ℕ) : ℕ :=
  5*S*((S*(3*S+4)+3)+S)+S+5*S+1

/-- A deliberately generous explicit scalar polynomial, fixed before all calls. -/
theorem inventoryPolynomial_le (S : ℕ) : inventoryPolynomial S ≤ 100*(S+1)^4 := by
  unfold inventoryPolynomial
  nlinarith [Nat.zero_le (S^4),Nat.zero_le (S^3),Nat.zero_le (S^2)]

/-- Entire literal network storage keeps the full table exponential. -/
theorem inventoryCap_le (s : ℕ) (hl:1000 ≤ logarithm s) :
    inventoryCap s ≤ 100*(scalar s+1)^4*2^(degreeCap s) := by
  have hs: s ≤ scalar s:=(base_caps s hl).1
  have hr:=rankCap_le s hl
  have hp:=precisionCap_le s hl
  have hd:=degreeCap_le s hl
  have hD:1 ≤ 2^(degreeCap s):=Nat.one_le_two_pow
  let S:=scalar s
  let D:=2^(degreeCap s)
  change 1 ≤ D at hD
  have hSD:S ≤ S*D:=by nlinarith
  have htail:S+5*S+1 ≤ (S+5*S+1)*D:=by nlinarith
  calc
    _  ≤  5*S*((S*(3*S+4)+3)*D+S)+S+5*S+1 := by unfold inventoryCap;gcongr
    _  ≤  inventoryPolynomial S*D := by unfold inventoryPolynomial;nlinarith
    _  ≤  100*(S+1)^4*D := Nat.mul_le_mul_right D (inventoryPolynomial_le S)

/-- The scalar itself is included in the full storage cap. -/
theorem scalar_le_storageCap (S D : ℕ) (hD:1 ≤ D) : S ≤ 100*(S+1)^4*D := by
  have hp:S+1 ≤ (S+1)^4:=le_self_pow (by omega) (by decide:(4:ℕ)≠0)
  have hm: (S+1)^4 ≤ (S+1)^4*D:=by nlinarith
  nlinarith

/-- The diagonal of the executed tape-leaf polynomial is a fixed polynomial. -/
theorem tape_diagonal_monomial : SemiprimeReportPolynomialGrowth.Bound
    (fun U=>SemiprimeD1TensorTapeLeafBudget.polynomial U U U U U U U) := by
  unfold SemiprimeD1TensorTapeLeafBudget.polynomial SemiprimeD1JetRingBounds.mulBudget
    SemiprimeD1JetRingBounds.mulAtBudget SemiprimeD1JetRingBounds.termBudget
  boundArithmetic

/-- Original actual tape-leaf polynomial is bounded before its independent
2^leafSize enumeration is applied. The coefficient and exponent precede s. -/
theorem tape_original_polynomial : ∃C k:ℕ,∀s:ℕ,1000 ≤ logarithm s→
    SemiprimeD1TensorTapeLeafBudget.originalPolynomial s ≤
      C*(scalar s+1)^k*2^(C*degreeCap s) := by
  obtain ⟨C,k,hpoly⟩:=tape_diagonal_monomial
  refine ⟨C*101^k+k+1,4*k,?_⟩
  intro s hl
  let S:=scalar s
  let D:=2^(degreeCap s)
  let U:=100*(S+1)^4*D
  have hD:1 ≤ D:=Nat.one_le_two_pow
  have hSU:S ≤ U:=scalar_le_storageCap S D hD
  have hc:=base_caps s hl
  have hI:inventoryCap s ≤ U:=inventoryCap_le s hl
  have hactual:SemiprimeD1TensorTapeLeafBudget.originalPolynomial s ≤
      SemiprimeD1TensorTapeLeafBudget.polynomial U U U U U U U:=by
    unfold SemiprimeD1TensorTapeLeafBudget.originalPolynomial
    exact SemiprimeD1TensorTapeLeafBudget.polynomial_mono
      (hc.1.trans hSU) (hc.2.2.trans hSU) ((rankCap_le s hl).trans hSU)
      ((precisionCap_le s hl).trans hSU) (hc.2.1.trans hSU) hI hI
  have hbase:U+1 ≤ 101*(S+1)^4*D:=by
    have hsp:1 ≤ (S+1)^4:=one_le_pow₀ (by omega)
    dsimp only [U]
    nlinarith
  have hpower: C*(U+1)^k ≤ C*101^k*(S+1)^(4*k)*2^(k*degreeCap s):=by
    calc
      _  ≤  C*(101*(S+1)^4*D)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase k)
      _ = _ := by
        dsimp only [D]
        rw [show k*degreeCap s=degreeCap s*k by ring,pow_mul]
        simp only [mul_pow,pow_mul]
        ring
  have hcoef:C*101^k ≤ C*101^k+k+1:=by omega
  have hexp:k*degreeCap s ≤ (C*101^k+k+1)*degreeCap s:=Nat.mul_le_mul_right _ (by omega)
  exact (hactual.trans (hpoly U)).trans (hpower.trans (by gcongr))

end RiemannGaussian.SemiprimeD1OriginalInventoryScalar
