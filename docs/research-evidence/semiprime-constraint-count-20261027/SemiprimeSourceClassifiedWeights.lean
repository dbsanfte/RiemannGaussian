/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceCountPowers
import RiemannGaussian.SemiprimeSourceScoreWeightAcquisition

/-! # Cached source weights from the acquired collision powers
The already acquired square is exactly U=r^(2Q). Reusing it removes unary
universal-cardinality expansion and its magnitude-linear re-encoding. The
once-per-caller power acquisition is charged separately by that caller.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceClassifiedWeights
open SemiprimeBitArithmetic SemiprimeSourceOffsetInputsCore SemiprimeSourceScoreWeightBits
open SemiprimeSourceCountPowers (Powers)
open SemiprimeReportPolynomialGrowth

/-- Acquire the three original dimensions and execute the seven cached products. -/
def acquire (M n lam : ℕ) (powers : Powers) : Weights :=
  let m := natBits M
  let nn := natBits n
  let l := natBits lam
  let out := weights m.bits nn.bits l.bits powers.square
  ⟨out.incidence,out.head,m.clock+nn.clock+l.clock+out.clock+5⟩

/-- Both actual coefficients agree with the original integer objective. -/
theorem acquire_value (M n r Q lam : ℕ) :
    bitValue (acquire M n lam (SemiprimeSourceCountPowers.acquire r Q)).incidence=
        n^2*lam^2*(r^(2*Q))^2 ∧
      bitValue (acquire M n lam (SemiprimeSourceCountPowers.acquire r Q)).head=4*M^2 := by
  have h := weights_value (natBits M).bits (natBits n).bits (natBits lam).bits
    (SemiprimeSourceCountPowers.acquire r Q).square
  simpa only [acquire,natBits_value,(SemiprimeSourceCountPowers.acquire_value r Q).1] using h

/-- Original semantic weights are unchanged although padding/acquisition differs. -/
theorem acquire_old_value (M n r Q lam : ℕ) :
    bitValue (acquire M n lam (SemiprimeSourceCountPowers.acquire r Q)).incidence=
        bitValue (SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam).incidence ∧
      bitValue (acquire M n lam (SemiprimeSourceCountPowers.acquire r Q)).head=
        bitValue (SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam).head := by
  rw [(acquire_value M n r Q lam).1,(acquire_value M n r Q lam).2,
    (SemiprimeSourceScoreWeightAcquisition.acquire_value M n r Q lam).1,
    (SemiprimeSourceScoreWeightAcquisition.acquire_value M n r Q lam).2]
  exact ⟨rfl,rfl⟩

/-- Input-array width from original dimensions and executed multiplication growth. -/
def inputWidth (M n lam r Q : ℕ) : ℕ := M+n+lam+SemiprimeSourceCountPowers.width r Q+3

/-- All cached coefficient widths are derived internally. -/
theorem acquire_length (M n r Q lam : ℕ) :
    (acquire M n lam (SemiprimeSourceCountPowers.acquire r Q)).incidence.length ≤
        weightWidth (inputWidth M n lam r Q) ∧
      (acquire M n lam (SemiprimeSourceCountPowers.acquire r Q)).head.length ≤
        weightWidth (inputWidth M n lam r Q) := by
  have hM := natBits_length M
  have hn := natBits_length n
  have hl := natBits_length lam
  have hU := (SemiprimeSourceCountPowers.acquire_length r Q).1
  apply weights_length <;> unfold inputWidth <;> omega

/-- All three original input encoders and all seven products remain paid. -/
def budget (M n lam r Q : ℕ) : ℕ :=
  20*(M+1)^2+20*(n+1)^2+20*(lam+1)^2+weightBudget (inputWidth M n lam r Q)+5

/-- No exponential materialization or encoded-weight advice enters acquisition. -/
theorem acquire_clock (M n r Q lam : ℕ) :
    (acquire M n lam (SemiprimeSourceCountPowers.acquire r Q)).clock ≤ budget M n lam r Q := by
  have hM := natBits_length M
  have hn := natBits_length n
  have hl := natBits_length lam
  have hU := (SemiprimeSourceCountPowers.acquire_length r Q).1
  have hw := weights_clock (natBits M).bits (natBits n).bits (natBits lam).bits
    (SemiprimeSourceCountPowers.acquire r Q).square (inputWidth M n lam r Q)
    (by unfold inputWidth;omega) (by unfold inputWidth;omega)
    (by unfold inputWidth;omega) (by unfold inputWidth;omega)
  have cM := natBits_clock M
  have cn := natBits_clock n
  have cl := natBits_clock lam
  unfold acquire budget
  dsimp only
  omega

/-- Fixed constants bound the initializer uniformly over original dimensions. -/
theorem budget_monomial : ∃ C k : ℕ,∀ M n lam r Q S,
    M ≤ S → n ≤ S → lam ≤ S → r ≤ S → Q ≤ S → budget M n lam r Q ≤ C*(S+1)^k := by
  have hp : Bound (fun S => budget S S S S S) := by
    simp only [budget,inputWidth,SemiprimeSourceCountPowers.width,weightBudget,weightWidth]
    boundArithmetic
  obtain ⟨C,k,h⟩ := hp
  refine ⟨C,k,?_⟩
  intro M n lam r Q S hM hn hl hr hQ
  apply le_trans _ (h S)
  simp only [budget,inputWidth,SemiprimeSourceCountPowers.width,weightBudget,weightWidth]
  gcongr

end RiemannGaussian.SemiprimeSourceClassifiedWeights
