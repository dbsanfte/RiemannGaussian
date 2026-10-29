/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreWeightBits
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Original-dimension acquisition for the integer score weights
The universal cardinality and all magnitudes are actually constructed. Natural
loop parameters are an explicit host boundary; no encoded weight/count is supplied.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceScoreWeightAcquisition
open SemiprimeSourceScoreWeightBits SemiprimeSourceOffsetInputsCore SemiprimeBitArithmetic
open SemiprimeReportPolynomialGrowth

/-- Acquire original dimensions and U once before caching the two score weights. -/
def acquire (M n r Q lam : ℕ) : Weights :=
  let bank := unaryPower r (2*Q)
  let m := natBits M
  let nn := natBits n
  let l := natBits lam
  let u := natBits bank.cells.length
  let out := weights m.bits nn.bits l.bits u.bits
  ⟨out.incidence,out.head,bank.clock+bank.cells.length+1+
    m.clock+nn.clock+l.clock+u.clock+out.clock+10⟩

/-- Both weights are derived from the actual original inputs and acquired U. -/
theorem acquire_value (M n r Q lam : ℕ) :
    bitValue (acquire M n r Q lam).incidence=n^2*lam^2*(r^(2*Q))^2 ∧
      bitValue (acquire M n r Q lam).head=4*M^2 := by
  have h := weights_value (natBits M).bits (natBits n).bits (natBits lam).bits
    (natBits (unaryPower r (2*Q)).cells.length).bits
  simpa only [acquire,natBits_value,unaryPower_length] using h

/-- Common input-array cap before the physical weight computation. -/
def inputWidth (M n lam U : ℕ) : ℕ := M+n+lam+U+1

/-- All original acquired weight arrays have the displayed polynomial width. -/
theorem acquire_length (M n r Q lam : ℕ) :
    (acquire M n r Q lam).incidence.length ≤ weightWidth (inputWidth M n lam (r^(2*Q))) ∧
      (acquire M n r Q lam).head.length ≤ weightWidth (inputWidth M n lam (r^(2*Q))) := by
  have hM := natBits_length M
  have hn := natBits_length n
  have hl := natBits_length lam
  have hU := natBits_length (unaryPower r (2*Q)).cells.length
  rw [unaryPower_length] at hU
  change (weights (natBits M).bits (natBits n).bits (natBits lam).bits
    (natBits (unaryPower r (2*Q)).cells.length).bits).incidence.length ≤ _ ∧ _
  simp only [unaryPower_length]
  apply weights_length <;> unfold inputWidth <;> omega

/-- Actual universal cardinality, four encoders and seven products, all retained. -/
def acquisitionBudget (M n r Q lam U : ℕ) : ℕ :=
  2+2*Q*(r*(3*U+3)+U+5)+U+1+
    80*(inputWidth M n lam U+1)^2+weightBudget (inputWidth M n lam U)+10

/-- Original-resource cost of the complete cached-weight acquisition. -/
theorem acquire_clock (M n r Q lam : ℕ) (hr : 0<r) :
    (acquire M n r Q lam).clock ≤ acquisitionBudget M n r Q lam (r^(2*Q)) := by
  let U := r^(2*Q)
  let L := inputWidth M n lam U
  have hM := natBits_length M
  have hn := natBits_length n
  have hl := natBits_length lam
  have hU := natBits_length (unaryPower r (2*Q)).cells.length
  rw [unaryPower_length] at hU
  have hw := weights_clock (natBits M).bits (natBits n).bits (natBits lam).bits
    (natBits (unaryPower r (2*Q)).cells.length).bits L
    (by dsimp [L,inputWidth];omega) (by dsimp [L,inputWidth];omega)
    (by dsimp [L,inputWidth];omega) (by simpa only [unaryPower_length] using (show (natBits U).bits.length ≤ L from by dsimp [U,L,inputWidth];omega))
  simp only [unaryPower_length] at hw
  have hb := unaryPower_clock r Q hr (2*Q) (by omega)
  have cM := natBits_clock M
  have cn := natBits_clock n
  have cl := natBits_clock lam
  have cu := natBits_clock (unaryPower r (2*Q)).cells.length
  rw [unaryPower_length] at cu
  have hmL : M ≤ L := by dsimp [L,inputWidth];omega
  have hnL : n ≤ L := by dsimp [L,inputWidth];omega
  have hlL : lam ≤ L := by dsimp [L,inputWidth];omega
  have huL : U ≤ L := by dsimp [L,inputWidth];omega
  have pM : (M+1)^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have pn : (n+1)^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have pl : (lam+1)^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have pu : (U+1)^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  simp only [acquire,unaryPower_length,acquisitionBudget]
  change _ ≤ 2+2*Q*(r*(3*U+3)+U+5)+U+1+80*(L+1)^2+weightBudget L+10
  dsimp only [U] at hb pu ⊢
  omega

/-- Encode acquired natural counts by actual Boolean additions, then weight them. -/
def evaluate (w : Weights) (I H : ℕ) : NatRun :=
  let i := natBits I
  let h := natBits H
  let out := combine w i.bits h.bits
  ⟨out.bits,i.clock+h.clock+out.clock+4⟩

/-- No integer count-to-word oracle is assumed at this host-natural interface. -/
theorem evaluate_value (w : Weights) (I H : ℕ) :
    bitValue (evaluate w I H).bits=bitValue w.incidence*I+bitValue w.head*H := by
  simp only [evaluate,combine_value,natBits_value]

/-- The original W=n²λ²U² I+4M² H is computed from the actual acquired data. -/
theorem evaluate_original (M n r Q lam I H : ℕ) :
    bitValue (evaluate (acquire M n r Q lam) I H).bits=
      n^2*lam^2*(r^(2*Q))^2*I+4*M^2*H := by
  rw [evaluate_value,(acquire_value M n r Q lam).1,(acquire_value M n r Q lam).2]

/-- Per-candidate acquisition and physical arithmetic budget from natural count caps. -/
theorem evaluate_clock (w : Weights) (I H L : ℕ)
    (ha : w.incidence.length ≤ L) (hb : w.head.length ≤ L)
    (hi : I+1 ≤ L) (hh : H+1 ≤ L) :
    (evaluate w I H).clock ≤ 40*(L+1)^2+combineBudget L+4 := by
  have ci := natBits_clock I
  have ch := natBits_clock H
  have hli := natBits_length I
  have hlh := natBits_length H
  have hc := combine_clock w (natBits I).bits (natBits H).bits L ha hb
    (hli.trans hi) (hlh.trans hh)
  have pi : (I+1)^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have ph : (H+1)^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  dsimp only [evaluate]
  omega

/-- An original-data width covering both cached weights and acquired count words. -/
def candidateWidth (M n r Q lam I H : ℕ) : ℕ :=
  weightWidth (inputWidth M n lam (r^(2*Q)))+I+H+1

/-- Per-candidate cost at original acquired weights, with no width advice. -/
theorem evaluate_acquired_clock (M n r Q lam I H : ℕ) :
    (evaluate (acquire M n r Q lam) I H).clock ≤
      40*(candidateWidth M n r Q lam I H+1)^2+
        combineBudget (candidateWidth M n r Q lam I H)+4 := by
  have hw := acquire_length M n r Q lam
  apply evaluate_clock
  · exact hw.1.trans (by unfold candidateWidth;omega)
  · exact hw.2.trans (by unfold candidateWidth;omega)
  · unfold candidateWidth;omega
  · unfold candidateWidth;omega

/-- Componentwise monotonicity in independent materialized original resources. -/
theorem acquisitionBudget_mono {M n r Q lam U M' n' r' Q' lam' U' : ℕ}
    (hM : M ≤ M') (hn : n ≤ n') (hr : r ≤ r') (hQ : Q ≤ Q')
    (hl : lam ≤ lam') (hU : U ≤ U') :
    acquisitionBudget M n r Q lam U ≤ acquisitionBudget M' n' r' Q' lam' U' := by
  unfold acquisitionBudget inputWidth weightBudget weightWidth
  gcongr

/-- Fixed monomial growth in the actual materialized resource dimensions. -/
theorem acquisition_monomial : ∃ C k : ℕ,∀ S,
    acquisitionBudget S S S S S S ≤ C*(S+1)^k := by
  change Bound (fun S => acquisitionBudget S S S S S S)
  simp only [acquisitionBudget,inputWidth,weightBudget,weightWidth]
  boundArithmetic

end RiemannGaussian.SemiprimeSourceScoreWeightAcquisition
