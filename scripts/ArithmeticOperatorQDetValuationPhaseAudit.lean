/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Literal determinant depth phases

This finite audit preserves the phase at every prime-power depth. It proves
an exact product ledger and an actual q-binomial determinant's 7-adic fiber
annihilation at a primitive third root. It proves no physical-prime source
response, asymptotic prime estimate, or assertion about zeta zero ordinates.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option warningAsError true
noncomputable section
open scoped BigOperators
namespace OpenAIReview.QDetValuationPhase

/-- The literal phase packet at depths one through v. -/
def depthPacket (z : ℂ) (v : ℕ) : ℂ := ∑ r∈Finset.range v,z^(r+1)

/-- Multiplication of integer factors shifts the second depth packet. -/
theorem depth_add (z : ℂ) (u v : ℕ) :
    depthPacket z (u+v)=depthPacket z u+z^u*depthPacket z v := by
  simp only [depthPacket,Finset.sum_range_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [← pow_add]
  congr 1

/-- Extracting a cube keeps three successive blocks, with their phases. -/
theorem depth_triple (z : ℂ) (a : ℕ) :
    depthPacket z (3*a)=(1+z^a+z^(2*a))*depthPacket z a := by
  have h : 3*a=a+(a+a) := by omega
  rw [h,depth_add,depth_add]
  rw [show 2*a=a+a by omega,pow_add]
  ring

/-- Exact cube-extraction ledger, including every extra quotient depth. -/
theorem depth_extraction (z : ℂ) (a c : ℕ) :
    depthPacket z (3*a+c)=
      (1+z^a+z^(2*a))*depthPacket z a+z^(3*a)*depthPacket z c := by
  rw [depth_add,depth_triple]

/-- The exact discrepancy from resetting each factor's depth to one. -/
theorem reset_defect (z : ℂ) (a c : ℕ) :
    depthPacket z (3*a+c)-3*depthPacket z a-depthPacket z c=
      (z^a+z^(2*a)-2)*depthPacket z a+(z^(3*a)-1)*depthPacket z c := by
  rw [depth_extraction]
  ring

/-- A cubic phase satisfying the cyclotomic equation is nonzero. -/
theorem cubic_ne_zero (z : ℂ) (hz : z^2+z+1=0) : z≠0 := by
  rintro rfl
  norm_num at hz

/-- The cyclotomic equation forces period three. -/
theorem cubic_pow (z : ℂ) (hz : z^2+z+1=0) : z^3=1 := by
  linear_combination (z-1)*hz

/-- Three consecutive positive depths cancel at a primitive cubic phase. -/
theorem cubic_three (z : ℂ) (hz : z^2+z+1=0) : depthPacket z 3=0 := by
  simp only [depthPacket,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num only [Nat.reduceAdd] at *
  rw [cubic_pow z hz]
  linear_combination hz

/-- Every full three-depth block cancels without resetting the quotient. -/
theorem cubic_blocks (z : ℂ) (hz : z^2+z+1=0) (a : ℕ) :
    depthPacket z (3*a)=0 := by
  induction a with
  | zero => simp [depthPacket]
  | succ a ih =>
    rw [Nat.mul_succ,depth_add,ih,cubic_three z hz]
    ring

/-- Only the quotient depth modulo three survives at a cubic phase. -/
theorem cubic_extraction (z : ℂ) (hz : z^2+z+1=0) (a c : ℕ) :
    depthPacket z (3*a+c)=depthPacket z c := by
  rw [depth_add,cubic_blocks z hz,pow_mul,cubic_pow z hz]
  simp

/-- The actual positive-exponent complex cubic phase. -/
def cubicPhase : ℂ := Complex.exp (2*Real.pi*Complex.I/3)

/-- The literal phase satisfies the primitive cubic equation. -/
theorem cubicPhase_relation : cubicPhase^2+cubicPhase+1=0 := by
  have h:= (Complex.isPrimitiveRoot_exp 3 (by norm_num)).geom_sum_eq_zero (by norm_num)
  simpa [cubicPhase,Finset.sum_range_succ,add_comm,add_left_comm,add_assoc] using h

/-- The literal physical phase at the first depth of a prime. -/
def physicalPhase (p : ℕ) (y : ℝ) : ℂ :=
  Complex.exp (((-y*Real.log p : ℝ) : ℂ)*Complex.I)

/-- The depth exponent is literally the phase at p to the r, with no reset. -/
theorem physicalPhase_pow (p r : ℕ) (y : ℝ) :
    physicalPhase p y ^ r=
      Complex.exp (((-y*Real.log ((p : ℝ)^r) : ℝ) : ℂ)*Complex.I) := by
  rw [physicalPhase,← Complex.exp_nat_mul,Real.log_pow]
  congr 1
  push_cast
  ring

/-- A genuine real height realizing the cubic phase on the seven-fiber. -/
def cubicHeight : ℝ := -(2*Real.pi)/(3*Real.log 7)

/-- The physical height yields the very same phase, without a depth reset. -/
theorem physicalPhase_at_height : physicalPhase 7 cubicHeight=cubicPhase := by
  have hl : Real.log 7≠0 := ne_of_gt (Real.log_pos (by norm_num))
  have h : -cubicHeight*Real.log 7=2*Real.pi/3 := by
    unfold cubicHeight
    field_simp
  unfold physicalPhase
  norm_num only [Nat.cast_ofNat]
  rw [h]
  unfold cubicPhase
  congr 1
  push_cast
  ring

/-- The ordinary integer q-integer; the samples below use base two. -/
def qInteger (b j : ℕ) : ℕ := (b^j-1)/(b-1)

/-- The literal integer q-factorial. -/
def qFactorial (b N : ℕ) : ℕ := ∏ j∈Finset.range N,qInteger b (j+1)

/-- The native factorial quotient defining an integer Gaussian binomial. -/
def qBinomial (b N K : ℕ) : ℕ :=
  qFactorial b N/(qFactorial b K*qFactorial b (N-K))

/-- The actual negative determinant at base two and index three, as an integer. -/
def sampleDeterminant : ℤ :=
  let z : ℤ := 2^9
  let F : ℤ := 1+z+z^2+z^3+z^4
  (qBinomial 2 15 3 : ℤ)*(F+z^2)-(qBinomial 2 12 6 : ℤ)*F

/-- Kernel computation of the literal q-binomial determinant, with its sign. -/
theorem sampleDeterminant_value : sampleDeterminant= -1465731801504914208720 := by
  decide +kernel

/-- The actual positive integer norm in the sample. -/
def sampleNorm : ℕ := sampleDeterminant.natAbs

/-- The norm is computed from the signed native determinant. -/
theorem sampleNorm_value : sampleNorm=1465731801504914208720 := by
  simp [sampleNorm,sampleDeterminant_value]

/-- The literal third cyclotomic value at base two. -/
def sampleCyclotomic : ℕ := ((Polynomial.cyclotomic 3 ℤ).eval 2).natAbs

/-- The actual cyclotomic factor has value seven. -/
theorem sampleCyclotomic_value : sampleCyclotomic=7 := by
  norm_num [sampleCyclotomic,Polynomial.cyclotomic_three]

/-- The extracted cyclotomic factor has one 7-adic depth. -/
theorem sampleCyclotomic_depth : sampleCyclotomic.factorization 7=1 := by
  rw [sampleCyclotomic_value]
  exact Nat.Prime.factorization_self (by norm_num)

/-- The quotient has no hidden fourth 7-adic depth. -/
theorem sampleQuotient_depth : (4273270558323365040 : ℕ).factorization 7=0 := by
  exact Nat.factorization_eq_zero_of_not_dvd (by norm_num)

/-- Exact native valuation, including the quotient nondivisibility check. -/
theorem sampleNorm_depth : sampleNorm.factorization 7=3 := by
  rw [sampleNorm_value]
  have h : (1465731801504914208720 : ℕ)=7^3*4273270558323365040 := by norm_num
  rw [h,Nat.factorization_mul (by norm_num) (by norm_num),Finsupp.add_apply,
    Nat.factorization_pow_self (by norm_num : Nat.Prime 7),sampleQuotient_depth]

/-- The actual determinant's complete 7-depth packet is zero at this phase. -/
theorem native_fiber_zero :
    depthPacket cubicPhase (sampleNorm.factorization 7)=0 := by
  rw [sampleNorm_depth]
  exact cubic_three cubicPhase cubicPhase_relation

/-- The annihilation occurs at an actual real prime-power phase height. -/
theorem physical_native_fiber_zero :
    depthPacket (physicalPhase 7 cubicHeight) (sampleNorm.factorization 7)=0 := by
  rw [physicalPhase_at_height,native_fiber_zero]

/-- The extracted single cyclotomic depth is nonzero at the same phase. -/
theorem extracted_fiber_ne_zero :
    depthPacket cubicPhase (sampleCyclotomic.factorization 7)≠0 := by
  rw [sampleCyclotomic_depth]
  simpa [depthPacket] using cubic_ne_zero cubicPhase cubicPhase_relation

/-- Multiplying by log seven does not rescue the vanished complete packet. -/
theorem native_log_fiber_zero :
    (Real.log 7 : ℂ)*depthPacket cubicPhase (sampleNorm.factorization 7)=0 := by
  rw [native_fiber_zero,mul_zero]

/-- No positive lower bound for the extracted packet transfers fiberwise. -/
theorem no_positive_fiber_transfer (ε : ℝ) (hε : 0<ε) :
    ¬ε*‖depthPacket cubicPhase (sampleCyclotomic.factorization 7)‖≤
      ‖depthPacket cubicPhase (sampleNorm.factorization 7)‖ := by
  rw [native_fiber_zero,norm_zero]
  exact not_le.mpr (mul_pos hε (norm_pos_iff.mpr extracted_fiber_ne_zero))

end OpenAIReview.QDetValuationPhase

#lint+ in OpenAIReview.QDetValuationPhase

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty q-determinant phase audit."
  logInfo m!"Q-determinant phase audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-qdet-valuation-phase-gate"
  IO.FS.writeFile ".lake/arithmetic-operator-qdet-valuation-phase-gate/axioms.json"
    (Json.mkObj [("scope",toJson "exact depth phase ledger and literal q-binomial determinant 7-fiber obstruction; physical cutoff/source estimates paper-level"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingHelpers",toJson theorems),
      ("details",Json.arr reports)]).pretty
