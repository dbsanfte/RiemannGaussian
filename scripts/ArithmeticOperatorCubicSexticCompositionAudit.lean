/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Tactic
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Conditional composition of the cubic marked-prime and sextic numerator norms

No arithmetic large-sieve theorem or native separability claim is imported.
The displayed single-collision budget concerns a matching PRIME physical index;
the paper audit separately prices the full divisor expansion for squarefree indices.
The exact `divisor_kernel` preserves its residual cofactor-only twist.

The literal physical row index contains all supported ideals. No source coverage
for the matching squarefree block or whole-detector estimate is asserted.
The finite composition requires one common physical-index vector and a cofactor-only
multiplier. The rate ledger assumes the stated native normalizers. For actual
non-sixth-power-free numerators the paper audit uses bounded row coefficients
and triangle summation of sixth-power dyads; no unrestricted-row moment is claimed.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RiemannGaussian.ArithmeticOperatorCubicSexticCompositionAudit

/-- Two genuine matrix estimates compose through any cofactor-only contraction.
The outer and inner arithmetic estimates remain explicit hypotheses. -/
theorem finite_composition {M I P : Type*} (ms : Finset M) (is : Finset I) (ps : Finset P)
    (C : I → P → ℂ) (D : M → I → ℂ) (b : I → ℂ) (v : P → ℂ)
    (K3 K6 : ℝ) (hK6 : 0≤K6)
    (h3 : ∀ w : P → ℂ,
      (∑ i ∈ is, ‖∑ p ∈ ps, C i p*w p‖^2)≤K3*(∑ p ∈ ps, ‖w p‖^2))
    (h6 : ∀ w : I → ℂ,
      (∑ m ∈ ms, ‖∑ i ∈ is, D m i*w i‖^2)≤K6*(∑ i ∈ is, ‖w i‖^2))
    (hb : ∀ i ∈ is, ‖b i‖≤1) :
    (∑ m ∈ ms, ‖∑ i ∈ is, D m i*(b i*(∑ p ∈ ps, C i p*v p))‖^2)≤
      (K6*K3)*(∑ p ∈ ps, ‖v p‖^2) := by
  calc
    _ ≤ K6*(∑ i ∈ is, ‖b i*(∑ p ∈ ps, C i p*v p)‖^2) := h6 _
    _ ≤ K6*(∑ i ∈ is, ‖∑ p ∈ ps, C i p*v p‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hK6
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      have hle : ‖b i‖*‖∑ p ∈ ps, C i p*v p‖≤‖∑ p ∈ ps, C i p*v p‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (hb i hi)
      exact sq_le_sq₀ (by positivity) (norm_nonneg _) |>.mpr hle
    _ ≤ K6*(K3*(∑ p ∈ ps, ‖v p‖^2)) := mul_le_mul_of_nonneg_left (h3 v) hK6
    _ = _ := by ring

/-- Numerator norm-volume exponent. -/
def rowExponent (d : ℝ) : ℝ := 5/6-2*d
/-- Cofactor norm exponent, after matching the physical prime. -/
def cofactorExponent : ℝ := 11/16
/-- Physical marked-prime norm exponent. -/
def primeExponent (d : ℝ) : ℝ := 23/48-d
/-- Conditional sixth-order squared-operator exponent. -/
def delta6 (a b : ℝ) : ℝ := max (max a b) (max ((5/6)*a+b/3) (a/3+(5/6)*b))
/-- Conditional cubic squared-operator exponent. -/
def delta3 (a b : ℝ) : ℝ := max (max a b) ((2/3)*(a+b))
/-- Rate after both genuine norms and all stated native normalizers. -/
def composedRate (d : ℝ) : ℝ :=
  (delta6 (rowExponent d) cofactorExponent+
    delta3 cofactorExponent (primeExponent d)-2*primeExponent d-cofactorExponent)/2-d/2
/-- Rate for the explicitly retained physical-prime divisibility correction. -/
def collisionRate (d : ℝ) : ℝ :=
  delta6 (rowExponent d-primeExponent d) cofactorExponent/2-primeExponent d-d/2

/-- The numerator cannot contain two comparable physical prime factors at these lengths. -/
theorem row_lt_two_prime (d : ℝ) : rowExponent d<2*primeExponent d := by
  unfold rowExponent primeExponent
  linarith

/-- The first sextic mixed term controls shallow depths. -/
theorem delta6_shallow {d : ℝ} (hd : 0≤d) (hdeep : d≤7/96) :
    delta6 (rowExponent d) cofactorExponent=133/144-(5/3)*d := by
  unfold delta6 rowExponent cofactorExponent
  have he : (5/6:ℝ)*(5/6-2*d)+(11/16:ℝ)/3=133/144-(5/3)*d := by ring
  rw [← he]
  apply le_antisymm
  · apply max_le <;> apply max_le <;> linarith
  · exact (le_max_left _ _).trans (le_max_right _ _)

/-- The second sextic mixed term controls deeper depths. -/
theorem delta6_deep {d : ℝ} (hd : 7/96≤d) (hdeep : d≤1/6) :
    delta6 (rowExponent d) cofactorExponent=245/288-(2/3)*d := by
  unfold delta6 rowExponent cofactorExponent
  have he : (5/6-2*d)/3+(5/6:ℝ)*(11/16:ℝ)=245/288-(2/3)*d := by ring
  rw [← he]
  apply le_antisymm
  · apply max_le <;> apply max_le <;> linarith
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- The cubic mixed term persists until depth13/96. -/
theorem delta3_shallow {d : ℝ} (hd : 0≤d) (hdeep : d≤13/96) :
    delta3 cofactorExponent (primeExponent d)=7/9-(2/3)*d := by
  unfold delta3 cofactorExponent primeExponent
  rw [max_eq_right (by apply max_le <;> linarith)]
  ring

/-- The cofactor term controls the final cubic range. -/
theorem delta3_deep {d : ℝ} (hd : 13/96≤d) :
    delta3 cofactorExponent (primeExponent d)=11/16 := by
  unfold delta3 cofactorExponent primeExponent
  apply le_antisymm
  · apply max_le
    · exact max_le (le_refl _) (by linarith)
    · linarith
  · exact (le_max_left _ _).trans (le_max_left _ _)

/-- Exact first branch of the composed conditional budget. -/
theorem composedRate_shallow {d : ℝ} (hd : 0≤d) (hdeep : d≤7/96) :
    composedRate d=1/36-(2/3)*d := by
  unfold composedRate
  rw [delta6_shallow hd hdeep,delta3_shallow hd (by linarith)]
  unfold primeExponent cofactorExponent
  ring

/-- Exact middle branch of the composed conditional budget. -/
theorem composedRate_middle {d : ℝ} (hd : 7/96≤d) (hdeep : d≤13/96) :
    composedRate d= -5/576-d/6 := by
  unfold composedRate
  rw [delta6_deep hd (by linarith),delta3_shallow (by linarith) hdeep]
  unfold primeExponent cofactorExponent
  ring

/-- Exact final branch of the composed conditional budget. -/
theorem composedRate_deep {d : ℝ} (hd : 13/96≤d) (hdeep : d≤1/6) :
    composedRate d= -31/576+d/6 := by
  unfold composedRate
  rw [delta6_deep (by linarith) hdeep,delta3_deep hd]
  unfold primeExponent cofactorExponent
  ring

/-- Uniform rate credit remains conditional on both arithmetic norms and separation. -/
theorem composedRate_le {d : ℝ} (hd : 0≤d) (hdeep : d≤1/6) : composedRate d≤1/36 := by
  by_cases h : d≤7/96
  · rw [composedRate_shallow hd h]; linarith
  · by_cases h' : d≤13/96
    · rw [composedRate_middle (by linarith) h']; linarith
    · rw [composedRate_deep (by linarith) hdeep]; linarith

/-- The candidate main rate has a strict margin over the old target. -/
theorem composedRate_lt_baseline {d : ℝ} (hd : 0≤d) (hdeep : d≤1/6) :
    composedRate d<3/16 := by
  have h := composedRate_le hd hdeep
  linarith

/-- The physical-prime collision has a uniformly decaying candidate budget. -/
theorem collisionRate_le {d : ℝ} (hdeep : d≤1/6) : collisionRate d≤ -5/96 := by
  unfold collisionRate delta6 rowExponent primeExponent cofactorExponent
  have h1 : (5/6-2*d)-(23/48-d)≤2*((23/48-d)+d/2-5/96) := by linarith
  have h2 : (11/16:ℝ)≤2*((23/48-d)+d/2-5/96) := by linarith
  have h3 : (5/6)*((5/6-2*d)-(23/48-d))+(11/16:ℝ)/3≤
      2*((23/48-d)+d/2-5/96) := by linarith
  have h4 : ((5/6-2*d)-(23/48-d))/3+(5/6)*(11/16:ℝ)≤
      2*((23/48-d)+d/2-5/96) := by linarith
  have hmax := max_le (max_le h1 h2) (max_le h3 h4)
  linarith

/-- The two norm costs satisfy a uniform budget over all shorter cofactor scales.
This does not supply coverage of the native physical rows or their source. -/
theorem norm_exponent_sum_le {d u : ℝ} (hd' : d≤1/6)
    (hu : 0≤u) (hu' : u≤11/16) :
    delta6 (rowExponent d) u+delta3 u (primeExponent d)≤
      rowExponent d+primeExponent d+u := by
  unfold delta6 delta3 rowExponent primeExponent
  simp only [max_def]
  split_ifs <;> linarith

/-- The cofactor-uniform rational implication preserves the exterior V cost. -/
theorem general_composed_rate_le {d u : ℝ} (v : ℝ) (hd' : d≤1/6)
    (hu : 0≤u) (hu' : u≤11/16) :
    (delta6 (rowExponent d) u+delta3 u (primeExponent d)-2*primeExponent d-u)/2-d/2-v
      ≤17/96-d-v := by
  have h := norm_exponent_sum_le hd' hu hu'
  unfold rowExponent primeExponent at h ⊢
  linarith

/-- A physical squarefree-index puncture divisor leaves a cofactor-only twist.
Multiplicativity is used without any inverse or deletion of nonunit zeros. -/
theorem divisor_kernel {A : Type*} [CommMonoid A] (phase : A → ℂ)
    (hmul : ∀ a b, phase (a*b)=phase a*phase b) (d p n : A) :
    phase (d*p)^4*phase (d*n)=phase d^5*phase p^4*phase n := by
  rw [hmul,hmul,mul_pow]
  ring

end RiemannGaussian.ArithmeticOperatorCubicSexticCompositionAudit

#lint+ in RiemannGaussian.ArithmeticOperatorCubicSexticCompositionAudit

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
  logInfo m!"Conditional cubic/sextic composition: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile ".lake/arithmetic-operator-sextic-period-correlation/axioms.json"
    (Json.mkObj [("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
