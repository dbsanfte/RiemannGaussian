/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseExactDuality
import RiemannGaussian.ZetaPhaseContactPrimal
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The exact family inside the full space of phase sequences

An exact finite-to-infinite transport identifies the constructed coefficient
row as a genuine phase sequence with finite height budget. Any normalized
feasible family attaining the exact contact bound must equal this sequence:
strict penalties first force finite support, and the contact geometry then
forces the coefficients. Feasibility of the constructed kernel itself is
still the separate polynomial-positivity obligation.
-/

open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

private theorem phaseFrequency_injective : Function.Injective phaseContactFrequency := by decide

private theorem phaseFrequencies_eq_image :
    phaseContactFrequencies = Finset.univ.image phaseContactFrequency := by decide

private theorem phaseFrequency_mem (i : Fin 9) : phaseContactFrequency i ∈ phaseContactFrequencies := by
  rw [phaseFrequencies_eq_image]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Extend an indexed coefficient row to the complete natural-frequency axis. -/
def phaseContactFrequencyFamily (a : Fin 9 → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin 9, if n = phaseContactFrequency i then a i else 0

/-- The finite polynomial in the cosine coordinate for an arbitrary row. -/
def phaseContactIndexedKernel (a : Fin 9 → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin 9, a i * phaseChebyshevValue (phaseContactFrequency i) x

/-- No coefficient information is lost in extension to the full frequency axis. -/
theorem phaseContactFrequencyFamily_apply (a : Fin 9 → ℝ) (i : Fin 9) :
    phaseContactFrequencyFamily a (phaseContactFrequency i) = a i := by
  simp [phaseContactFrequencyFamily, phaseFrequency_injective.eq_iff]

/-- The finite extension vanishes at every unselected frequency. -/
theorem phaseContactFrequencyFamily_eq_zero {n : ℕ} (hn : n ∉ phaseContactFrequencies) (a : Fin 9 → ℝ) :
    phaseContactFrequencyFamily a n = 0 := by
  unfold phaseContactFrequencyFamily
  apply Finset.sum_eq_zero
  intro i _
  apply if_neg
  intro h
  apply hn
  rw [h]
  exact phaseFrequency_mem i

/-- A sequence supported on the selected frequencies is recovered exactly
from its indexed coefficients. -/
theorem phaseContactFrequencyFamily_reconstruct {a : ℕ → ℝ}
    (ha : ∀ n, n ∉ phaseContactFrequencies → a n = 0) :
    phaseContactFrequencyFamily (fun i ↦ a (phaseContactFrequency i)) = a := by
  ext n
  by_cases hn : n ∈ phaseContactFrequencies
  · rw [phaseFrequencies_eq_image] at hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact phaseContactFrequencyFamily_apply _ i
  · rw [phaseContactFrequencyFamily_eq_zero hn, ha n hn]

/-- Every weighted sum of the finite extension genuinely converges and
has the expected value. This supports phase and height-cost transport alike. -/
theorem phaseContactFrequencyFamily_hasSum_mul (a : Fin 9 → ℝ) (f : ℕ → ℝ) :
    HasSum (fun n ↦ phaseContactFrequencyFamily a n * f n)
      (∑ i : Fin 9, a i * f (phaseContactFrequency i)) := by
  have h := hasSum_sum (s := (Finset.univ : Finset (Fin 9)))
    (fun i _ ↦ hasSum_ite_eq (phaseContactFrequency i) (a i * f (phaseContactFrequency i)))
  apply h.congr_fun
  intro n
  unfold phaseContactFrequencyFamily
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hn : n = phaseContactFrequency i <;> simp [hn]

/-- The full phase sum equals its finite trigonometric expansion. -/
theorem phaseContactFrequencyFamily_kernel (a : Fin 9 → ℝ) (t : ℝ) :
    phaseContactKernel (phaseContactFrequencyFamily a) t =
      ∑ i : Fin 9, a i * Real.cos ((phaseContactFrequency i : ℝ) * t) :=
  (phaseContactFrequencyFamily_hasSum_mul a (fun n ↦ Real.cos ((n : ℝ) * t))).tsum_eq

/-- The continuous polynomial and natural-frequency representations commute. -/
theorem phaseContactFrequencyFamily_kernel_cos (a : Fin 9 → ℝ) (t : ℝ) :
    phaseContactKernel (phaseContactFrequencyFamily a) t = phaseContactIndexedKernel a (Real.cos t) := by
  rw [phaseContactFrequencyFamily_kernel]
  simp only [phaseContactIndexedKernel, phaseChebyshevValue_cos]

/-- The complete height budget is the indexed coefficient cost. -/
theorem phaseContactFrequencyFamily_budget (a : Fin 9 → ℝ) :
    phaseContactBudget (phaseContactFrequencyFamily a) =
      ∑ i : Fin 9, a i * phaseContactCost (phaseContactFrequency i) := by
  have h := phaseContactFrequencyFamily_hasSum_mul a phaseContactCost
  have h' : HasSum (fun n ↦ phaseContactCost n * phaseContactFrequencyFamily a n)
      (∑ i : Fin 9, a i * phaseContactCost (phaseContactFrequency i)) := by
    apply h.congr_fun
    intro n
    ring
  exact h'.tsum_eq

/-- The source term is preserved exactly by the same extension. -/
theorem phaseContactFrequencyFamily_source (a : Fin 9 → ℝ) :
    phaseContactSource (phaseContactFrequencyFamily a) =
      ∑ i : Fin 9, a i * phaseContactSourceCoeff (phaseContactFrequency i) := by
  have h0 : phaseContactFrequencyFamily a 0 = a 0 := phaseContactFrequencyFamily_apply a 0
  have h1 : phaseContactFrequencyFamily a 1 = a 1 := phaseContactFrequencyFamily_apply a 1
  unfold phaseContactSource
  rw [h0, h1]
  simp [Fin.sum_univ_succ, phaseContactFrequency, phaseContactSourceCoeff]
  ring

/-- The exact, mathematically defined candidate as a complete phase sequence. -/
def phaseContactExactFamily : ℕ → ℝ := phaseContactFrequencyFamily phaseContactExactCoefficients

/-- All coefficients of the complete exact family are nonnegative. -/
theorem phaseContactExactFamily_nonneg (n : ℕ) : 0 ≤ phaseContactExactFamily n := by
  unfold phaseContactExactFamily phaseContactFrequencyFamily
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (phaseContactExactCoefficients_pos i).le
  · exact le_rfl

/-- The exact family's full height budget converges to one. -/
theorem phaseContactExactFamily_hasSum_budget :
    HasSum (fun n ↦ phaseContactCost n * phaseContactExactFamily n) 1 := by
  have h := phaseContactFrequencyFamily_hasSum_mul phaseContactExactCoefficients phaseContactCost
  rw [phaseContactExactCoefficients_cost] at h
  apply h.congr_fun
  intro n
  change phaseContactCost n * phaseContactFrequencyFamily phaseContactExactCoefficients n = _
  ring

/-- The exact family's signed source is the contact root's efficiency. -/
theorem phaseContactExactFamily_source : phaseContactSource phaseContactExactFamily = phaseContactExactRoot 8 := by
  rw [phaseContactExactFamily, phaseContactFrequencyFamily_source, phaseContactExactCoefficients_source]

/-- The full sequence has the same continuous kernel as the exact polynomial. -/
theorem phaseContactExactFamily_kernel (t : ℝ) :
    phaseContactKernel phaseContactExactFamily t = phaseContactExactKernel (Real.cos t) :=
  phaseContactFrequencyFamily_kernel_cos phaseContactExactCoefficients t

/-- The exact candidate's nonzero coefficients are precisely the nine
selected frequencies, including the constant term. -/
theorem phaseContactExactFamily_ne_zero_iff (n : ℕ) :
    phaseContactExactFamily n ≠ 0 ↔ n ∈ phaseContactFrequencies := by
  refine ⟨?_, ?_⟩
  · intro h
    by_contra hn
    exact h (phaseContactFrequencyFamily_eq_zero hn _)
  · intro hn
    rw [phaseFrequencies_eq_image] at hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    change phaseContactFrequencyFamily phaseContactExactCoefficients (phaseContactFrequency i) ≠ 0
    rw [phaseContactFrequencyFamily_apply]
    exact ne_of_gt (phaseContactExactCoefficients_pos i)

/-- Among all finite or infinite feasible phase sequences with cost one,
attainment of the exact contact bound determines a unique family. This does
not assume or assert that the constructed kernel is already feasible. -/
theorem phaseContactExactFamily_unique_at_bound {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t) (hb : phaseContactBudget a = 1)
    (he : phaseContactSource a = phaseContactExactRoot 8) : a = phaseContactExactFamily := by
  have he' : phaseContactSource a = phaseContactExactRoot 8 * phaseContactBudget a := by rw [hb, mul_one, he]
  have hoff := fun n hn ↦ phaseContactExact_offSupport_eq_zero_of_equality ha hs hp he' (n := n) hn
  let v : Fin 9 → ℝ := fun i ↦ a (phaseContactFrequency i)
  have hva : phaseContactFrequencyFamily v = a := phaseContactFrequencyFamily_reconstruct hoff
  have hcost : (∑ i : Fin 9, v i * phaseContactCost (phaseContactFrequency i)) = 1 := by
    rw [← phaseContactFrequencyFamily_budget, hva, hb]
  have hvalue (j : Fin 4) : phaseContactIndexedKernel v
      (phaseContactExactRoot (phaseContactCosineCoordinate j)) = 0 := by
    have h := phaseContactExact_contact_eq_zero_of_equality ha hs hp he' j
    rw [← hva, phaseContactFrequencyFamily_kernel_cos] at h
    have hq := (abs_lt.mp (abs_phaseContactExactRoot_cosine_lt_one j))
    simpa only [phaseContactExactAngle, Real.cos_arccos hq.1.le hq.2.le] using h
  have hpositive {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ phaseContactIndexedKernel v x := by
    have h := hp (Real.arccos x)
    rw [← hva, phaseContactFrequencyFamily_kernel_cos,
      Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2] at h
    exact h
  have hslope (j : Fin 4) : ∑ i : Fin 9, v i * phaseChebyshevSecant
      (phaseContactExactRoot (phaseContactCosineCoordinate j))
      (phaseContactExactRoot (phaseContactCosineCoordinate j)) (phaseContactFrequency i) = 0 := by
    let q := phaseContactExactRoot (phaseContactCosineCoordinate j)
    have hq : -1 < q ∧ q < 1 := abs_lt.mp (abs_phaseContactExactRoot_cosine_lt_one j)
    have hlocal : IsLocalMin (phaseContactIndexedKernel v) q := by
      filter_upwards [Ioo_mem_nhds hq.1 hq.2] with x hx
      change phaseContactIndexedKernel v q ≤ phaseContactIndexedKernel v x
      rw [hvalue j]
      exact hpositive (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
    have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 9)))
      (fun i _ ↦ (hasDerivAt_phaseChebyshevValue (phaseContactFrequency i) q).const_mul (v i))
    exact hlocal.hasDerivAt_eq_zero hd
  have hv : v = phaseContactExactCoefficients := phaseContactExactCoefficients_unique hcost hvalue hslope
  rw [← hva, hv]
  rfl

end

end RiemannGaussian
