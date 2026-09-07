import RiemannGaussian.MoebiusHarmonicCancellation
import RiemannGaussian.EtaMomentInverseRegion

/-!+# Harmonic cancellation of the original truncated inverse coefficients

The full physical hyperbola is truncated only in its inner Möbius divisor.
Exact product grouping retains the original completed moments, phases,
integer quotients, and translated centers. The accumulated signed product
coefficient equals the cutoff times the harmonic Möbius prefix, with every
Euclidean remainder retained. Its quantitative bound controls a growing
two-divisor region; it is a linear coefficient estimate, not an estimate
for the quadratic completed current.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The actual positive inverse region with the inner Möbius divisor capped at `D`. -/
def pairedEtaInverseInnerCap (M D : ℕ) : Finset (ℕ × ℕ) :=
  (pairedEtaInverseHyperbolicRegion M).filter (fun p ↦ p.2 ≤ D)

/-- Inner truncation retains the complete original physical product constraint. -/
theorem pairedEtaInverseInnerCap_subset (M D : ℕ) :
    pairedEtaInverseInnerCap M D ⊆ pairedEtaInverseHyperbolicRegion M :=
  Finset.filter_subset _ _

/-- The original completed inverse on this region retains all complex atoms before its coefficients are estimated. -/
theorem pairedEtaCompletedMomentInverseInnerCap_eq_atoms
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M D : ℕ) :
    pairedEtaCompletedMomentInverseRegion rho k a M (pairedEtaInverseInnerCap M D) =
      pairedEtaWeightedMomentDivisorFamily rho k
        (fun n ↦ pairedEtaInverseRegionCoefficient (pairedEtaInverseInnerCap M D) n) a M M :=
  pairedEtaCompletedMomentInverseRegion_eq_atoms rho k a M (pairedEtaInverseInnerCap_subset M D)

/-- Regrouping by the actual inner divisor preserves the complete complex weight on each integer product. -/
theorem sum_pairedEtaInverseInnerCap_mul (M D : ℕ) (f : ℕ → ℂ) :
    (∑ p ∈ pairedEtaInverseInnerCap M D, (μ p.2 : ℂ) * f (p.1 * p.2)) =
      ∑ d ∈ Finset.Icc 1 D, (μ d : ℂ) * ∑ e ∈ Finset.Icc 1 (M / d), f (e * d) := by
  let g : ℕ × ℕ → ℂ := fun p ↦ (μ p.2 : ℂ) * f (p.1 * p.2)
  have hf := Finset.sum_fiberwise_of_maps_to (s := pairedEtaInverseInnerCap M D)
    (t := Finset.Icc 1 D) (g := fun p : ℕ × ℕ ↦ p.2)
    (fun p hp ↦ Finset.mem_Icc.mpr
      ⟨(mem_pairedEtaInverseHyperbolicRegion.mp (Finset.mem_filter.mp hp).1).2.1,
        (Finset.mem_filter.mp hp).2⟩) g
  change (∑ p ∈ pairedEtaInverseInnerCap M D, g p) = _
  rw [← hf]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp := (Finset.mem_Icc.mp hd).1
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun e _ ↦ (e, d))
  · intro e he
    obtain ⟨he1, heM⟩ := Finset.mem_Icc.mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, (Finset.mem_Icc.mp hd).2⟩, rfl⟩
    exact mem_pairedEtaInverseHyperbolicRegion.mpr
      ⟨he1, hdp, (Nat.le_div_iff_mul_le hdp).mp heM⟩
  · intro e he e' he' heq
    exact congrArg Prod.fst heq
  · intro p hp
    obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
    obtain ⟨he, _, hprod⟩ := mem_pairedEtaInverseHyperbolicRegion.mp (Finset.mem_filter.mp hpS).1
    refine ⟨p.1, Finset.mem_Icc.mpr ⟨he, ?_⟩, ?_⟩
    · exact (Nat.le_div_iff_mul_le hdp).mpr (by simpa only [hpd] using hprod)
    · exact Prod.ext rfl hpd.symm
  · intro e he
    rfl

/-- All product coefficients in the actual inner-truncated inverse sum to one literal floor-weighted Möbius prefix. -/
theorem sum_pairedEtaInverseInnerCapCoefficient_eq (M D : ℕ) :
    (∑ n ∈ Finset.Icc 1 M,
      (pairedEtaInverseRegionCoefficient (pairedEtaInverseInnerCap M D) n : ℝ)) =
        ∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) * (M / d : ℕ) := by
  have hp := sum_pairedEtaInverseRegionCoefficient_mul
    (pairedEtaInverseInnerCap_subset M D) (fun _ ↦ (1 : ℂ))
  rw [sum_pairedEtaInverseInnerCap_mul M D (fun _ ↦ (1 : ℂ))] at hp
  have hr := congrArg Complex.re hp
  simpa using hr

/-- The signed rounding correction at arbitrary physical and inner cutoffs. -/
def pairedEtaInverseInnerCapRounding (M D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) * (M % d : ℕ) / d

/-- Every floor remainder in the original accumulated inverse coefficients has total cost at most the inner cutoff. -/
theorem abs_pairedEtaInverseInnerCapRounding_le (M D : ℕ) :
    |pairedEtaInverseInnerCapRounding M D| ≤ D := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdp : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hrem : ((M % d : ℕ) : ℝ) ≤ d := by
        exact_mod_cast (Nat.mod_lt M (Finset.mem_Icc.mp hd).1).le
      rw [abs_div, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ ((M % d : ℕ) : ℝ) from Nat.cast_nonneg _),
        abs_of_pos hdp, div_le_iff₀ hdp, one_mul]
      have hm := abs_real_moebius_le_one d
      nlinarith [Nat.cast_nonneg (α := ℝ) (M % d)]
    _ = _ := by simp

/-- Exact harmonic reduction of the complete signed coefficient sum, with its original integer rounding and sign. -/
theorem sum_pairedEtaInverseInnerCapCoefficient_harmonic (M D : ℕ) :
    (∑ n ∈ Finset.Icc 1 M,
      (pairedEtaInverseRegionCoefficient (pairedEtaInverseInnerCap M D) n : ℝ)) =
        (M : ℝ) * moebiusHarmonicPrefix D - pairedEtaInverseInnerCapRounding M D := by
  rw [sum_pairedEtaInverseInnerCapCoefficient_eq, eq_sub_iff_add_eq]
  unfold moebiusHarmonicPrefix pairedEtaInverseInnerCapRounding
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hd).1)
  have he : (M : ℝ) = ((M % d : ℕ) : ℝ) + (d : ℝ) * (M / d : ℕ) := by
    exact_mod_cast (Nat.mod_add_div M d).symm
  rw [he]
  field_simp
  ring

/-- The original accumulated signed coefficients have a harmonic main bound and a complete finite rounding budget. -/
theorem abs_sum_pairedEtaInverseInnerCapCoefficient_le (M D : ℕ) :
    |∑ n ∈ Finset.Icc 1 M,
      (pairedEtaInverseRegionCoefficient (pairedEtaInverseInnerCap M D) n : ℝ)| ≤
        (M : ℝ) * |moebiusHarmonicPrefix D| + D := by
  rw [sum_pairedEtaInverseInnerCapCoefficient_harmonic]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ M from Nat.cast_nonneg _)]
  exact add_le_add le_rfl (abs_pairedEtaInverseInnerCapRounding_le M D)

/-- Quantitative harmonic cancellation controls the signed product coefficients across the entire actual inner-truncated hyperbola at every physical cutoff. -/
theorem exists_pairedEtaInverseInnerCapCoefficient_cubic_rate :
    ∃ H : ℝ, 22 ≤ H ∧ ∀ h : ℝ, H ≤ h → ∀ M D : ℕ,
      Real.exp (2 * moebiusFiniteContourCenter h) ≤ (D : ℝ) →
        |∑ n ∈ Finset.Icc 1 M,
          (pairedEtaInverseRegionCoefficient (pairedEtaInverseInnerCap M D) n : ℝ)| ≤
            moebiusHarmonicCancellationConstant * Real.exp (-h / 8) * M + D := by
  obtain ⟨H, hH, hbound⟩ := exists_moebiusHarmonicPrefix_cubic_rate
  refine ⟨H, hH, fun h hh M D hD ↦ ?_⟩
  apply (abs_sum_pairedEtaInverseInnerCapCoefficient_le M D).trans
  have hb := mul_le_mul_of_nonneg_left (hbound h hh D hD) (Nat.cast_nonneg (α := ℝ) M)
  linarith

end

end RiemannGaussian
