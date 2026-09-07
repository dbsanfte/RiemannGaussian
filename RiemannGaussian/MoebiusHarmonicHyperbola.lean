import RiemannGaussian.MoebiusFiniteHyperbola
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The original harmonic Möbius prefix and its full hyperbola error

The finite reciprocal-weighted sum keeps every signed integer remainder.
An exact hyperbola identity bounds all quotient prefixes together, including
the floor corrections. This is an ordered finite sum; no absolute
convergence of the harmonic Möbius series is asserted.
-/

open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The original signed Möbius sum with its literal harmonic inverse weight. -/
def moebiusHarmonicPrefix (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) / d

/-- The exact signed Euclidean-division remainder in the finite harmonic hyperbola. -/
def moebiusHarmonicRounding (D Q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) * ((D * Q) % d : ℕ) / d

/-- Every integer rounding contribution is retained, and their total absolute cost is at most the number of terms. -/
theorem abs_moebiusHarmonicRounding_le (D Q : ℕ) : |moebiusHarmonicRounding D Q| ≤ D := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdp : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hrem : (((D * Q) % d : ℕ) : ℝ) ≤ d := by
        exact_mod_cast (Nat.mod_lt (D * Q) (Finset.mem_Icc.mp hd).1).le
      rw [abs_div, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (((D * Q) % d : ℕ) : ℝ) from Nat.cast_nonneg _), abs_of_pos hdp,
        div_le_iff₀ hdp, one_mul]
      have hm := abs_real_moebius_le_one d
      nlinarith [Nat.cast_nonneg (α := ℝ) ((D * Q) % d)]
    _ = _ := by simp

/-- Multiplying the actual harmonic prefix by the product cutoff keeps its complete floor part and signed remainder exactly. -/
theorem moebiusHarmonicPrefix_mul_cutoff (D Q : ℕ) :
    ((D * Q : ℕ) : ℝ) * moebiusHarmonicPrefix D =
      (∑ d ∈ Finset.Icc 1 D, ((μ d : ℤ) : ℝ) * ((D * Q) / d : ℕ)) + moebiusHarmonicRounding D Q := by
  unfold moebiusHarmonicPrefix moebiusHarmonicRounding
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hd).1)
  have he : ((D * Q : ℕ) : ℝ) = (((D * Q) % d : ℕ) : ℝ) + (d : ℝ) * ((D * Q) / d : ℕ) := by
    exact_mod_cast (Nat.mod_add_div (D * Q) d).symm
  rw [he]
  field_simp
  ring

/-- The full signed harmonic inverse is exactly its hyperbola unit, both quotient-prefix terms, and every rounding correction. -/
theorem moebiusHarmonicPrefix_hyperbola_identity {D Q : ℕ} (hD : 0 < D) (hQ : 0 < Q) :
    ((D * Q : ℕ) : ℝ) * moebiusHarmonicPrefix D =
      1 + (Q : ℝ) * moebiusFinitePrefix D -
        (∑ q ∈ Finset.Icc 1 Q, moebiusFinitePrefix ((D * Q) / q)) + moebiusHarmonicRounding D Q := by
  have hf := moebiusHarmonicPrefix_mul_cutoff D Q
  have hh := moebiusFinitePrefix_hyperbola_identity hD hQ
  linarith

/-- The complete harmonic prefix has a joint finite bound in all quotient prefixes and the full rounding budget. -/
theorem abs_moebiusHarmonicPrefix_mul_cutoff_le {D Q : ℕ} (hD : 0 < D) (hQ : 0 < Q) :
    ((D * Q : ℕ) : ℝ) * |moebiusHarmonicPrefix D| ≤
      1 + (Q : ℝ) * |moebiusFinitePrefix D| +
        (∑ q ∈ Finset.Icc 1 Q, |moebiusFinitePrefix ((D * Q) / q)|) + D := by
  calc
    _ = |((D * Q : ℕ) : ℝ) * moebiusHarmonicPrefix D| := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ((D * Q : ℕ) : ℝ) from Nat.cast_nonneg _)]
    _ = _ := congrArg abs (moebiusHarmonicPrefix_hyperbola_identity hD hQ)
    _ ≤ |1 + (Q : ℝ) * moebiusFinitePrefix D -
        (∑ q ∈ Finset.Icc 1 Q, moebiusFinitePrefix ((D * Q) / q))| + |moebiusHarmonicRounding D Q| :=
      abs_add_le _ _
    _ ≤ (|1 + (Q : ℝ) * moebiusFinitePrefix D| +
        |∑ q ∈ Finset.Icc 1 Q, moebiusFinitePrefix ((D * Q) / q)|) + D :=
      add_le_add (abs_sub _ _) (abs_moebiusHarmonicRounding_le D Q)
    _ ≤ ((|1| + |(Q : ℝ) * moebiusFinitePrefix D|) +
        (∑ q ∈ Finset.Icc 1 Q, |moebiusFinitePrefix ((D * Q) / q)|)) + D :=
      add_le_add (add_le_add (abs_add_le _ _) (Finset.abs_sum_le_sum_abs _ _)) le_rfl
    _ = _ := by rw [abs_one, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ Q from Nat.cast_nonneg _)]

/-- A proved bound on all original prefixes above the lower cutoff controls the entire harmonic sum, with logarithmic rather than linear quotient cost. -/
theorem abs_moebiusHarmonicPrefix_le_hyperbola {D Q : ℕ} (hD : 0 < D) (hQ : 0 < Q)
    {delta : ℝ} (hd : 0 ≤ delta)
    (hprefix : ∀ n : ℕ, D ≤ n → |moebiusFinitePrefix n| ≤ delta * n) :
    |moebiusHarmonicPrefix D| ≤ 2 / (Q : ℝ) + delta * (2 + Real.log Q) := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsum : (∑ q ∈ Finset.Icc 1 Q, |moebiusFinitePrefix ((D * Q) / q)|) ≤
      delta * ((D * Q : ℕ) : ℝ) * (1 + Real.log Q) := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, delta * ((D * Q : ℕ) : ℝ) * (1 / (q : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqp : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
        have hcut : D ≤ (D * Q) / q := (Nat.le_div_iff_mul_le (Finset.mem_Icc.mp hq).1).mpr
          (Nat.mul_le_mul_left D (Finset.mem_Icc.mp hq).2)
        have hdiv : (((D * Q) / q : ℕ) : ℝ) ≤ ((D * Q : ℕ) : ℝ) / q := by
          rw [le_div_iff₀ hqp]
          exact_mod_cast Nat.div_mul_le_self (D * Q) q
        apply (hprefix _ hcut).trans
        exact (mul_le_mul_of_nonneg_left hdiv hd).trans_eq (by ring)
      _ = delta * ((D * Q : ℕ) : ℝ) * (∑ q ∈ Finset.Icc 1 Q, 1 / (q : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
          using harmonic_le_one_add_log Q
  have hb := (abs_moebiusHarmonicPrefix_mul_cutoff_le hD hQ).trans
    (add_le_add (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (hprefix D le_rfl) hQp.le)) hsum) le_rfl)
  have hM : 0 < ((D * Q : ℕ) : ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hM).mp
  apply hb.trans
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  simp only [Nat.cast_mul]
  have he : ((D : ℝ) * Q) * (2 / Q + delta * (2 + Real.log Q)) =
      2 * D + delta * ((D : ℝ) * Q) * (2 + Real.log Q) := by field_simp
  rw [he]
  nlinarith

end

end RiemannGaussian
