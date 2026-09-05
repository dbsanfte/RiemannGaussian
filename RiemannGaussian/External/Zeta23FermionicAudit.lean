import Mathlib

/-!
# Local audit of two proposed fourth-moment shortcuts

These are rejection tests for research proposals, not zeta certificates.
The exterior-product numerator does not cancel pair-sum resonance. The
short-channel positive-square ansatz below also has a quantitative obstruction,
even if its proposed moment values are granted. No prime moment asymptotic is
asserted or assumed as a theorem in this file.
-/

namespace RiemannGaussian.FermionicAudit

noncomputable section

open scoped BigOperators

/-- The exterior minor of the two first-jet vectors `(1,a)` and `(1,b)`. -/
def jetMinor (a b : ℝ) : ℝ := 1 * b - a * 1

/-- Exterior minors vanish at equal individual frequencies. -/
theorem jetMinor_eq (a b : ℝ) : jetMinor a b = b - a := by
  simp [jetMinor]

/-- The four-frequency resonance has a different zero set from the exterior
numerator: all four frequencies in this example are distinct and positive. -/
theorem pair_sum_resonance_survives :
    (1 : ℝ) + 4 - 2 - 3 = 0 ∧ jetMinor 1 4 * jetMinor 2 3 = 3 := by
  norm_num [jetMinor]

/-- There is no everywhere-defined factorization of this numerator by the
pair-sum gap. In particular a formal exterior-product identity cannot supply
the proposed cancellation. -/
theorem no_pair_gap_factorization :
    ¬ ∃ f : ℝ → ℝ → ℝ → ℝ → ℝ,
      ∀ a b c d, jetMinor a b * jetMinor c d = (a + b - c - d) * f a b c d := by
  rintro ⟨f, hf⟩
  have h := hf 1 4 2 3
  norm_num [jetMinor] at h

/-- The obstruction persists for nonzero pair-sum gaps arbitrarily close
to zero; this is not an issue caused by division at zero. -/
theorem exterior_quotient_unbounded (B : ℝ) (hB : 0 ≤ B) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      (1 : ℝ) + 4 - 2 - (3 + t) ≠ 0 ∧
      B < |jetMinor 1 4 * jetMinor 2 (3 + t) /
        ((1 : ℝ) + 4 - 2 - (3 + t))| := by
  let t : ℝ := 1 / (B + 1)
  have hb : 0 < B + 1 := by linarith
  have ht : 0 < t := one_div_pos.mpr hb
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hb).mpr (by linarith)
  have hgap : (1 : ℝ) + 4 - 2 - (3 + t) = -t := by ring
  have hquot : jetMinor 1 4 * jetMinor 2 (3 + t) /
      ((1 : ℝ) + 4 - 2 - (3 + t)) = -3 * (B + 2) := by
    dsimp [jetMinor, t]
    field_simp
    ring
  refine ⟨t, ht, ht1, ?_, ?_⟩
  · rw [hgap]
    exact neg_ne_zero.mpr ht.ne'
  · rw [hquot, abs_of_neg (by nlinarith : -3 * (B + 2) < 0)]
    linarith

/-- On pair space, the exterior square of `A²` retains exactly the fourth
spectral moment. Its positivity alone does not evaluate that moment. The
ordered distinct-pair sum here is twice its trace. -/
theorem exterior_square_keeps_fourth_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    (∑ i, x i ^ 2) ^ 2 =
      (∑ i, x i ^ 4) + ∑ i, ∑ j ∈ Finset.univ.erase i, x i ^ 2 * x j ^ 2 := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.add_sum_erase Finset.univ (fun j => x i ^ 2 * x j ^ 2)
    (Finset.mem_univ i)]
  congr 1
  ring

/-- Model energy of `I - a A + (s I + t B)²` at the proposed half-length
short-channel moments. This definition does not assert those values for zeta. -/
def shortSquareEnergy (a s t : ℝ) : ℝ :=
  (1 - a + s ^ 2) ^ 2 + a ^ 2 / 3 - 2 / 3 * a * s * t +
    2 / 3 * s ^ 2 * t ^ 2 + (1 - a + s ^ 2) * t ^ 2 / 3 +
    19 / 240 * t ^ 4

/-- Exact sum-of-squares decomposition of the short-channel model energy. -/
theorem shortSquareEnergy_eq_squares (a s t : ℝ) :
    shortSquareEnergy a s t =
      (1 - a + s ^ 2 + t ^ 2 / 6) ^ 2 +
        (a - s * t) ^ 2 / 3 + (s * t) ^ 2 / 3 + 37 / 720 * (t ^ 2) ^ 2 := by
  unfold shortSquareEnergy
  ring

/-- A rational quantitative obstruction for every real choice of the
short-square parameters; no numerical optimizer is trusted. -/
theorem shortSquareEnergy_lower (a s t : ℝ) :
    (25 : ℝ) / 103 ≤ shortSquareEnergy a s t := by
  let u : ℝ := 1 - a + s ^ 2 + t ^ 2 / 6
  let v : ℝ := a - s * t
  let p : ℝ := s * t
  have hlinear : 1 ≤ u + v + p / 5 := by
    dsimp [u, v, p]
    nlinarith [sq_nonneg (s - 2 / 5 * t), sq_nonneg t]
  have hcs : (u + v + p / 5) ^ 2 ≤
      103 / 25 * (u ^ 2 + v ^ 2 / 3 + p ^ 2 / 3) := by
    nlinarith [sq_nonneg (v - 3 * u), sq_nonneg (p - 3 / 5 * u),
      sq_nonneg (p - v / 5)]
  have henergy : shortSquareEnergy a s t =
      u ^ 2 + v ^ 2 / 3 + p ^ 2 / 3 + 37 / 720 * (t ^ 2) ^ 2 :=
    shortSquareEnergy_eq_squares a s t
  nlinarith [sq_nonneg (t ^ 2), sq_nonneg (u + v + p / 5 - 1)]

/-- Even in the proposed favorable short-channel moment model, this ansatz
cannot supply an inertia certificate above 68 percent. This is a method
obstruction, not an upper bound on the actual proportion of zeta zeros. -/
theorem shortSquare_certificate_below_gate (a s t : ℝ) :
    1 - 2 * shortSquareEnergy a s t ≤ (53 : ℝ) / 103 ∧
      (53 : ℝ) / 103 < 17 / 25 := by
  constructor
  · linarith [shortSquareEnergy_lower a s t]
  · norm_num

end

end RiemannGaussian.FermionicAudit
