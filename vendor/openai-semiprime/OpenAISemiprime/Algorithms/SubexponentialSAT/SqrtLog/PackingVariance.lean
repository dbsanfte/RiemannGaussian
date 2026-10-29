import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.TypeDistribution
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubexpBlockPacking

namespace OAI.Algorithms

/-! Exact collision-energy bounds used in correlated incidence packing. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance

noncomputable section

variable {Ω I U : Type*} [Fintype Ω] [Fintype I] [Fintype U]
  [DecidableEq I] [DecidableEq U] [Nonempty Ω] [Nonempty U]

/-- Sum of squared deviations of the actual type counts. -/
def energy (label : I → U) : ℚ :=
  ∑ u, (((Finset.univ.filter fun i => label i = u).card : ℚ) -
    (Fintype.card I : ℚ) / (Fintype.card U : ℚ)) ^ 2

omit [DecidableEq I] [Nonempty U] in
theorem energy_nonneg (label : I → U) : 0 ≤ energy label := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq I] in
theorem energy_eq_collisions (label : I → U) :
    energy label = (∑ i, ∑ j, if label i = label j then (1 : ℚ) else 0) -
      (Fintype.card I : ℚ)^2 / (Fintype.card U : ℚ) := by
  exact SubexponentialSAT.TypeDistribution.squared_deviation_eq_collisions label

omit [Nonempty U] in
theorem collision_eq_indicator_sum (x y : U) :
    (if x = y then (1 : ℚ) else 0) =
      ∑ u : U, (if x = u then (1 : ℚ) else 0) * (if y = u then 1 else 0) := by
  simp [ ]

omit [Nonempty Ω] in
theorem mean_collision_of_indicators (X Y : Ω → U)
    (h : ∀ u, mean uniformWeight (fun ω =>
      (if X ω = u then (1 : ℚ) else 0) * (if Y ω = u then 1 else 0)) =
        (1 / (Fintype.card U : ℚ)) * (1 / (Fintype.card U : ℚ))) :
    mean uniformWeight (fun ω => if X ω = Y ω then (1 : ℚ) else 0) =
      1 / (Fintype.card U : ℚ) := by
  have hf : (fun ω => if X ω = Y ω then (1 : ℚ) else 0) =
      (fun ω => ∑ u : U, (if X ω = u then (1 : ℚ) else 0) *
        (if Y ω = u then 1 else 0)) := by
    funext ω
    exact collision_eq_indicator_sum (X ω) (Y ω)
  rw [hf, mean_sum]
  simp_rw [h]
  have hN : (Fintype.card U : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Inclusive dependency sets give a bound without a factor of the type count. -/
theorem mean_energy_le (label : Ω → I → U) (deps : I → Finset I) (d : ℕ)
    (hcard : ∀ i, (deps i).card ≤ d)
    (hind : ∀ i j, j ∉ deps i →
      mean uniformWeight (fun ω => if label ω i = label ω j then (1 : ℚ) else 0) =
        1 / (Fintype.card U : ℚ)) :
    mean uniformWeight (fun ω => energy (label ω)) ≤
      (d : ℚ) * (Fintype.card I : ℚ) := by
  let c (i j : I) : ℚ :=
    mean uniformWeight (fun ω => if label ω i = label ω j then (1 : ℚ) else 0) -
      1 / (Fintype.card U : ℚ)
  have hbound (i j : I) : c i j ≤ 1 := by
    have hm : mean uniformWeight
        (fun ω => if label ω i = label ω j then (1 : ℚ) else 0) ≤ 1 := by
      calc
        _ ≤ mean uniformWeight (fun _ : Ω => (1 : ℚ)) := by
          apply mean_mono _ uniformWeight_nonneg
          intro ω
          split_ifs <;> norm_num
        _ = 1 := mean_const _ uniformWeight_sum _
    have hn : 0 ≤ 1 / (Fintype.card U : ℚ) := by positivity
    dsimp [c]
    linarith
  have hrow (i : I) : (∑ j, c i j) ≤ (d : ℚ) := by
    calc
      _ ≤ ∑ j, if j ∈ deps i then (1 : ℚ) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j ∈ deps i
        · simpa only [ite_eq_left hj] using hbound i j
        · simp [hj, c, hind i j hj]
      _ = ((deps i).card : ℚ) := by simp
      _ ≤ (d : ℚ) := by exact_mod_cast hcard i
  have heq : mean uniformWeight (fun ω => energy (label ω)) = ∑ i, ∑ j, c i j := by
    simp_rw [energy_eq_collisions, mean_sub, mean_sum]
    rw [mean_const _ uniformWeight_sum]
    dsimp [c]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ∑ _i : I, (d : ℚ) := Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp [mul_comm]

end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
