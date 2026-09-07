import RiemannGaussian.EtaMoebiusTrialCoefficients
import RiemannGaussian.EtaTranslateGridError

/-!
# Exact coefficient blocks under refinement of the physical Möbius grid

The signed arithmetic primitive telescopes on every refined grid cell.
All leading and trailing coefficients omitted by reindexing are proved
zero using the actual support of that primitive. These identities retain
the entire finite coefficient vector before any square-error bound.
-/

open Complex

namespace RiemannGaussian

noncomputable section

/-- A signed coefficient indexed by its positive physical denominator, extended to all natural indices. -/
def pairedEtaMoebiusTrialEdgeCoefficient (d M : ℕ) (w : ℕ → ℝ) (m : ℕ) : ℝ :=
  pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / m) -
    pairedEtaMoebiusTrialPrimitive M w ((d : ℝ) / (m + 1 : ℝ))

/-- The denominator-indexed coefficient is the unchanged original coefficient on every actual grid point. -/
theorem pairedEtaMoebiusTrialEdgeCoefficient_eq (d M : ℕ) (w : ℕ → ℝ) (j : Fin d) :
    pairedEtaMoebiusTrialEdgeCoefficient d M w (j.1 + 1) =
      pairedEtaMoebiusTrialCoefficient d M w j := by
  simp only [pairedEtaMoebiusTrialEdgeCoefficient, pairedEtaMoebiusTrialCoefficient,
    Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]

/-- Every coefficient wholly beyond the primitive's arithmetic endpoint vanishes exactly. -/
theorem pairedEtaMoebiusTrialEdgeCoefficient_eq_zero_of_small
    {d M m : ℕ} (hm : 0 < m) (hcut : M * (m + 1) ≤ d) (w : ℕ → ℝ) :
    pairedEtaMoebiusTrialEdgeCoefficient d M w m = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hcut' : (M : ℝ) * (m + 1 : ℝ) ≤ d := by exact_mod_cast hcut
  have h₁ : (M : ℝ) ≤ (d : ℝ) / m := (le_div_iff₀ hmpos).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) M])
  have h₂ : (M : ℝ) ≤ (d : ℝ) / (m + 1 : ℝ) := (le_div_iff₀ (by positivity)).mpr hcut'
  rw [pairedEtaMoebiusTrialEdgeCoefficient,
    pairedEtaMoebiusTrialPrimitive_eq_zero_of_cutoff_le M w h₁,
    pairedEtaMoebiusTrialPrimitive_eq_zero_of_cutoff_le M w h₂, sub_self]

/-- Every coefficient below the unit physical endpoint vanishes exactly. -/
theorem pairedEtaMoebiusTrialEdgeCoefficient_eq_zero_of_large
    {d m : ℕ} (hm : d < m) (M : ℕ) (w : ℕ → ℝ) :
    pairedEtaMoebiusTrialEdgeCoefficient d M w m = 0 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hdm : (d : ℝ) < m := by exact_mod_cast hm
  have h₁ : (d : ℝ) / m < 1 := (div_lt_one hmpos).mpr hdm
  have h₂ : (d : ℝ) / (m + 1 : ℝ) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  rw [pairedEtaMoebiusTrialEdgeCoefficient,
    pairedEtaMoebiusTrialPrimitive_eq_zero_of_lt_one M w h₁,
    pairedEtaMoebiusTrialPrimitive_eq_zero_of_lt_one M w h₂, sub_self]

/-- Every active coefficient reaches the arithmetic endpoint rather than remaining in a zero part of the primitive. -/
theorem pairedEtaMoebiusTrialEdgeCoefficient_active {d M m : ℕ} (hm : 0 < m)
    {w : ℕ → ℝ} (hc : pairedEtaMoebiusTrialEdgeCoefficient d M w m ≠ 0) :
    d < M * (m + 1) := by
  by_contra h
  exact hc (pairedEtaMoebiusTrialEdgeCoefficient_eq_zero_of_small hm (by omega) w)

/-- The entire signed refined block is exactly its original coarse-grid coefficient. -/
theorem sum_pairedEtaMoebiusTrialEdgeCoefficient_block {q : ℕ} (hq : 0 < q)
    (d M j : ℕ) (w : ℕ → ℝ) :
    (∑ l ∈ Finset.range q, pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (q * (j + 1) + l)) =
      pairedEtaMoebiusTrialEdgeCoefficient d M w (j + 1) := by
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hq)
  have htel := Finset.sum_range_sub'
    (fun l : ℕ ↦ pairedEtaMoebiusTrialPrimitive M w ((d * q : ℕ) / (q * (j + 1) + l : ℝ))) q
  have heq : (∑ l ∈ Finset.range q, pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (q * (j + 1) + l)) =
      pairedEtaMoebiusTrialPrimitive M w ((d * q : ℕ) / (q * (j + 1) : ℝ)) -
        pairedEtaMoebiusTrialPrimitive M w ((d * q : ℕ) / (q * (j + 1) + q : ℝ)) := by
    simpa only [pairedEtaMoebiusTrialEdgeCoefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_zero, add_zero, add_assoc] using htel
  rw [heq, pairedEtaMoebiusTrialEdgeCoefficient]
  congr 1 <;> congr 1
  · push_cast
    field_simp
  · push_cast
    have hjreal : (j + 1 + 1 : ℝ) ≠ 0 := by positivity
    field_simp

private theorem sum_range_blocks {α : Type*} [AddCommMonoid α] (f : ℕ → α) (d q : ℕ) :
    (∑ i ∈ Finset.range (d * q), f i) =
      ∑ j ∈ Finset.range d, ∑ l ∈ Finset.range q, f (q * j + l) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    simp only [Nat.mul_comm d q]

/-- Regrouping the complete complex refinement sum preserves each coarse-grid test value and signed coefficient. -/
theorem sum_pairedEtaMoebiusTrialEdgeCoefficient_mul_block {q : ℕ} (hq : 0 < q)
    (d M : ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ) :
    (∑ i : Fin (d * q), (pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (i.1 + q) : ℂ) * F (i.1 / q)) =
      ∑ j : Fin d, (pairedEtaMoebiusTrialEdgeCoefficient d M w (j.1 + 1) : ℂ) * F j.1 := by
  have h : (∑ i ∈ Finset.range (d * q),
      (pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (i + q) : ℂ) * F (i / q)) =
        ∑ j ∈ Finset.range d, (pairedEtaMoebiusTrialEdgeCoefficient d M w (j + 1) : ℂ) * F j := by
    rw [sum_range_blocks]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (∑ l ∈ Finset.range q,
          (pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (q * (j + 1) + l) : ℂ)) * F j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l hl
        have hdiv : (q * j + l) / q = j := by
          rw [Nat.add_comm (q * j), Nat.add_mul_div_left l j hq,
            Nat.div_eq_of_lt (Finset.mem_range.mp hl), zero_add]
        rw [hdiv]
        congr 3
        ring
      _ = _ := by
        rw [← Complex.ofReal_sum, sum_pairedEtaMoebiusTrialEdgeCoefficient_block hq]
  simpa only [← Fin.sum_univ_eq_sum_range] using h

private theorem sum_range_shift_eq {α : Type*} [AddCommMonoid α] (f : ℕ → α) (d s : ℕ)
    (hfirst : ∀ i < s, f i = 0) (hlast : ∀ i < s, f (d + i) = 0) :
    (∑ i ∈ Finset.range d, f (i + s)) = ∑ i ∈ Finset.range d, f i := by
  have h₁ := Finset.sum_range_add f s d
  have h₂ := Finset.sum_range_add f d s
  have hf : (∑ i ∈ Finset.range s, f i) = 0 :=
    Finset.sum_eq_zero (fun i hi ↦ hfirst i (Finset.mem_range.mp hi))
  have hl : (∑ i ∈ Finset.range s, f (d + i)) = 0 :=
    Finset.sum_eq_zero (fun i hi ↦ hlast i (Finset.mem_range.mp hi))
  rw [hf, zero_add] at h₁
  rw [hl, add_zero] at h₂
  rw [← h₂, Nat.add_comm d s, h₁]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm i s]

/-- Shifting to complete refinement blocks preserves any full coefficient-weighted sum; every omitted boundary term is proved zero. -/
theorem sum_pairedEtaMoebiusTrialEdgeCoefficient_shift {α : Type*} [AddCommMonoid α]
    {d M q : ℕ} (hMd : M ≤ d) (hq : 0 < q) (w : ℕ → ℝ) (F : ℕ → ℝ → α)
    (hzero : ∀ m, F m 0 = 0) :
    (∑ i : Fin (d * q), F (i.1 + q) (pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (i.1 + q))) =
      ∑ i : Fin (d * q), F (i.1 + 1) (pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (i.1 + 1)) := by
  let f := fun i : ℕ ↦ F (i + 1) (pairedEtaMoebiusTrialEdgeCoefficient (d * q) M w (i + 1))
  have hf (i : ℕ) (hi : i < q - 1) : f i = 0 := by
    have hcut : M * (i + 1 + 1) ≤ d * q := by
      have hiq : i + 1 + 1 ≤ q := by omega
      exact (Nat.mul_le_mul_left M hiq).trans (Nat.mul_le_mul_right q hMd)
    dsimp only [f]
    rw [pairedEtaMoebiusTrialEdgeCoefficient_eq_zero_of_small (by omega) hcut, hzero]
  have hl (i : ℕ) (_hi : i < q - 1) : f (d * q + i) = 0 := by
    dsimp only [f]
    rw [pairedEtaMoebiusTrialEdgeCoefficient_eq_zero_of_large (by omega), hzero]
  have h := sum_range_shift_eq f (d * q) (q - 1) hf hl
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at h
  simpa only [f, show ∀ i : ℕ, i + (q - 1) + 1 = i + q from fun i ↦ by omega] using h

end

end RiemannGaussian
