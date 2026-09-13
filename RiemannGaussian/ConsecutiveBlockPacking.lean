/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorWindowEnergy
import Mathlib.Data.Fintype.Sort
import Mathlib.GroupTheory.Perm.Fin

/-!+# Consecutive blocks of arbitrary size

Average all shifts before paying for the span. For blocks of `k + 1`
ordered points, the span cost is exactly at most `k / (k + 1)` of the
enclosing range. Only the incomplete blocks at the two ends are lost.
-/

namespace RiemannGaussian.ConsecutiveBlockPacking
noncomputable section
open scoped BigOperators

/-- Number of complete blocks after an initial shift. -/
def count (n k r : ℕ) : ℕ := (n - r) / (k + 1)

/-- Sum of the spans of complete consecutive blocks at one shift. -/
def spanSum (x : ℕ → ℝ) (n k r : ℕ) : ℝ :=
  ∑ b : Fin (count n k r),
    (x (r + (k + 1) * (b : ℕ) + k) - x (r + (k + 1) * (b : ℕ)))

/-- Every position of a complete block belongs to the original list. -/
theorem index_lt {n k r : ℕ} (b : Fin (count n k r)) (j : Fin (k + 1)) :
    r + (k + 1) * (b : ℕ) + (j : ℕ) < n := by
  have hb : (b : ℕ) < (n - r) / (k + 1) := b.isLt
  have hr : r ≤ n := by
    by_contra h
    have hz : n - r = 0 := by omega
    simp [hz] at hb
  have hmul := Nat.mul_le_mul_left (k + 1) (Nat.succ_le_of_lt hb)
  have hdiv := Nat.mul_div_le (n - r) (k + 1)
  have hbound : (k + 1) * ((b : ℕ) + 1) ≤ n - r := by
    simpa only [Nat.mul_comm (k + 1)] using hmul.trans hdiv
  nlinarith [j.isLt, Nat.sub_add_cancel hr]

/-- The start indices of all shifted complete blocks are distinct. -/
theorem all_starts_injective (n k : ℕ) : Function.Injective
    (fun p : Σ r : Fin (k + 1), Fin (count n k r) =>
      (p.1 : ℕ) + (k + 1) * (p.2 : ℕ)) := by
  rintro ⟨r, b⟩ ⟨r', b'⟩ h
  have hrval : (r : ℕ) = r' := by
    have hmod := congrArg (fun t => t % (k + 1)) h
    simpa only [Nat.add_mod, Nat.mul_mod_right, add_zero,
      Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt r'.isLt] using hmod
  have hr : r = r' := Fin.ext hrval
  subst r'
  have hb : b = b' := by
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) (Nat.add_left_cancel h)
  subst b'
  rfl

/-- Summing all shifts charges each complete-window start at most once. -/
theorem sum_translates_le (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (n k : ℕ) :
    (∑ r : Fin (k + 1), ∑ b : Fin (count n k r),
      f ((r : ℕ) + (k + 1) * (b : ℕ))) ≤
        ∑ i ∈ Finset.range (n - k), f i := by
  classical
  let start : (Σ r : Fin (k + 1), Fin (count n k r)) → ℕ :=
    fun p => (p.1 : ℕ) + (k + 1) * (p.2 : ℕ)
  have hsum : (∑ r : Fin (k + 1), ∑ b : Fin (count n k r),
      f ((r : ℕ) + (k + 1) * (b : ℕ))) = ∑ p, f (start p) :=
    (Fintype.sum_sigma (fun p => f (start p))).symm
  rw [hsum]
  change (∑ p, f (start p)) ≤ _
  rw [← Finset.sum_image (all_starts_injective n k).injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨⟨r, b⟩, _, rfl⟩ := Finset.mem_image.mp hi
    have h := index_lt b (Fin.last k)
    simp only [Finset.mem_range, Fin.val_last] at h ⊢
    omega
  · intro i _ _
    exact hf i

/-- Keeping every shift until after telescoping yields the sharp total
span budget for arbitrary block size. -/
theorem sum_spanSum_le (x : ℕ → ℝ) (hx : Monotone x) (n k : ℕ) :
    (∑ r : Fin (k + 1), spanSum x n k r) ≤
      (k : ℝ) * (x (n - 1) - x 0) := by
  have hstart := sum_translates_le (fun i => x (i + k) - x i)
    (fun i => sub_nonneg.mpr (hx (by omega))) n k
  change (∑ r : Fin (k + 1), spanSum x n k r) ≤ _ at hstart
  by_cases hkn : k ≤ n
  · have hpressure := MontgomeryTaylorWindowEnergy.sum_windowPressure_le
      (fun _ => (1 : ℝ)) x hx hkn (fun _ _ => zero_le_one)
    have htelescope : ∀ start,
        MontgomeryTaylorWindowEnergy.windowPressure (fun _ => 1) x k start =
          x (start + k) - x start := by
      intro start
      simp only [MontgomeryTaylorWindowEnergy.windowPressure, one_mul]
      have h := MontgomeryTaylorWindowEnergy.sum_gaps (fun i => x (start + i)) k
      simpa only [Nat.add_zero, ← Nat.add_assoc] using h
    simp_rw [htelescope] at hpressure
    simpa using hstart.trans hpressure
  · have hz : n - k = 0 := by omega
    simp only [hz, Finset.range_zero, Finset.sum_empty] at hstart
    exact hstart.trans (mul_nonneg (Nat.cast_nonneg k)
      (sub_nonneg.mpr (hx (Nat.zero_le _))))

/-- At least one shift pays at most the average span cost. -/
theorem exists_spanSum_le (x : ℕ → ℝ) (hx : Monotone x) (n k : ℕ) :
    ∃ r : Fin (k + 1),
      (k + 1 : ℕ) * spanSum x n k r ≤ (k : ℝ) * (x (n - 1) - x 0) := by
  have hsum := mul_le_mul_of_nonneg_left (sum_spanSum_le x hx n k)
    (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ (k + 1 : ℕ))
  have hcompare :
      (∑ r : Fin (k + 1), (k + 1 : ℕ) * spanSum x n k r) ≤
        ∑ _r : Fin (k + 1), (k : ℝ) * (x (n - 1) - x 0) := by
    simpa only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_left_comm] using hsum
  obtain ⟨r, _, hr⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (k + 1))).Nonempty) hcompare
  exact ⟨r, hr⟩

/-- Completing a partition requires at most `k` zero padding columns. -/
theorem ceiling_bounds (n k : ℕ) :
    n ≤ (k + 1) * ((n + k) / (k + 1)) ∧
      (k + 1) * ((n + k) / (k + 1)) - n ≤ k := by
  have hdiv := Nat.mod_add_div (n + k) (k + 1)
  have hmod : (n + k) % (k + 1) < k + 1 := Nat.mod_lt _ (by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hdiv ⊢
  omega

/-- At most `k` initial and `k` final points are omitted by one shift. -/
theorem count_coverage (n k : ℕ) (r : Fin (k + 1)) :
    n ≤ (k + 1) * count n k r + 2 * k := by
  have hdiv := Nat.mod_add_div (n - r) (k + 1)
  have hmod : (n - r) % (k + 1) < k + 1 := Nat.mod_lt _ (by omega)
  unfold count
  simp only [Nat.add_mul, Nat.one_mul] at hdiv ⊢
  omega

/-- The complete blocks selected from a sublist fit in the full padded
partition of the enclosing list. -/
theorem count_le_ceiling {m n k r : ℕ} (hmn : m ≤ n) :
    count m k r ≤ (n + k) / (k + 1) := by
  apply Nat.div_le_div_right
  omega

/-- Within one shift, different block positions are different list indices. -/
theorem index_injective (k r q : ℕ) : Function.Injective
    (fun p : Fin (k + 1) × Fin q =>
      r + (k + 1) * (p.2 : ℕ) + (p.1 : ℕ)) := by
  rintro ⟨j, b⟩ ⟨j', b'⟩ h
  change r + (k + 1) * (b : ℕ) + (j : ℕ) =
    r + (k + 1) * (b' : ℕ) + (j' : ℕ) at h
  have h0 : (k + 1) * (b : ℕ) + (j : ℕ) =
      (k + 1) * (b' : ℕ) + (j' : ℕ) := by omega
  have hjval : (j : ℕ) = j' := by
    have hmod := congrArg (fun t => t % (k + 1)) h0
    simpa [Nat.add_mod, Nat.mod_eq_of_lt j.isLt,
      Nat.mod_eq_of_lt j'.isLt] using hmod
  have hj : j = j' := Fin.ext hjval
  subst j'
  have hb : b = b' := Fin.ext
    (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) (Nat.add_right_cancel h0))
  exact Prod.ext rfl hb

/-- Consecutive blocks in the increasing enumeration of a finite set. -/
def orderEmbedding {α : Type*} [LinearOrder α]
    (s : Finset α) (k r : ℕ) : Fin (k + 1) × Fin (count s.card k r) ↪ α :=
  let index : Fin (k + 1) × Fin (count s.card k r) ↪ Fin s.card :=
    { toFun := fun p =>
        ⟨r + (k + 1) * (p.2 : ℕ) + (p.1 : ℕ), index_lt p.2 p.1⟩
      inj' := fun _ _ h => index_injective k r _ (Fin.ext_iff.mp h) }
  index.trans (s.orderEmbOfFin rfl).toEmbedding

/-- Every selected block position lies in the original finite set. -/
theorem orderEmbedding_mem {α : Type*} [LinearOrder α]
    (s : Finset α) (k r : ℕ) (p : Fin (k + 1) × Fin (count s.card k r)) :
    orderEmbedding s k r p ∈ s :=
  Finset.orderEmbOfFin_mem s rfl _

/-- The positions within a selected block remain in increasing order. -/
theorem orderEmbedding_monotone {α : Type*} [LinearOrder α]
    (s : Finset α) (k r : ℕ) (b : Fin (count s.card k r)) :
    Monotone (fun j => orderEmbedding s k r (j, b)) := by
  intro i j hij
  apply (s.orderEmbOfFin rfl).monotone
  apply Fin.mk_le_mk.mpr
  change r + (k + 1) * (b : ℕ) + (i : ℕ) ≤
    r + (k + 1) * (b : ℕ) + (j : ℕ)
  omega

/-- A sorted finite set admits a shift with the sharp average span cost
for blocks of any fixed positive size. -/
theorem exists_orderEmbedding_span_le {α : Type*} [LinearOrder α]
    (s : Finset α) (v : α → ℝ) (hv : Monotone v) (k : ℕ)
    {lo hi : ℝ} (hlohi : lo ≤ hi)
    (hbounds : ∀ z ∈ s, lo ≤ v z ∧ v z ≤ hi) :
    ∃ r : Fin (k + 1),
      (k + 1 : ℕ) * (∑ b : Fin (count s.card k r),
        (v (orderEmbedding s k r (Fin.last k, b)) -
          v (orderEmbedding s k r (0, b)))) ≤ (k : ℝ) * (hi - lo) := by
  by_cases hs0 : s.card = 0
  · refine ⟨0, ?_⟩
    have : IsEmpty (Fin (count s.card k (0 : Fin (k + 1)))) :=
      ⟨fun b => by simpa [count, hs0] using b.isLt⟩
    rw [Finset.sum_of_isEmpty, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hlohi)
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hs0
  let cap : ℕ → Fin s.card := fun n => ⟨min n M, by omega⟩
  let x : ℕ → ℝ := fun n => v (s.orderEmbOfFin rfl (cap n))
  have hx : Monotone x := by
    intro a b hab
    apply hv
    apply (s.orderEmbOfFin rfl).monotone
    apply Fin.mk_le_mk.mpr
    exact min_le_min hab le_rfl
  obtain ⟨r, hspan⟩ := exists_spanSum_le x hx s.card k
  have hxapply : ∀ (j : Fin (k + 1)) (b : Fin (count s.card k r)),
      x ((r : ℕ) + (k + 1) * (b : ℕ) + (j : ℕ)) =
        v (orderEmbedding s k r (j, b)) := by
    intro j b
    have hidx := index_lt b j
    have hleM : (r : ℕ) + (k + 1) * (b : ℕ) + (j : ℕ) ≤ M := by omega
    simp only [x, cap, Nat.min_eq_left hleM,
      orderEmbedding, Function.Embedding.trans_apply]
    rfl
  have hsum : spanSum x s.card k r =
      ∑ b : Fin (count s.card k r),
        (v (orderEmbedding s k r (Fin.last k, b)) -
          v (orderEmbedding s k r (0, b))) := by
    unfold spanSum
    apply Finset.sum_congr rfl
    intro b _
    have he := hxapply (Fin.last k) b
    have hs := hxapply 0 b
    simp only [Fin.val_last, Fin.val_zero, Nat.add_zero] at he hs
    rw [he, hs]
  have hfirst := hbounds (s.orderEmbOfFin rfl (cap 0))
    (Finset.orderEmbOfFin_mem s rfl _)
  have hlast := hbounds (s.orderEmbOfFin rfl (cap (s.card - 1)))
    (Finset.orderEmbOfFin_mem s rfl _)
  have hfull : x (s.card - 1) - x 0 ≤ hi - lo := by
    change v (s.orderEmbOfFin rfl (cap (s.card - 1))) -
      v (s.orderEmbOfFin rfl (cap 0)) ≤ _
    linarith [hfirst.1, hlast.2]
  refine ⟨r, ?_⟩
  rw [← hsum]
  exact hspan.trans (mul_le_mul_of_nonneg_left hfull (Nat.cast_nonneg k))

/-- Extend any injective selected-block family to a complete partition,
adding only the usual ceiling remainder as zero columns. -/
theorem exists_paddedEquiv_extending {α : Type*} [Fintype α]
    (k q : ℕ) (hq : q ≤ (Fintype.card α + k) / (k + 1))
    (f : Fin (k + 1) × Fin q ↪ α) :
    ∃ e : Fin (k + 1) × Fin ((Fintype.card α + k) / (k + 1)) ≃
        Sum α (Fin ((k + 1) * ((Fintype.card α + k) / (k + 1)) - Fintype.card α)),
      ∀ j b, e (j, Fin.castLE hq b) = Sum.inl (f (j, b)) := by
  classical
  let Q := (Fintype.card α + k) / (k + 1)
  let pad := (k + 1) * Q - Fintype.card α
  have hnQ : Fintype.card α ≤ (k + 1) * Q := (ceiling_bounds _ _).1
  have hcard : Fintype.card (Fin (k + 1) × Fin Q) =
      Fintype.card (Sum α (Fin pad)) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum, pad]
    omega
  let e0 : Fin (k + 1) × Fin Q ≃ Sum α (Fin pad) := Fintype.equivOfCardEq hcard
  let u : Fin (k + 1) × Fin q → Fin (k + 1) × Fin Q :=
    fun p => (p.1, Fin.castLE hq p.2)
  have hu : Function.Injective u := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab
    simpa only [u, Prod.mk.injEq, Fin.castLE_inj] using hab
  let g : Fin (k + 1) × Fin q → Sum α (Fin pad) := fun p => Sum.inl (f p)
  have hg : Function.Injective g := Sum.inl_injective.comp f.injective
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun p => e0 (u p)) g (e0.injective.comp hu) hg
  refine ⟨e0.trans σ, ?_⟩
  intro j b
  exact hσ (j, b)

end
end RiemannGaussian.ConsecutiveBlockPacking
