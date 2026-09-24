/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityInsertionPoisson

/-!
# Identification with repeated signed support insertion

The compensated count series is obtained by integrating the exact
omitted-share difference, with every subset sign retained.
-/

namespace RiemannGaussian.ZetaRieszParityInsertionPoisson
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- The order-`k` signed insertion before dividing by its factorial. -/
def rawInsertion (a : ℝ) (k : ℕ) (g : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*(-jumpMass a)^i*jumpCount a (k-i) g

theorem rawInsertion_eq (a : ℝ) (k : ℕ) (g : ℝ) :
    rawInsertion a k g = (k.factorial : ℝ)*insertion a k g := by
  rw [insertion, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by simp only [Finset.mem_range] at hi; omega
  have hf : (k.choose i : ℝ)*(i.factorial : ℝ)*((k-i).factorial : ℝ) = k.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
  have hi0 : (i.factorial : ℝ) ≠ 0 := by positivity
  have hk0 : ((k-i).factorial : ℝ) ≠ 0 := by positivity
  rw [← hf]
  field_simp

theorem rawInsertion_zero (a g : ℝ) :
    rawInsertion a 0 g = ZetaRieszZeroParityCascade.supportKernel g 0 := by
  simp [rawInsertion, jumpCount, ZetaRieszZeroParityCascade.supportKernel]

private theorem raw_weighted (a : ℝ) (k : ℕ) (g x : ℝ) :
    x⁻¹*rawInsertion a k (g-x) =
      ∑ i ∈ Finset.range (k+1), ((k.choose i : ℝ)*(-jumpMass a)^i)*
        (x⁻¹*jumpCount a (k-i) (g-x)) := by
  rw [rawInsertion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem integrable_rawInsertion {a : ℝ} (ha : 0 < a) (k : ℕ) (g : ℝ) :
    IntegrableOn (fun x : ℝ => x⁻¹*rawInsertion a k (g-x)) (Ioc a cutoff) := by
  simp_rw [raw_weighted]
  exact integrable_finsetSum _ (fun i _ => (integrable_jumpCount ha (k-i) g).const_mul _)

theorem integral_rawInsertion {a : ℝ} (ha : 0 < a) (k : ℕ) (g : ℝ) :
    (∫ x in Ioc a cutoff, x⁻¹*rawInsertion a k (g-x)) =
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*(-jumpMass a)^i*jumpCount a (k-i+1) g := by
  simp_rw [raw_weighted]
  rw [integral_finsetSum _ (fun i _ => (integrable_jumpCount ha (k-i) g).const_mul _)]
  simp_rw [integral_const_mul]
  rfl

/-- Exact integration of one additional signed omitted share. -/
theorem rawInsertion_succ {a : ℝ} (ha : 0 < a) (k : ℕ) (g : ℝ) :
    rawInsertion a (k+1) g = ∫ x in Ioc a cutoff,
      x⁻¹*(rawInsertion a k (g-x)-rawInsertion a k g) := by
  have hs := Finset.sum_choose_succ_mul
    (fun i j : ℕ => (-jumpMass a)^i*jumpCount a j g) k
  have he1 : (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*
      ((-jumpMass a)^i*jumpCount a (k+1-i) g)) =
        ∫ x in Ioc a cutoff, x⁻¹*rawInsertion a k (g-x) := by
    rw [integral_rawInsertion ha]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := by simp only [Finset.mem_range] at hi; omega
    rw [show k+1-i = k-i+1 by omega]
    ring
  have he2 : (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*
      ((-jumpMass a)^(i+1)*jumpCount a (k-i) g)) =
        -(jumpMass a*rawInsertion a k g) := by
    rw [rawInsertion, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  simp only [← mul_assoc] at hs
  change rawInsertion a (k+1) g = _ at hs
  simp only [← mul_assoc] at he1 he2
  rw [he1, he2] at hs
  rw [show (fun x : ℝ => x⁻¹*(rawInsertion a k (g-x)-rawInsertion a k g)) =
      (fun x => x⁻¹*rawInsertion a k (g-x)-x⁻¹*rawInsertion a k g) by ext; ring,
    integral_sub (integrable_rawInsertion ha k g) ((integrable_density ha).mul_const _),
    integral_mul_const]
  exact hs

/-- The supported-kernel insertion itself has this same difference law. -/
theorem insertedSupport_insert {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x : ι → ℝ) (s d : ℝ) {i : ι} (hi : i ∉ S) :
    ZetaRieszZeroParityCascade.insertedSupport (insert i S) x s d =
      ZetaRieszZeroParityCascade.insertedSupport S x (s-x i) d-
      ZetaRieszZeroParityCascade.insertedSupport S x (s-x i) (d-x i) := by
  unfold ZetaRieszZeroParityCascade.insertedSupport
  rw [Finset.sum_powerset_insert hi, Finset.sum_insert hi]
  have hh : s-(x i+∑ j ∈ S, x j) = s-x i-∑ j ∈ S, x j := by ring
  rw [hh]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  have hiA : i ∉ A := fun h => hi (Finset.mem_powerset.mp hA h)
  rw [Finset.card_insert_of_notMem hiA, Finset.sum_insert hiA, pow_succ]
  have hh2 : d-(x i+∑ j ∈ A, x j) = d-x i-∑ j ∈ A, x j := by ring
  rw [hh2]
  ring

/-- Nested integration of the exact two-shift support difference. The
moving total and cutoff coordinates are both retained. -/
def nestedSupport (a : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, s, d => ZetaRieszZeroParityCascade.supportKernel s d
  | k+1, s, d => ∫ x in Ioc a cutoff,
      x⁻¹*(nestedSupport a k (s-x) d-nestedSupport a k (s-x) (d-x))

theorem nestedSupport_eq {a : ℝ} (ha : 0 < a) (k : ℕ) (s d : ℝ) :
    nestedSupport a k s d = rawInsertion a k (s-d) := by
  induction k generalizing s d with
  | zero =>
    rw [nestedSupport, rawInsertion_zero]
    unfold ZetaRieszZeroParityCascade.supportKernel
    congr 1
    exact propext (by constructor <;> intro h <;> linarith)
  | succ k ih =>
    rw [nestedSupport, rawInsertion_succ ha]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ih, ih, show s-x-d = s-d-x by ring, show s-x-(d-x) = s-d by ring]

/-- The bounded signed count is the factorially normalised exact
support insertion, not an unrelated positive surrogate. -/
theorem insertion_eq_nestedSupport {a : ℝ} (ha : 0 < a) (k : ℕ) (s d : ℝ) :
    insertion a k (s-d) = nestedSupport a k s d/(k.factorial : ℝ) := by
  rw [nestedSupport_eq ha, rawInsertion_eq]
  field_simp

theorem jumpCount_eq_zero {a : ℝ} (_ha : 0 < a) (k : ℕ) {g : ℝ}
    (hg : (k : ℝ)*cutoff < g) : jumpCount a k g = 0 := by
  induction k generalizing g with
  | zero =>
    simp only [Nat.cast_zero, zero_mul] at hg
    simp [jumpCount, not_le.mpr hg]
  | succ k ih =>
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [ih (by push_cast at hg; nlinarith [hx.2]), mul_zero]
    rfl

theorem rawInsertion_eq_zero {a : ℝ} (ha : 0 < a) (k : ℕ) {g : ℝ}
    (hg : (k : ℝ)*cutoff < g) : rawInsertion a k g = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hki : ((k-i : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k i
  rw [jumpCount_eq_zero ha (k-i) (by
    have hc : (0 : ℝ) ≤ cutoff := by norm_num [cutoff]
    nlinarith), mul_zero]

theorem insertion_eq_zero {a : ℝ} (ha : 0 < a) (k : ℕ) {g : ℝ}
    (hg : (k : ℝ)*cutoff < g) : insertion a k g = 0 := by
  have hh := rawInsertion_eq_zero ha k hg
  rw [rawInsertion_eq] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by positivity)

theorem eleven_insertion_eq {a : ℝ} (ha : 0 < a) {g : ℝ}
    (hg : (289/1000 : ℝ) < g) : insertion a 11 g = jumpCount a 11 g/((11 : ℕ).factorial : ℝ) := by
  have hh : rawInsertion a 11 g = jumpCount a 11 g := by
    unfold rawInsertion
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i hi hi0
      have hik : 11-i ≤ 10 := by omega
      have hk : ((11-i : ℕ) : ℝ) ≤ 10 := by exact_mod_cast hik
      rw [jumpCount_eq_zero ha (11-i) (by norm_num [cutoff]; linarith), mul_zero]
    · simp
  rw [rawInsertion_eq] at hh
  apply (eq_div_iff (by positivity)).mpr
  simpa only [mul_comm] using hh

end
end RiemannGaussian.ZetaRieszParityInsertionPoisson
