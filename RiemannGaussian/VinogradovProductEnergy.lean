/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovResidueEnergy

/-!
# Actual conditioned product energy and the finite mixed-moment maximum

An exact bijection identifies each original conditioned block fibre with
its product of literal residue windows. Weighted product identities keep
arbitrary complex tail weights, including correlations and restrictions
between tail entries. The whole-moment theorem then reaches the actual
residue-polynomial product without a factorization premise.

The explicit finer-residue count and a weighted finite mean inequality
bound this energy by the maximum of actual single-residue mixed moments.
The endpoint has no unproved moment-budget premise. It supplies the product
and first finite Holder ingredients following Wooley (2012), equation (6.6).
The subsequent interpolation, singular conditioning, high-moment iteration
and Vinogradov--Korobov analytic saving still need their own proofs.
-/

namespace RiemannGaussian.VinogradovProductEnergy
noncomputable section
open scoped BigOperators Classical
open MeasureTheory UnitAddTorus VinogradovResidueEnergy VinogradovMomentPartition VinogradovPartitionEnergy

/-- The original conditioned block fibre with one complete finer residue tuple. -/
abbrev FineWindow (p k a b xi X : ℕ) [NeZero p] (c : GoodResidue p k a b xi) :=
  {x : ConditionedWindow p k a xi X //
    residueTuple (p := p) (b := b) (fun j => (x.val j).val + 1) = c.val}

/-- Every original block in a fixed finer fibre corresponds exactly to a
coordinate product of actual positive residue windows, with every entry retained. -/
def fineWindowEquiv {p k a b xi X : ℕ} [NeZero p]
    (ha : a + 1 ≤ k * b) (c : GoodResidue p k a b xi) :
    FineWindow p k a b xi X c ≃
      ((j : Fin k) → VinogradovResidueMoment.ResidueWindow (p ^ (k * b)) (c.val j).val X) where
  toFun x := fun j => ⟨x.val.val j, congrArg Fin.val (congrFun x.property j)⟩
  invFun n := by
    have he : residueTuple (p := p) (b := b) (fun j => (n j).val.val + 1) = c.val := by
      funext j
      apply Fin.ext
      exact (n j).property
    refine ⟨⟨fun j => (n j).val, ?_, ?_⟩, he⟩
    · intro j
      have hj := c.property.1 j
      rw [← he] at hj
      simpa only [residueTuple_class (by omega : a ≤ k * b)] using hj
    · intro j l hjl
      apply c.property.2
      rw [← he]
      simpa only [residueTuple_digit ha] using hjl
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv n := by
    funext j
    apply Subtype.ext
    rfl

/-- Expand the actual signed product into its full tuple frequencies exactly. -/
theorem product_residuePolynomial {p k a b xi X : ℕ}
    (c : GoodResidue p k a b xi) (colour : Fin k → Bool)
    (theta : UnitAddTorus (Fin k)) :
    VinogradovCongruenceEnergy.coarseSignedProduct X colour theta c.val =
      ∑ n : ((j : Fin k) → VinogradovResidueMoment.ResidueWindow (p ^ (k * b)) (c.val j).val X),
        mFourier (fun i => ∑ j, VinogradovSignedCongruence.sign (colour j) *
          ((n j).val.val + 1 : ℤ) ^ (i.val + 1)) theta := by
  unfold VinogradovCongruenceEnergy.coarseSignedProduct VinogradovCongruenceEnergy.residuePolynomial
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [VinogradovMeanValue.product_mFourier]
  apply congrArg (fun v : Fin k → ℤ => mFourier v theta)
  funext i
  simp only [Finset.sum_apply, VinogradovMeanValue.monomialFrequency, Nat.cast_add, Nat.cast_one]


/-- Restricting the original complex weight to a target is exactly a sum
over that full fibre, before any estimate or product factorization. -/
theorem target_polynomial_eq_subtype {ι κ d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (label : ι → κ) (c : κ) (theta : UnitAddTorus d) :
    polynomial v (targetWeight label w c) theta =
      ∑ z : {z : ι // label z = c}, w z.val * mFourier (v z.val) theta := by
  unfold polynomial targetWeight
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The actual conditioned block polynomial on a finer fibre is exactly
the product of its literal residue-window sums, with all signs retained. -/
theorem fine_block_polynomial_eq_product {p k a b xi X : ℕ} [NeZero p]
    (ha : a + 1 ≤ k * b) (c : GoodResidue p k a b xi) (colour : Fin k → Bool)
    (theta : UnitAddTorus (Fin k)) :
    polynomial (fun x : ConditionedWindow p k a xi X => fun i =>
      ∑ j, VinogradovSignedCongruence.sign (colour j) * ((x.val j).val + 1 : ℤ) ^ (i.val + 1))
      (targetWeight (fun x => residueTuple (p := p) (b := b) (fun j => (x.val j).val + 1))
        (fun _ => 1) c.val) theta =
      VinogradovCongruenceEnergy.coarseSignedProduct X colour theta c.val := by
  classical
  let : Fintype (FineWindow p k a b xi X c) :=
    @Subtype.fintype _ _ (fun _ => Classical.propDecidable _) _
  rw [target_polynomial_eq_subtype, product_residuePolynomial]
  simp only [one_mul]
  apply Fintype.sum_equiv (fineWindowEquiv (X := X) ha c)
  intro x
  rfl


/-- Independent weighted factors retain their full complex product and
complete summed frequencies, before taking any norm. -/
theorem polynomial_prod {α β d : Type*} [Fintype α] [Fintype β] [Fintype d]
    (v : α → d → ℤ) (u : β → d → ℤ) (w : α → ℂ) (z : β → ℂ)
    (theta : UnitAddTorus d) :
    polynomial (fun x : α × β => v x.1 + u x.2) (fun x => w x.1 * z x.2) theta =
      polynomial v w theta * polynomial u z theta := by
  unfold polynomial
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [mFourier_add]
  ring

/-- The unweighted full tail polynomial factors into its literal residue
sums with the original integer coefficients, without dropping a phase. -/
theorem tail_polynomial_eq_product {p k b r X : ℕ} (eta : ℤ) (tau : Fin r → ℤ)
    (theta : UnitAddTorus (Fin k)) :
    polynomial (fun u : Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X =>
        fun i => ∑ j, tau j * ((u j).val.val + 1 : ℤ) ^ (i.val + 1)) (fun _ => 1) theta =
      ∏ j, VinogradovCongruenceEnergy.residuePolynomial (p ^ b) (eta : ZMod (p ^ b)).val X k (tau j) theta := by
  unfold polynomial VinogradovCongruenceEnergy.residuePolynomial
  rw [Fintype.prod_sum]
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [VinogradovMeanValue.product_mFourier]
  apply congrArg (fun v : Fin k → ℤ => mFourier v theta)
  funext i
  simp only [Finset.sum_apply, VinogradovMeanValue.monomialFrequency, Nat.cast_add, Nat.cast_one]


/-- The full signed power vector of one original conditioned positive block. -/
def blockFrequency {p k a xi X : ℕ} (colour : Fin k → Bool)
    (x : ConditionedWindow p k a xi X) : Fin k → ℤ :=
  fun i => ∑ j, VinogradovSignedCongruence.sign (colour j) * ((x.val j).val + 1 : ℤ) ^ (i.val + 1)

/-- The original full integer-weighted tail frequency on the actual window. -/
def tailFrequency {p k b r X : ℕ} {eta : ℤ} (tau : Fin r → ℤ)
    (u : Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X) : Fin k → ℤ :=
  fun i => ∑ j, tau j * ((u j).val.val + 1 : ℤ) ^ (i.val + 1)

/-- The original configuration frequency is the sum of its block and tail
vectors, with the positive-integer convention preserved exactly. -/
theorem windowFrequency_eq_add {p k a b r xi X : ℕ} (eta : ℤ)
    (colour : Fin k → Bool) (tau : Fin r → ℤ) :
    windowFrequency (p := p) (a := a) (b := b) (xi := xi) (X := X) (eta := eta) colour tau =
      (fun z : WindowConfiguration p k a b r xi X eta =>
        blockFrequency colour z.1 + tailFrequency tau z.2) := by
  funext z i
  simp only [windowFrequency, mixedFrequency, blockFrequency, tailFrequency, windowBlock,
    Nat.cast_add, Nat.cast_one, Pi.add_apply]

/-- The full original window factors with arbitrary complex tail weights;
all correlations and joint restrictions inside that tail weight survive. -/
theorem window_polynomial_eq_product {p k a b r xi X : ℕ} (eta : ℤ)
    (colour : Fin k → Bool) (tau : Fin r → ℤ)
    (w : (Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X) → ℂ)
    (theta : UnitAddTorus (Fin k)) :
    polynomial (windowFrequency (p := p) (a := a) (b := b) (xi := xi) (X := X) (eta := eta) colour tau) (fun z => w z.2) theta =
      polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta *
        polynomial (tailFrequency tau) w theta := by
  rw [windowFrequency_eq_add]
  simpa only [one_mul] using polynomial_prod (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour)
    (tailFrequency tau) (fun _ => 1) w theta

/-- A full finer-residue window polynomial factors into the actual signed
block product and the original arbitrarily weighted tail polynomial. -/
theorem window_fine_polynomial_eq_product {p k a b r xi X : ℕ} [NeZero p]
    (ha : a + 1 ≤ k * b) (c : GoodResidue p k a b xi) (eta : ℤ)
    (colour : Fin k → Bool) (tau : Fin r → ℤ)
    (w : (Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X) → ℂ)
    (theta : UnitAddTorus (Fin k)) :
    polynomial (windowFrequency (p := p) (a := a) (b := b) (xi := xi) (X := X) (eta := eta) colour tau)
      (targetWeight (fun z => residueTuple (p := p) (b := b) (windowBlock z)) (fun z => w z.2) c.val) theta =
      VinogradovCongruenceEnergy.coarseSignedProduct X colour theta c.val *
        polynomial (tailFrequency tau) w theta := by
  let wb := targetWeight (fun x : ConditionedWindow p k a xi X =>
    residueTuple (p := p) (b := b) (fun j => (x.val j).val + 1)) (fun _ => (1 : ℂ)) c.val
  have hw : targetWeight (fun z => residueTuple (p := p) (b := b) (windowBlock z)) (fun z => w z.2) c.val =
      (fun z : WindowConfiguration p k a b r xi X eta => wb z.1 * w z.2) := by
    funext z
    unfold wb targetWeight
    split_ifs with h₁ h₂ h₂
    · simp
    · exact False.elim (h₂ h₁)
    · exact False.elim (h₁ h₂)
    · simp
  rw [hw, windowFrequency_eq_add, polynomial_prod]
  rw [show polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) wb theta =
      VinogradovCongruenceEnergy.coarseSignedProduct X colour theta c.val from
    fine_block_polynomial_eq_product ha c colour theta]


/-- Use the normalized Haar measure of the original moment identities. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The circle Haar measure used by the original moments has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The proved signed congruence count controls the full original product
energy, with actual residue factors and arbitrary complex tail correlations. -/
theorem conditioned_product_energy_le {p k a b r xi X : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (eta : ℤ)
    (colour : Fin k → Bool) (tau : Fin r → ℤ)
    (w : (Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X) → ℂ) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta *
        polynomial (tailFrequency tau) w theta‖ ^ 2) ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
      ∑ c : GoodResidue p k a b xi, ∫ theta : UnitAddTorus (Fin k),
        ‖VinogradovCongruenceEnergy.coarseSignedProduct X colour theta c.val *
          polynomial (tailFrequency tau) w theta‖ ^ 2 := by
  have ha : a + 1 ≤ k * b := by
    calc
      a + 1 ≤ b := hab
      _ ≤ k * b := by simpa only [Nat.mul_comm k b] using Nat.le_mul_of_pos_right b hk
  simpa only [window_polynomial_eq_product, window_fine_polynomial_eq_product ha] using
    window_whole_integral_le (xi := xi) hkp hk hab eta colour tau (fun z => w z.2)

/-- Only after the exact complex product identities, sign reversal
identifies each block-factor norm while retaining the full weighted tail. -/
theorem conditioned_product_norm_energy_le {p k a b r xi X : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (eta : ℤ)
    (colour : Fin k → Bool) (tau : Fin r → ℤ)
    (w : (Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X) → ℂ) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta‖ ^ 2 *
        ‖polynomial (tailFrequency tau) w theta‖ ^ 2) ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
      ∑ c : GoodResidue p k a b xi, ∫ theta : UnitAddTorus (Fin k),
        (∏ j, ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) (c.val j).val X k 1 theta‖ ^ 2) *
          ‖polynomial (tailFrequency tau) w theta‖ ^ 2 := by
  simpa only [norm_mul, mul_pow, VinogradovCongruenceEnergy.coarseSignedProduct_norm_sq] using
    conditioned_product_energy_le (xi := xi) hkp hk hab eta colour tau w


/-- The finite mean inequality bounds the product by its average k-th
powers, including zero entries and every positive number of factors. -/
theorem product_le_mean_powers {k : ℕ} (hk : 0 < k) (f : Fin k → ℝ)
    (hf : ∀ j, 0 ≤ f j) :
    ∏ j, f j ≤ (1 / (k : ℝ)) * ∑ j, f j ^ k := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hw : ∑ _ : Fin k, (1 / (k : ℝ)) = 1 := by simp [hkR]
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin k => 1 / (k : ℝ)) (fun j => f j ^ k)
    (fun _ _ => by positivity) hw (fun j _ => pow_nonneg (hf j) _)
  have hp (j : Fin k) : (f j ^ k) ^ (1 / (k : ℝ)) = f j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hf j), mul_one_div_cancel hkR, Real.rpow_one]
  simpa only [hp, ← Finset.mul_sum] using h

/-- Exact quotient injection bounds all finer residue tuples in the
original coarse class, paying every remaining coordinate choice. -/
theorem goodResidue_card_le {p k a b xi : ℕ} [Fact p.Prime] (ha : a ≤ k * b) :
    Fintype.card (GoodResidue p k a b xi) ≤ (p ^ (k * b - a)) ^ k := by
  let f (c : GoodResidue p k a b xi) : Fin k → Fin (p ^ (k * b - a)) :=
    fun j => VinogradovCoarseCongruence.coarseQuotient ha (c.val j)
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    exact VinogradovCoarseCongruence.coarse_quotient_injective ha xi
      c.property.1 d.property.1 he
  simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective f hf


/-- A common bound on the weighted k-th powers controls the weighted
product integral. All continuity, integrability and sum exchanges are paid. -/
theorem integral_product_mul_le_of_uniform {k : ℕ} {d : Type*} [Fintype d]
    (hk : 0 < k) (f : Fin k → UnitAddTorus d → ℝ) (g : UnitAddTorus d → ℝ)
    (hf : ∀ j, Continuous (f j)) (hg : Continuous g)
    (hf0 : ∀ j theta, 0 ≤ f j theta) (hg0 : ∀ theta, 0 ≤ g theta)
    (B : ℝ) (hB : ∀ j, (∫ theta : UnitAddTorus d, f j theta ^ k * g theta) ≤ B) :
    (∫ theta : UnitAddTorus d, (∏ j, f j theta) * g theta) ≤ B := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hi (j) : Integrable (fun theta : UnitAddTorus d => f j theta ^ k * g theta) :=
    (((hf j).pow k).mul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi0 : Integrable (fun theta : UnitAddTorus d => (∏ j, f j theta) * g theta) := by
    apply Continuous.integrable_of_hasCompactSupport (hcf := HasCompactSupport.of_compactSpace _)
    fun_prop
  have hn : 0 ≤ 1 / (k : ℝ) := by positivity
  calc
    (∫ theta : UnitAddTorus d, (∏ j, f j theta) * g theta) ≤
        ∫ theta : UnitAddTorus d, (1 / (k : ℝ)) * ∑ j, f j theta ^ k * g theta := by
      apply integral_mono hi0 ((integrable_finsetSum _ (fun j _ => hi j)).const_mul _)
      intro theta
      calc
        (∏ j, f j theta) * g theta ≤ ((1 / (k : ℝ)) * ∑ j, f j theta ^ k) * g theta :=
          mul_le_mul_of_nonneg_right (product_le_mean_powers hk _ (fun j => hf0 j theta)) (hg0 theta)
        _ = (1 / (k : ℝ)) * ∑ j, f j theta ^ k * g theta := by rw [mul_assoc, Finset.sum_mul]
    _ = (1 / (k : ℝ)) * ∑ j, ∫ theta : UnitAddTorus d, f j theta ^ k * g theta := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)]
    _ ≤ (1 / (k : ℝ)) * ∑ _ : Fin k, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hB j)) hn
    _ = B := by simp [hkR]


/-- The actual signed count and finite mean inequality reduce the whole
conditioned product to a uniform single-residue mixed-moment budget.
The next theorem supplies the budget as an actual finite maximum. -/
theorem conditioned_product_uniform_le {p k a b r xi X : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (eta : ℤ)
    (colour : Fin k → Bool) (tau : Fin r → ℤ)
    (w : (Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X) → ℂ)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ c : Fin (p ^ (k * b)), c.val % p ^ a = xi →
      (∫ theta : UnitAddTorus (Fin k),
        ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) c.val X k 1 theta‖ ^ (2 * k) *
          ‖polynomial (tailFrequency tau) w theta‖ ^ 2) ≤ B) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta‖ ^ 2 *
        ‖polynomial (tailFrequency tau) w theta‖ ^ 2) ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
        ((p ^ (k * b - a)) ^ k : ℕ) * B := by
  have htail := ((continuous_polynomial (tailFrequency (k := k) tau) w).norm).pow 2
  have hf (c : Fin (p ^ (k * b))) : Continuous (fun theta : UnitAddTorus (Fin k) =>
      ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) c.val X k 1 theta‖ ^ 2) := by
    unfold VinogradovCongruenceEnergy.residuePolynomial
    fun_prop
  have hb (c : GoodResidue p k a b xi) :
      (∫ theta : UnitAddTorus (Fin k),
        (∏ j, ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) (c.val j).val X k 1 theta‖ ^ 2) *
          ‖polynomial (tailFrequency tau) w theta‖ ^ 2) ≤ B := by
    apply integral_product_mul_le_of_uniform hk _ _ (fun j => hf (c.val j)) htail
      (fun j theta => sq_nonneg _) (fun theta => sq_nonneg _)
    intro j
    simpa only [← pow_mul, Pi.pow_apply] using hB (c.val j) (c.property.1 j)
  have ha : a ≤ k * b := by
    calc
      a ≤ b := hab.le
      _ ≤ k * b := by simpa only [Nat.mul_comm k b] using Nat.le_mul_of_pos_right b hk
  have hcard : (Fintype.card (GoodResidue p k a b xi) : ℝ) ≤ ((p ^ (k * b - a)) ^ k : ℕ) := by
    exact_mod_cast goodResidue_card_le (xi := xi) ha
  have hs : (∑ c : GoodResidue p k a b xi, ∫ theta : UnitAddTorus (Fin k),
        (∏ j, ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) (c.val j).val X k 1 theta‖ ^ 2) *
          ‖polynomial (tailFrequency tau) w theta‖ ^ 2) ≤
      ((p ^ (k * b - a)) ^ k : ℕ) * B := by
    calc
      _ ≤ ∑ _ : GoodResidue p k a b xi, B := Finset.sum_le_sum (fun c _ => hb c)
      _ = (Fintype.card (GoodResidue p k a b xi) : ℝ) * B := by simp
      _ ≤ ((p ^ (k * b - a)) ^ k : ℕ) * B := mul_le_mul_of_nonneg_right hcard hB0
  exact (conditioned_product_norm_energy_le (xi := xi) hkp hk hab eta colour tau w).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (by positivity :
      (0 : ℝ) ≤ ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ)))


/-- The literal finite maximum of single-residue mixed torus moments,
retaining the original arbitrary complex tail weight and every finer residue. -/
def fineMomentMaximum {p k b r X : ℕ} [NeZero p] {eta : ℤ} (tau : Fin r → ℤ)
    (w : (Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X) → ℂ) : ℝ :=
  (Finset.univ : Finset (Fin (p ^ (k * b)))).sup' Finset.univ_nonempty (fun c =>
    ∫ theta : UnitAddTorus (Fin k),
      ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) c.val X k 1 theta‖ ^ (2 * k) *
        ‖polynomial (tailFrequency tau) w theta‖ ^ 2)

/-- The full original conditioned product is bounded by an explicit
prime-power and sign-factorial cost times its actual mixed-moment maximum.
No moment-budget hypothesis is assumed; the later analytic saving remains open. -/
theorem conditioned_product_max_le {p k a b r xi X : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (eta : ℤ)
    (colour : Fin k → Bool) (tau : Fin r → ℤ)
    (w : (Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X) → ℂ) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta‖ ^ 2 *
        ‖polynomial (tailFrequency tau) w theta‖ ^ 2) ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
        ((p ^ (k * b - a)) ^ k : ℕ) * fineMomentMaximum (k := k) tau w := by
  have hm (c : Fin (p ^ (k * b))) :
      (∫ theta : UnitAddTorus (Fin k),
        ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) c.val X k 1 theta‖ ^ (2 * k) *
          ‖polynomial (tailFrequency tau) w theta‖ ^ 2) ≤ fineMomentMaximum (k := k) tau w := by
    unfold fineMomentMaximum
    exact Finset.le_sup' (fun z : Fin (p ^ (k * b)) =>
      ∫ theta : UnitAddTorus (Fin k),
        ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ (k * b)) z.val X k 1 theta‖ ^ (2 * k) *
          ‖polynomial (tailFrequency tau) w theta‖ ^ 2) (Finset.mem_univ c)
  apply conditioned_product_uniform_le hkp hk hab eta colour tau w _ ?_ (fun c _ => hm c)
  exact (integral_nonneg (fun theta => mul_nonneg (by positivity) (sq_nonneg _))).trans (hm 0)

end
end RiemannGaussian.VinogradovProductEnergy
