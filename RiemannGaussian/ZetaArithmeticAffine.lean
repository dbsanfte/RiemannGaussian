/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszConditionedEnergy
import RiemannGaussian.ZetaSquarefreeEulerMarks
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Exact affine operations and the original signed arithmetic correlations

Translation and multiplication preserve every complex coefficient. Exact
collisions have a gcd compatibility criterion, and all lag correlations
recombine to the original Riesz carrier square. Affine pushforward preserves
total mass, so orthogonality alone supplies no bound for the carrier.
-/

namespace RiemannGaussian.ZetaArithmeticAffine
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory Set Filter Topology

/-- A finite complex arithmetic vector, with integers as its exact labels. -/
abbrev ArithmeticVector := ℤ →₀ ℂ

/-- Push each coefficient along the actual map n ↦ b*n+a, summing only at
identical outputs. No norms are taken. -/
def affine (a b : ℤ) (w : ArithmeticVector) : ArithmeticVector :=
  w.mapDomain (fun n => b * n + a)

/-- Addition acts as translation of the complete coefficient vector. -/
def translate (a : ℤ) (w : ArithmeticVector) : ArithmeticVector := affine a 1 w

/-- Multiplication acts as dilation of the complete coefficient vector. -/
def dilate (b : ℤ) (w : ArithmeticVector) : ArithmeticVector := affine 0 b w

/-- Observe the full vector with an arbitrary complex test function. -/
def observe (w : ArithmeticVector) (f : ℤ → ℂ) : ℂ :=
  w.sum (fun n c => c * f n)

/-- Every finite sequence of affine operations has its exact affine normal form. -/
theorem affine_comp (a b c d : ℤ) (w : ArithmeticVector) :
    affine a b (affine c d w) = affine (b * c + a) (b * d) w := by
  unfold affine
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro n hn
  dsimp only [Function.comp_apply]
  ring

/-- Multiplication and addition satisfy their full noncommuting interaction law. -/
theorem dilate_translate (a b : ℤ) (w : ArithmeticVector) :
    dilate b (translate a w) = translate (b * a) (dilate b w) := by
  simp only [dilate, translate, affine_comp, mul_one, one_mul, mul_zero, add_zero, zero_add]

/-- Pushforward and observation commute exactly by pulling back the test
function, retaining all arithmetic labels and complex coefficients. -/
theorem observe_affine (a b : ℤ) (w : ArithmeticVector) (f : ℤ → ℂ) :
    observe (affine a b w) f = observe w (fun n => f (b * n + a)) := by
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)

/-- Observation is additive in the original complex vector. -/
theorem observe_add (w v : ArithmeticVector) (f : ℤ → ℂ) :
    observe (w + v) f = observe w f + observe v f := by
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

/-- One arithmetic atom retains exactly its coefficient and test value. -/
theorem observe_single (n : ℤ) (c : ℂ) (f : ℤ → ℂ) :
    observe (Finsupp.single n c) f = c * f n := by
  exact Finsupp.sum_single_index (zero_mul _)

/-- Finite superposition is observed without merging or discarding terms. -/
theorem observe_sum {ι : Type*} (S : Finset ι) (w : ι → ArithmeticVector) (f : ℤ → ℂ) :
    observe (∑ i ∈ S, w i) f = ∑ i ∈ S, observe (w i) f := by
  induction S using Finset.induction_on with
  | empty => simp [observe]
  | @insert i S hi ih => simp only [Finset.sum_insert hi, observe_add, ih]

/-- An additive Fourier character, with angular frequency measured in radians. -/
def fourierKernel (θ : ℝ) (n : ℤ) : ℂ :=
  Complex.exp (Complex.I * (θ : ℂ) * (n : ℂ))

/-- Addition of integer labels becomes multiplication of Fourier phases. -/
theorem fourierKernel_add (θ : ℝ) (a n : ℤ) :
    fourierKernel θ (a + n) = fourierKernel θ a * fourierKernel θ n := by
  simp only [fourierKernel, Int.cast_add, mul_add, Complex.exp_add]

/-- Translation is diagonal under Fourier observation, with its full phase intact. -/
theorem observe_translate_fourier (a : ℤ) (w : ArithmeticVector) (θ : ℝ) :
    observe (translate a w) (fourierKernel θ) =
      fourierKernel θ a * observe w (fourierKernel θ) := by
  unfold translate
  rw [observe_affine]
  simp only [one_mul]
  unfold observe Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [add_comm n a, fourierKernel_add]
  ring

/-- Dilation changes Fourier frequency exactly; it does not destroy phase. -/
theorem observe_dilate_fourier (b : ℤ) (w : ArithmeticVector) (θ : ℝ) :
    observe (dilate b w) (fourierKernel θ) =
      observe w (fourierKernel ((b : ℝ) * θ)) := by
  unfold dilate
  rw [observe_affine]
  congr 1
  funext n
  simp only [fourierKernel, add_zero, Int.cast_mul, Complex.ofReal_mul, Complex.ofReal_intCast]
  congr 1
  ring

/-- The Mellin character n ↦ exp(-s log n). Its arithmetic use below is
explicitly restricted to positive integer labels. -/
def mellinKernel (s : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (-(s * (Real.log (n : ℝ) : ℂ)))

/-- On natural labels this is precisely the existing zeta prime feature,
rather than a new surrogate for the repository's exponential kernel. -/
theorem mellinKernel_nat_eq_zetaPrimeFeature (s : ℂ) (n : ℕ) :
    mellinKernel s (n : ℤ) = zetaPrimeFeature s n := by
  simp only [mellinKernel, zetaPrimeFeature, Int.cast_natCast]

/-- Multiplication of positive labels becomes multiplication of Mellin values. -/
theorem mellinKernel_mul (s : ℂ) {b n : ℤ} (hb : 0 < b) (hn : 0 < n) :
    mellinKernel s (b * n) = mellinKernel s b * mellinKernel s n := by
  have hb' : (b : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hb)
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hn)
  simp only [mellinKernel, Int.cast_mul, Real.log_mul hb' hn', Complex.ofReal_add,
    mul_add, neg_add, Complex.exp_add]

/-- On positive support, dilation is diagonal under Mellin observation.
This is an exact finite Dirichlet-polynomial identity, with arbitrary complex weights. -/
theorem observe_dilate_mellin {b : ℤ} (hb : 0 < b) (w : ArithmeticVector)
    (hpositive : ∀ n ∈ w.support, 0 < n) (s : ℂ) :
    observe (dilate b w) (mellinKernel s) =
      mellinKernel s b * observe w (mellinKernel s) := by
  unfold dilate
  rw [observe_affine]
  simp only [add_zero]
  unfold observe Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [mellinKernel_mul s hb (hpositive n hn)]
  ring

/-- The unnormalized total signed mass is observation by the constant one. -/
def mass (w : ArithmeticVector) : ℂ := observe w (fun _ => 1)

/-- Every affine operation preserves the entire signed mass, even when its
output labels collide. This limits what the operator algebra alone can prove. -/
theorem mass_affine (a b : ℤ) (w : ArithmeticVector) :
    mass (affine a b w) = mass w := observe_affine a b w (fun _ => 1)

/-- The full complex mixed Gram entry of two finite coefficient vectors. -/
def pairing (w v : ArithmeticVector) : ℂ := observe w (fun n => starRingEnd ℂ (v n))

/-- The affine Gram entry preserves every cross term on its exact collision
set, with the two original complex coefficient families intact. -/
theorem pairing_affine (a b c d : ℤ) (w v : ArithmeticVector) :
    pairing (affine a b w) (affine c d v) =
      ∑ x ∈ w.support, ∑ y ∈ v.support,
        if b * x + a = d * y + c then w x * starRingEnd ℂ (v y) else 0 := by
  unfold pairing
  rw [observe_affine]
  unfold observe
  apply Finset.sum_congr rfl
  intro x hx
  simp only [affine, Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply,
    Finsupp.single_apply, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : b * x + a = d * y + c
  · simp [h]
  · simp [h, Ne.symm h]

/-- A collision forces every shared divisor of the two multiplicative
channels to divide the additive displacement. -/
theorem collision_divisibility {a b c d x y q : ℤ}
    (hb : q ∣ b) (hd : q ∣ d) (h : b * x + a = d * y + c) : q ∣ c - a := by
  have hx : q ∣ b * x := dvd_mul_of_dvd_left hb x
  have hy : q ∣ d * y := dvd_mul_of_dvd_left hd y
  have he : b * x - d * y = c - a := by linarith only [h]
  rw [← he]
  exact dvd_sub hx hy

/-- The gcd condition is the exact criterion for an integer collision.
It classifies the ambient affine lines; finite supports may impose additional
restrictions and admissible collisions may still cancel in a Gram entry. -/
theorem collision_iff_gcd_dvd (a b c d : ℤ) :
    (∃ x y : ℤ, b * x + a = d * y + c) ↔ (Int.gcd b d : ℤ) ∣ c - a := by
  constructor
  · rintro ⟨x, y, h⟩
    exact collision_divisibility (Int.gcd_dvd_left b d) (Int.gcd_dvd_right b d) h
  · rintro ⟨k, hk⟩
    refine ⟨Int.gcdA b d * k, -(Int.gcdB b d * k), ?_⟩
    rw [Int.gcd_eq_gcd_ab] at hk
    nlinarith only [hk]

/-- A shared prime or composite divisor incompatible with the translation
makes the entire complex mixed Gram entry zero, for every coefficient family. -/
theorem pairing_affine_eq_zero_of_divisor {a b c d q : ℤ}
    (hb : q ∣ b) (hd : q ∣ d) (hshift : ¬ q ∣ c - a) (w v : ArithmeticVector) :
    pairing (affine a b w) (affine c d v) = 0 := by
  rw [pairing_affine]
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  exact if_neg (fun h => hshift (collision_divisibility hb hd h))

/-- The complete common-divisor obstruction is visible in a single exact
Gram entry, before any norm or unweighted energy bound. -/
theorem pairing_affine_eq_zero_of_gcd {a b c d : ℤ}
    (hshift : ¬ (Int.gcd b d : ℤ) ∣ c - a) (w v : ArithmeticVector) :
    pairing (affine a b w) (affine c d v) = 0 :=
  pairing_affine_eq_zero_of_divisor (Int.gcd_dvd_left b d) (Int.gcd_dvd_right b d) hshift w v

/-- At additive displacement one, only coprime multiplicative channels can
have a nonzero mixed Gram entry. -/
theorem pairing_unit_shift_eq_zero {b d : ℤ} (h : Int.gcd b d ≠ 1) (w v : ArithmeticVector) :
    pairing (dilate b w) (translate 1 (dilate d v)) = 0 := by
  simp only [dilate, translate, affine_comp, one_mul, mul_zero, zero_add]
  apply pairing_affine_eq_zero_of_gcd
  simpa only [sub_zero, ← Int.natCast_one, Int.natCast_dvd_natCast, Nat.dvd_one] using h

/-- Embed exactly the original Riesz band weights, with their original
integer support, squarefree/composite restrictions, signs and zeta kernel. -/
def rieszVector (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) : ArithmeticVector :=
  ∑ n : Fin (2 ^ (32 * N)), Finsupp.single ((n.val + 1 : ℕ) : ℤ)
    (ZetaRieszConditionedEnergy.bandWeight L P N y (n.val + 1))

/-- Constant observation recovers the literal original arithmetic carrier. -/
theorem mass_rieszVector (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    mass (rieszVector L P N y) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y := by
  unfold mass rieszVector
  rw [observe_sum]
  simp only [observe_single, mul_one]
  exact ZetaRieszConditionedEnergy.bandWeight_sum L P N y

/-- The actual signed carrier is unchanged by every affine relabelling;
orthogonality of transformed channels alone does not bound its total mass. -/
theorem affine_riesz_mass (a b : ℤ) (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    mass (affine a b (rieszVector L P N y)) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y := by
  rw [mass_affine, mass_rieszVector]

/-- The shared-divisor orthogonality applies directly to two arbitrary
original Riesz bands, without replacing their arithmetic weights. -/
theorem original_riesz_channels_orthogonal {a b c d q : ℤ}
    (hb : q ∣ b) (hd : q ∣ d) (hshift : ¬ q ∣ c - a)
    (L₁ L₂ : ℝ) (P₁ P₂ : Polynomial ℂ) (N₁ N₂ : ℕ) (y₁ y₂ : ℝ) :
    pairing (affine a b (rieszVector L₁ P₁ N₁ y₁))
      (affine c d (rieszVector L₂ P₂ N₂ y₂)) = 0 :=
  pairing_affine_eq_zero_of_divisor hb hd hshift _ _

/-- For coprime dilation parameters, every collision is a unique point on
one arithmetic progression through any fixed collision. -/
theorem coprime_collision_parameterization {b d h x₀ y₀ x y : ℤ}
    (hb : b ≠ 0) (hcoprime : Int.gcd b d = 1) (h₀ : b * x₀ - d * y₀ = h) :
    b * x - d * y = h ↔ ∃! k : ℤ, x = x₀ + d * k ∧ y = y₀ + b * k := by
  constructor
  · intro hxy
    have he : b * (x - x₀) = d * (y - y₀) := by nlinarith only [hxy, h₀]
    have hbdiv : b ∣ d * (y - y₀) := by
      rw [← he]
      exact dvd_mul_right b (x - x₀)
    obtain ⟨k, hk⟩ := Int.dvd_of_dvd_mul_right_of_gcd_one hbdiv hcoprime
    have he' : b * (x - x₀) = b * (d * k) := by
      rw [he, hk]
      ring
    have hx := mul_left_cancel₀ hb he'
    refine ⟨k, ⟨by linarith only [hx], by linarith only [hk]⟩, ?_⟩
    intro j hj
    apply mul_left_cancel₀ hb
    linarith only [hk, hj.2]
  · rintro ⟨k, ⟨hx, hy⟩, _⟩
    rw [hx, hy]
    nlinarith only [h₀]

/-- After dividing the dilation parameters by their gcd, every surviving
integer pair is enumerated exactly once. Finite supports then restrict the
single progression parameter without enlarging the original sum. -/
theorem collision_parameterization {b d h x₀ y₀ x y : ℤ}
    (hb : b ≠ 0) (h₀ : b * x₀ - d * y₀ = h) :
    b * x - d * y = h ↔ ∃! k : ℤ,
      x = x₀ + (d / (Int.gcd b d : ℤ)) * k ∧
      y = y₀ + (b / (Int.gcd b d : ℤ)) * k := by
  let g : ℤ := Int.gcd b d
  let B : ℤ := b / g
  let D : ℤ := d / g
  have hg : 0 < Int.gcd b d := Int.gcd_pos_of_ne_zero_left d hb
  have hg0 : g ≠ 0 := by
    dsimp only [g]
    exact_mod_cast (Nat.ne_of_gt hg)
  have hBmul : B * g = b := Int.ediv_mul_cancel (Int.gcd_dvd_left b d)
  have hDmul : D * g = d := Int.ediv_mul_cancel (Int.gcd_dvd_right b d)
  have hB : B ≠ 0 := by
    intro he
    apply hb
    simpa only [he, zero_mul] using hBmul.symm
  have hcoprime : Int.gcd B D = 1 := Int.gcd_div_gcd_div_gcd hg
  have hfactor (u v : ℤ) : g * (B * u - D * v) = b * u - d * v := by
    calc
      _ = (B * g) * u - (D * g) * v := by ring
      _ = _ := by rw [hBmul, hDmul]
  have he : b * x - d * y = h ↔ B * x - D * y = B * x₀ - D * y₀ := by
    constructor
    · intro hxy
      apply mul_left_cancel₀ hg0
      rw [hfactor, hfactor, hxy, h₀]
    · intro hxy
      have hm := congrArg (fun z => g * z) hxy
      rw [hfactor, hfactor, h₀] at hm
      exact hm
  exact he.trans (coprime_collision_parameterization hB hcoprime rfl)

/-- Every prime common to the two whole products must divide the lag.
This includes restrictions involving the original input labels. -/
theorem collision_product_gcd_dvd {b d x y h : ℤ} (he : b * x - d * y = h) :
    (Int.gcd (b * x) (d * y) : ℤ) ∣ h := by
  rw [← he]
  exact dvd_sub (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)

/-- At unit lag the two whole products are coprime, retaining all four
cross restrictions between their dilation factors and input labels. -/
theorem unit_lag_products_coprime {b d x y : ℤ} (he : b * x - d * y = 1) :
    Int.gcd (b * x) (d * y) = 1 := by
  have hd := collision_product_gcd_dvd he
  simpa only [← Int.natCast_one, Int.natCast_dvd_natCast, Nat.dvd_one] using hd

/-- The complete finite correlation vector, indexed by exact integer lag.
Every ordered pair contributes once, with both complex weights intact. -/
def correlation (b d : ℤ) (w v : ArithmeticVector) : ArithmeticVector :=
  ∑ x ∈ w.support, ∑ y ∈ v.support,
    Finsupp.single (b * x - d * y) (w x * starRingEnd ℂ (v y))

/-- A coefficient of the correlation vector enumerates every pair at that lag. -/
theorem correlation_apply (b d h : ℤ) (w v : ArithmeticVector) :
    correlation b d w v h =
      ∑ x ∈ w.support, ∑ y ∈ v.support,
        if b * x - d * y = h then w x * starRingEnd ℂ (v y) else 0 := by
  simp only [correlation, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- Every affine mixed Gram entry is a coefficient of the same correlation
vector; changing translations changes only the requested lag. -/
theorem correlation_eq_pairing (a b c d : ℤ) (w v : ArithmeticVector) :
    correlation b d w v (c - a) = pairing (affine a b w) (affine c d v) := by
  rw [correlation_apply, pairing_affine]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have he : b * x - d * y = c - a ↔ b * x + a = d * y + c := by
    constructor <;> intro h <;> linarith only [h]
  simp only [he]

/-- Arbitrary observations of the entire lag distribution retain every
weighted pair and are exact finite sums. -/
theorem observe_correlation (b d : ℤ) (w v : ArithmeticVector) (f : ℤ → ℂ) :
    observe (correlation b d w v) f =
      ∑ x ∈ w.support, ∑ y ∈ v.support,
        (w x * starRingEnd ℂ (v y)) * f (b * x - d * y) := by
  simp only [correlation, observe_sum, observe_single]

/-- The gcd obstruction removes every forbidden coefficient of the complete
correlation vector simultaneously, for arbitrary complex families. -/
theorem correlation_eq_zero_of_gcd {b d h : ℤ}
    (hh : ¬ (Int.gcd b d : ℤ) ∣ h) (w v : ArithmeticVector) :
    correlation b d w v h = 0 := by
  have he := correlation_eq_pairing 0 b h d w v
  simp only [sub_zero] at he
  rw [he]
  exact pairing_affine_eq_zero_of_gcd (by simpa only [sub_zero] using hh) w v

/-- Summing all lags recovers the product of the original signed sums.
This is the direct link from the correlation enumeration to the target carrier. -/
theorem mass_correlation (b d : ℤ) (w v : ArithmeticVector) :
    mass (correlation b d w v) = mass w * starRingEnd ℂ (mass v) := by
  rw [mass, observe_correlation]
  simp only [mul_one, mass, observe, Finsupp.sum, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Subtracting integer labels becomes multiplication by a conjugate Fourier phase. -/
theorem fourierKernel_sub (θ : ℝ) (m n : ℤ) :
    fourierKernel θ (m - n) = fourierKernel θ m * starRingEnd ℂ (fourierKernel θ n) := by
  simp only [fourierKernel, Int.cast_sub, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal, map_intCast, ← Complex.exp_add]
  congr 1
  ring

/-- One Fourier generating function contains every lag correlation, retaining
the exact dilation frequencies and conjugate phases of both original vectors. -/
theorem fourier_correlation (b d : ℤ) (w v : ArithmeticVector) (θ : ℝ) :
    observe (correlation b d w v) (fourierKernel θ) =
      observe w (fourierKernel ((b : ℝ) * θ)) *
        starRingEnd ℂ (observe v (fourierKernel ((d : ℝ) * θ))) := by
  rw [observe_correlation, ← observe_dilate_fourier b w θ, ← observe_dilate_fourier d v θ]
  simp only [dilate, observe_affine]
  simp only [add_zero, observe, Finsupp.sum, map_sum,
    map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [fourierKernel_sub]
  ring

/-- The total original Riesz autocorrelation is the actual carrier times its
complex conjugate, with all lags and original weights retained. -/
theorem original_riesz_correlation_mass (b d : ℤ) (L : ℝ) (P : Polynomial ℂ)
    (N : ℕ) (y : ℝ) :
    mass (correlation b d (rieszVector L P N y) (rieszVector L P N y)) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y *
        starRingEnd ℂ (zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y) := by
  rw [mass_correlation, mass_rieszVector]

end
end RiemannGaussian.ZetaArithmeticAffine
