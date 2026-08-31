import RiemannGaussian.External.Zeta23InverseSamplingKernelBridge
import Zeta23.Tail.Grid

/-!
# Finite-sampler tail for the literal Zeta23 Gram matrix

The inverse-sampling kernel is realized by a complete integer lattice, whereas
the Zeta23 zero-side matrix uses the finite sample range `0 ≤ k < d(T)`.  This
file bounds the two omitted lattice tails for ordinates in the interior of the
dyadic zero window.  The bound is explicit and tends to zero after the exact
Poisson normalization.
-/

noncomputable section

open Complex Filter Real
open scoped BigOperators

namespace RiemannGaussian
namespace Zeta23InverseSampling

/-- The elementary fourth-power lattice tail, obtained by passing the checked
finite telescoping estimate to the nonnegative infinite sum. -/
lemma tsum_inv_pow_four_add_mul_le
    {D h : ℝ} (hD : 0 < D) (hh : 0 < h) :
    (∑' n : ℕ, ((D + n * h) ^ 4)⁻¹) ≤
      (D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro n
    simpa only [Finset.sum_attach, Finset.sum_range] using
      (Zeta23.Tail.sum_inv_pow_four_le hD hh n)

lemma summable_inv_pow_four_add_mul
    {D h : ℝ} (hD : 0 < D) (hh : 0 < h) :
    Summable (fun n : ℕ => ((D + n * h) ^ 4)⁻¹) := by
  apply summable_of_sum_range_le
  · intro n
    positivity
  · intro n
    simpa only [Finset.sum_attach, Finset.sum_range] using
      (Zeta23.Tail.sum_inv_pow_four_le hD hh n)

open Zeta23

/-- The checked `r⁻²` transform estimate, squared and weakened to any positive
lower bound for the frequency magnitude. -/
lemma atD_phiHatR_sq_le_inv_four
    {P : Params} (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
    {r R : ℝ} (hR : 0 < R) (hRr : R ≤ |r|) :
    (P.atD T).phiHatR T r ^ 2 ≤
      (ThmD.cDT P.ϱ P.lam / P.w) ^ 2 * (R ^ 4)⁻¹ := by
  have hW := ThmD.admWindow_params hP h8
  have hraw := hW.abs_vHatR_mul_sq_le r
  rw [← ThmD.atD_phiHatR hP T] at hraw
  let C : ℝ := ThmD.cDT P.ϱ P.lam / P.w
  have hC : 0 ≤ C := div_nonneg hW.c_nonneg hW.w_pos.le
  have hr2 : R ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs r]
    exact pow_le_pow_left₀ hR.le hRr 2
  have hr2pos : 0 < r ^ 2 := lt_of_lt_of_le (sq_pos_of_pos hR) hr2
  have hf : |(P.atD T).phiHatR T r| ≤ C / (R ^ 2) := by
    calc
      |(P.atD T).phiHatR T r| ≤ C / (r ^ 2) := by
        rw [le_div_iff₀ hr2pos]
        exact hraw
      _ ≤ C / (R ^ 2) := by
        exact div_le_div_of_nonneg_left hC (sq_pos_of_pos hR) hr2
  have hs := pow_le_pow_left₀ (abs_nonneg ((P.atD T).phiHatR T r)) hf 2
  rw [sq_abs] at hs
  calc
    (P.atD T).phiHatR T r ^ 2 ≤ (C / R ^ 2) ^ 2 := hs
    _ = C ^ 2 * (R ^ 4)⁻¹ := by
      field_simp
    _ = _ := rfl

/-- Squared Fourier mass on the omitted negative sample half-lattice. -/
lemma atD_negativeSamplerTail_sq_le
    {P : Params} (hP : P.Valid) {T gamma : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (hT : 0 < T)
    (hgamma : T + Real.sqrt T ≤ gamma) :
    (∑' n : ℕ, (P.atD T).phiHatR T
        (gamma - (P.atD T).tau T (Int.negSucc n)) ^ 2) ≤
      (ThmD.cDT P.ϱ P.lam / P.w) ^ 2 *
        (((Real.sqrt T / 2) ^ 4)⁻¹ +
          ((Real.sqrt T / 2) ^ 3)⁻¹ /
            (3 * (2 * Real.pi / P.L T))) := by
  let D : ℝ := Real.sqrt T / 2
  let h : ℝ := 2 * Real.pi / P.L T
  let C : ℝ := ThmD.cDT P.ϱ P.lam / P.w
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hD : 0 < D := by dsimp [D]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hpoint : ∀ n : ℕ,
      (P.atD T).phiHatR T
          (gamma - (P.atD T).tau T (Int.negSucc n)) ^ 2 ≤
        C ^ 2 * ((D + n * h) ^ 4)⁻¹ := by
    intro n
    apply atD_phiHatR_sq_le_inv_four hP h8
    · positivity
    · rw [abs_of_nonneg]
      · simp only [ThmD.atD_tau_eq, Int.cast_negSucc, Nat.cast_add,
          Nat.cast_one]
        dsimp [D, h]
        have hsqrt := Real.sqrt_pos.2 hT
        have hgrid : 0 < 2 * Real.pi / P.L T := by positivity
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      · simp only [ThmD.atD_tau_eq, Int.cast_negSucc, Nat.cast_add,
          Nat.cast_one]
        have hsqrt := Real.sqrt_pos.2 hT
        have hgrid : 0 < 2 * Real.pi / P.L T := by positivity
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hg := (summable_inv_pow_four_add_mul hD hh).mul_left (C ^ 2)
  have hf : Summable (fun n : ℕ =>
      (P.atD T).phiHatR T
        (gamma - (P.atD T).tau T (Int.negSucc n)) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpoint hg
  calc
    (∑' n : ℕ, (P.atD T).phiHatR T
        (gamma - (P.atD T).tau T (Int.negSucc n)) ^ 2) ≤
        ∑' n : ℕ, C ^ 2 * ((D + n * h) ^ 4)⁻¹ :=
      hf.tsum_le_tsum hpoint hg
    _ = C ^ 2 * ∑' n : ℕ, ((D + n * h) ^ 4)⁻¹ :=
      tsum_mul_left
    _ ≤ C ^ 2 * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) := by
      gcongr
      exact tsum_inv_pow_four_add_mul_le hD hh
    _ = _ := rfl

/-- The first omitted nonnegative sample lies less than one grid spacing to
the left of `2T`.  This is the strict lower floor bound complementary to the
standard upper estimate for `d(T)`. -/
lemma atD_tau_d_gt_two_mul_sub_grid
    {P : Params} {T : ℝ} (hL : 0 < P.L T) (hT : 0 < T) :
    2 * T - 2 * Real.pi / P.L T <
      (P.atD T).tau T (P.d T : ℤ) := by
  let x : ℝ := P.L T * T / (2 * Real.pi)
  let h : ℝ := 2 * Real.pi / P.L T
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hfloor : x < (P.d T : ℝ) + 1 := by
    simpa only [Params.d] using Nat.lt_floor_add_one x
  have hmul := mul_lt_mul_of_pos_right hfloor hh
  have hxh : x * h = T := by
    dsimp [x, h]
    field_simp
  rw [hxh] at hmul
  rw [ThmD.atD_tau_eq]
  push_cast
  linarith

/-- Squared Fourier mass on the omitted upper sample half-lattice. -/
lemma atD_upperSamplerTail_sq_le
    {P : Params} (hP : P.Valid) {T gamma : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (hT : 0 < T)
    (hgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2)
    (hgamma : gamma ≤ 2 * T - Real.sqrt T) :
    (∑' n : ℕ, (P.atD T).phiHatR T
        (gamma - (P.atD T).tau T ((P.d T + n : ℕ) : ℤ)) ^ 2) ≤
      (ThmD.cDT P.ϱ P.lam / P.w) ^ 2 *
        (((Real.sqrt T / 2) ^ 4)⁻¹ +
          ((Real.sqrt T / 2) ^ 3)⁻¹ /
            (3 * (2 * Real.pi / P.L T))) := by
  let D : ℝ := Real.sqrt T / 2
  let h : ℝ := 2 * Real.pi / P.L T
  let C : ℝ := ThmD.cDT P.ϱ P.lam / P.w
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hD : 0 < D := by dsimp [D]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have htau := atD_tau_d_gt_two_mul_sub_grid (P := P) hL hT
  have hpoint : ∀ n : ℕ,
      (P.atD T).phiHatR T
          (gamma - (P.atD T).tau T ((P.d T + n : ℕ) : ℤ)) ^ 2 ≤
        C ^ 2 * ((D + n * h) ^ 4)⁻¹ := by
    intro n
    apply atD_phiHatR_sq_le_inv_four hP h8
    · positivity
    · rw [ThmD.atD_tau_eq]
      push_cast
      rw [abs_of_nonpos]
      ·
        dsimp [D, h]
        have hsqrt := Real.sqrt_pos.2 hT
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have htau' : 2 * T - 2 * Real.pi / P.L T <
            T + (P.d T : ℝ) * (2 * Real.pi / P.L T) := by
          simpa only [ThmD.atD_tau_eq, Int.cast_natCast] using htau
        nlinarith
      ·
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have htau' : 2 * T - 2 * Real.pi / P.L T <
            T + (P.d T : ℝ) * (2 * Real.pi / P.L T) := by
          simpa only [ThmD.atD_tau_eq, Int.cast_natCast] using htau
        nlinarith [Real.sqrt_pos.2 hT]
  have hg := (summable_inv_pow_four_add_mul hD hh).mul_left (C ^ 2)
  have hf : Summable (fun n : ℕ =>
      (P.atD T).phiHatR T
        (gamma - (P.atD T).tau T ((P.d T + n : ℕ) : ℤ)) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpoint hg
  calc
    (∑' n : ℕ, (P.atD T).phiHatR T
        (gamma - (P.atD T).tau T ((P.d T + n : ℕ) : ℤ)) ^ 2) ≤
        ∑' n : ℕ, C ^ 2 * ((D + n * h) ^ 4)⁻¹ :=
      hf.tsum_le_tsum hpoint hg
    _ = C ^ 2 * ∑' n : ℕ, ((D + n * h) ^ 4)⁻¹ :=
      tsum_mul_left
    _ ≤ C ^ 2 * ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h)) := by
      gcongr
      exact tsum_inv_pow_four_add_mul_le hD hh
    _ = _ := rfl

/-! ## Exact full/finite/tail decomposition -/

/-- The unnormalized finite correlation occurring in the literal Zeta23 Gram
entry. -/
def atDFiniteSampleCorrelation (P : Params) (T gamma gamma' : ℝ) : ℝ :=
  ∑ k : Fin (P.d T),
    (P.atD T).phiHatR T (gamma - (P.atD T).tau T k) *
      (P.atD T).phiHatR T (gamma' - (P.atD T).tau T k)

/-- The complete unnormalized lattice correlation. -/
def atDFullSampleCorrelation (P : Params) (T gamma gamma' : ℝ) : ℝ :=
  ∑' k : ℤ,
    (P.atD T).phiHatR T (gamma - (P.atD T).tau T k) *
      (P.atD T).phiHatR T (gamma' - (P.atD T).tau T k)

/-- The omitted negative half-lattice. -/
def atDNegativeSampleCorrelation (P : Params) (T gamma gamma' : ℝ) : ℝ :=
  ∑' n : ℕ,
    (P.atD T).phiHatR T
        (gamma - (P.atD T).tau T (Int.negSucc n)) *
      (P.atD T).phiHatR T
        (gamma' - (P.atD T).tau T (Int.negSucc n))

/-- The omitted nonnegative half-lattice beginning at `d(T)`. -/
def atDUpperSampleCorrelation (P : Params) (T gamma gamma' : ℝ) : ℝ :=
  ∑' n : ℕ,
    (P.atD T).phiHatR T
        (gamma - (P.atD T).tau T ((P.d T + n : ℕ) : ℤ)) *
      (P.atD T).phiHatR T
        (gamma' - (P.atD T).tau T ((P.d T + n : ℕ) : ℤ))

/-- Absolute summability of the complete correlation, derived solely from
the two checked diagonal Poisson series. -/
lemma summable_abs_atD_sampleCorrelation
    {P : Params} (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (gamma gamma' : ℝ) :
    Summable (fun k : ℤ =>
      |(P.atD T).phiHatR T (gamma - (P.atD T).tau T k) *
        (P.atD T).phiHatR T (gamma' - (P.atD T).tau T k)|) := by
  let a : ℤ → ℝ := fun k =>
    (P.atD T).phiHatR T (gamma - (P.atD T).tau T k)
  let b : ℤ → ℝ := fun k =>
    (P.atD T).phiHatR T (gamma' - (P.atD T).tau T k)
  have ha : Summable (fun k => a k ^ 2) := by
    have h := (atD_hasSum_phiHatR_mul hP h8 gamma gamma).summable
    simpa only [a, pow_two] using h
  have hb : Summable (fun k => b k ^ 2) := by
    have h := (atD_hasSum_phiHatR_mul hP h8 gamma' gamma').summable
    simpa only [b, pow_two] using h
  have hab : ∀ k, |a k * b k| ≤ a k ^ 2 + b k ^ 2 := by
    intro k
    rw [abs_mul]
    nlinarith [sq_nonneg (|a k| - |b k|), sq_abs (a k), sq_abs (b k)]
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hab (ha.add hb)

/-- The complete integer lattice is exactly the literal finite sampler plus
its two omitted half-lattices. -/
theorem atDFullSampleCorrelation_eq_finite_add_tails
    {P : Params} (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (gamma gamma' : ℝ) :
    atDFullSampleCorrelation P T gamma gamma' =
      atDFiniteSampleCorrelation P T gamma gamma' +
        atDUpperSampleCorrelation P T gamma gamma' +
        atDNegativeSampleCorrelation P T gamma gamma' := by
  let f : ℤ → ℝ := fun k =>
    (P.atD T).phiHatR T (gamma - (P.atD T).tau T k) *
      (P.atD T).phiHatR T (gamma' - (P.atD T).tau T k)
  have hf : Summable f :=
    (atD_hasSum_phiHatR_mul hP h8 gamma gamma').summable
  have hnat : Summable (fun n : ℕ => f n) :=
    hf.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => f (Int.negSucc n)) :=
    hf.comp_injective (@Int.negSucc.inj)
  have hsplit := hnat.sum_add_tsum_nat_add (P.d T)
  have hfinite : (∑ i ∈ Finset.range (P.d T), f i) =
      atDFiniteSampleCorrelation P T gamma gamma' := by
    unfold atDFiniteSampleCorrelation f
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
      (P.atD T).phiHatR T (gamma - (P.atD T).tau T n) *
        (P.atD T).phiHatR T (gamma' - (P.atD T).tau T n)) (P.d T)]
  have hupper : (∑' i : ℕ, f ((i + P.d T : ℕ) : ℤ)) =
      atDUpperSampleCorrelation P T gamma gamma' := by
    unfold atDUpperSampleCorrelation f
    apply tsum_congr
    intro n
    rw [add_comm n (P.d T)]
  have hnegative : (∑' n : ℕ, f (-((n : ℤ) + 1))) =
      atDNegativeSampleCorrelation P T gamma gamma' := by
    unfold atDNegativeSampleCorrelation f
    apply tsum_congr
    intro n
    rw [Int.negSucc_eq]
  change (∑' k : ℤ, f k) = _
  rw [tsum_of_nat_of_neg_add_one hnat hneg, ← hsplit,
    hfinite, hupper, hnegative]

/-- The scalar Young inequality in the exact form used for lattice tails. -/
lemma abs_mul_le_half_sq (x y : ℝ) :
    |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_mul]
  have h := two_mul_le_add_sq |x| |y|
  rw [sq_abs, sq_abs] at h
  linarith

/-- Cauchy--Schwarz in the elementary `2|ab| ≤ a²+b²` form, with all
infinite-sum obligations explicit. -/
lemma abs_tsum_mul_le_half_sq
    {a b : ℕ → ℝ}
    (ha : Summable (fun n => a n ^ 2))
    (hb : Summable (fun n => b n ^ 2)) :
    |∑' n, a n * b n| ≤
      ((∑' n, a n ^ 2) + ∑' n, b n ^ 2) / 2 := by
  have hpoint : ∀ n, |a n * b n| ≤ (a n ^ 2 + b n ^ 2) / 2 :=
    fun n => abs_mul_le_half_sq (a n) (b n)
  have hadd : Summable (fun n => a n ^ 2 + b n ^ 2) := ha.add hb
  have hrhs0 : Summable (fun n => (1 / 2 : ℝ) *
      (a n ^ 2 + b n ^ 2)) := hadd.mul_left (1 / 2)
  have hrhs : Summable (fun n => (a n ^ 2 + b n ^ 2) / 2) :=
    hrhs0.congr (fun n => by
      simp only [div_eq_mul_inv, one_mul, mul_comm])
  have habs : Summable (fun n => |a n * b n|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpoint hrhs
  have hsum0 : HasSum (fun n => (1 / 2 : ℝ) *
      (a n ^ 2 + b n ^ 2))
      ((1 / 2 : ℝ) * ((∑' n, a n ^ 2) + ∑' n, b n ^ 2)) :=
    (ha.hasSum.add hb.hasSum).mul_left (1 / 2 : ℝ)
  have hsum1 : HasSum (fun n => (a n ^ 2 + b n ^ 2) / 2)
      ((1 / 2 : ℝ) * ((∑' n, a n ^ 2) + ∑' n, b n ^ 2)) :=
    hsum0.congr (fun n => by
      simp only [div_eq_mul_inv, one_mul, mul_comm])
  have hsum : HasSum (fun n => (a n ^ 2 + b n ^ 2) / 2)
      (((∑' n, a n ^ 2) + ∑' n, b n ^ 2) / 2) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hsum1
  have hnorm : Summable (fun n => ‖a n * b n‖) := by
    simpa only [Real.norm_eq_abs] using habs
  calc
    |∑' n, a n * b n| ≤ ∑' n, |a n * b n| := by
      have h := norm_tsum_le_tsum_norm hnorm
      simpa only [Real.norm_eq_abs] using h
    _ ≤ ∑' n, (a n ^ 2 + b n ^ 2) / 2 :=
      habs.tsum_le_tsum hpoint hrhs
    _ = ((∑' n, a n ^ 2) + ∑' n, b n ^ 2) / 2 := hsum.tsum_eq

/-- The omitted negative correlation is bounded by the common one-sided
squared-mass envelope. -/
lemma abs_atDNegativeSampleCorrelation_le
    {P : Params} (hP : P.Valid) {T gamma gamma' : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (hT : 0 < T)
    (hgamma : T + Real.sqrt T ≤ gamma)
    (hgamma' : T + Real.sqrt T ≤ gamma') :
    |atDNegativeSampleCorrelation P T gamma gamma'| ≤
      (ThmD.cDT P.ϱ P.lam / P.w) ^ 2 *
        (((Real.sqrt T / 2) ^ 4)⁻¹ +
          ((Real.sqrt T / 2) ^ 3)⁻¹ /
            (3 * (2 * Real.pi / P.L T))) := by
  let a : ℕ → ℝ := fun n => (P.atD T).phiHatR T
    (gamma - (P.atD T).tau T (Int.negSucc n))
  let b : ℕ → ℝ := fun n => (P.atD T).phiHatR T
    (gamma' - (P.atD T).tau T (Int.negSucc n))
  have ha : Summable (fun n => a n ^ 2) := by
    have h := (atD_hasSum_phiHatR_mul hP h8 gamma gamma).summable
      |>.comp_injective (@Int.negSucc.inj)
    exact h.congr (fun n => by simp only [Function.comp_apply, a, pow_two])
  have hb : Summable (fun n => b n ^ 2) := by
    have h := (atD_hasSum_phiHatR_mul hP h8 gamma' gamma').summable
      |>.comp_injective (@Int.negSucc.inj)
    exact h.congr (fun n => by simp only [Function.comp_apply, b, pow_two])
  have hCS := abs_tsum_mul_le_half_sq ha hb
  have haBound := atD_negativeSamplerTail_sq_le hP h8 hT hgamma
  have hbBound := atD_negativeSamplerTail_sq_le hP h8 hT hgamma'
  change |∑' n, a n * b n| ≤ _
  linarith

lemma upperSampleIndex_injective (d : ℕ) :
    Function.Injective (fun n : ℕ => ((d + n : ℕ) : ℤ)) := by
  intro m n h
  exact Nat.add_left_cancel (Int.ofNat_injective h)

/-- The omitted upper correlation obeys the same one-sided envelope. -/
lemma abs_atDUpperSampleCorrelation_le
    {P : Params} (hP : P.Valid) {T gamma gamma' : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (hT : 0 < T)
    (hgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2)
    (hgamma : gamma ≤ 2 * T - Real.sqrt T)
    (hgamma' : gamma' ≤ 2 * T - Real.sqrt T) :
    |atDUpperSampleCorrelation P T gamma gamma'| ≤
      (ThmD.cDT P.ϱ P.lam / P.w) ^ 2 *
        (((Real.sqrt T / 2) ^ 4)⁻¹ +
          ((Real.sqrt T / 2) ^ 3)⁻¹ /
            (3 * (2 * Real.pi / P.L T))) := by
  let a : ℕ → ℝ := fun n => (P.atD T).phiHatR T
    (gamma - (P.atD T).tau T ((P.d T + n : ℕ) : ℤ))
  let b : ℕ → ℝ := fun n => (P.atD T).phiHatR T
    (gamma' - (P.atD T).tau T ((P.d T + n : ℕ) : ℤ))
  have ha : Summable (fun n => a n ^ 2) := by
    have h := (atD_hasSum_phiHatR_mul hP h8 gamma gamma).summable
      |>.comp_injective (upperSampleIndex_injective (P.d T))
    exact h.congr (fun n => by simp only [Function.comp_apply, a, pow_two])
  have hb : Summable (fun n => b n ^ 2) := by
    have h := (atD_hasSum_phiHatR_mul hP h8 gamma' gamma').summable
      |>.comp_injective (upperSampleIndex_injective (P.d T))
    exact h.congr (fun n => by simp only [Function.comp_apply, b, pow_two])
  have hCS := abs_tsum_mul_le_half_sq ha hb
  have haBound := atD_upperSamplerTail_sq_le hP h8 hT hgrid hgamma
  have hbBound := atD_upperSamplerTail_sq_le hP h8 hT hgrid hgamma'
  change |∑' n, a n * b n| ≤ _
  linarith

/-- A convenient common envelope for the two omitted half-lattices. -/
def finiteSamplerTailEnvelope (P : Zeta23.Params) (T : ℝ) : ℝ :=
  let D := Real.sqrt T / 2
  let h := 2 * Real.pi / P.L T
  2 * (Zeta23.ThmD.cDT P.ϱ P.lam / P.w) ^ 2 *
    ((D ^ 4)⁻¹ + (D ^ 3)⁻¹ / (3 * h))

lemma finiteSamplerTailEnvelope_nonneg
    {P : Zeta23.Params} {T : ℝ} (hT : 0 < T) (hL : 0 < P.L T) :
    0 ≤ finiteSamplerTailEnvelope P T := by
  unfold finiteSamplerTailEnvelope
  have hsqrt : 0 < Real.sqrt T / 2 := by positivity
  have hgrid : 0 < 2 * Real.pi / P.L T := by positivity
  positivity

/-- Exact elementary form of the normalized finite-sampler tail.  It exposes
the two decaying scales used in the endpoint argument. -/
lemma finiteSamplerTailEnvelope_div_eq
    {P : Zeta23.Params} {T a : ℝ}
    (hT : 0 < T) (hL : 0 < P.L T) (ha : 0 < a) :
    finiteSamplerTailEnvelope P T / (a * P.L T ^ 2) =
      32 * (Zeta23.ThmD.cDT P.ϱ P.lam / P.w) ^ 2 /
          (a * P.L T ^ 2 * T ^ 2) +
        8 * (Zeta23.ThmD.cDT P.ϱ P.lam / P.w) ^ 2 /
          (3 * Real.pi * a * P.L T * T * Real.sqrt T) := by
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsquare : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  have hcube : Real.sqrt T ^ 3 = Real.sqrt T * T := by
    calc
      Real.sqrt T ^ 3 = Real.sqrt T * Real.sqrt T ^ 2 := by ring
      _ = Real.sqrt T * T := by rw [hsquare]
  unfold finiteSamplerTailEnvelope
  field_simp
  rw [hcube]
  ring_nf
  rw [hsquare]
  ring

/-- A deliberately coarse majorant, independent of the window width and
normalization.  Its `T⁻¹` decay is all the certificate endgame needs. -/
lemma finiteSamplerTailEnvelope_div_le
    {P : Zeta23.Params} {T a : ℝ}
    (hT : 1 ≤ T) (hL : 1 ≤ P.L T) (ha : 1 / 2 ≤ a) :
    finiteSamplerTailEnvelope P T / (a * P.L T ^ 2) ≤
      80 * (Zeta23.ThmD.cDT P.ϱ P.lam / P.w) ^ 2 / T := by
  let C : ℝ := Zeta23.ThmD.cDT P.ϱ P.lam / P.w
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hLpos : 0 < P.L T := lt_of_lt_of_le zero_lt_one hL
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hT0 : 0 ≤ T := hTpos.le
  have hL2 : 1 ≤ P.L T ^ 2 := by nlinarith [sq_nonneg (P.L T - 1)]
  have hT2 : T ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
  have hLT : T ≤ P.L T ^ 2 * T ^ 2 := by
    calc
      T ≤ T ^ 2 := hT2
      _ = 1 * T ^ 2 := by ring
      _ ≤ P.L T ^ 2 * T ^ 2 :=
        mul_le_mul_of_nonneg_right hL2 (sq_nonneg T)
  have hden1 : (1 / 2 : ℝ) * T ≤ a * P.L T ^ 2 * T ^ 2 := by
    calc
      (1 / 2 : ℝ) * T ≤ a * T :=
        mul_le_mul_of_nonneg_right ha hT0
      _ ≤ a * (P.L T ^ 2 * T ^ 2) :=
        mul_le_mul_of_nonneg_left hLT hapos.le
      _ = a * P.L T ^ 2 * T ^ 2 := by ring
  have hterm1 :
      32 * C ^ 2 / (a * P.L T ^ 2 * T ^ 2) ≤ 64 * C ^ 2 / T := by
    calc
      32 * C ^ 2 / (a * P.L T ^ 2 * T ^ 2) ≤
          32 * C ^ 2 / ((1 / 2 : ℝ) * T) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden1
      _ = 64 * C ^ 2 / T := by field_simp; ring
  have hsqrt1 : 1 ≤ Real.sqrt T := Real.one_le_sqrt.mpr hT
  have h3pi : 1 ≤ 3 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hpa : (1 / 2 : ℝ) ≤ 3 * Real.pi * a := by
    calc
      (1 / 2 : ℝ) = 1 * (1 / 2 : ℝ) := by ring
      _ ≤ (3 * Real.pi) * a :=
        mul_le_mul h3pi ha (by positivity) (by positivity)
  have hpaL : (1 / 2 : ℝ) ≤ 3 * Real.pi * a * P.L T := by
    calc
      (1 / 2 : ℝ) = (1 / 2 : ℝ) * 1 := by ring
      _ ≤ (3 * Real.pi * a) * P.L T :=
        mul_le_mul hpa hL (by positivity) (by positivity)
  have hpaLs : (1 / 2 : ℝ) ≤
      3 * Real.pi * a * P.L T * Real.sqrt T := by
    calc
      (1 / 2 : ℝ) = (1 / 2 : ℝ) * 1 := by ring
      _ ≤ (3 * Real.pi * a * P.L T) * Real.sqrt T :=
        mul_le_mul hpaL hsqrt1 (by positivity) (by positivity)
  have hden2 : (1 / 2 : ℝ) * T ≤
      3 * Real.pi * a * P.L T * T * Real.sqrt T := by
    calc
      (1 / 2 : ℝ) * T ≤
          (3 * Real.pi * a * P.L T * Real.sqrt T) * T :=
        mul_le_mul_of_nonneg_right hpaLs hT0
      _ = 3 * Real.pi * a * P.L T * T * Real.sqrt T := by ring
  have hterm2 :
      8 * C ^ 2 /
          (3 * Real.pi * a * P.L T * T * Real.sqrt T) ≤
        16 * C ^ 2 / T := by
    calc
      8 * C ^ 2 /
          (3 * Real.pi * a * P.L T * T * Real.sqrt T) ≤
          8 * C ^ 2 / ((1 / 2 : ℝ) * T) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden2
      _ = 16 * C ^ 2 / T := by field_simp; ring
  rw [finiteSamplerTailEnvelope_div_eq hTpos hLpos hapos]
  change 32 * C ^ 2 / (a * P.L T ^ 2 * T ^ 2) +
      8 * C ^ 2 / (3 * Real.pi * a * P.L T * T * Real.sqrt T) ≤
    80 * C ^ 2 / T
  calc
    _ ≤ 64 * C ^ 2 / T + 16 * C ^ 2 / T := add_le_add hterm1 hterm2
    _ = 80 * C ^ 2 / T := by ring

/-- After the exact Poisson normalization, both omitted sampler tails vanish
at the endpoint scale. -/
theorem tendsto_finiteSamplerTailEnvelope_normalized_zero
    {P : Zeta23.Params} (hP : P.Valid) :
    Tendsto (fun T : ℝ =>
      finiteSamplerTailEnvelope P T /
        ((P.atD T).a T * P.L T ^ 2)) atTop (nhds 0) := by
  let C : ℝ := Zeta23.ThmD.cDT P.ϱ P.lam / P.w
  have hT : ∀ᶠ T : ℝ in atTop, 1 ≤ T := eventually_ge_atTop 1
  have hL : ∀ᶠ T : ℝ in atTop, 1 ≤ P.L T :=
    (Zeta23.ThmD.tendsto_L hP).eventually_ge_atTop 1
  have ha : ∀ᶠ T : ℝ in atTop, 1 / 2 ≤ (P.atD T).a T :=
    (Zeta23.ThmD.eventually_aD_range hP).mono fun _ h => h.1
  have hnonneg : ∀ᶠ T : ℝ in atTop,
      0 ≤ finiteSamplerTailEnvelope P T /
        ((P.atD T).a T * P.L T ^ 2) := by
    filter_upwards [hT, hL, ha] with T hT' hL' ha'
    exact div_nonneg
      (finiteSamplerTailEnvelope_nonneg (by linarith) (by linarith))
      (by positivity)
  have hle : ∀ᶠ T : ℝ in atTop,
      finiteSamplerTailEnvelope P T /
          ((P.atD T).a T * P.L T ^ 2) ≤
        80 * C ^ 2 / T := by
    filter_upwards [hT, hL, ha] with T hT' hL' ha'
    exact finiteSamplerTailEnvelope_div_le hT' hL' ha'
  have hmajor : Tendsto (fun T : ℝ => 80 * C ^ 2 / T)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id
  exact squeeze_zero' hnonneg hle hmajor

/-! ## Identification with the literal simple-zero Gram -/

/-- Membership in the literal `S₁` index set supplies the critical-line
equation needed to turn `gammaOf` into the real ordinate. -/
lemma blockData_simpleZero_re_eq_half
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T P}
    (z : (Zeta23.ZeroSide.blockData Z T P hconj).S₁) :
    ((z.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).re = 1 / 2 := by
  have hz :
      (Zeta23.ZeroSide.blockData Z T P hconj).σ z.1 = z.1 ∧
        (Zeta23.ZeroSide.blockData Z T P hconj).m z.1 = 1 := by
    simpa [Zeta23.ZeroSide.ZeroBlockData.S₁] using z.2
  exact (Zeta23.ZeroSide.mkData_σ_eq_iff Z T
    (Zeta23.ZeroSide.evalVec Z T P)
    (Zeta23.ZeroSide.evalVec_reflect hconj) z.1).mp hz.1

/-- A normalized literal simple-zero column is the real finite sampler,
viewed in `ℂ`. -/
lemma atD_simpleVhat_apply_eq
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T (P.atD T)}
    (z : (Zeta23.ZeroSide.blockData Z T (P.atD T) hconj).S₁)
    (k : Fin (P.d T)) :
    Zeta23InverseSampling.ZeroBlockData.simpleVhat
        (Zeta23.ZeroSide.blockData Z T (P.atD T) hconj)
        ((P.atD T).a T * P.L T ^ 2) z k =
      ((P.atD T).phiHatR T
          (((z.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im -
            (P.atD T).tau T k) : ℂ) /
        (Real.sqrt ((P.atD T).a T * P.L T ^ 2) : ℂ) := by
  have hz := blockData_simpleZero_re_eq_half z
  simp only [Zeta23InverseSampling.ZeroBlockData.simpleVhat,
    Zeta23.ZeroSide.blockData, Zeta23.ZeroSide.mkData_v,
    Zeta23.ZeroSide.evalVec]
  rw [Zeta23.ZeroSide.gammaOf_of_re_eq_half hz,
    ← Complex.ofReal_sub, Zeta23.GzGp.phiHat_ofReal]

/-- Entrywise identity between the actual Zeta23 simple-zero Gram and the
finite real correlation bounded above. -/
theorem atD_zetaSimpleGram_apply_eq
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    {hconj : Zeta23.ZeroSide.PhiHatConj T (P.atD T)}
    (hc : 0 < (P.atD T).a T * P.L T ^ 2)
    (z z' : (Zeta23.ZeroSide.blockData Z T (P.atD T) hconj).S₁) :
    zetaSimpleGram Z T (P.atD T) hconj z z' =
      (atDFiniteSampleCorrelation P T
          (((z.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im)
          (((z'.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im) /
        ((P.atD T).a T * P.L T ^ 2) : ℂ) := by
  classical
  have hsqrt :
      (Real.sqrt ((P.atD T).a T * P.L T ^ 2) : ℂ) ^ 2 =
        (((P.atD T).a T * P.L T ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hc.le]
  have hsqrt0 :
      (Real.sqrt ((P.atD T).a T * P.L T ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hc).ne'
  unfold zetaSimpleGram ZeroBlockData.simpleGram
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply,
    Zeta23.ZeroSide.RankTraceMult.Wmat, Real.sqrt_one,
    RCLike.star_def]
  simp only [Zeta23.Params.atD_L, map_one, one_mul]
  unfold atDFiniteSampleCorrelation
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [atD_simpleVhat_apply_eq z k, atD_simpleVhat_apply_eq z' k,
    map_div₀, Complex.conj_ofReal, Complex.conj_ofReal,
    div_mul_div_comm, ← sq, hsqrt]
  push_cast
  rfl

/-- Uniform unnormalized error between the complete and literal finite
correlations for two interior ordinates. -/
theorem abs_atDFull_sub_finite_le_finiteSamplerTailEnvelope
    {P : Zeta23.Params} (hP : P.Valid) {T gamma gamma' : ℝ}
    (h8 : 8 * P.w ≤ P.L T) (hT : 0 < T)
    (hgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2)
    (hgammaLo : T + Real.sqrt T ≤ gamma)
    (hgammaHi : gamma ≤ 2 * T - Real.sqrt T)
    (hgammaLo' : T + Real.sqrt T ≤ gamma')
    (hgammaHi' : gamma' ≤ 2 * T - Real.sqrt T) :
    |atDFullSampleCorrelation P T gamma gamma' -
        atDFiniteSampleCorrelation P T gamma gamma'| ≤
      finiteSamplerTailEnvelope P T := by
  have hneg := abs_atDNegativeSampleCorrelation_le
    hP h8 hT hgammaLo hgammaLo'
  have hupp := abs_atDUpperSampleCorrelation_le
    hP h8 hT hgrid hgammaHi hgammaHi'
  rw [atDFullSampleCorrelation_eq_finite_add_tails hP h8]
  have htri := abs_add_le
    (atDUpperSampleCorrelation P T gamma gamma')
    (atDNegativeSampleCorrelation P T gamma gamma')
  unfold finiteSamplerTailEnvelope
  dsimp only
  rw [show atDFiniteSampleCorrelation P T gamma gamma' +
      atDUpperSampleCorrelation P T gamma gamma' +
      atDNegativeSampleCorrelation P T gamma gamma' -
      atDFiniteSampleCorrelation P T gamma gamma' =
      atDUpperSampleCorrelation P T gamma gamma' +
        atDNegativeSampleCorrelation P T gamma gamma' by ring]
  linarith

/-- The actual finite endpoint sampler realizes the Montgomery--Taylor kernel
on the interior zero window.  Both errors are explicit: `14w/L` is the ramp
error and the second term is the discarded lattice tail. -/
theorem atD_finiteNormalizedCorrelation_close_montgomeryTaylorKernel
    {P : Zeta23.Params} (hP : P.Valid) (hlam : P.lam = 1)
    {T gamma gamma' : ℝ}
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hT : 0 < T)
    (hgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2)
    (hgammaLo : T + Real.sqrt T ≤ gamma)
    (hgammaHi : gamma ≤ 2 * T - Real.sqrt T)
    (hgammaLo' : T + Real.sqrt T ≤ gamma')
    (hgammaHi' : gamma' ≤ 2 * T - Real.sqrt T) :
    |atDFiniteSampleCorrelation P T gamma gamma' /
          ((P.atD T).a T * P.L T ^ 2) -
        montgomeryTaylorKernel (P.L T * (gamma - gamma'))| ≤
      14 * (P.w / P.L T) +
        finiteSamplerTailEnvelope P T /
          ((P.atD T).a T * P.L T ^ 2) := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have ha : 0 < (P.atD T).a T := by
    linarith [(Zeta23.ThmD.aD_range_of hP h8 h4pi).1]
  have hden : 0 < (P.atD T).a T * P.L T ^ 2 := by positivity
  have htail0 := abs_atDFull_sub_finite_le_finiteSamplerTailEnvelope
    hP h8 hT hgrid hgammaLo hgammaHi hgammaLo' hgammaHi'
  have htail :
      |atDFiniteSampleCorrelation P T gamma gamma' /
          ((P.atD T).a T * P.L T ^ 2) -
        atDFullSampleCorrelation P T gamma gamma' /
          ((P.atD T).a T * P.L T ^ 2)| ≤
        finiteSamplerTailEnvelope P T /
          ((P.atD T).a T * P.L T ^ 2) := by
    rw [← sub_div, abs_div, abs_of_pos hden,
      div_le_div_iff_of_pos_right hden]
    simpa only [abs_sub_comm] using htail0
  have hfull := atD_fullNormalizedCorrelation_close_montgomeryTaylorKernel
    hP hlam h8 h4pi gamma gamma'
  change |atDFullSampleCorrelation P T gamma gamma' /
      ((P.atD T).a T * P.L T ^ 2) -
        montgomeryTaylorKernel (P.L T * (gamma - gamma'))| ≤
      14 * (P.w / P.L T) at hfull
  calc
    |atDFiniteSampleCorrelation P T gamma gamma' /
          ((P.atD T).a T * P.L T ^ 2) -
        montgomeryTaylorKernel (P.L T * (gamma - gamma'))| ≤
      |atDFiniteSampleCorrelation P T gamma gamma' /
          ((P.atD T).a T * P.L T ^ 2) -
        atDFullSampleCorrelation P T gamma gamma' /
          ((P.atD T).a T * P.L T ^ 2)| +
      |atDFullSampleCorrelation P T gamma gamma' /
          ((P.atD T).a T * P.L T ^ 2) -
        montgomeryTaylorKernel (P.L T * (gamma - gamma'))| := by
      exact abs_sub_le _ _ _
    _ ≤ 14 * (P.w / P.L T) +
        finiteSamplerTailEnvelope P T /
          ((P.atD T).a T * P.L T ^ 2) := by linarith

/-- The literal simple-zero Gram entry, rather than an abstract correlation,
is uniformly close to the endpoint Montgomery--Taylor kernel for interior
zeros. -/
theorem atD_zetaSimpleGram_apply_close_montgomeryTaylorKernel
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} (hP : P.Valid)
    (hlam : P.lam = 1) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T)
    (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hT : 0 < T)
    (hgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2)
    {hconj : Zeta23.ZeroSide.PhiHatConj T (P.atD T)}
    (z z' : (Zeta23.ZeroSide.blockData Z T (P.atD T) hconj).S₁)
    (hzLo : T + Real.sqrt T ≤
      ((z.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im)
    (hzHi : ((z.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im ≤
      2 * T - Real.sqrt T)
    (hzLo' : T + Real.sqrt T ≤
      ((z'.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im)
    (hzHi' : ((z'.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im ≤
      2 * T - Real.sqrt T) :
    ‖zetaSimpleGram Z T (P.atD T) hconj z z' -
        (montgomeryTaylorKernel
          (P.L T *
            (((z.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im -
              ((z'.1 : Zeta23.ZeroSide.ZI Z T) : ℂ).im)) : ℂ)‖ ≤
      14 * (P.w / P.L T) +
        finiteSamplerTailEnvelope P T /
          ((P.atD T).a T * P.L T ^ 2) := by
  have ha : 0 < (P.atD T).a T := by
    linarith [(Zeta23.ThmD.aD_range_of hP h8 h4pi).1]
  have hc : 0 < (P.atD T).a T * P.L T ^ 2 := by
    have hL : 0 < P.L T := by linarith [hP.one_le_w]
    positivity
  rw [atD_zetaSimpleGram_apply_eq hc]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_div, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact atD_finiteNormalizedCorrelation_close_montgomeryTaylorKernel
    hP hlam h8 h4pi hT hgrid hzLo hzHi hzLo' hzHi'

end Zeta23InverseSampling
end RiemannGaussian
