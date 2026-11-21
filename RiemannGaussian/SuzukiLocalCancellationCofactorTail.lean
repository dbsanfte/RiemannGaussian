import RiemannGaussian.SuzukiLocalCancellationArithmeticBound
import RiemannGaussian.SuzukiLocalCancellationLatticeRemainder
import RiemannGaussian.SuzukiLocalCancellationLogSampling
import RiemannGaussian.SuzukiLocalCancellationTransfer
import RiemannGaussian.SuzukiLegendreDivisorDual

/-!
# The large-divisor remainder in the local prime comparison

Expanding log by the von Mangoldt divisor identity and isolating cofactor
one expresses the complete comparison through a shorter cofactor sum.
-/

namespace RiemannGaussian
noncomputable section

/-- Contribution of prime powers above V with cofactor at least two. -/
def suzukiLocalCofactorTail (X : ℝ) (V : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc V ⌊8 * X⌋₊, ArithmeticFunction.vonMangoldt d *
    ∑ k ∈ Finset.Ioc 1 ⌊8 * X / d⌋₊, suzukiLocalPhysicalKernel X ((d : ℝ) * k)

private theorem natPrefix_eq (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

private theorem dual_grid {X : ℝ} (hX : 0 < X) {d : ℕ} (hd : 0 < d) :
    suzukiDivisorDualKernel (fun n => suzukiLocalPhysicalKernel X n) ⌊8 * X⌋₊ d =
      ∑ k ∈ Finset.Icc 1 ⌊8 * X / d⌋₊, suzukiLocalPhysicalKernel X ((d : ℝ) * k) := by
  classical
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have he : (Finset.Icc 1 ⌊8 * X⌋₊).filter (fun n => d ∣ n) =
      (Finset.Icc 1 ⌊8 * X / d⌋₊).image (fun k => d * k) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hn, hN⟩, k, rfl⟩
      refine ⟨k, ⟨Nat.pos_of_mul_pos_left hn, ?_⟩, rfl⟩
      apply (Nat.le_floor_iff (by positivity)).mpr
      apply (le_div_iff₀ hd0).mpr
      have h := (Nat.le_floor_iff (by positivity)).mp hN
      push_cast at h
      linarith
    · rintro ⟨k, ⟨hk, hkN⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hd hk, ?_⟩, dvd_mul_right _ _⟩
      apply (Nat.le_floor_iff (by positivity)).mpr
      push_cast
      have h := (le_div_iff₀ hd0).mp ((Nat.le_floor_iff (by positivity)).mp hkN)
      linarith
  rw [suzukiDivisorDualKernel, ← Finset.sum_filter, he, Finset.sum_image]
  · simp
  · exact fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hd h

private theorem comparison_eq_physical {X : ℝ} (hX : 0 < X) :
    suzukiLocalArithmeticComparison X = ∑ d ∈ Finset.Ioc 0 ⌊8 * X⌋₊,
      ArithmeticFunction.vonMangoldt d * suzukiLocalPhysicalKernel X d := by
  have he := suzukiLocalArithmeticComparison_exp (Real.log X)
  rw [Real.exp_log hX, suzukiLocalPrimeComparison_eq_sum_signed_kernel] at he
  rw [he, suzukiArithmeticPrimeWindow, Real.exp_add, Real.exp_log hX,
    show 3 * Real.log 2 = Real.log 2 + Real.log 2 + Real.log 2 by ring,
    Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
    show X * (2 * 2 * 2) = 8 * X by ring, natPrefix_eq]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
  rw [suzukiLocalPhysicalKernel, Real.log_div hd0.ne' hX.ne']
  ring

/-- Exact decomposition before any estimates. All proper prime powers and
the strict lower endpoint of the cofactor tail are retained. -/
theorem suzukiLocal_log_eq_comparison_add_cofactorTail {X : ℝ} (hX : 1 ≤ X)
    {V : ℕ} (hV : (V : ℝ) ≤ X) :
    (∑ n ∈ Finset.Icc 1 ⌊8 * X⌋₊, suzukiLocalPhysicalKernel X n * Real.log n) =
      suzukiLocalArithmeticComparison X + suzukiLocalCofactorTail X V +
        suzukiLocalVaughanSmallCross X 1 V := by
  have hX0 : 0 < X := by linarith
  let N := ⌊8 * X⌋₊
  let w (d k : ℕ) := suzukiLocalPhysicalKernel X ((d : ℝ) * k)
  let A (d : ℕ) := ArithmeticFunction.vonMangoldt d * suzukiLocalPhysicalKernel X d
  let B (d : ℕ) := ArithmeticFunction.vonMangoldt d * ∑ k ∈ Finset.Ioc 1 ⌊8*X/d⌋₊, w d k
  let L (d : ℕ) := ArithmeticFunction.vonMangoldt d * ∑ k ∈ Finset.Icc 1 ⌊8*X/d⌋₊, w d k
  have heq (d : ℕ) (hd : d ∈ Finset.Ioc 0 N) : L d = A d + B d := by
    obtain ⟨hd0, hdN⟩ := Finset.mem_Ioc.mp hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
    have hdX := (Nat.le_floor_iff (by positivity)).mp hdN
    have h1 : 1 ≤ ⌊8 * X / d⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by
      simpa using (one_le_div hdpos).mpr hdX)
    dsimp [L, A, B]
    rw [natPrefix_eq, ← Finset.sum_Ioc_consecutive (w d) (by decide : 0 ≤ 1) h1]
    simp [w, mul_add]
  have hVn : V ≤ N := (Nat.le_floor_iff (by positivity)).mpr (by linarith)
  have hsmall (d : ℕ) (hd : d ∈ Finset.Ioc 0 V) : B d = L d := by
    have hdn := (Finset.mem_Ioc.mp hd).2
    have hdx : (d : ℝ) ≤ X := (by exact_mod_cast hdn : (d : ℝ) ≤ V).trans hV
    have hz : A d = 0 := by simp [A, suzukiLocalPhysicalKernel_eq_zero_of_le hX0 hdx]
    simpa [hz] using (heq d (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hd).1, hdn.trans hVn⟩)).symm
  have hcross : suzukiLocalVaughanSmallCross X 1 V = ∑ d ∈ Finset.Ioc 0 V, L d := by
    simp [suzukiLocalVaughanSmallCross, L, w]
  rw [sum_weight_mul_log_eq_vonMangoldt_divisorDual, natPrefix_eq,
    comparison_eq_physical hX0, hcross]
  change (∑ d ∈ Finset.Ioc 0 N, _ ) = (∑ d ∈ Finset.Ioc 0 N, A d) +
    (∑ d ∈ Finset.Ioc V N, B d) + ∑ d ∈ Finset.Ioc 0 V, L d
  calc
    _ = ∑ d ∈ Finset.Ioc 0 N, (A d + B d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [dual_grid hX0 (Finset.mem_Ioc.mp hd).1]
      exact heq d hd
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_Ioc_consecutive B (Nat.zero_le V) hVn,
        Finset.sum_congr rfl hsmall]
      ring

/-- Subtract the first logarithmic moment from the tail at the three-quarter
cutoff. Its upper excursions control the lower excursions of the prime sum. -/
def suzukiLocalCenteredCofactorTail (X : ℝ) : ℝ :=
  suzukiLocalCofactorTail X ⌊X ^ (3/4 : ℝ)⌋₊ -
    (-4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2 - 1) ^ 2) * Real.sqrt X

/-- Every cofactor in the remaining sum lies below eight times the fourth root. -/
theorem suzukiLocalCofactorTail_cofactor_lt {X : ℝ} (hX : 0 < X) {d k : ℕ}
    (hd : ⌊X ^ (3/4 : ℝ)⌋₊ < d) (hk : k ≤ ⌊8 * X / d⌋₊) :
    (k : ℝ) < 8 * X ^ (1/4 : ℝ) := by
  have hp := Real.rpow_pos_of_pos hX (3/4 : ℝ)
  have hd' : X ^ (3/4 : ℝ) < d := lt_of_not_ge (fun h =>
    (not_le_of_gt hd) ((Nat.le_floor_iff hp.le).mpr h))
  have hden : (0 : ℝ) < d := hp.trans hd'
  have hx : X ^ (1/4 : ℝ) * X ^ (3/4 : ℝ) = X := by
    rw [← Real.rpow_add hX, show (1/4 : ℝ) + 3/4 = 1 by norm_num, Real.rpow_one]
  apply ((Nat.le_floor_iff (by positivity)).mp hk).trans_lt
  apply (div_lt_iff₀ hden).mpr
  calc
    8 * X = (8 * X ^ (1/4 : ℝ)) * X ^ (3/4 : ℝ) := by rw [mul_assoc, hx]
    _ < _ := mul_lt_mul_of_pos_left hd' (by positivity)

/-- For cofactors with k V ≤ X, the original prime comparison reappears
at X/k, with its exact weight. This includes every fixed cofactor at all
sufficiently large X when V is the three-quarter cutoff. -/
theorem suzukiLocalCofactorRow_eq_comparison {X : ℝ} (hX : 0 < X)
    {k V : ℕ} (hk : 2 ≤ k) (hkV : (k : ℝ) * V ≤ X) :
    (∑ d ∈ Finset.Ioc V ⌊8 * X / k⌋₊, ArithmeticFunction.vonMangoldt d *
      suzukiLocalPhysicalKernel X ((d : ℝ) * k)) =
        (Real.sqrt k)⁻¹ * suzukiLocalArithmeticComparison (X / k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rw [comparison_eq_physical (div_pos hX hk0), ← mul_div_assoc, Finset.mul_sum]
  have hcut : Finset.Ioc V ⌊8 * X / k⌋₊ ⊆ Finset.Ioc 0 ⌊8 * X / k⌋₊ :=
    Finset.Ioc_subset_Ioc_left (Nat.zero_le V)
  rw [← Finset.sum_subset hcut (fun d hd h => ?_)]
  · apply Finset.sum_congr rfl
    intro d _
    rw [mul_comm (d : ℝ) (k : ℝ), suzukiLocalPhysicalKernel_mul_eq hX hk0]
    ring
  · have hdV : d ≤ V := le_of_not_gt (fun h' => h (Finset.mem_Ioc.mpr ⟨h', (Finset.mem_Ioc.mp hd).2⟩))
    have hV : (V : ℝ) ≤ X / k := (le_div_iff₀ hk0).mpr (by linarith)
    rw [suzukiLocalPhysicalKernel_eq_zero_of_le (div_pos hX hk0)
      ((by exact_mod_cast hdV : (d : ℝ) ≤ V).trans hV), mul_zero, mul_zero]

/-- All errors outside the centered cofactor tail have a uniform constant
cost at every real cutoff, including the noninteger endpoints. -/
theorem abs_suzukiLocalComparison_add_centeredCofactorTail_le {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalArithmeticComparison X + suzukiLocalCenteredCofactorTail X| ≤ 1076 := by
  let V := ⌊X ^ (3/4 : ℝ)⌋₊
  have hX0 := zero_lt_one.trans_le hX
  have hV : (V : ℝ) ≤ X ^ (3/4 : ℝ) := Nat.floor_le (by positivity)
  have hVX : (V : ℝ) ≤ X := hV.trans (Real.rpow_le_self_of_one_le hX (by norm_num))
  have hc := suzukiLocalVaughanSmallCross_abs_le_of_product_le_three_quarters hX0 1 V
    (by simpa using hV)
  have hs := suzukiLocalPhysicalKernel_log_prefix_sampling_error_le (q := 1) hX le_rfl hX
  rw [suzukiLocalPhysicalKernel_scaled_log_integral hX0 (by norm_num)] at hs
  simp only [div_one, one_mul] at hs
  rw [suzukiLocal_log_eq_comparison_add_cofactorTail hX hVX] at hs
  have hroot : 1 ≤ Real.sqrt X := (Real.one_le_sqrt).mpr hX
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hX0)
  rw [Real.log_sqrt hX0.le] at hl
  have hl8 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
  have he : (53 * Real.log (8 * X) + 21) / Real.sqrt X ≤ 500 := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hX0)).mpr
    linarith
  have hh := abs_le.mp (hs.trans he)
  have hhc := abs_le.mp hc
  unfold suzukiLocalCenteredCofactorTail
  change |_ + (suzukiLocalCofactorTail X V - _)| ≤ _
  rw [abs_le]
  constructor <;> linarith [hh.1, hh.2, hhc.1, hhc.2]

/-- Failure of Mathlib's RH forces positive power-size excursions of the
centered cofactor tail at arbitrarily large real cutoffs. -/
theorem exists_centeredCofactorTail_excursions_of_not_rh (h : ¬ RiemannHypothesis) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 0 ≤ C → ∀ X₀ : ℝ, 2 ≤ X₀ →
      ∃ X : ℝ, X₀ ≤ X ∧ C * X ^ ε < suzukiLocalCenteredCofactorTail X := by
  by_contra! hnone
  apply h
  apply riemannHypothesis_of_suzukiLocalArithmeticComparison_subpolynomial_lower_bound
  intro ε hε
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ := hnone ε hε
  refine ⟨C + 1076, by linarith, X₀, hX₀, fun X hX => ?_⟩
  have h1 : 1 ≤ X := by linarith
  have hb := (abs_le.mp (abs_suzukiLocalComparison_add_centeredCofactorTail_le h1)).1
  have hp := Real.one_le_rpow h1 hε.le
  nlinarith [hbound X hX]

/-- The centered sum restricted to ordinary primes at the three-quarter cutoff. -/
def suzukiLocalCenteredPrimeCofactorTail (X : ℝ) : ℝ :=
  (∑ d ∈ (Finset.Ioc ⌊X ^ (3/4 : ℝ)⌋₊ ⌊8 * X⌋₊).filter Nat.Prime, Real.log d *
    ∑ k ∈ Finset.Ioc 1 ⌊8 * X / d⌋₊, suzukiLocalPhysicalKernel X ((d : ℝ) * k)) -
    (-4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2 - 1) ^ 2) * Real.sqrt X

private theorem cofactor_grid_bound {X : ℝ} (hX : 1 ≤ X) {d : ℕ}
    (hd : 0 < d) (hdX : (d : ℝ) ≤ 8 * X) :
    |∑ k ∈ Finset.Ioc 1 ⌊8 * X / d⌋₊, suzukiLocalPhysicalKernel X ((d : ℝ) * k)| ≤
      56 / Real.sqrt X := by
  have hX0 := zero_lt_one.trans_le hX
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := suzukiLocalPhysicalKernel_prefix_sum_abs_le hX0 hd0
  have h1 : 1 ≤ ⌊8 * X / d⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by
    simpa using (one_le_div hd0).mpr hdX)
  rw [natPrefix_eq, ← Finset.sum_Ioc_consecutive _ (by decide : 0 ≤ 1) h1] at hs
  simp at hs
  have hatom : |suzukiLocalPhysicalKernel X d| ≤ 3 / Real.sqrt X := by
    by_cases h : (d : ℝ) ≤ X
    · rw [suzukiLocalPhysicalKernel_eq_zero_of_le hX0 h, abs_zero]
      positivity
    · have hk := abs_suzukiLocalSignedKernel_le (Real.log (d / X))
      have h2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      have hK : (Real.sqrt 2 + 1) * Real.log 2 ≤ 3 := by
        nlinarith [mul_le_mul_of_nonneg_left hl
          (by positivity : 0 ≤ Real.sqrt 2 + 1)]
      rw [suzukiLocalPhysicalKernel, abs_div, abs_of_pos (Real.sqrt_pos.mpr hd0)]
      exact div_le_div₀ (by norm_num) (hk.trans hK) (Real.sqrt_pos.mpr hX0)
        (Real.sqrt_le_sqrt (le_of_not_ge h))
  rw [abs_le] at hs hatom ⊢
  rw [show (56 : ℝ) / Real.sqrt X = 53 / Real.sqrt X + 3 / Real.sqrt X by ring]
  constructor <;> linarith [hatom.1, hatom.2, hs.1, hs.2]

/-- All proper prime powers in the cofactor tail together cost at most 3024.
Within each divisor row the lattice cancellation precedes absolute values. -/
theorem abs_suzukiLocalCenteredCofactorTail_sub_prime_le {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalCenteredCofactorTail X - suzukiLocalCenteredPrimeCofactorTail X| ≤ 3024 := by
  let S := Finset.Ioc ⌊X ^ (3/4 : ℝ)⌋₊ ⌊8 * X⌋₊
  let a (d : ℕ) : ℝ := if d.Prime then 0 else ArithmeticFunction.vonMangoldt d
  let row (d : ℕ) := ∑ k ∈ Finset.Ioc 1 ⌊8 * X / d⌋₊, suzukiLocalPhysicalKernel X ((d : ℝ) * k)
  have ha (d : ℕ) : 0 ≤ a d := by dsimp [a]; split_ifs <;> positivity
  have hX0 := zero_lt_one.trans_le hX
  have he :
      suzukiLocalCenteredCofactorTail X - suzukiLocalCenteredPrimeCofactorTail X =
        ∑ d ∈ S, a d * row d := by
    unfold suzukiLocalCenteredCofactorTail suzukiLocalCenteredPrimeCofactorTail suzukiLocalCofactorTail
    rw [sub_sub_sub_cancel_right, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hp : d.Prime <;> simp [hp, a, row, ArithmeticFunction.vonMangoldt_apply_prime]
  have hmass : (∑ d ∈ S, a d) ≤ 54 * Real.sqrt X := by
    have hsub : S ⊆ Finset.Icc 0 ⌊8 * X⌋₊ := fun d hd =>
      Finset.mem_Icc.mpr ⟨Nat.zero_le d, (Finset.mem_Ioc.mp hd).2⟩
    have ht : (∑ d ∈ Finset.Icc 0 ⌊8 * X⌋₊, a d) = Chebyshev.psi (8*X) - Chebyshev.theta (8*X) := by
      rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hp : d.Prime <;> simp [hp, a, ArithmeticFunction.vonMangoldt_apply_prime]
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => ha d)).trans
    rw [ht]
    apply (chebyshevPsi_sub_theta_le_eighteen_sqrt (by linarith : 1 ≤ 8 * X)).trans
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    have h8 : Real.sqrt 8 ≤ 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    nlinarith [mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg X)]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ S, a d * (56 / Real.sqrt X) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdV, hdN⟩ := Finset.mem_Ioc.mp hd
      rw [abs_mul, abs_of_nonneg (ha d)]
      exact mul_le_mul_of_nonneg_left (cofactor_grid_bound hX (by omega)
        ((Nat.le_floor_iff (by positivity)).mp hdN)) (ha d)
    _ = (∑ d ∈ S, a d) * (56 / Real.sqrt X) := by rw [Finset.sum_mul]
    _ ≤ (54 * Real.sqrt X) * (56 / Real.sqrt X) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = _ := by have := Real.sqrt_pos.mpr hX0; field_simp; norm_num

/-- Uniform comparison between the complete Suzuki packet and the centered
short-cofactor sum over ordinary primes. -/
theorem abs_suzukiLocalComparison_add_centeredPrimeCofactorTail_le {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalArithmeticComparison X + suzukiLocalCenteredPrimeCofactorTail X| ≤ 4100 := by
  have h := abs_le.mp (abs_suzukiLocalComparison_add_centeredCofactorTail_le hX)
  have hp := abs_le.mp (abs_suzukiLocalCenteredCofactorTail_sub_prime_le hX)
  rw [abs_le]
  constructor <;> linarith [h.1, h.2, hp.1, hp.2]

/-- A bound B on zero real parts gives a bound at exponent B - 1/2 on the
centered ordinary-prime sum at every real cutoff. The additive 4100 pays
for the comparison and the proper prime powers. -/
theorem abs_centeredPrimeCofactorTail_le_of_re_le {B : ℝ} (hB : B ∈ Set.Icc 0 1)
    (hβ : ∀ rho : NontrivialZetaZero, rho.1.re ≤ B) {X : ℝ} (hX : 1 ≤ X) :
    |suzukiLocalCenteredPrimeCofactorTail X| ≤ 4100 + 100 * X ^ (B - 1/2) := by
  have hG := abs_suzukiLocalArithmeticComparison_le_of_re_le hB hβ hX
  have hC : 192 * ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24) ≤ 100 := by
    have hp : Real.pi ^ 2 ≤ (63 / 20 : ℝ) ^ 2 := by
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    linarith
  have h := abs_le.mp (hG.trans (mul_le_mul_of_nonneg_right hC (by positivity)))
  have hT := abs_le.mp (abs_suzukiLocalComparison_add_centeredPrimeCofactorTail_le hX)
  rw [abs_le]
  constructor <;> linarith [h.1, h.2, hT.1, hT.2]

/-- An off-line zero would force arbitrarily large positive power-size
excursions after restricting the remaining divisor sum to ordinary primes. -/
theorem exists_centeredPrimeCofactorTail_excursions_of_not_rh (h : ¬ RiemannHypothesis) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 0 ≤ C → ∀ X₀ : ℝ, 2 ≤ X₀ →
      ∃ X : ℝ, X₀ ≤ X ∧ C * X ^ ε < suzukiLocalCenteredPrimeCofactorTail X := by
  obtain ⟨ε, hε, he⟩ := exists_centeredCofactorTail_excursions_of_not_rh h
  refine ⟨ε, hε, fun C hC X₀ hX₀ => ?_⟩
  obtain ⟨X, hX, heX⟩ := he (C + 3024) (by linarith) X₀ hX₀
  have h1 : 1 ≤ X := by linarith
  have hb := (abs_le.mp (abs_suzukiLocalCenteredCofactorTail_sub_prime_le h1)).2
  refine ⟨X, hX, ?_⟩
  nlinarith [Real.one_le_rpow h1 hε.le]

/-- The explicit threshold at B = 1/2 gives a single uniform one-sided
criterion for the ordinary-prime sum. Even an eventual upper bound suffices. -/
theorem riemannHypothesis_iff_centeredPrimeCofactorTail_eventually_le :
    RiemannHypothesis ↔ ∃ X₀ : ℝ, 2 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      suzukiLocalCenteredPrimeCofactorTail X ≤ 4200 := by
  constructor
  · intro h
    refine ⟨2, le_rfl, fun X hX => ?_⟩
    have hβ (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 :=
      (h rho.1 rho.2.1 rho.2.2.1 rho.2.2.2).le
    have ht := abs_centeredPrimeCofactorTail_le_of_re_le (by constructor <;> norm_num)
      hβ (by linarith : 1 ≤ X)
    norm_num at ht
    exact (le_abs_self _).trans ht
  · rintro ⟨X₀,hX₀,h⟩
    by_contra hf
    obtain ⟨ε,hε,he⟩ := exists_centeredPrimeCofactorTail_excursions_of_not_rh hf
    obtain ⟨X,hX,hbig⟩ := he 4200 (by norm_num) X₀ hX₀
    linarith [h X hX, Real.one_le_rpow (by linarith : 1 ≤ X) hε.le]

end
end RiemannGaussian
