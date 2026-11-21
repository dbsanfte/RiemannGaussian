import RiemannGaussian.SuzukiLocalCancellationCofactorMellin
import RiemannGaussian.SuzukiLocalCancellationReciprocal
import Mathlib.NumberTheory.ZetaValues

/-! # The Bernoulli sum governing a band of actual prime cofactors

Integrating a physical hinge gives the normalized logarithmic hinge. This
allows the signed Suzuki functional to test a quadratic lattice remainder. -/

namespace RiemannGaussian.SuzukiReciprocal
noncomputable section
open Set MeasureTheory

private theorem hinge_int {r a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hr : r ≤ a) :
    (∫ x in a..z, max (x-r) 0 / x^2) = Real.log z + r/z - (Real.log a+r/a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le haz] at hx
    have hx0 := ha.trans_le hx.1
    rw [max_eq_left (sub_nonneg.mpr (hr.trans hx.1))]
    have hd := (Real.hasDerivAt_log hx0.ne').add
      ((hasDerivAt_const x r).div (hasDerivAt_id x) hx0.ne')
    convert hd using 1
    · rfl
    · dsimp
      field_simp
      ring
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le haz]
    exact continuousOn_of_forall_continuousAt fun x hx => by
      have hx0 := ha.trans_le hx.1
      fun_prop (disch := positivity)

private theorem hinge_int_zero {r a z : ℝ} (haz : a ≤ z) (hr : z ≤ r) :
    (∫ x in a..z, max (x-r) 0 / x^2) = 0 := by
  have he : (∫ x in a..z, max (x-r) 0 / x^2) = ∫ _x : ℝ in a..z, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le haz] at hx
    simp [max_eq_right (sub_nonpos.mpr (hx.2.trans hr))]
  rw [he]
  simp

private theorem log_hinge {z r : ℝ} (hz : 1 ≤ z) (hr : 0 < r) :
    max (Real.log z - Real.log r) 0 - max (0-Real.log r) 0 =
      max (z-r) 0 / z - max (1-r) 0 +
        ∫ x in (1:ℝ)..z, max (x-r) 0 / x^2 := by
  have hz0 := zero_lt_one.trans_le hz
  by_cases h : r ≤ 1
  · have hlog := Real.log_nonpos hr.le h
    rw [hinge_int zero_lt_one hz h, max_eq_left (sub_nonneg.mpr (Real.log_le_log hr (h.trans hz))),
      max_eq_left (sub_nonneg.mpr hlog), max_eq_left (sub_nonneg.mpr (h.trans hz)),
      max_eq_left (sub_nonneg.mpr h), Real.log_one]
    field_simp
    ring
  · have h1 := le_of_lt (lt_of_not_ge h)
    have hlog := Real.log_nonneg h1
    rw [max_eq_right (sub_nonpos.mpr hlog), max_eq_right (sub_nonpos.mpr h1)]
    by_cases hrz : z ≤ r
    · rw [hinge_int_zero hz hrz, max_eq_right (sub_nonpos.mpr hrz),
        max_eq_right (sub_nonpos.mpr (Real.log_le_log hz0 hrz))]
      simp
    · have hrz' := (lt_of_not_ge hrz).le
      have hi (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
          IntervalIntegrable (fun x : ℝ => max (x-r) 0 / x^2) volume a b := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hab]
        exact continuousOn_of_forall_continuousAt fun x hx => by
          have hx0 := ha.trans_le hx.1
          fun_prop (disch := positivity)
      rw [← intervalIntegral.integral_add_adjacent_intervals (hi 1 r zero_lt_one h1) (hi r z hr hrz'),
        hinge_int_zero h1 le_rfl, hinge_int hr hrz' le_rfl,
        max_eq_left (sub_nonneg.mpr hrz'), max_eq_left (sub_nonneg.mpr (Real.log_le_log hr hrz'))]
      field_simp
      ring

private theorem poly_int {z : ℝ} (hz : 1 ≤ z) (a b c : ℝ) :
    (∫ x in (1:ℝ)..z, (a*x^2+b*x+c)/x^2) =
      a*z+b*Real.log z-c/z - (a-c) := by
  rw [show a-c = a*1+b*Real.log 1-c/1 by simp]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hz] at hx
    have hx0 := zero_lt_one.trans_le hx.1
    have hd := (((hasDerivAt_id x).const_mul a).add
      ((Real.hasDerivAt_log hx0.ne').const_mul b)).sub
        ((hasDerivAt_const x c).div (hasDerivAt_id x) hx0.ne')
    convert hd using 1
    · rfl
    · dsimp
      field_simp
      ring
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hz]
    exact continuousOn_of_forall_continuousAt fun x hx => by
      have hx0 := zero_lt_one.trans_le hx.1
      fun_prop (disch := positivity)

/-- For a signed finite set of physical atoms, a quadratic approximation
to its physical hinge primitive bounds the complete signed packet. -/
theorem physical_hinge_bound {ι : Type*} (I : Finset ι) (w r : ι → ℝ)
    (hr : ∀ i ∈ I, 0 < r i) {a b c E : ℝ} (hE : 0 ≤ E)
    (h : ∀ y ∈ Icc (1:ℝ) 8, |(∑ i ∈ I, w i * max (y-r i) 0) - (a*y^2+b*y+c)| ≤ E) :
    |∑ i ∈ I, w i * suzukiLocalPhysicalKernel 1 (r i)| ≤ 192*E := by
  let S (y : ℝ) := ∑ i ∈ I, w i*max (y-r i) 0
  let F (s : ℝ) := ∑ i ∈ I, w i*max (s-Real.log (r i)) 0
  let q (y : ℝ) := a*y^2+b*y+c
  let R := fun y => S y-q y
  have hcS : Continuous S := continuous_finsetSum _ (fun i _ => by fun_prop)
  have hcq : Continuous q := by dsimp [q]; fun_prop
  have hcR : Continuous R := hcS.sub hcq
  have hkernel (i : ι) (hi : i ∈ I) : suzukiLocalPhysicalKernel 1 (r i) =
      Real.exp (-(Real.log (r i))/2)*suzukiLocalSignedKernel (Real.log (r i)-0) := by
    rw [suzukiLocalPhysicalKernel, div_one, sub_zero, neg_div, Real.exp_neg, Real.exp_half, Real.exp_log (hr i hi)]
    ring
  have hEq {z : ℝ} (hz : 1 ≤ z) : F (Real.log z)-F 0 =
      S z/z-S 1 + ∫ y in (1:ℝ)..z, S y/y^2 := by
    have hi (i : ι) : IntervalIntegrable (fun y : ℝ => w i * (max (y-r i) 0 / y^2)) volume 1 z := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hz]
      exact continuousOn_of_forall_continuousAt fun y hy => by
        have hy0 := zero_lt_one.trans_le hy.1
        fun_prop (disch := positivity)
    have hsum := Finset.sum_congr rfl (s₁ := I) (fun i hi => congrArg (w i * ·) (log_hinge hz (hr i hi)))
    simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← intervalIntegral.integral_const_mul] at hsum
    rw [← intervalIntegral.integral_finsetSum (fun i _ => hi i)] at hsum
    simpa only [F,S,← mul_div_assoc, ← Finset.sum_div] using hsum
  have hbd (z : ℝ) (hz : z ∈ Icc (1:ℝ) 8) :
      |R z/z + ∫ y in (1:ℝ)..z, R y/y^2| ≤ 8*E := by
    have hd : |R z/z| ≤ E := by
      rw [abs_div, abs_of_pos (zero_lt_one.trans_le hz.1)]
      exact (div_le_self (abs_nonneg _) hz.1).trans (h z hz)
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (C := E)
      (f := fun y : ℝ => R y/y^2) (a := 1) (b := z) (fun y hy => by
        rw [uIoc_of_le hz.1] at hy
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg y)]
        apply (div_le_self (abs_nonneg _) _).trans (h y ⟨hy.1.le,hy.2.trans hz.2⟩)
        nlinarith [hy.1])
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hz.1)] at hi
    exact (abs_add_le ..).trans (by nlinarith [mul_le_mul_of_nonneg_left hz.2 hE])
  rw [Finset.sum_congr rfl (fun i hi => congrArg (w i * ·) (hkernel i hi))]
  have hh := abs_suzukiLocal_weighted_atomic_sum_le I w (fun i => Real.log (r i)) (t := 0)
    (B := 8*E) (c := 2*a) (a := F 0-S 1-a+b+c) (b := b) (by positivity) (fun s hs => by
      let z := Real.exp s
      have hz : z ∈ Icc (1:ℝ) 8 := by
        refine ⟨Real.one_le_exp_iff.mpr hs.1, ?_⟩
        have he := Real.exp_le_exp.mpr hs.2
        norm_num [show (3:ℝ)*Real.log 2 = Real.log 2+Real.log 2+Real.log 2 by ring,
          Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2)] at he
        exact he
      have hz0 := zero_lt_one.trans_le hz.1
      have hi (f : ℝ → ℝ) (hf : Continuous f) :
          IntervalIntegrable (fun y => f y/y^2) volume 1 z := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hz.1]
        exact continuousOn_of_forall_continuousAt fun y hy => by
          have hy0 := zero_lt_one.trans_le hy.1
          fun_prop (disch := positivity)
      have he := hEq hz.1
      have hsplit : (∫ y in (1:ℝ)..z, R y/y^2) =
          (∫ y in (1:ℝ)..z, S y/y^2) - (∫ y in (1:ℝ)..z, q y/y^2) := by
        simp only [R,sub_div]
        exact intervalIntegral.integral_sub (hi S hcS) (hi q hcq)
      have hpoly : (∫ y in (1:ℝ)..z, q y/y^2) = a*z+b*Real.log z-c/z-(a-c) := poly_int hz.1 a b c
      have hb := hbd z hz
      change |F s - (2*a*z+(F 0-S 1-a+b+c)+b*s)| ≤ _
      convert hb using 2
      rw [hsplit,hpoly]
      dsimp only [R,q]
      have hez : Real.log z = s := Real.log_exp _
      rw [hez] at he ⊢
      field_simp at he ⊢
      linarith)
  norm_num [← mul_assoc] at hh ⊢
  exact hh

private theorem grid_index_sum (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, (k:ℝ)) = n*((n:ℝ)+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.cast_succ]
    ring

/-- Exact hinge quadrature on a complete positive grid. The Fourier remainder
is the ordinary second Bernoulli polynomial at the fractional part. -/
theorem grid_hinge {v y : ℝ} (hv : 0 < v) (hy : 0 ≤ y) {N : ℕ}
    (hN : ⌊y/v⌋₊ ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, max (y-v*k) 0) =
      y^2/(2*v)-y/2+v/12-v/2*bernoulliFun 2 (Int.fract (y/v)) := by
  let n := ⌊y/v⌋₊
  have hq : 0 ≤ y/v := div_nonneg hy hv.le
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_right hN
  rw [← Finset.sum_subset hsub (fun k hk hk' => ?_)]
  · have he (k : ℕ) (hk : k ∈ Finset.Icc 1 n) : max (y-v*k) 0 = y-v*k := by
      apply max_eq_left
      have hky := (Nat.le_floor_iff hq).mp (Finset.mem_Icc.mp hk).2
      linarith [(le_div_iff₀ hv).mp hky]
    rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, ← Finset.mul_sum, grid_index_sum,
      Finset.sum_const, Nat.card_Icc]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, bernoulliFun_two, Int.fract,
      ← natCast_floor_eq_intCast_floor hq]
    dsimp [n]
    field_simp
    ring
  · have hkn : n < k := by
      have hp := (Finset.mem_Icc.mp hk).1
      exact lt_of_not_ge (fun h => hk' (Finset.mem_Icc.mpr ⟨hp,h⟩))
    apply max_eq_right
    have hky := (Nat.floor_lt hq).mp hkn
    linarith [(div_lt_iff₀ hv).mp hky]

private theorem profile_full {v : ℝ} (hv : 0 < v) (h1 : v ≤ 1) :
    suzukiLocalCofactorProfile v =
      ∑ k ∈ Finset.Icc 1 ⌊8/v⌋₊, suzukiLocalPhysicalKernel 1 (v*k) := by
  have he : Finset.Icc 1 ⌊8/v⌋₊ = Finset.Ioc 0 ⌊8/v⌋₊ := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have hn : 1 ≤ ⌊8/v⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by
    simpa using (one_le_div hv).mpr (by linarith : v ≤ 8))
  rw [suzukiLocalCofactorProfile_eq_row hv, he,
    ← Finset.sum_Ioc_consecutive _ (by decide : 0 ≤ 1) hn,
    show Finset.Ioc 0 1 = ({1} : Finset ℕ) by decide]
  simp [suzukiLocalPhysicalKernel_eq_zero_of_le (by norm_num : (0:ℝ)<1) h1]

/-- Cancellation of the Bernoulli sum controls the actual joint proper-cofactor
sum, uniformly in the number, spacings, signs and sizes of its weights. -/
theorem weighted_profile_le {ι : Type*} (I : Finset ι) (w v : ι → ℝ)
    (hv : ∀ i ∈ I, v i ∈ Ioc (0:ℝ) 1) {E : ℝ} (hE : 0 ≤ E)
    (hb : ∀ y ∈ Icc (1:ℝ) 8,
      |∑ i ∈ I, w i * v i * bernoulliFun 2 (Int.fract (y/v i))| ≤ E) :
    |∑ i ∈ I, w i*suzukiLocalCofactorProfile (v i)| ≤ 96*E := by
  classical
  let K (i : ι) := Finset.Icc 1 ⌊8/v i⌋₊
  let T := I.sigma K
  let wt (j : Σ _ : ι, ℕ) := w j.1
  let atx (j : Σ _ : ι, ℕ) := v j.1*j.2
  have hpos (j : Σ _ : ι, ℕ) (hj : j ∈ T) : 0 < atx j := by
    obtain ⟨hji,hjk⟩ := Finset.mem_sigma.mp hj
    exact mul_pos (hv _ hji).1 (by exact_mod_cast (Finset.mem_Icc.mp hjk).1)
  let a := ∑ i ∈ I, w i/(2*v i)
  let b := ∑ i ∈ I, -w i/2
  let c := ∑ i ∈ I, w i*v i/12
  have hg (y : ℝ) (hy : y ∈ Icc (1:ℝ) 8) :
      (∑ j ∈ T, wt j*max (y-atx j) 0) =
        a*y^2+b*y+c-(1/2)*∑ i ∈ I, w i*v i*bernoulliFun 2 (Int.fract (y/v i)) := by
    simp only [T, wt, atx, Finset.sum_sigma, a, b, c, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_sum, grid_hinge (hv i hi).1 (by linarith [hy.1])
      (Nat.floor_le_floor (div_le_div_of_nonneg_right hy.2 (hv i hi).1.le))]
    ring
  have hq := physical_hinge_bound T wt atx hpos (a := a) (b := b) (c := c) (E := E/2)
    (by positivity) (fun y hy => by
      rw [hg y hy, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      linarith [hb y hy])
  have hr : (∑ j ∈ T, wt j * suzukiLocalPhysicalKernel 1 (atx j)) =
      ∑ i ∈ I, w i * suzukiLocalCofactorProfile (v i) := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro i hi
    rw [profile_full (hv i hi).1 (hv i hi).2, Finset.mul_sum]
  rw [hr] at hq
  linarith

private theorem bernoulli_cos (y : ℝ) :
    HasSum (fun n : ℕ => 1/(n:ℝ)^2 * Real.cos (2*Real.pi*n*y))
      (Real.pi^2 * bernoulliFun 2 (Int.fract y)) := by
  have hh := hasSum_one_div_nat_pow_mul_cos (k := 1) (by decide)
    (x := Int.fract y) ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have he (n : ℕ) : Real.cos (2*Real.pi*n*Int.fract y) = Real.cos (2*Real.pi*n*y) := by
    rw [show 2*Real.pi*n*Int.fract y = 2*Real.pi*n*y - (((n:ℤ)*⌊y⌋:ℤ):ℝ)*(2*Real.pi) by
      push_cast
      rw [Int.fract]
      ring, Real.cos_sub_int_mul_two_pi]
  change HasSum _ (_ * bernoulliFun (2*1) (Int.fract y)) at hh
  norm_num [Nat.factorial, mul_pow, he] at hh
  simp only [one_div, bernoulliFun_two]
  convert hh using 1
  ring

private theorem sum_bernoulli_cos {ι : Type*} (I : Finset ι) (a t : ι → ℝ) :
    HasSum (fun n : ℕ => 1/(n:ℝ)^2 * ∑ i ∈ I, a i * Real.cos (2*Real.pi*n*t i))
      (Real.pi^2 * ∑ i ∈ I, a i * bernoulliFun 2 (Int.fract (t i))) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [hasSum_zero]
  | @insert i I hi ih =>
    have hh := ((bernoulli_cos (t i)).mul_left (a i)).add ih
    simp only [Finset.sum_insert hi, mul_add]
    convert hh using 1
    · ext n
      ring
    · ring

/-- A summable majorant for the weighted cosine modes gives a bound on the
original signed cofactor sum. The zero frequency on the left is zero. -/
theorem weighted_profile_le_of_modes {ι : Type*} (I : Finset ι) (w v : ι → ℝ)
    (hv : ∀ i ∈ I, v i ∈ Ioc (0:ℝ) 1) {U : ℕ → ℝ} {C : ℝ}
    (hU : HasSum U C) (hC : 0 ≤ C)
    (hm : ∀ y ∈ Icc (1:ℝ) 8, ∀ n : ℕ,
      |1/(n:ℝ)^2 * ∑ i ∈ I, w i*v i*Real.cos (2*Real.pi*n*(y/v i))| ≤ U n) :
    |∑ i ∈ I, w i*suzukiLocalCofactorProfile (v i)| ≤ 96*(C/Real.pi^2) := by
  apply weighted_profile_le I w v hv (by positivity)
  intro y hy
  have hp := sum_bernoulli_cos I (fun i => w i*v i) (fun i => y/v i)
  have hu := hasSum_le (fun n => (abs_le.mp (hm y hy n)).2) hp hU
  have hl := hasSum_le (fun n => (abs_le.mp (hm y hy n)).1) hU.neg hp
  have hab := abs_le.mpr ⟨hl,hu⟩
  rw [abs_mul,abs_of_nonneg (sq_nonneg _)] at hab
  exact (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr (by simpa only [mul_comm] using hab)

/-- The ordinary-prime contribution from an exact half-open interval. -/
def ordinaryPrimeBand (X : ℝ) (P Q : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc P Q).filter Nat.Prime, Real.log p *
    ∑ k ∈ Finset.Ioc 1 ⌊8*X/p⌋₊, suzukiLocalPhysicalKernel X ((p:ℝ)*k)

/-- A bound for the actual reciprocal prime modes yields a bound on the
original two-variable prime sum with its full Fourier and dilation constants. -/
theorem ordinaryPrimeBand_le_of_modes {X : ℝ} (hx : 0 < X) (P Q : ℕ) (hQ : (Q:ℝ) ≤ X)
    {U : ℕ → ℝ} {C : ℝ} (hU : HasSum U C) (hC : 0 ≤ C)
    (hm : ∀ y ∈ Icc (1:ℝ) 8, ∀ n : ℕ, |1/(n:ℝ)^2 *
      ∑ p ∈ (Finset.Ioc P Q).filter Nat.Prime,
        (p:ℝ)*Real.log p*Real.cos (2*Real.pi*n*y*X/p)| ≤ U n) :
    |ordinaryPrimeBand X P Q| ≤ 96*C/(Real.pi^2*X*Real.sqrt X) := by
  let I := (Finset.Ioc P Q).filter Nat.Prime
  have hpos (p : ℕ) (hp : p ∈ I) : (0:ℝ) < p := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have hv (p : ℕ) (hp : p ∈ I) : (p:ℝ)/X ∈ Ioc (0:ℝ) 1 := by
    refine ⟨div_pos (hpos p hp) hx, (div_le_one hx).mpr ?_⟩
    exact le_trans (by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2) hQ
  have hh := weighted_profile_le_of_modes I (fun p => X*Real.log p) (fun p => (p:ℝ)/X)
    hv hU hC (fun y hy n => by
      convert hm y hy n using 3
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 := (hpos p hp).ne'
      rw [show 2*Real.pi*n*(y/((p:ℝ)/X)) = 2*Real.pi*n*y*X/p by field]
      field)
  have he : X*Real.sqrt X*ordinaryPrimeBand X P Q =
      ∑ p ∈ I, X*Real.log p*suzukiLocalCofactorProfile (p/X) := by
    unfold ordinaryPrimeBand
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← suzukiLocalCofactorProfile_scaled_row hx (hpos p hp)]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hx)]
  rw [← he, abs_mul, abs_of_pos (mul_pos hx (Real.sqrt_pos.mpr hx))] at hh
  apply (le_div_iff₀ (by positivity)).mpr
  have hk := (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mp
    (show X*Real.sqrt X*|ordinaryPrimeBand X P Q| ≤ 96*C/Real.pi^2 by
      simpa only [mul_div_assoc] using hh)
  linarith only [hk]

/-- The same physical sum and center with a selectable lower prime cutoff. -/
def centeredPrimeTailFrom (X : ℝ) (Q : ℕ) : ℝ :=
  ordinaryPrimeBand X Q ⌊8*X⌋₊ -
    (-4*Real.log 2*Real.sqrt 2*(Real.sqrt 2-1)^2)*Real.sqrt X

/-- Removing an exact band keeps the original center and both endpoint conventions. -/
theorem band_add_centeredPrimeTailFrom {X : ℝ} {Q : ℕ}
    (hQ : ⌊X^(3/4:ℝ)⌋₊ ≤ Q) (hQ' : Q ≤ ⌊8*X⌋₊) :
    ordinaryPrimeBand X ⌊X^(3/4:ℝ)⌋₊ Q + centeredPrimeTailFrom X Q =
      suzukiLocalCenteredPrimeCofactorTail X := by
  unfold centeredPrimeTailFrom suzukiLocalCenteredPrimeCofactorTail ordinaryPrimeBand
  simp only [Finset.sum_filter, ← add_sub_assoc, Finset.sum_Ioc_consecutive _ hQ hQ']

/-- An interval with eventual cost at most one can be removed in the
contradiction with the numerical threshold 4201. -/
theorem riemannHypothesis_iff_centeredPrimeTailFrom_le (Q : ℝ → ℕ) {A : ℝ} (hA : 2 ≤ A)
    (hb : ∀ X ≥ A, ⌊X^(3/4:ℝ)⌋₊ ≤ Q X ∧ Q X ≤ ⌊8*X⌋₊ ∧
      |ordinaryPrimeBand X ⌊X^(3/4:ℝ)⌋₊ (Q X)| ≤ 1) :
    RiemannHypothesis ↔ ∃ B : ℝ, 2 ≤ B ∧ ∀ X ≥ B, centeredPrimeTailFrom X (Q X) ≤ 4201 := by
  constructor
  · intro h
    obtain ⟨B,hB,ht⟩ := riemannHypothesis_iff_centeredPrimeCofactorTail_eventually_le.mp h
    refine ⟨max A B,hB.trans (le_max_right ..),fun X hX => ?_⟩
    obtain ⟨h1,h2,h3⟩ := hb X ((le_max_left ..).trans hX)
    linarith [band_add_centeredPrimeTailFrom h1 h2, (abs_le.mp h3).1,
      ht X ((le_max_right ..).trans hX)]
  · rintro ⟨B,_,ht⟩
    by_contra h
    obtain ⟨ε,hε,he⟩ := exists_centeredPrimeCofactorTail_excursions_of_not_rh h
    obtain ⟨X,hX,hbig⟩ := he 4202 (by norm_num) (max A B) (hA.trans (le_max_left ..))
    have hAX := (le_max_left A B).trans hX
    obtain ⟨h1,h2,h3⟩ := hb X hAX
    have hp := Real.one_le_rpow (show 1 ≤ X by linarith) hε.le
    linarith [band_add_centeredPrimeTailFrom h1 h2, (abs_le.mp h3).2,
      ht X ((le_max_right ..).trans hX)]

/-- The classical Ingham and Huxley density exponents on the two halves of
their range of application. -/
def primeBandDensityExponent (σ : ℝ) : ℝ :=
  if σ ≤ 3/4 then 3*(1-σ)/(2-σ) else 3*(1-σ)/(3*σ-1)

/-- The real-part range supplied by the repository's seven-eighths theorem
gives a negative power after summing reciprocal phases at cutoff 33/40. -/
theorem primeBand_density_exponent {σ : ℝ} (hσ : 1/2 ≤ σ) (hβ : σ ≤ 7/8) :
    33/40*(σ+3/2-primeBandDensityExponent σ)+primeBandDensityExponent σ-2 ≤ -(1/4160) := by
  unfold primeBandDensityExponent
  split_ifs with h
  · by_cases hsmall : σ ≤ 13/20
    · have hd : 3*(1-σ)/(2-σ) ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
      linarith
    · have hd : 3*(1-σ)/(2-σ) ≤ 7/9 := (div_le_iff₀ (by linarith)).mpr (by linarith)
      linarith
  · have hpos : 0 < 3*σ-1 := by linarith
    have hp : (σ-7/8)*(10296*σ-6120) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    have he := div_mul_cancel₀ (3*(1-σ)) hpos.ne'
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith only [hp,he]

/-- This exponent bound applies to every actual zero in the right half of
the critical strip, with no zero-location hypothesis on the caller. -/
theorem primeBand_zero_density_exponent (ρ : NontrivialZetaZero) (hρ : 1/2 ≤ ρ.1.re) :
    33/40*(ρ.1.re+3/2-primeBandDensityExponent ρ.1.re)+
      primeBandDensityExponent ρ.1.re-2 ≤ -(1/4160) :=
  primeBand_density_exponent hρ (suzukiLocalZero_re_le_seven_eighths ρ)

end
end RiemannGaussian.SuzukiReciprocal
