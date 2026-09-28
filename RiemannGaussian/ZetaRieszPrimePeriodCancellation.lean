/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBroadTripleBudget

/-!
# Signed cancellation across a literal prime phase period

The original prime windows are summed before taking an absolute value.
The comparison is relative to their local radial mass, not a source-scale
PNT approximation. Its use in a whole-sum bound must retain the unselected
population and pay this explicit relative cost.
-/

namespace RiemannGaussian.ZetaRieszPrimePeriodCancellation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszCapacityPhaseBudget

/-- The phase mesh partitions literal primes exactly, including the
half-open endpoint convention. It is not a replacement of the measure. -/
theorem sum_logPrimes_grid {β : Type*} [AddCommMonoid β] (f : ℕ → β)
    (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (M : ℕ) :
    (∑ p ∈ logPrimes a (M*h), f p) =
      ∑ i ∈ Finset.range M, ∑ p ∈ logPrimes (a+i*h) h, f p := by
  induction M with
  | zero =>
    have he : logPrimes a 0 = ∅ := by
      ext p
      simp only [ZetaRieszMacroPrimeWindows.mem_logPrimes_iff,Finset.notMem_empty,iff_false]
      rintro ⟨_,hl,hu⟩
      linarith
    simp [he]
  | succ M ih =>
    rw [Nat.cast_succ,add_mul,one_mul,
      ZetaRieszMacroPrimeWindows.logPrimes_add a (mul_nonneg (Nat.cast_nonneg _) hh) hh,
      Finset.sum_union (ZetaRieszMacroPrimeWindows.logPrimes_adjacent_disjoint a (M*h) h),
      Finset.sum_range_succ,ih]

/-- A complete period is the same prime population before and after
phase meshing; the cofactor logarithm is present on both sides. -/
theorem sum_prime_period {β : Type*} [AddCommMonoid β] (f : ℕ → β)
    {m : ℕ} (hm : 0 < m) (v b y : ℝ) (hy : 0 < |y|) :
    (∑ p ∈ logPrimes (v-Real.pi/|y|-b) (2*Real.pi/|y|), f p) =
      ∑ i ∈ Finset.range (8*m), ∑ p ∈ logPrimes
        (v+periodAngle m i/|y|-b) (Real.pi/(4*m*|y|)), f p := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hwidth : ((8*m : ℕ) : ℝ)*(Real.pi/(4*m*|y|)) = 2*Real.pi/|y| := by
    push_cast
    field_simp
    ring
  rw [← hwidth,sum_logPrimes_grid f _ (by positivity)]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  unfold periodAngle
  field_simp
  ring

/-- Opposite half-periods cancel exactly, at the existing finite mesh. -/
theorem sum_period_cos_eq_zero {m : ℕ} (hm : 0 < m) :
    (∑ i ∈ Finset.range (8*m), Real.cos (periodAngle m i)) = 0 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hshift (i : ℕ) : Real.cos (periodAngle m (4*m+i)) =
      -Real.cos (periodAngle m i) := by
    have he : periodAngle m (4*m+i) = periodAngle m i+Real.pi := by
      unfold periodAngle
      push_cast
      field_simp [ne_of_gt hmR]
      ring
    rw [he,Real.cos_add_pi]
  rw [show 8*m = 4*m+4*m by omega,Finset.sum_range_add]
  simp only [hshift,Finset.sum_neg_distrib]
  ring

/-- A full signed period pays only variation of its cell masses and
within-cell phases. No individual adverse cosine is replaced by its norm. -/
theorem signed_period_bound {m : ℕ} (hm : 0 < m)
    (F mass : ℕ → ℝ) {M η ε : ℝ} (hε : 0 ≤ ε)
    (hmass : ∀ i ∈ Finset.range (8*m), |mass i-M| ≤ η*M)
    (hphase : ∀ i ∈ Finset.range (8*m),
      |F i+Real.cos (periodAngle m i)*mass i| ≤ ε*mass i) :
    |∑ i ∈ Finset.range (8*m), F i| ≤
      (8*m : ℝ)*(η+ε*(1+η))*M := by
  have hrow (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      |F i+Real.cos (periodAngle m i)*M| ≤ (η+ε*(1+η))*M := by
    have hd := hmass i hi
    have hdu : mass i ≤ (1+η)*M := by linarith [(abs_le.mp hd).2]
    have hc : |Real.cos (periodAngle m i)*(M-mass i)| ≤ η*M := by
      rw [abs_mul,abs_sub_comm]
      exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans
        (by simpa using hd)
    calc
      _ = |(F i+Real.cos (periodAngle m i)*mass i)+
          Real.cos (periodAngle m i)*(M-mass i)| := by congr 1; ring
      _ ≤ |F i+Real.cos (periodAngle m i)*mass i|+
          |Real.cos (periodAngle m i)*(M-mass i)| := abs_add_le _ _
      _ ≤ ε*mass i+η*M := add_le_add (hphase i hi) hc
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hdu hε]
  have he : (∑ i ∈ Finset.range (8*m), F i) =
      ∑ i ∈ Finset.range (8*m), (F i+Real.cos (periodAngle m i)*M) := by
    rw [Finset.sum_add_distrib,← Finset.sum_mul,sum_period_cos_eq_zero hm]
    simp
  rw [he]
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hrow).trans_eq (by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
    ring))

/-- Keep the phase inside each actual weighted prime sum. The cofactor
logarithm remains in the literal window endpoint and in every cosine. -/
theorem weighted_cell_phase_bound (w : ℕ → ℝ) {a h b y : ℝ}
    (hw : ∀ p ∈ logPrimes a h, 0 ≤ w p) :
    |(∑ p ∈ logPrimes a h, w p*Real.cos (y*(Real.log p+b)))-
      Real.cos (y*(a+b))*(∑ p ∈ logPrimes a h, w p)| ≤
        (|y| * h)*(∑ p ∈ logPrimes a h, w p) := by
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hb := logPrimes_bounds hp
  have hd : |y*(Real.log p+b)-y*(a+b)| ≤ |y| * h := by
    rw [show y*(Real.log p+b)-y*(a+b) = y*(Real.log p-a) by ring,
      abs_mul,abs_of_nonneg (show 0 ≤ Real.log p-a by linarith [hb.2.1])]
    exact mul_le_mul_of_nonneg_left (by linarith [hb.2.2]) (abs_nonneg y)
  have hc := (Real.abs_cos_sub_cos_le (y*(Real.log p+b)) (y*(a+b))).trans hd
  calc
    _ = w p*|Real.cos (y*(Real.log p+b))-Real.cos (y*(a+b))| := by
      rw [mul_comm (Real.cos (y*(a+b))),← mul_sub,abs_mul,abs_of_nonneg (hw p hp)]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc (hw p hp)]

/-- Near-constant nonnegative weights on the actual prime windows lose
at most one five-hundredth of the common full-period mass. All prime
counting premises are discharged by the proved sharp interval estimates. -/
theorem eventually_weighted_prime_period {m : ℕ} (hm : 0 < m)
    {y α : ℝ} (hy : 54 ≤ |y|) (hα : 0 < α)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ N : ℕ in atTop, ∀ (v b W : ℝ) (w : ℕ → ℝ),
      Real.cos (y*v) = -1 → α*N+1 ≤ v-b → 0 ≤ W →
      (∀ i ∈ Finset.range (8*m), ∀ p ∈ logPrimes
        (v+periodAngle m i/|y|-b) (Real.pi/(4*m*|y|)),
          W ≤ w p ∧ w p ≤ (1003/1000 : ℝ)*W) →
      |∑ i ∈ Finset.range (8*m), ∑ p ∈ logPrimes
          (v+periodAngle m i/|y|-b) (Real.pi/(4*m*|y|)),
          w p*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b))| ≤
        (1/500 : ℝ)*(8*m)*W*(Real.pi/(4*m*|y|))/(v-b) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := abs_pos.mp hy0
  let h := Real.pi/(4*m*|y|)
  have hh : 0 < h := by dsimp [h]; positivity
  have ht : Tendsto (fun N : ℕ => α*N) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hα
  filter_upwards [ZetaRieszPhaseBudget.eventually_phase_window_mass hh hsmall hα,
    ht.eventually_ge_atTop 100000] with N hN hlarge v b W w hv hab hW hw
  let a := v-b
  let T := fun i => v+periodAngle m i/|y|-b
  let mass := fun i => ∑ p ∈ logPrimes (T i) h, w p*(p : ℝ)⁻¹
  let F := fun i => ∑ p ∈ logPrimes (T i) h,
    w p*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b))
  let M := (2003/2000 : ℝ)*W*h/a
  have ha : (100000 : ℝ) ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hT (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      α*N ≤ T i ∧ a-1 ≤ T i ∧ T i ≤ a+1 := by
    have hb := periodAngle_bounds hm (Finset.mem_range.mp hi).le
    have hl := div_le_div_of_nonneg_right hb.1 hy0.le
    have hu := div_le_div_of_nonneg_right hb.2 hy0.le
    have hp : Real.pi/|y| ≤ 1 := (div_le_iff₀ hy0).mpr (by linarith [Real.pi_lt_four])
    rw [neg_div] at hl
    dsimp only [T,a]
    constructor
    · linarith
    · constructor <;> linarith
  have hmass (i : ℕ) (hi : i ∈ Finset.range (8*m)) : |mass i-M| ≤ (7/4000 : ℝ)*M := by
    have hb := hT i hi
    have hTi : 0 < T i := by linarith
    have hprime := hN (T i) hb.1
    have hlow : W*((9999/10000 : ℝ)*h/(T i)) ≤ mass i := by
      apply (mul_le_mul_of_nonneg_left hprime.1 hW).trans
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right
        (hw i hi p hp).1 (inv_nonneg.mpr (Nat.cast_nonneg p)))
    have hupp : mass i ≤ ((1003/1000 : ℝ)*W)*((10001/10000 : ℝ)*h/(T i)) := by
      calc
        _ ≤ ∑ p ∈ logPrimes (T i) h, ((1003/1000 : ℝ)*W)*(p : ℝ)⁻¹ :=
          Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right
            (hw i hi p hp).2 (inv_nonneg.mpr (Nat.cast_nonneg p)))
        _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hprime.2 (by positivity)
    have hratioL : (4999/5000 : ℝ)/a ≤ (9999/10000)/(T i) := by
      apply (div_le_div_iff₀ ha0 hTi).mpr
      linarith [hb.2.2]
    have hratioU : (1003/1000 : ℝ)*(10001/10000)/(T i) ≤ (627/625)/a := by
      apply (div_le_div_iff₀ hTi ha0).mpr
      linarith [hb.2.1]
    have hL := mul_le_mul_of_nonneg_left hratioL (show 0 ≤ W*h by positivity)
    have hU := mul_le_mul_of_nonneg_left hratioU (show 0 ≤ W*h by positivity)
    apply abs_le.mpr
    dsimp only [M] at hM ⊢
    ring_nf at hlow hupp hL hU hM ⊢
    constructor <;> linarith only [hlow,hupp,hL,hU,hM]
  have hcell (i : ℕ) (hi : i ∈ Finset.range (8*m)) :
      |F i+Real.cos (periodAngle m i)*mass i| ≤ (|y| * h)*mass i := by
    have he : T i+b = v+periodAngle m i/|y| := by dsimp [T]; ring
    have hc := weighted_cell_phase_bound (fun p => w p*(p : ℝ)⁻¹)
      (a := T i) (h := h) (b := b) (y := y) (fun p hp =>
        mul_nonneg (hW.trans (hw i hi p hp).1) (inv_nonneg.mpr (Nat.cast_nonneg p)))
    rw [he] at hc
    have hp := ZetaRieszPhaseBudget.phase_at_negative_peak hyne hv (periodAngle m i)
    dsimp only [F,mass]
    rw [← hp]
    simpa only [neg_mul,sub_eq_add_neg] using hc
  have hs := signed_period_bound hm F mass (show 0 ≤ |y| * h by positivity) hmass hcell
  have hsmall' : ((7/4000 : ℝ)+(|y| * h)*(1+7/4000))*(2003/2000) ≤ 1/500 := by
    change |y| * h ≤ 1/10000 at hphase
    linarith only [hphase]
  have hp := mul_le_mul_of_nonneg_right hsmall'
    (show 0 ≤ (8*m : ℝ)*(W*h/a) by positivity)
  change |∑ i ∈ Finset.range (8*m), F i| ≤ _
  dsimp only [M,a] at hs hp
  apply hs.trans
  convert hp using 1 <;> dsimp only [h] <;> ring

/-- The same signed cancellation retains the actual factorial kernel
and its extra logarithm from the triple Riesz coefficient. The endpoints
move with the unchanged cofactor logarithm; no saddle is frozen. -/
theorem eventually_factorial_prime_period {m : ℕ} (hm : 0 < m)
    {y α : ℝ} (hy : 54 ≤ |y|) (hα : 0 < α)
    (hsmall : Real.pi/(4*m*|y|) ≤ 1/100000)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ 1/10000) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ,
      Real.cos (y*v) = -1 →
      (39/20 : ℝ)*N ≤ v-Real.pi/|y| → v+Real.pi/|y| ≤ (203/100 : ℝ)*N →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (501/500 : ℝ)*V ∧
      ∀ b : ℝ, α*N+1 ≤ v-b →
      |∑ i ∈ Finset.range (8*m), ∑ p ∈ logPrimes
          (v+periodAngle m i/|y|-b) (Real.pi/(4*m*|y|)),
          (Real.exp (-(Real.log p+b)/2)*(Real.log p+b)^(N+1)/N.factorial)*
            (p : ℝ)⁻¹*Real.cos (y*(Real.log p+b))| ≤
        (1/500 : ℝ)*(8*m)*(V*(v-Real.pi/|y|))*(Real.pi/(4*m*|y|))/(v-b) := by
  have hy0 : 0 < |y| := by linarith
  have hwidth : 2*Real.pi/|y| ≤ 1/8 :=
    (div_le_iff₀ hy0).mpr (by nlinarith [Real.pi_lt_d4])
  rw [mul_div_assoc] at hwidth
  filter_upwards [eventually_weighted_prime_period hm hy hα hsmall hphase,
    eventually_ge_atTop (1000 : ℕ)] with N hN hlarge v hv hlo hhi
  have hNR : (1000 : ℝ) ≤ N := by exact_mod_cast hlarge
  obtain ⟨V,hV,hperiod⟩ := ZetaRieszPhaseBudget.radial_period_comparable
    (by omega : 0 < N) hy hlo hhi
  refine ⟨V,hV,?_,?_,?_⟩
  · simpa only [zero_div,add_zero] using
      (hperiod 0 (by constructor <;> linarith [Real.pi_pos])).1
  · simpa only [zero_div,add_zero] using
      (hperiod 0 (by constructor <;> linarith [Real.pi_pos])).2
  intro b hab
  let w := fun p : ℕ => Real.exp (-(Real.log p+b)/2)*(Real.log p+b)^(N+1)/N.factorial
  have htlo : 0 < v-Real.pi/|y| := by nlinarith
  apply hN v b (V*(v-Real.pi/|y|)) w hv hab (by positivity)
  intro i hi p hp
  have ht := period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
  have hb := (logPrimes_bounds hp).2
  let T := Real.log p+b
  have hTl : v-Real.pi/|y| ≤ T := by dsimp [T]; linarith [ht.1,hb.1]
  have hTu : T ≤ v+Real.pi/|y| := by dsimp [T]; linarith [ht.2,hb.2]
  have hT0 : 0 ≤ T := htlo.le.trans hTl
  have hx : (T-v)*|y| ∈ Set.Icc (-Real.pi) Real.pi := by
    constructor
    · have hh := mul_le_mul_of_nonneg_right hTl hy0.le
      rw [sub_mul,div_mul_cancel₀ _ hy0.ne'] at hh
      nlinarith only [hh]
    · have hh := mul_le_mul_of_nonneg_right hTu hy0.le
      rw [add_mul v (Real.pi/|y|),div_mul_cancel₀ _ hy0.ne'] at hh
      nlinarith only [hh]
  have hrad := hperiod ((T-v)*|y|) hx
  rw [mul_div_cancel_right₀ _ hy0.ne',add_sub_cancel] at hrad
  have hwe : w p = (Real.exp (-T/2)*T^N/N.factorial)*T := by dsimp [w,T]; rw [pow_succ]; ring
  rw [hwe]
  constructor
  · exact mul_le_mul hrad.1 hTl htlo.le (by positivity)
  · have hc : (501/500 : ℝ)*T ≤ (1003/1000)*(v-Real.pi/|y|) := by
      have hh : T ≤ (v-Real.pi/|y|)+1/8 := by linarith only [hTu,hwidth]
      nlinarith only [hh,hlo,hNR]
    have ha := mul_le_mul_of_nonneg_right hrad.2 hT0
    have hb := mul_le_mul_of_nonneg_left hc hV.le
    nlinarith only [ha,hb]

end
end RiemannGaussian.ZetaRieszPrimePeriodCancellation
