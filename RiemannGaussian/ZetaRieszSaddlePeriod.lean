/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimePeriodCancellation

/-!
# Arbitrarily small signed prime-period costs at the factorial saddle

The precision is fixed before taking the order to infinity. Both prime
counts and the original radial weight are uniform on the moving period.
-/

namespace RiemannGaussian.ZetaRieszSaddlePeriod
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes ZetaRieszPhaseBudget
open ZetaRieszPrimePeriodCancellation ZetaRieszCapacityPhaseBudget

/-- At the actual factorial saddle the relative radial oscillation can
be made arbitrarily small, without replacing the moment order. -/
theorem saddle_weight_ratio {N : ℕ} {η a b : ℝ}
    (hη : 0 < η) (hηu : η ≤ 1) (hN : 20/η ≤ (N : ℝ))
    (ha : 2*N-1 ≤ a) (hau : a ≤ 2*N+2)
    (hb : 2*N-1 ≤ b) (hbu : b ≤ 2*N+2) :
    Real.exp (-b/2)*b^(N+1)/N.factorial ≤
      (1+η)*(Real.exp (-a/2)*a^(N+1)/N.factorial) := by
  have hnη : 20 ≤ (N : ℝ)*η := (div_le_iff₀ hη).mp hN
  have hn : (20 : ℝ) ≤ N := by nlinarith
  have hn0 : (0 : ℝ) < N := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hlow : 0 ≤ ((N : ℝ)+1)/a-1/2 := by
    have hh : (1/2 : ℝ) ≤ ((N : ℝ)+1)/a :=
      (le_div_iff₀ ha0).mpr (by linarith)
    linarith
  have hhigh : ((N : ℝ)+1)/a-1/2 ≤ η/6 := by
    have ht : (N : ℝ)*η ≤ a*η := mul_le_mul_of_nonneg_right (by linarith : (N : ℝ) ≤ a) hη.le
    have hh : ((N : ℝ)+1)/a ≤ 1/2+η/6 :=
      (div_le_iff₀ ha0).mpr (by nlinarith)
    linarith
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hb0 ha0)) (show 0 ≤ (N : ℝ)+1 by positivity)
  rw [Real.log_div hb0.ne' ha0.ne'] at hlog
  have halg : ((N : ℝ)+1)*(b/a-1)-(b-a)/2 =
      (b-a)*(((N : ℝ)+1)/a-1/2) := by field_simp
  have he : (b-a)*(((N : ℝ)+1)/a-1/2) ≤ η/2 := by
    rcases le_total a b with hab | hba
    · nlinarith [mul_le_mul_of_nonneg_left hhigh (sub_nonneg.mpr hab)]
    · have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hba) hlow
      linarith
  have hexp : -b/2+((N : ℝ)+1)*Real.log b ≤
      η/2+(-a/2+((N : ℝ)+1)*Real.log a) := by linarith
  have hsmall : Real.exp (η/2) ≤ 1+η := by
    apply (Real.exp_bound_div_one_sub_of_interval (by positivity : 0 ≤ η/2)
      (by linarith : η/2 < 1)).trans
    apply (div_le_iff₀ (by linarith : 0 < 1-η/2)).mpr
    nlinarith
  have hpow (x : ℝ) (hx : 0 < x) : x^(N+1) = Real.exp (((N : ℝ)+1)*Real.log x) := by
    rw [← Nat.cast_add_one,Real.exp_nat_mul,Real.exp_log hx]
  rw [hpow a ha0,hpow b hb0,← Real.exp_add,← Real.exp_add]
  calc
    _ ≤ Real.exp (η/2+(-a/2+((N : ℝ)+1)*Real.log a))/N.factorial :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = Real.exp (η/2)*(Real.exp (-a/2+((N : ℝ)+1)*Real.log a)/N.factorial) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (by positivity)

/-- Uniform relative prime mass with an arbitrary fixed precision. -/
theorem eventually_window_mass {h α η : ℝ}
    (hh : 0 < h) (hhu : h ≤ η/10) (hα : 0 < α)
    (hη : 0 < η) (hηu : η ≤ 1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, α*N ≤ a →
      (1-η)*h/a ≤ ∑ p ∈ logPrimes a h, (p : ℝ)⁻¹ ∧
      (∑ p ∈ logPrimes a h, (p : ℝ)⁻¹) ≤ (1+η)*h/a := by
  have heinv : Real.exp (-h) ≤ 1/(1+h) := by
    rw [Real.exp_neg,← one_div]
    exact one_div_le_one_div_of_le (by linarith)
      (by simpa only [add_comm] using Real.add_one_le_exp h)
  have hlow : (1-η/10)*h ≤ 1-Real.exp (-h) := by
    have ht : (1-η/10)*h ≤ h/(1+h) := by
      apply (le_div_iff₀ (by linarith : 0 < 1+h)).mpr
      have hc : (1-η/10)*(1+h) ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hc hh.le]
    have he : h/(1+h) = 1-1/(1+h) := by field_simp; ring
    rw [he] at ht
    linarith
  have hupp : Real.exp h-1 ≤ (1+η/5)*h := by
    have he := Real.exp_bound_div_one_sub_of_interval hh.le (by linarith : h < 1)
    have ht : h/(1-h) ≤ (1+η/5)*h := by
      apply (div_le_iff₀ (by linarith : 0 < 1-h)).mpr
      have hx : (1+η/5)*h ≤ (1+η/5)*(η/10) :=
        mul_le_mul_of_nonneg_left hhu (by positivity)
      have hc : 1 ≤ (1+η/5)*(1-h) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hc hh.le]
    have hi : h/(1-h) = 1/(1-h)-1 := by field_simp [show 1-h ≠ 0 by linarith]; ring
    rw [hi] at ht
    linarith
  have ht : Tendsto (fun N : ℕ => α*N) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hα
  filter_upwards [ZetaRieszSharpPrimeWindows.eventually_reciprocal_bounds hh hα
    (show 0 < η/10 by positivity),ht.eventually_ge_atTop 1] with N hN hN1 a ha
  have ha1 : (1 : ℝ) ≤ a := hN1.trans ha
  have ha0 : 0 < a := by linarith
  have hend : (1-η/10)/a ≤ 1/(a+h) := by
    apply (div_le_div_iff₀ ha0 (by positivity : 0 < a+h)).mpr
    nlinarith [mul_le_mul_of_nonneg_left ha1 hη.le]
  have hmass := hN a ha
  constructor
  · have hprod := mul_le_mul hlow hend (div_nonneg (by linarith) ha0.le)
      (mul_nonneg (by linarith : 0 ≤ 1-η/10) hh.le |>.trans hlow)
    have hc := mul_le_mul_of_nonneg_left hprod (by linarith : 0 ≤ 1-η/10)
    have hpoly : 1-η ≤ (1-η/10)^3 := by nlinarith [sq_nonneg η]
    calc
      _ ≤ (1-η/10)^3*(h/a) := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hpoly (show 0 ≤ h/a by positivity)
      _ ≤ (1-η/10)*(1-Real.exp (-h))/(a+h) := by
        ring_nf at hc ⊢
        exact hc
      _ ≤ _ := hmass.1
  · apply hmass.2.trans
    have hc := mul_le_mul_of_nonneg_left hupp (by positivity : 0 ≤ 1+η/10)
    have hpoly : (1+η/10)*(1+η/5) ≤ 1+η := by nlinarith
    have hd := mul_le_mul_of_nonneg_right hpoly hh.le
    have he : (1+η/10)*((1+η/5)*h) ≤ (1+η)*h := by nlinarith only [hd]
    exact div_le_div_of_nonneg_right (hc.trans he) ha0.le

/-- The full signed period has arbitrarily small relative cost; the
unsigned companion is used only for cutoff variation. -/
theorem eventually_weighted_period {m : ℕ} (hm : 0 < m)
    {y α η : ℝ} (hy : 54 ≤ |y|) (hα : 0 < α)
    (hη : 0 < η) (hηu : η ≤ 1/100)
    (hsmall : Real.pi/(4*m*|y|) ≤ η/10)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ η) :
    ∀ᶠ N : ℕ in atTop, ∀ (v b W : ℝ) (w : ℕ → ℝ),
      Real.cos (y*v) = -1 → α*N+1 ≤ v-b → 0 ≤ W →
      (∀ i ∈ Finset.range (8*m), ∀ p ∈ logPrimes
        (v+periodAngle m i/|y|-b) (Real.pi/(4*m*|y|)),
          W ≤ w p ∧ w p ≤ (1+η)*W) →
      |∑ i ∈ Finset.range (8*m), ∑ p ∈ logPrimes
          (v+periodAngle m i/|y|-b) (Real.pi/(4*m*|y|)),
          w p*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b))| ≤
        (8*η)*(8*m)*W*(Real.pi/(4*m*|y|))/(v-b) ∧
      (∑ i ∈ Finset.range (8*m), ∑ p ∈ logPrimes
          (v+periodAngle m i/|y|-b) (Real.pi/(4*m*|y|)), w p*(p : ℝ)⁻¹) ≤
        2*(8*m)*W*(Real.pi/(4*m*|y|))/(v-b) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 < |y| := by linarith
  have hyne : y ≠ 0 := abs_pos.mp hy0
  let h := Real.pi/(4*m*|y|)
  have hh : 0 < h := by dsimp [h]; positivity
  have ht : Tendsto (fun N : ℕ => α*N) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hα
  filter_upwards [eventually_window_mass hh hsmall hα hη hηu,
    ht.eventually_ge_atTop (4/η)] with N hN hlarge v b W w hv hab hW hw
  let a := v-b
  let T := fun i => v+periodAngle m i/|y|-b
  let mass := fun i => ∑ p ∈ logPrimes (T i) h, w p*(p : ℝ)⁻¹
  let F := fun i => ∑ p ∈ logPrimes (T i) h,
    w p*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b))
  let M := W*h/a
  have ha : 4/η ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := (by positivity : (0 : ℝ) < 4/η).trans_le ha
  have haη : 4 ≤ a*η := (div_le_iff₀ hη).mp ha
  have ha2 : 2 ≤ a := by nlinarith
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
  have hmass (i : ℕ) (hi : i ∈ Finset.range (8*m)) : |mass i-M| ≤ (6*η)*M := by
    have hb := hT i hi
    have hTi : 0 < T i := by nlinarith [mul_le_mul_of_nonneg_left hb.2.1 (show 0 ≤ 1+6*η by positivity),mul_nonneg (show 0 ≤ a*η by positivity) (show 0 ≤ 1/100-η by linarith)]
    have hprime := hN (T i) hb.1
    have hlow : W*((1-η)*h/(T i)) ≤ mass i := by
      apply (mul_le_mul_of_nonneg_left hprime.1 hW).trans
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right
        (hw i hi p hp).1 (inv_nonneg.mpr (Nat.cast_nonneg p)))
    have hupp : mass i ≤ ((1+η)*W)*((1+η)*h/(T i)) := by
      calc
        _ ≤ ∑ p ∈ logPrimes (T i) h, ((1+η)*W)*(p : ℝ)⁻¹ :=
          Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right
            (hw i hi p hp).2 (inv_nonneg.mpr (Nat.cast_nonneg p)))
        _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hprime.2 (by positivity)
    have hratioL : (1-3*η)/a ≤ (1-η)/(T i) := by
      apply (div_le_div_iff₀ ha0 hTi).mpr
      nlinarith [hb.2.2,mul_le_mul_of_nonneg_left hb.2.2 (show 0 ≤ 1-3*η by linarith)]
    have hratioU : (1+η)*(1+η)/(T i) ≤ (1+6*η)/a := by
      apply (div_le_div_iff₀ hTi ha0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hb.2.1 (show 0 ≤ 1+6*η by positivity),mul_nonneg (show 0 ≤ a*η by positivity) (show 0 ≤ 1/100-η by linarith)]
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
  have hsmall' : 6*η+(|y| * h)*(1+6*η) ≤ 8*η := by
    change |y| * h ≤ η at hphase
    nlinarith [mul_le_mul_of_nonneg_right hphase (show 0 ≤ 1+6*η by positivity)]
  constructor
  · change |∑ i ∈ Finset.range (8*m), F i| ≤ _
    apply hs.trans
    have hp := mul_le_mul_of_nonneg_left hsmall' (show 0 ≤ (8*m : ℝ)*M by positivity)
    dsimp only [M,a,h] at hp
    convert hp using 1 <;> ring
  · change (∑ i ∈ Finset.range (8*m), mass i) ≤ _
    have hh : (∑ i ∈ Finset.range (8*m), mass i) ≤ (8*m : ℝ)*(2*M) := by
      calc
        _ ≤ ∑ i ∈ Finset.range (8*m), 2*M := Finset.sum_le_sum (by
          intro i hi
          have hd := (abs_le.mp (hmass i hi)).2
          nlinarith [mul_nonneg (show 0 ≤ 1-6*η by linarith) hM])
        _ = _ := by simp
    dsimp only [M,a,h] at hh
    convert hh using 1; ring

/-- The moving factorial saddle gives an arbitrarily precise signed
prime period and an unsigned bound for coefficient variation. -/
theorem eventually_factorial_period {m : ℕ} (hm : 0 < m)
    {y α η : ℝ} (hy : 54 ≤ |y|) (hα : 0 < α)
    (hη : 0 < η) (hηu : η ≤ 1/100)
    (hsmall : Real.pi/(4*m*|y|) ≤ η/10)
    (hphase : |y| * (Real.pi/(4*m*|y|)) ≤ η) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ,
      2*(N : ℝ) ≤ v → v ≤ 2*N+1 → Real.cos (y*v) = -1 →
      ∃ V : ℝ, 0 < V ∧ V ≤ Real.exp (-v/2)*v^N/N.factorial ∧
        Real.exp (-v/2)*v^N/N.factorial ≤ (1+η)*V ∧
      ∀ b : ℝ, α*N+1 ≤ v-b →
      let w := fun p : ℕ => Real.exp (-(Real.log p+b)/2)*
        (Real.log p+b)^(N+1)/N.factorial
      let D := logPrimes (v-Real.pi/|y|-b) (2*Real.pi/|y|)
      |∑ p ∈ D, w p*(p : ℝ)⁻¹*Real.cos (y*(Real.log p+b))| ≤
        (64*η)*m*V*v*(Real.pi/(4*m*|y|))/(v-b) ∧
      (∑ p ∈ D, w p*(p : ℝ)⁻¹) ≤
        16*m*V*v*(Real.pi/(4*m*|y|))/(v-b) := by
  have hy0 : 0 < |y| := by linarith
  have hπ : Real.pi/|y| ≤ 1 := (div_le_iff₀ hy0).mpr (by linarith [Real.pi_lt_four])
  filter_upwards [eventually_weighted_period hm hy hα hη hηu hsmall hphase,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (20/η)]
    with N hN hlarge v hv hvu hpeak
  have hNR : (20 : ℝ) ≤ N := by
    have h := (div_le_iff₀ hη).mp hlarge
    nlinarith
  have hv0 : 0 < v := by linarith
  let W : ℝ → ℝ := fun x => Real.exp (-(v+x/|y|)/2)*(v+x/|y|)^(N+1)/N.factorial
  have hb (x : ℝ) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
      2*(N : ℝ)-1 ≤ v+x/|y| ∧ v+x/|y| ≤ 2*N+2 := by
    have hl := div_le_div_of_nonneg_right hx.1 hy0.le
    have hu := div_le_div_of_nonneg_right hx.2 hy0.le
    rw [neg_div] at hl
    constructor <;> linarith
  have hcont : Continuous W := by dsimp [W]; fun_prop
  obtain ⟨x₀,hx₀,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (-Real.pi) Real.pi).Nonempty from ⟨0,by
      constructor <;> linarith [Real.pi_pos]⟩) hcont.continuousOn
  have hW : 0 < W x₀ := by
    have hpos : 0 < v+x₀/|y| := by linarith [(hb x₀ hx₀).1]
    dsimp [W]; positivity
  have hrad (x : ℝ) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
      W x₀ ≤ W x ∧ W x ≤ (1+η)*W x₀ :=
    ⟨hmin hx,saddle_weight_ratio hη (by linarith) hlarge
      (hb x₀ hx₀).1 (hb x₀ hx₀).2 (hb x hx).1 (hb x hx).2⟩
  let V := W x₀/v
  have hzero := hrad 0 (by constructor <;> linarith [Real.pi_pos])
  have he : W 0 = (Real.exp (-v/2)*v^N/N.factorial)*v := by
    dsimp [W]; rw [zero_div,add_zero,pow_succ]; ring
  rw [he] at hzero
  have hVeq : V*v = W x₀ := div_mul_cancel₀ _ hv0.ne'
  refine ⟨V,by dsimp [V]; positivity,?_,?_,?_⟩
  · exact (div_le_iff₀ hv0).mpr hzero.1
  · apply (mul_le_mul_iff_right₀ hv0).mp
    rw [← hVeq] at hzero
    nlinarith only [hzero.2]
  intro b hab
  dsimp only
  let w := fun p : ℕ => Real.exp (-(Real.log p+b)/2)*(Real.log p+b)^(N+1)/N.factorial
  have hh := hN v b (W x₀) w hpeak hab hW.le (by
    intro i hi p hp
    have hc := period_cell_bounds hm (Finset.mem_range.mp hi) v hy0
    have hp' := (logPrimes_bounds hp).2
    let T := Real.log p+b
    have hTl : v-Real.pi/|y| ≤ T := by dsimp [T]; linarith [hc.1,hp'.1]
    have hTu : T ≤ v+Real.pi/|y| := by dsimp [T]; linarith [hc.2,hp'.2]
    have hx : (T-v)*|y| ∈ Set.Icc (-Real.pi) Real.pi := by
      constructor
      · have h := mul_le_mul_of_nonneg_right hTl hy0.le
        rw [sub_mul,div_mul_cancel₀ _ hy0.ne'] at h
        nlinarith only [h]
      · have h := mul_le_mul_of_nonneg_right hTu hy0.le
        rw [add_mul v (Real.pi/|y|),div_mul_cancel₀ _ hy0.ne'] at h
        nlinarith only [h]
    have hh := hrad ((T-v)*|y|) hx
    simpa only [W,mul_div_cancel_right₀ _ hy0.ne',add_sub_cancel,T] using hh)
  rw [← sum_prime_period _ hm v b y hy0,← sum_prime_period _ hm v b y hy0] at hh
  rw [← hVeq] at hh
  constructor
  · convert hh.1 using 1; ring
  · convert hh.2 using 1; ring

end
end RiemannGaussian.ZetaRieszSaddlePeriod
