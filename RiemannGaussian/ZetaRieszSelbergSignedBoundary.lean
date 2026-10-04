/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSelbergAdjacentOrders
import RiemannGaussian.ZetaRieszPrimePeriodCancellation

/-!
# Signed endpoint test on the unchanged balanced pair mask

This leaf tests the joined adjacent-order expression on the ENTIRE existing
balanced box. A finite mesh is only an exact partition in the proof, never
a new paid sector. Qualitative PNT is used at relative scale, not as an
unpaid source-scale approximation. No sampled height is asserted to be a
zeta zero, and no conclusion about the whole joined carrier follows from
an isolated mask.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Real Filter Topology MeasureTheory
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszSelbergSignedBoundary
open ZetaRieszAllowancePrimeBoxes ZetaRieszSelbergAdjacentOrders
open ZetaRieszLowCountSelbergAudit
open ZetaRieszGlobalHeadPriceAudit

/-- Fixed quadrature mesh. It never changes the literal prime mask. -/
def mesh : ℕ := 100000000
/-- Width of the fixed proof partition; not a new carrier mask. -/
def width : ℝ := 1/(mesh : ℝ)

private theorem width_data : 0 < width ∧ width = 1/100000000 ∧
    (mesh : ℝ)*width = 1 := by norm_num [width,mesh]

/-- Arbitrarily accurate PNT budgets are needed only relatively on a
fixed mesh, so no fixed power saving or short-interval premise is used. -/
theorem eventually_mesh_mass :
    ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, (N : ℝ) ≤ a → a ≤ N+2 →
      |(N : ℝ)*(∑ p ∈ logPrimes a width,(p : ℝ)⁻¹)-width| ≤
        (1/1000000 : ℝ)*width := by
  have hw := width_data
  have hplus : 0 < 1+width := by linarith only [hw.1]
  have heL : (1-1/100000000 : ℝ)*width ≤ 1-exp (-width) := by
    have he : exp (-width) ≤ 1/(1+width) := by
      rw [exp_neg,←one_div]
      exact one_div_le_one_div_of_le hplus (by simpa only [add_comm] using add_one_le_exp width)
    have hb : (1-1/100000000 : ℝ)*width ≤ width/(1+width) := by
      rw [hw.2.1]; norm_num
    have hh : width/(1+width)=1-1/(1+width) := by field_simp; ring
    rw [hh] at hb
    linarith only [he,hb]
  have heU : exp width-1 ≤ (1+2/100000000 : ℝ)*width := by
    have he := exp_bound_div_one_sub_of_interval hw.1.le (by rw [hw.2.1]; norm_num)
    have hb : 1/(1-width)-1 ≤ (1+2/100000000 : ℝ)*width := by
      rw [hw.2.1]; norm_num
    linarith only [he,hb]
  filter_upwards [ZetaRieszSharpPrimeWindows.eventually_reciprocal_bounds hw.1
      (by norm_num : (0 : ℝ)<1) (by norm_num : (0 : ℝ)<1/100000000),
    eventually_ge_atTop (1000000000 : ℕ)] with N hP hN a ha hau
  have hNr : (1000000000 : ℝ) ≤ N := by exact_mod_cast hN
  have ha0 : 0 < a := by linarith only [ha,hNr]
  have hah : 0 < a+width := by linarith only [ha0,hw.1]
  have hb := hP a (by simpa only [one_mul] using ha)
  have hlo : (1-1/1000000 : ℝ)*width ≤
      (N : ℝ)*((1-1/100000000)*(1-exp (-width))/(a+width)) := by
    have hp := mul_le_mul_of_nonneg_left heL (by norm_num : (0 : ℝ) ≤ 1-1/100000000)
    have he : (1-1/1000000 : ℝ)*width*(a+width) ≤
        (N : ℝ)*((1-1/100000000)^2*width) := by
      rw [hw.2.1]
      nlinarith only [hau,hNr]
    have hp' : (1-1/100000000 : ℝ)^2*width ≤
        (1-1/100000000)*(1-exp (-width)) := by nlinarith only [hp]
    have he' := he.trans (mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg N))
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hah).mpr
    exact he'
  have hhi : (N : ℝ)*((1+1/100000000)*(exp width-1)/a) ≤
      (1+1/1000000 : ℝ)*width := by
    have hp := mul_le_mul_of_nonneg_left heU (by norm_num : (0 : ℝ) ≤ 1+1/100000000)
    have he : (N : ℝ)*((1+1/100000000)*((1+2/100000000)*width)) ≤
        (1+1/1000000 : ℝ)*width*a := by
      rw [hw.2.1]
      nlinarith only [ha,hNr]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ ha0).mpr
    exact
      (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N)).trans he
  have hlow := hlo.trans (mul_le_mul_of_nonneg_left hb.1 (Nat.cast_nonneg N))
  have hupp := (mul_le_mul_of_nonneg_left hb.2 (Nat.cast_nonneg N)).trans hhi
  apply abs_le.mpr
  constructor <;> linarith only [hlow,hupp]

/-- A Riemann sum error at a FIXED mesh; this is used only to detect
the signed boundary, never to transport an exponentially growing error
into a putative constant ceiling. -/
theorem mesh_integral_error (f : ℝ → ℝ) (hc : Continuous f)
    (hLip : ∀ x z : ℝ, |f x-f z| ≤ 60*|x-z|) :
    |width*(∑ i ∈ Finset.range mesh,f ((i : ℝ)*width))-
      ∫ t in (0 : ℝ)..1,f t| ≤ 60*width := by
  have hw := width_data
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ)*width) (n := mesh)
    (μ := volume) (fun _ _ => hc.intervalIntegrable _ _)
  simp only [Nat.cast_zero,zero_mul,hw.2.2] at hs
  rw [←hs,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hb (i : ℕ) :
      |width*f ((i : ℝ)*width)-
        ∫ t in ((i : ℝ)*width)..((i+1 : ℕ)*width),f t| ≤ 60*width^2 := by
    have ha : (i : ℝ)*width ≤ ((i+1 : ℕ) : ℝ)*width := by
      norm_num only [Nat.cast_add,Nat.cast_one]
      nlinarith only [hw.1]
    have he : width*f ((i : ℝ)*width)=
        ∫ _t in ((i : ℝ)*width)..((i+1 : ℕ)*width),f ((i : ℝ)*width) := by
      rw [intervalIntegral.integral_const]
      simp only [Nat.cast_add,Nat.cast_one,smul_eq_mul]
      ring
    rw [he,←intervalIntegral.integral_sub intervalIntegrable_const
      (hc.intervalIntegrable _ _)]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (i : ℝ)*width) (b := ((i+1 : ℕ) : ℝ)*width)
      (C := 60*width) (f := fun t => f ((i : ℝ)*width)-f t) (by
        intro t ht
        rw [Set.uIoc_of_le ha] at ht
        rw [Real.norm_eq_abs]
        apply (hLip _ _).trans
        rw [abs_of_nonpos (by linarith only [ht.1] : (i : ℝ)*width-t ≤ 0)]
        norm_num only [Nat.cast_add,Nat.cast_one] at ht
        linarith only [ht.2])
    norm_num only [Real.norm_eq_abs,Nat.cast_add,Nat.cast_one] at hh
    rw [abs_of_nonneg (by nlinarith only [hw.1] :
      ((i : ℝ)+1)*width-(i : ℝ)*width ≥ 0)] at hh
    have hh' : |∫ t in ((i : ℝ)*width)..((i+1 : ℕ)*width),
        f ((i : ℝ)*width)-f t| ≤ 60*width^2 := by
      simpa only [Nat.cast_add,Nat.cast_one,
        show 60*width*(((i : ℝ)+1)*width-i*width)=60*width^2 by ring] using hh
    exact hh'
  calc
    _ ≤ ∑ i ∈ Finset.range mesh,60*width^2 := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw [pow_two,mul_left_comm (mesh : ℝ),←mul_assoc (mesh : ℝ),hw.2.2]
      ring

/-- PNT plus the exact literal mesh gives a relative quadrature bound
for either sine or cosine on BOTH original prime windows. -/
theorem eventually_prime_quadrature (f : ℝ → ℝ) (hc : Continuous f)
    (hf : ∀ t : ℝ, |f t| ≤ 1)
    (hLip : ∀ x z : ℝ, |f x-f z| ≤ 60*|x-z|) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
      |(N : ℝ)*(∑ p ∈ logPrimes ((N : ℝ)+c) 1,
        (p : ℝ)⁻¹*f (log p-N-c))-∫ t in (0 : ℝ)..1,f t| ≤ 1/100000 := by
  have hw := width_data
  have hquad := mesh_integral_error f hc hLip
  filter_upwards [eventually_mesh_mass] with N hN c hc0 hc1
  let a := fun i : ℕ => (N : ℝ)+c+i*width
  let m := fun i : ℕ => (N : ℝ)*∑ p ∈ logPrimes (a i) width,(p : ℝ)⁻¹
  let row := fun i : ℕ => (N : ℝ)*∑ p ∈ logPrimes (a i) width,
    (p : ℝ)⁻¹*f (log p-N-c)
  have ha (i : ℕ) (hi : i ∈ Finset.range mesh) :
      (N : ℝ) ≤ a i ∧ a i ≤ N+2 := by
    have hiR : (i : ℝ) ≤ mesh := by exact_mod_cast (Finset.mem_range.mp hi).le
    have hh := mul_le_mul_of_nonneg_right hiR hw.1.le
    rw [hw.2.2] at hh
    dsimp only [a]
    constructor <;> nlinarith only [hc0,hc1,hh,mul_nonneg (Nat.cast_nonneg i) hw.1.le]
  have hm (i : ℕ) (hi : i ∈ Finset.range mesh) :
      |m i-width| ≤ (1/1000000 : ℝ)*width := hN _ (ha i hi).1 (ha i hi).2
  have hrow (i : ℕ) (hi : i ∈ Finset.range mesh) :
      |row i-width*f ((i : ℝ)*width)| ≤
        ((1/1000000 : ℝ)+60*width*(1+1/1000000))*width := by
    have hmass := hm i hi
    have hm0 : 0 ≤ m i := by dsimp only [m]; positivity
    have hmU : m i ≤ (1+1/1000000 : ℝ)*width := by
      linarith only [(abs_le.mp hmass).2]
    have hs : |row i-f ((i : ℝ)*width)*m i| ≤ 60*width*m i := by
      have he : row i-f ((i : ℝ)*width)*m i=
          (N : ℝ)*∑ p ∈ logPrimes (a i) width,
            (p : ℝ)⁻¹*(f (log p-N-c)-f ((i : ℝ)*width)) := by
        dsimp only [row,m]
        simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
        ring
      rw [he,abs_mul,abs_of_nonneg (Nat.cast_nonneg N)]
      apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)).trans
      have hp (p : ℕ) (hp : p ∈ logPrimes (a i) width) :
          |(p : ℝ)⁻¹*(f (log p-N-c)-f ((i : ℝ)*width))| ≤
            60*width*(p : ℝ)⁻¹ := by
        have ht := (logPrimes_bounds hp).2
        have hd : |(log p-N-c)-(i : ℝ)*width| ≤ width := by
          rw [abs_of_nonneg (by dsimp only [a] at ht; linarith only [ht.1])]
          dsimp only [a] at ht
          linarith only [ht.2]
        rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
        have hh := (hLip _ _).trans (by nlinarith only [hd] :
          60*|(log p-N-c)-(i : ℝ)*width| ≤ 60*width)
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh
          (inv_nonneg.mpr (Nat.cast_nonneg p))
      have hh := Finset.sum_le_sum hp
      rw [←Finset.mul_sum] at hh
      simpa only [m,mul_assoc,mul_comm,mul_left_comm] using
        mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N)
    have he : row i-width*f ((i : ℝ)*width)=
        (row i-f ((i : ℝ)*width)*m i)+f ((i : ℝ)*width)*(m i-width) := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    have hp : |f ((i : ℝ)*width)*(m i-width)| ≤ (1/1000000 : ℝ)*width := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hf _) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hmass)
    have hprod := mul_le_mul_of_nonneg_left hmU
      (show 0 ≤ 60*width from mul_nonneg (by norm_num) hw.1.le)
    nlinarith only [hs,hp,hprod]
  have he : (N : ℝ)*(∑ p ∈ logPrimes ((N : ℝ)+c) 1,
      (p : ℝ)⁻¹*f (log p-N-c)) = ∑ i ∈ Finset.range mesh,row i := by
    rw [←hw.2.2,ZetaRieszPrimePeriodCancellation.sum_logPrimes_grid _ _ hw.1.le,Finset.mul_sum]
  have hb : |(∑ i ∈ Finset.range mesh,row i)-width*(∑ i ∈ Finset.range mesh,f ((i : ℝ)*width))| ≤
      (1/1000000 : ℝ)+60*width*(1+1/1000000) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum hrow).trans_eq
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [mul_left_comm (mesh : ℝ),hw.2.2,mul_one]
  rw [he]
  have htri := abs_sub_le (∑ i ∈ Finset.range mesh,row i)
    (width*(∑ i ∈ Finset.range mesh,f ((i : ℝ)*width))) (∫ t in (0 : ℝ)..1,f t)
  have he := htri.trans (add_le_add hb hquad)
  rw [hw.2.1] at he
  exact he.trans (by norm_num)

/-- A fixed test height, NOT a claimed actual zero ordinate. -/
def testHeight : ℝ := 19*Real.pi

theorem testHeight_bounds : 54 < testHeight ∧ testHeight < 60 := by
  unfold testHeight
  constructor <;> linarith [Real.pi_gt_three,Real.pi_lt_d4]

private theorem integral_test_cos :
    (∫ t in (0 : ℝ)..1,cos (testHeight*t))=0 := by
  have hy : testHeight ≠ 0 := ne_of_gt (by linarith only [testHeight_bounds.1])
  rw [intervalIntegral.integral_comp_mul_left (f := cos) hy,integral_cos]
  have hs : sin testHeight=0 := by simpa [testHeight] using sin_nat_mul_pi 19
  simp only [mul_one,mul_zero,hs,sin_zero,sub_zero,smul_zero]

private theorem integral_test_sin :
    (∫ t in (0 : ℝ)..1,sin (testHeight*t))=2/testHeight := by
  have hy : testHeight ≠ 0 := ne_of_gt (by linarith only [testHeight_bounds.1])
  rw [intervalIntegral.integral_comp_mul_left (f := sin) hy,integral_sin]
  have hs : cos testHeight = -1 := by
    have hh := cos_nat_mul_pi 19
    norm_num only [Nat.cast_ofNat,pow_succ,neg_one_mul,one_pow,neg_neg,pow_zero] at hh
    exact hh
  simp only [mul_one,mul_zero,hs,cos_zero,smul_eq_mul]
  ring

private theorem test_cos_lipschitz (x z : ℝ) :
    |cos (testHeight*x)-cos (testHeight*z)| ≤ 60*|x-z| := by
  have hh := abs_cos_sub_cos_le (testHeight*x) (testHeight*z)
  rw [←mul_sub,abs_mul,
    abs_of_pos (by linarith only [testHeight_bounds.1] : 0<testHeight)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right testHeight_bounds.2.le (abs_nonneg _))

private theorem test_sin_lipschitz (x z : ℝ) :
    |sin (testHeight*x)-sin (testHeight*z)| ≤ 60*|x-z| := by
  have hh := abs_sin_sub_sin_le (testHeight*x) (testHeight*z)
  rw [←mul_sub,abs_mul,
    abs_of_pos (by linarith only [testHeight_bounds.1] : 0<testHeight)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right testHeight_bounds.2.le (abs_nonneg _))

/-- The offset identity is exact at EVERY native integer order. The
phase remains the actual prime product phase; it is never frozen. -/
theorem test_phase_identity (N : ℕ) (x z : ℝ) :
    cos (testHeight*(x+z))=
      sin (testHeight*(x-N))*sin (testHeight*(z-N-1))-
      cos (testHeight*(x-N))*cos (testHeight*(z-N-1)) := by
  have he : testHeight*(x+z)=
      testHeight*(x-N)+testHeight*(z-N-1)+(19*(2*N+1 : ℕ) : ℕ)*Real.pi := by
    simp only [testHeight,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    ring
  rw [he,cos_add_nat_mul_pi,cos_add]
  have hp : (-1 : ℝ)^(19*(2*N+1))=-1 := by
    rw [show 19*(2*N+1)=2*(19*N)+19 by omega,pow_add,pow_mul]
    norm_num
  rw [hp]
  ring

/-- The signed phase of the ENTIRE original balanced prime box is
positive at this test height. This does not bound or sample an exposed
zero. Both prime windows and the diagonal exclusion remain unchanged. -/
theorem eventually_balanced_phase :
    ∀ᶠ N : ℕ in atTop,
      (1/1000 : ℝ) ≤ (N : ℝ)^2*(∑ e ∈ balancedPairs N,
        (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*cos (testHeight*log (e.1*e.2 : ℕ))) ∧
      (N : ℝ)^2*(∑ e ∈ balancedPairs N,(e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹) ≤ 2 := by
  have hcos := eventually_prime_quadrature (fun t => cos (testHeight*t))
    (by fun_prop) (fun t => abs_cos_le_one _) test_cos_lipschitz
  have hsin := eventually_prime_quadrature (fun t => sin (testHeight*t))
    (by fun_prop) (fun t => abs_sin_le_one _) test_sin_lipschitz
  have hmass := eventually_prime_quadrature (fun _ => (1 : ℝ))
    continuous_const (by intro t; norm_num) (by intro x z; simp)
  rw [integral_test_cos] at hcos
  rw [integral_test_sin] at hsin
  simp only [intervalIntegral.integral_const,sub_zero,one_smul] at hmass
  filter_upwards [hcos,hsin,hmass] with N hC hS hM
  let C := fun c : ℝ => (N : ℝ)*∑ p ∈ logPrimes ((N : ℝ)+c) 1,
    (p : ℝ)⁻¹*cos (testHeight*(log p-N-c))
  let S := fun c : ℝ => (N : ℝ)*∑ p ∈ logPrimes ((N : ℝ)+c) 1,
    (p : ℝ)⁻¹*sin (testHeight*(log p-N-c))
  let M := fun c : ℝ => (N : ℝ)*∑ p ∈ logPrimes ((N : ℝ)+c) 1,(p : ℝ)⁻¹
  have hC0 : |C 0| ≤ 1/100000 := by simpa [C] using hC 0 (by norm_num) (by norm_num)
  have hC1 : |C 1| ≤ 1/100000 := by simpa [C] using hC 1 (by norm_num) (by norm_num)
  have hS0 : (1/30 : ℝ)-1/100000 ≤ S 0 := by
    have hh := (abs_le.mp (hS 0 (by norm_num) (by norm_num))).1
    have ht : (1/30 : ℝ) ≤ 2/testHeight := by
      apply (le_div_iff₀ (by linarith only [testHeight_bounds.1] : 0<testHeight)).mpr
      linarith only [testHeight_bounds.2]
    simpa only [S,add_zero,sub_zero] using (by linarith only [hh,ht] :
      (1/30 : ℝ)-1/100000 ≤ (N : ℝ)*∑ p ∈ logPrimes ((N : ℝ)+0) 1,
        (p : ℝ)⁻¹*sin (testHeight*(log p-N-0)))
  have hS1 : (1/30 : ℝ)-1/100000 ≤ S 1 := by
    have hh := (abs_le.mp (hS 1 (by norm_num) (by norm_num))).1
    have ht : (1/30 : ℝ) ≤ 2/testHeight := by
      apply (le_div_iff₀ (by linarith only [testHeight_bounds.1] : 0<testHeight)).mpr
      linarith only [testHeight_bounds.2]
    exact (by linarith only [hh,ht] : (1/30 : ℝ)-1/100000 ≤ S 1)
  have hM0 : M 0 ≤ 1+1/100000 := by
    have hh := (abs_le.mp (hM 0 (by norm_num) (by norm_num))).2
    simp only [mul_one] at hh
    simpa [M] using (by linarith only [hh] :
      (N : ℝ)*∑ p ∈ logPrimes ((N : ℝ)+0) 1,(p : ℝ)⁻¹ ≤ 1+1/100000)
  have hM1 : M 1 ≤ 1+1/100000 := by
    have hh := (abs_le.mp (hM 1 (by norm_num) (by norm_num))).2
    simp only [mul_one] at hh
    exact (by linarith only [hh] : M 1 ≤ 1+1/100000)
  have hM0pos : 0 ≤ M 0 := by dsimp only [M]; positivity
  have hM1pos : 0 ≤ M 1 := by dsimp only [M]; positivity
  have hphase : (N : ℝ)^2*(∑ e ∈ balancedPairs N,
      (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*cos (testHeight*log (e.1*e.2 : ℕ)))=
      S 0*S 1-C 0*C 1 := by
    have hp (e : ℕ×ℕ) (he : e ∈ balancedPairs N) :
        log (e.1*e.2 : ℕ)=log e.1+log e.2 := by
      obtain ⟨hp,hq,_⟩ := balanced_pair_data he
      rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
    have he := Finset.sum_congr (s₁ := balancedPairs N)
      (f := fun e : ℕ×ℕ => (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*
        cos (testHeight*log (e.1*e.2 : ℕ)))
      (g := fun e : ℕ×ℕ => (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*
        (sin (testHeight*(log e.1-N))*sin (testHeight*(log e.2-N-1))-
         cos (testHeight*(log e.1-N))*cos (testHeight*(log e.2-N-1)))) rfl (fun e he => by
      rw [hp e he,test_phase_identity N])
    rw [he]
    have hrect (f g : ℕ → ℝ) : (∑ e ∈ balancedPairs N,f e.1*g e.2)=
        (∑ p ∈ logPrimes N 1,f p)*(∑ q ∈ logPrimes ((N : ℝ)+1) 1,g q) := by
      simp only [balancedPairs,Finset.product_eq_sprod,Finset.sum_product,
        ←Finset.mul_sum,←Finset.sum_mul]
    have hfactor (e : ℕ×ℕ) :
        (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*
          (sin (testHeight*(log e.1-N))*sin (testHeight*(log e.2-N-1))-
           cos (testHeight*(log e.1-N))*cos (testHeight*(log e.2-N-1))) =
        ((e.1 : ℝ)⁻¹*sin (testHeight*(log e.1-N)))*
          ((e.2 : ℝ)⁻¹*sin (testHeight*(log e.2-N-1)))-
        ((e.1 : ℝ)⁻¹*cos (testHeight*(log e.1-N)))*
          ((e.2 : ℝ)⁻¹*cos (testHeight*(log e.2-N-1))) := by ring
    simp_rw [hfactor]
    rw [Finset.sum_sub_distrib,
      hrect (fun p => (p : ℝ)⁻¹*sin (testHeight*(log p-N)))
        (fun q => (q : ℝ)⁻¹*sin (testHeight*(log q-N-1))),
      hrect (fun p => (p : ℝ)⁻¹*cos (testHeight*(log p-N)))
        (fun q => (q : ℝ)⁻¹*cos (testHeight*(log q-N-1)))]
    simp only [C,S,add_zero,sub_zero]
    ring
  have hmass' : (N : ℝ)^2*(∑ e ∈ balancedPairs N,
      (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹)=M 0*M 1 := by
    simp only [balancedPairs,Finset.product_eq_sprod,Finset.sum_product,M,
      add_zero,←Finset.mul_sum,←Finset.sum_mul]
    ring
  constructor
  · rw [hphase]
    have hprod := mul_le_mul hS0 hS1 (by norm_num : (0 : ℝ)≤1/30-1/100000)
      (by linarith only [hS0] : 0≤S 0)
    have hcprod : C 0*C 1 ≤ (1/100000 : ℝ)^2 := by
      have hh := mul_le_mul hC0 hC1 (abs_nonneg _) (by norm_num : (0 : ℝ)≤1/100000)
      rw [←abs_mul] at hh
      exact (le_abs_self _).trans (by simpa only [pow_two] using hh)
    nlinarith only [hprod,hcprod]
  · rw [hmass']
    have hmprod := mul_le_mul hM0 hM1 hM1pos (by norm_num : (0 : ℝ) ≤ 1+1/100000)
    nlinarith only [hmprod]

/-- The saddle factor on the SAME fixed balanced box. -/
def saddleFactor (N : ℕ) (T : ℝ) : ℝ :=
  exp (-(T-2*N)/2)*(T/(2*N))^N

/-- Unlike a whole-core absolute envelope, this relative saddle bound
has a bounded logarithmic width and an exact common normalization. -/
theorem saddleFactor_bounds {N : ℕ} (hN : 1 ≤ N) {T : ℝ}
    (hlo : 2*(N : ℝ) ≤ T) (hhi : T ≤ 2*N+3) :
    0 ≤ saddleFactor N T ∧ saddleFactor N T ≤ 1 ∧
      |saddleFactor N T-1| ≤ 2/(N : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0<N)
  let v := (T-2*N)/(2*N)
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hvD : 2*(N : ℝ)*v=T-2*N := by dsimp only [v]; field_simp
  have hT : 0 < T := by linarith only [hlo,hn]
  have hratio : T/(2*N)=1+v := by dsimp only [v]; field_simp; ring
  have hl : v-v^2/2 ≤ log (1+v) := by
    have hh := le_log_one_add_of_nonneg hv
    have he : v-v^2/2 ≤ 2*v/(v+2) := by
      apply (le_div_iff₀ (by linarith only [hv] : 0<v+2)).mpr
      nlinarith only [hv,pow_nonneg hv 3]
    exact he.trans hh
  have hu : log (1+v) ≤ v := by
    simpa only [add_sub_cancel_left] using
      log_le_sub_one_of_pos (by linarith only [hv] : 0<1+v)
  have he : saddleFactor N T=exp ((N : ℝ)*log (1+v)-(T-2*N)/2) := by
    unfold saddleFactor
    have hp : (1+v)^N=exp ((N : ℝ)*log (1+v)) := by
      rw [exp_nat_mul,exp_log (by linarith only [hv] : 0<1+v)]
    rw [hratio,hp,←exp_add]
    congr 1
    ring
  have hw : (T-2*N)^2 ≤ 9 := by
    have hx : 0 ≤ T-2*N := sub_nonneg.mpr hlo
    have hxU : T-2*N ≤ 3 := by linarith only [hhi]
    nlinarith only [hx,hxU]
  have hv2 : (N : ℝ)*v^2/2 ≤ 2/N := by
    apply (le_div_iff₀ hn).mpr
    have hh : (2*(N : ℝ)*v)^2 ≤ 9 := by simpa only [hvD] using hw
    nlinarith only [hh]
  have hexL : -2/(N : ℝ) ≤ (N : ℝ)*log (1+v)-(T-2*N)/2 := by
    have hh := mul_le_mul_of_nonneg_left hl hn.le
    calc
      _ ≤ -(N : ℝ)*v^2/2 := by
        simpa only [neg_div,neg_mul] using neg_le_neg hv2
      _ = (N : ℝ)*(v-v^2/2)-(T-2*N)/2 := by linear_combination -hvD/2
      _ ≤ _ := sub_le_sub_right hh _
  have hexU : (N : ℝ)*log (1+v)-(T-2*N)/2 ≤ 0 := by
    have hh := mul_le_mul_of_nonneg_left hu hn.le
    nlinarith only [hh,hvD]
  rw [he]
  refine ⟨(exp_pos _).le,exp_le_one_iff.mpr hexU,?_⟩
  apply abs_le.mpr
  constructor
  · have hh := add_one_le_exp ((N : ℝ)*log (1+v)-(T-2*N)/2)
    rw [neg_div] at hexL
    linarith only [hexL,hh]
  · have hh := exp_le_one_iff.mpr hexU
    have hd : 0 ≤ 2/(N : ℝ) := by positivity
    linarith only [hh,hd]

/-- The common signed saddle coefficient, with no asymptotic length
substitution and no change of factorial order. -/
def saddleCoefficient (N : ℕ) (L : ℝ) : ℝ := 3*N-4*(N : ℝ)^2/L

theorem saddleCoefficient_bounds {N : ℕ} (hN : 65536 ≤ N) {L : ℝ}
    (hL : (277/200 : ℝ)*N ≤ L) :
    (N : ℝ)/10 ≤ saddleCoefficient N L ∧ saddleCoefficient N L ≤ 3*N := by
  have hn : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hL0 : 0<L := by nlinarith only [hn,hL]
  have hterm : 4*(N : ℝ)^2/L ≤ (29/10 : ℝ)*N := by
    apply (div_le_iff₀ hL0).mpr
    have hh := mul_le_mul_of_nonneg_left hL hn.le
    nlinarith only [hh]
  have hp : 0 ≤ 4*(N : ℝ)^2/L := by positivity
  dsimp only [saddleCoefficient]
  constructor <;> linarith only [hterm,hp]

/-- All three adjacent-order terms remain joined. Their common scalar
weight differs from the exact saddle value by a FIXED absolute constant,
not by the full balanced-pair mass. -/
theorem joined_saddle_error {N : ℕ} (hN : 65536 ≤ N) {L x z : ℝ}
    (hL : (277/200 : ℝ)*N ≤ L)
    (hx : (N : ℝ) ≤ x) (hxU : x ≤ N+1)
    (hz : (N : ℝ)+1 ≤ z) (hzU : z ≤ N+2) :
    |(3/2*(x+z)-(x+z)^2/L-(x-z)^2/(2*(x+z)))*
        saddleFactor N (x+z)-saddleCoefficient N L| ≤ 26 := by
  have hn : (65536 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ)<N := by linarith only [hn]
  have hL0 : 0<L := by nlinarith only [hn0,hL]
  have hT : 0<x+z := by linarith only [hx,hz,hn]
  have hTlo : 2*(N : ℝ) ≤ x+z := by linarith only [hx,hz]
  have hThi : x+z ≤ 2*N+3 := by linarith only [hxU,hzU]
  have hw : 0≤x+z-2*N ∧ x+z-2*N≤3 := by constructor <;> linarith only [hTlo,hThi]
  have hi : (x-z)^2 ≤ 4 := by
    have hlo : -2≤x-z := by linarith only [hx,hzU]
    have hhi : x-z≤0 := by linarith only [hxU,hz]
    nlinarith only [hlo,hhi]
  have htL : 0 ≤ ((x+z)^2-4*(N : ℝ)^2)/L := by
    apply div_nonneg _ hL0.le
    nlinarith only [hTlo,hn0]
  have htU : ((x+z)^2-4*(N : ℝ)^2)/L ≤ 12 := by
    apply (div_le_iff₀ hL0).mpr
    have hh := pow_le_pow_left₀ hT.le hThi 2
    nlinarith only [hh,hL,hn]
  have hi0 : 0 ≤ (x-z)^2/(2*(x+z)) := by positivity
  have hi1 : (x-z)^2/(2*(x+z)) ≤ 1 := by
    apply (div_le_iff₀ (by linarith only [hT] : 0<2*(x+z))).mpr
    linarith only [hi,hTlo,hn]
  let D := 3/2*(x+z)-(x+z)^2/L-(x-z)^2/(2*(x+z))
  let B := saddleCoefficient N L
  have hd : |D-B| ≤ 20 := by
    have he : D-B=3/2*(x+z-2*N)-((x+z)^2-4*(N : ℝ)^2)/L-
        (x-z)^2/(2*(x+z)) := by dsimp only [D,B,saddleCoefficient]; ring
    rw [he]
    apply abs_le.mpr
    constructor <;> linarith only [htL,htU,hi0,hi1,hw.1,hw.2]
  have hs := saddleFactor_bounds (by omega : 1≤N) hTlo hThi
  have hB := saddleCoefficient_bounds hN hL
  have hB0 : 0 ≤ B := by dsimp only [B]; linarith only [hB.1,hn]
  have hB1 : B ≤ 3*N := hB.2
  have he : D*saddleFactor N (x+z)-B=(D-B)*saddleFactor N (x+z)+
      B*(saddleFactor N (x+z)-1) := by ring
  change |D*saddleFactor N (x+z)-B| ≤ 26
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg hs.1,abs_of_nonneg hB0]
  have hfirst := mul_le_mul hd hs.2.1 hs.1 (by norm_num : (0 : ℝ)≤20)
  have hsecond := mul_le_mul hB1 hs.2.2 (abs_nonneg _) (by linarith only [hn] : 0≤3*(N : ℝ))
  have heq : (3*(N : ℝ))*(2/N)=6 := by field_simp; ring
  rw [heq] at hsecond
  linarith only [hfirst,hsecond]

/-- A signed lower bound for the WHOLE joined scalar weight on the
existing pair mask. The mesh has been summed out; no phase half, count,
or new prime population appears on either side. -/
theorem eventually_joined_saddle_lower :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℝ, (277/200 : ℝ)*N ≤ L →
      1/(20000*(N : ℝ)) ≤ ∑ e ∈ balancedPairs N,
        (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*
        (3/2*(log e.1+log e.2)-(log e.1+log e.2)^2/L-
          (log e.1-log e.2)^2/(2*(log e.1+log e.2)))*
        saddleFactor N (log e.1+log e.2)*
        cos (testHeight*log (e.1*e.2 : ℕ)) := by
  filter_upwards [eventually_balanced_phase,eventually_ge_atTop (1000000000 : ℕ)]
    with N hP hN L hL
  have hNr : (1000000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0 : ℝ)<N := by linarith only [hNr]
  let B := saddleCoefficient N L
  let H := ∑ e ∈ balancedPairs N,(e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*
    cos (testHeight*log (e.1*e.2 : ℕ))
  let M := ∑ e ∈ balancedPairs N,(e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹
  let W := ∑ e ∈ balancedPairs N,
    (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*
    (3/2*(log e.1+log e.2)-(log e.1+log e.2)^2/L-
      (log e.1-log e.2)^2/(2*(log e.1+log e.2)))*
    saddleFactor N (log e.1+log e.2)*cos (testHeight*log (e.1*e.2 : ℕ))
  have hB := saddleCoefficient_bounds (by omega : 65536≤N) hL
  have hB0 : 0 ≤ B := by dsimp only [B]; linarith only [hB.1,hn]
  have he : |W-B*H| ≤ 26*M := by
    dsimp only [W,H,M]
    rw [Finset.mul_sum,←Finset.sum_sub_distrib,Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro e he
    obtain ⟨_hp,_hq,_hpq,hpL,hpU,hqL,hqU⟩ := balanced_pair_data he
    have herr := joined_saddle_error (by omega : 65536≤N) hL hpL.le hpU hqL.le hqU
    have hweight : 0 ≤ (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹ := by positivity
    have hident :
        (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*
        (3/2*(log e.1+log e.2)-(log e.1+log e.2)^2/L-
          (log e.1-log e.2)^2/(2*(log e.1+log e.2)))*
        saddleFactor N (log e.1+log e.2)*cos (testHeight*log (e.1*e.2 : ℕ))-
        B*((e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*cos (testHeight*log (e.1*e.2 : ℕ))) =
        ((3/2*(log e.1+log e.2)-(log e.1+log e.2)^2/L-
          (log e.1-log e.2)^2/(2*(log e.1+log e.2)))*
          saddleFactor N (log e.1+log e.2)-B)*
          ((e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹)*cos (testHeight*log (e.1*e.2 : ℕ)) := by ring
    rw [hident,abs_mul,abs_mul,abs_of_nonneg hweight]
    have ht := mul_le_mul_of_nonneg_right herr hweight
    have hu := mul_le_mul ht (abs_cos_le_one (testHeight*log (e.1*e.2 : ℕ))) (abs_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ)≤26) hweight)
    simpa only [B,mul_one,mul_assoc] using hu
  have hfloor : B*H-26*M ≤ W := by linarith only [(abs_le.mp he).1]
  have hp := mul_le_mul_of_nonneg_left hP.1 hB0
  have hm := mul_le_mul_of_nonneg_left hP.2 (by norm_num : (0 : ℝ)≤26)
  have hw := mul_le_mul_of_nonneg_left hfloor (sq_nonneg (N : ℝ))
  have hcross : (N : ℝ)/20000 ≤ (N : ℝ)^2*W := by
    have hh : B/1000-52 ≤ (N : ℝ)^2*W := by
      dsimp only [H,M] at hfloor
      change B*(1/1000 : ℝ) ≤ B*((N : ℝ)^2*H) at hp
      change 26*((N : ℝ)^2*M) ≤ 26*2 at hm
      nlinarith only [hp,hm,hw]
    nlinarith only [hh,hB.1,hNr]
  change 1/(20000*(N : ℝ)) ≤ W
  calc
    _ = ((N : ℝ)/20000)/(N : ℝ)^2 := by field_simp
    _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos hn)).mpr (by simpa only [mul_comm] using hcross)

private theorem kernel_re_saddle {N n : ℕ} (hN : 0<N) (hn : 0<n) (y : ℝ) :
    (zetaPrimeLogKernel N (3/2+Complex.I*y) n).re=
      (exp (-(N : ℝ))*(2*N)^N/(N.factorial : ℝ))*
        saddleFactor N (log n)*(n : ℝ)⁻¹*cos (y*log n) := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hr := ZetaRieszCosineCarrier.re_filterKernel_one N y (n : ℝ)
  rw [ZetaRieszJointAllocation.filter_one_eq] at hr
  rw [hr,saddleFactor]
  have hp : (2*(N : ℝ))^N*(log (n : ℝ)/(2*N))^N=log (n : ℝ)^N := by
    rw [←mul_pow,mul_div_cancel₀ _ (by positivity : (2*(N : ℝ))≠0)]
  have hi : (n : ℝ)⁻¹=exp (-log n) := by rw [exp_neg,exp_log hnR]
  have he : exp (-(N : ℝ))*exp (-(log (n : ℝ)-2*N)/2)*exp (-log n)=
      exp (-(3/2 : ℝ)*log n) := by
    rw [←exp_add,←exp_add]
    congr 1
    ring
  rw [hi]
  calc
    _ = (exp (-(3/2 : ℝ)*log n)/(N.factorial : ℝ))*
        ((2*(N : ℝ))^N*(log (n : ℝ)/(2*N))^N)*cos (y*log n) := by rw [hp]; ring
    _ = _ := by rw [←he]; ring

/-- Exact bridge to the ACTUAL Selberg defect times its original
factorial kernel. No divisor, owner, phase or pair mask is completed. -/
theorem balanced_atom_eq_saddle {u : ℝ} (hu : 1/2≤u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) {N p q : ℕ}
    (hN : 65536≤N) (he : (p,q) ∈ balancedPairs N) :
    (selbergDefect u N (p*q)*zetaPrimeLogKernel N (3/2+Complex.I*testHeight) (p*q)).re=
      (exp (-(N : ℝ))*(2*N)^N/(N.factorial : ℝ))*
        (p : ℝ)⁻¹*(q : ℝ)⁻¹*
        (3/2*(log p+log q)-(log p+log q)^2/SquarefreeVaughanLogSource.length u N-
          (log p-log q)^2/(2*(log p+log q)))*
        saddleFactor N (log p+log q)*cos (testHeight*log (p*q : ℕ)) := by
  obtain ⟨hp,hq,_⟩ := balanced_pair_data he
  have hn := Nat.mul_pos hp.pos hq.pos
  have ht : log (p*q : ℕ)=log p+log q := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hq.ne_zero)]
  rw [balanced_selbergDefect_eq hu hU hN he,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    kernel_re_saddle (by omega) hn testHeight,ht,Nat.cast_mul,mul_inv_rev]
  ring

/-- A genuine signed growth lower bound on the UNCHANGED balanced
mask. This is stronger than the prior absolute mask-jump audit. The
test height is not assumed to be a zero, so this is a method no-go,
not a counterexample to the desired exposed-zero ceiling. -/
theorem eventually_balanced_signed_growth {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    ∀ᶠ N : ℕ in atTop,
      (u/120000)*(2*u)^N/((N : ℝ)+1)^2 ≤
        ((u : ℂ)^(N+1)*(∑ e ∈ balancedPairs N,
          selbergDefect u N (e.1*e.2)*
            zetaPrimeLogKernel N (3/2+Complex.I*testHeight) (e.1*e.2))).re := by
  filter_upwards [eventually_joined_saddle_lower,eventually_ge_atTop (65536 : ℕ)]
    with N hS hN
  have hn : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hu0 : 0<u := by linarith only [hu]
  have hL := ZetaRieszPostHingeEnergy.length_ge_rational hN hu0 hU
  let V := exp (-(N : ℝ))*(2*N)^N/(N.factorial : ℝ)
  have hV : 0≤V := by dsimp only [V]; positivity
  have hsum : ((u : ℂ)^(N+1)*(∑ e ∈ balancedPairs N,
      selbergDefect u N (e.1*e.2)*
        zetaPrimeLogKernel N (3/2+Complex.I*testHeight) (e.1*e.2))).re =
      u^(N+1)*V*(∑ e ∈ balancedPairs N,
        (e.1 : ℝ)⁻¹*(e.2 : ℝ)⁻¹*
        (3/2*(log e.1+log e.2)-(log e.1+log e.2)^2/SquarefreeVaughanLogSource.length u N-
          (log e.1-log e.2)^2/(2*(log e.1+log e.2)))*
        saddleFactor N (log e.1+log e.2)*cos (testHeight*log (e.1*e.2 : ℕ))) := by
    rw [←Complex.ofReal_pow,Complex.re_ofReal_mul,Complex.re_sum]
    have he := Finset.sum_congr rfl (fun e he => balanced_atom_eq_saddle
      (by linarith only [hu]) hU hN he)
    rw [he]
    simp only [V,mul_assoc,←Finset.mul_sum]
  rw [hsum]
  have hfactor := PrimeWindow.factorial_le_six_mul_stirling (by omega : 1≤N)
  have hVlow : (2 : ℝ)^N/(6*N) ≤ V := by
    have hpow : ((N : ℝ)/exp 1)^N=(N : ℝ)^N*exp (-(N : ℝ)) := by
      rw [div_pow,exp_one_pow]
      rw [div_eq_mul_inv,←exp_neg]
    rw [hpow] at hfactor
    have hd : 0 < (6*(N : ℝ))*((N : ℝ)^N*exp (-(N : ℝ))) := by positivity
    have hb := div_le_div_of_nonneg_left
      (show 0 ≤ exp (-(N : ℝ))*(2*N)^N by positivity)
      (by positivity : 0<(N.factorial : ℝ)) hfactor
    apply le_trans _ hb
    have he : exp (-(N : ℝ))*(2*N)^N/
        (6*N*((N : ℝ)^N*exp (-(N : ℝ))))=(2 : ℝ)^N/(6*N) := by
      rw [mul_pow]
      field_simp
    rw [he]
  have hlo := mul_le_mul_of_nonneg_left (hS _ hL)
    (mul_nonneg (pow_nonneg hu0.le (N+1)) hV)
  have hVL := mul_le_mul_of_nonneg_left hVlow
    (show 0≤u^(N+1)/(20000*(N : ℝ)) by positivity)
  have hid : (u/120000)*(2*u)^N/(N : ℝ)^2=
      (u^(N+1)/(20000*(N : ℝ)))*((2 : ℝ)^N/(6*N)) := by
    rw [mul_pow,pow_succ]
    field_simp
    ring
  calc
    _ ≤ (u/120000)*(2*u)^N/(N : ℝ)^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith only [hn]
    _ = _ := hid
    _ ≤ (u^(N+1)/(20000*(N : ℝ)))*V := hVL
    _ = u^(N+1)*V*(1/(20000*(N : ℝ))) := by ring
    _ ≤ _ := hlo

/-- Adjacent-order cancellation on the common balanced mask does NOT
give a uniform all-height bound: its signed value actually diverges at
this test height. The rest of the literal carrier is not removed. -/
theorem balanced_signed_tendsto_atTop {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N : ℕ => ((u : ℂ)^(N+1)*(∑ e ∈ balancedPairs N,
      selbergDefect u N (e.1*e.2)*
        zetaPrimeLogKernel N (3/2+Complex.I*testHeight) (e.1*e.2))).re)
      atTop atTop := by
  have hc : 0<u/120000 := by linarith only [hu]
  have ht := (ZetaRieszAllowanceGrowth.geometric_over_successor_four_tendsto
    (show 1<2*u by linarith only [hu])).const_mul_atTop hc
  refine tendsto_atTop_mono' atTop ?_ ht
  filter_upwards [eventually_balanced_signed_growth hu hU] with N hN
  apply le_trans _ hN
  rw [←mul_div_assoc]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hn : 1≤(N : ℝ)+1 := by linarith only [Nat.cast_nonneg (α := ℝ) N]
  have hs : 1≤((N : ℝ)+1)^2 := one_le_pow₀ hn
  simpa only [show (4 : ℕ)=2+2 from rfl,pow_add] using le_mul_of_one_le_right
    (sq_nonneg ((N : ℝ)+1)) hs

/-- The actual factorial-prefix correction has already been paid once
by the existing geometric theorem. It cannot remove the signed endpoint
growth. This is the literal balanced part of prefixPairDefect, not just
a surrogate Selberg polynomial. -/
theorem balanced_literal_prefix_tendsto_atTop {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun N : ℕ => ((u : ℂ)^(N+1)*(∑ e ∈ balancedPairs N,
      (ZetaRieszPairPrefixPayment.prefixCoefficient u N (e.1*e.2)-
        selbergCoefficient (e.1*e.2))*
        zetaPrimeLogKernel N (3/2+Complex.I*testHeight) (e.1*e.2))).re)
      atTop atTop := by
  have hu' : 1/2≤u := by linarith only [hu]
  have hY : 54≤|testHeight| := by
    rw [abs_of_pos (by linarith only [testHeight_bounds.1] : 0<testHeight)]
    exact testHeight_bounds.1.le
  have hprefix := Complex.continuous_re.tendsto 0 |>.comp
    (balanced_factorialPrefix_tendsto hu' hU hY)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ((u : ℂ)^(N+1)*(∑ e ∈ balancedPairs N,
        factorialPrefixTerm N (SquarefreeVaughanLogSource.length u N)
          e.1 e.2 (3/2+Complex.I*testHeight))).re < 1 :=
    hprefix.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))
  refine tendsto_atTop.2 (fun M => ?_)
  filter_upwards [(balanced_signed_tendsto_atTop hu hU).eventually_gt_atTop (M+1),
    hsmall,eventually_ge_atTop (65536 : ℕ)] with N hlarge hP hN
  have he := Finset.sum_congr (s₁ := balancedPairs N) rfl
    (fun e he => balanced_prefix_kernel hu' hU hN he (3/2+Complex.I*testHeight))
  rw [he,Finset.sum_sub_distrib,mul_sub,Complex.sub_re]
  linarith only [hlarge,hP]

/-- No constant cofinal ceiling holds even on the ORIGINAL dyadic
schedule for this isolated literal balanced prefix. A successful bound
must use the exposed-zero hypothesis or joint cancellation with the
retained signed mask complement. -/
theorem not_frequently_native_balanced_prefix_ceiling {u : ℝ} (hu : 1/2<u)
    (hU : u≤ZetaRieszWideOwnerAudit.radiusCeiling) (M : ℝ) :
    ¬ ∃ᶠ j : ℕ in atTop,
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      ((u : ℂ)^(N+1)*(∑ e ∈ balancedPairs N,
        (ZetaRieszPairPrefixPayment.prefixCoefficient u N (e.1*e.2)-
          selbergCoefficient (e.1*e.2))*
          zetaPrimeLogKernel N (3/2+Complex.I*testHeight) (e.1*e.2))).re ≤ M := by
  intro h
  have ht := (balanced_literal_prefix_tendsto_atTop hu hU).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder
  obtain ⟨j,hle,hgt⟩ := (h.and_eventually (ht.eventually_gt_atTop M)).exists
  exact hgt.not_ge hle

end RiemannGaussian.ZetaRieszSelbergSignedBoundary
