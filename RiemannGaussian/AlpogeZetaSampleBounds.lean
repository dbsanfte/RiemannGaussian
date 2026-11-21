import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! # Interpolation of the modulus-one reciprocal prime ramp on real intervals -/

namespace RiemannGaussian.AlpogeZetaSamples
noncomputable section
open Finset Set Filter
open scoped ArithmeticFunction.vonMangoldt

/-- The uncentered reciprocal prime-power ramp in Alpöge's zeta specialization. -/
def ramp (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊+1), Λ n * max (x/n-1) 0

/-- The real arithmetic function to which the power-window criterion applies. -/
def G (x : ℝ) : ℝ := ramp x - x*Real.log x + (1+Real.eulerMascheroniConstant)*x

private theorem fixed_ramp {x b : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) :
    ramp x = ∑ n ∈ Finset.range (⌊b⌋₊+1), Λ n * max (x/n-1) 0 := by
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.floor_mono hxb)))
  intro n _ hn
  have hfloor : ⌊x⌋₊ < n := by simp only [Finset.mem_range] at hn; omega
  have hnx := (Nat.floor_lt hx).mp hfloor
  rw [max_eq_right (sub_nonpos.mpr ((div_le_one (hx.trans_lt hnx)).mpr hnx.le)),mul_zero]

/-- Every new prime event has nonnegative mass, so the reciprocal ramp lies below its chord. -/
theorem ramp_le_chord {a x b u v : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : u+v=1) (hx : x=u*a+v*b) :
    ramp x ≤ u*ramp a+v*ramp b := by
  rw [fixed_ramp (ha.trans hax) hxb,fixed_ramp ha (hax.trans hxb),fixed_ramp (ha.trans (hax.trans hxb)) le_rfl,
    Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n _
  have he : x/n-1 = u*(a/n-1)+v*(b/n-1) := by rw [hx]; linear_combination hs
  have hh : max (x/n-1) 0 ≤ u*max (a/n-1) 0+v*max (b/n-1) 0 := by
    apply max_le
    · rw [he]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hu)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hv)
    · positivity
  have hh' := mul_le_mul_of_nonneg_left hh (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  linarith only [hh']

/-- The sole cost of interpolation between any two observations of the actual centered ramp is
at most the squared gap divided by four times the physical position. -/
theorem G_le_chord {a x b : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    G x ≤ max (G a) (G b) + (b-a)^2/(4*x) := by
  rcases eq_or_lt_of_le (hax.trans hxb) with he|hab
  · obtain rfl := le_antisymm hax (he ▸ hxb)
    simp [he]
  let u := (b-x)/(b-a)
  let v := (x-a)/(b-a)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr hab.le)
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hab.le)
  have hs : u+v=1 := by dsimp [u,v]; field_simp; ring
  have hx : x=u*a+v*b := by dsimp [u,v]; field_simp; ring
  have hx0 := ha.trans_le hax
  have hb0 := ha.trans hab
  have hlog (t : ℝ) (ht : 0 < t) : t*(Real.log t-Real.log x) ≤ t*(t/x-1) := by
    rw [← Real.log_div ht.ne' hx0.ne']
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ht hx0)) ht.le
  have hcost : u*(a*(a/x-1))+v*(b*(b/x-1)) = (x-a)*(b-x)/x := by
    dsimp [u,v]; field_simp; ring
  have herr : (x-a)*(b-x)/x ≤ (b-a)^2/(4*x) := by
    field_simp; nlinarith [sq_nonneg (2*x-a-b)]
  have hl := ((add_le_add (mul_le_mul_of_nonneg_left (hlog a ha) hu)
    (mul_le_mul_of_nonneg_left (hlog b hb0) hv)).trans (hcost.le.trans herr))
  have hconv := ramp_le_chord ha.le hax hxb hu hv hs hx
  have hm := add_le_add (mul_le_mul_of_nonneg_left (le_max_left (G a) (G b)) hu)
    (mul_le_mul_of_nonneg_left (le_max_right (G a) (G b)) hv)
  rw [← add_mul,hs,one_mul] at hm
  apply le_trans _ (add_le_add hm (le_refl ((b-a)^2/(4*x))))
  unfold G
  nlinarith only [hl,hconv,congrArg (fun z => z*Real.log x) hx,
    congrArg (fun z => z*(1+Real.eulerMascheroniConstant)) hx]

/-- From two consecutive fourth powers to every real point between them, at square-root cost. -/
theorem G_le_fourth_endpoints {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc ((n:ℝ)^4) (((n:ℝ)+1)^4)) :
    G x ≤ max (G ((n:ℝ)^4)) (G (((n:ℝ)+1)^4)) + (225/4)*Real.sqrt x := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n:ℝ) := by linarith
  have hx0 := (pow_pos hpos 4).trans_le hx.1
  have hgap : ((n:ℝ)+1)^4-(n:ℝ)^4 ≤ 15*(n:ℝ)^3 := by
    nlinarith only [mul_nonneg (show 0 ≤ (n:ℝ)-1 by linarith)
      (show 0 ≤ 11*(n:ℝ)^2+5*n+1 by positivity)]
  have hp : ((n:ℝ)+1)^4-(n:ℝ)^4 ≥ 0 := by linarith [hx.1,hx.2]
  have hr : (n:ℝ)^2 ≤ Real.sqrt x := (Real.le_sqrt (sq_nonneg _) hx0.le).mpr (by nlinarith [hx.1])
  apply (G_le_chord (pow_pos hpos 4) hx.1 hx.2).trans
  apply add_le_add_right
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [sq_le_sq' (by linarith : -(15*(n:ℝ)^3) ≤ ((n:ℝ)+1)^4-(n:ℝ)^4) hgap,
    mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ 225*x),
    mul_le_mul_of_nonneg_left hx.1 (by positivity : 0 ≤ 225*(n:ℝ)^2)]

/-- A complete real interval follows from the consecutive fourth-power samples bracketing it.
Only the two fourth roots at the ends of the interval need rounding. -/
theorem G_le_on_interval_of_fourth_samples {A T C θ : ℝ} (hA : 1 ≤ A) (hC : 0 ≤ C)
    (hθ : 1/2 ≤ θ) (hθ1 : θ ≤ 1)
    (hs : ∀ n ∈ Finset.Icc ⌊A^(1/4:ℝ)⌋₊ (⌊T^(1/4:ℝ)⌋₊+1),
      G ((n:ℝ)^4) ≤ C*((n:ℝ)^4)^θ) {y : ℝ} (hy : y ∈ Set.Icc A T) :
    G y ≤ (16*C+225/4)*y^θ := by
  have hy1 := hA.trans hy.1
  have hy0 := zero_lt_one.trans_le hy1
  let r := y^(1/4:ℝ)
  let n := ⌊r⌋₊
  have hr1 : 1 ≤ r := Real.one_le_rpow hy1 (by norm_num)
  have hn1 : 1 ≤ n := Nat.le_floor (by simpa using hr1)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hr : r^4 = y := by dsimp [r]; rw [← Real.rpow_mul_natCast hy0.le]; norm_num
  have hlo : (n:ℝ)^4 ≤ y := hr ▸ pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (zero_le_one.trans hr1)) 4
  have hhi : y ≤ ((n:ℝ)+1)^4 := hr ▸ pow_le_pow_left₀ (zero_le_one.trans hr1) (Nat.lt_floor_add_one r).le 4
  have hlm : ⌊A^(1/4:ℝ)⌋₊ ≤ n := Nat.floor_mono (Real.rpow_le_rpow (by linarith) hy.1 (by norm_num))
  have hhm : n ≤ ⌊T^(1/4:ℝ)⌋₊ := Nat.floor_mono (Real.rpow_le_rpow hy0.le hy.2 (by norm_num))
  have ha := hs n (Finset.mem_Icc.mpr ⟨hlm,by omega⟩)
  have hb := hs (n+1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  rw [Nat.cast_add_one] at hb
  have hsize : ((n:ℝ)+1)^4 ≤ 16*y := by
    calc _ ≤ (2*(n:ℝ))^4 := pow_le_pow_left₀ (by positivity) (by linarith) _
         _ ≤ _ := by nlinarith only [hlo]
  have hmax {z : ℝ} (hz : 0 ≤ z) (hzy : z ≤ 16*y) : C*z^θ ≤ 16*C*y^θ := by
    have hh := Real.rpow_le_rpow hz hzy (by linarith : 0 ≤ θ)
    rw [Real.mul_rpow (by norm_num) hy0.le] at hh
    have hc : (16:ℝ)^θ ≤ 16 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1).trans_eq (Real.rpow_one _)
    nlinarith only [mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_right hc
      (Real.rpow_nonneg hy0.le θ))) hC]
  have htop := max_le (ha.trans (hmax (by positivity) (by linarith))) (hb.trans (hmax (by positivity) hsize))
  have hroot : Real.sqrt y ≤ y^θ := by rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hy1 hθ
  linarith [G_le_fourth_endpoints hn1 ⟨hlo,hhi⟩]

open Real Topology in
private theorem log_step_bounds {x : ℝ} (hx : 0 < x) :
    1/(x+1) + 1/(2*(x+1)) - 1/(2*(x+2)) ≤ log (x+1)-log x ∧
    log (x+1)-log x ≤ 1/(x+1) + 1/(2*x) - 1/(2*(x+1)) := by
  let z := 1/(2*x+1)
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z < 1 := by dsimp [z]; apply (div_lt_iff₀ (by positivity)).mpr; linarith
  have he : (1+z)/(1-z) = (x+1)/x := by dsimp [z]; field_simp; ring
  have hL := sum_range_le_log_div hz.le hz1 1
  have hU := log_div_le_sum_range_add hz.le hz1 0
  rw [he,log_div (by positivity) hx.ne'] at hL hU
  norm_num at hL hU
  constructor
  · calc _ ≤ 2*z := by dsimp [z]; field_simp; nlinarith
         _ ≤ _ := by linarith
  · calc _ ≤ 2*(z/(1-z^2)) := by linarith only [hU]
         _ = _ := by
           have hden : 0 < 1-z^2 := by nlinarith only [mul_self_lt_mul_self hz.le hz1]
           rw [← mul_div_assoc,div_eq_iff hden.ne']
           dsimp [z]; field_simp; ring

open Real Topology in
/-- The harmonic remainder lies between the endpoint half-weights at n and n+1. -/
theorem harmonic_half_bounds {n : ℕ} (hn : 0 < n) :
    1/(2*((n:ℝ)+1)) ≤ (harmonic n:ℝ)-log n-eulerMascheroniConstant ∧
    (harmonic n:ℝ)-log n-eulerMascheroniConstant ≤ 1/(2*(n:ℝ)) := by
  let F (j : ℕ) : ℝ := (harmonic (j+1):ℝ)-log ((j:ℝ)+1)
  let L (j : ℕ) : ℝ := F j - 1/(2*((j:ℝ)+2))
  let U (j : ℕ) : ℝ := F j - 1/(2*((j:ℝ)+1))
  have hF : Tendsto F atTop (𝓝 eulerMascheroniConstant) := by
    simpa only [F,Nat.cast_add_one] using (tendsto_add_atTop_iff_nat 1).mpr tendsto_harmonic_sub_log
  have hz : Tendsto (fun j : ℕ => 1/(2*((j:ℝ)+1))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/2)
    simpa only [mul_zero,div_mul_div_comm,one_mul] using h
  have hz' : Tendsto (fun j : ℕ => 1/(2*((j:ℝ)+2))) atTop (𝓝 0) := by
    convert (tendsto_add_atTop_iff_nat 1).mpr hz using 1
    funext j
    push_cast
    ring
  have hLt : Tendsto L atTop (𝓝 eulerMascheroniConstant) := by
    simpa only [sub_zero] using hF.sub hz'
  have hUt : Tendsto U atTop (𝓝 eulerMascheroniConstant) := by
    simpa only [sub_zero] using hF.sub hz
  have hstep (j : ℕ) : L (j+1) ≤ L j ∧ U j ≤ U (j+1) := by
    have bounds := log_step_bounds (x := (j:ℝ)+1) (by positivity)
    have hf : F (j+1) = F j + 1/((j:ℝ)+1+1) - log ((j:ℝ)+1+1) + log ((j:ℝ)+1) := by
      dsimp only [F]
      rw [harmonic_succ (j+1)]
      push_cast
      ring
    dsimp only [L,U]
    rw [hf,Nat.cast_add_one]
    rw [show (j:ℝ)+1+1 = j+2 by ring] at bounds ⊢
    constructor <;> linarith only [bounds.1,bounds.2]
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have ha := (antitone_nat_of_succ_le fun j => (hstep j).1).le_of_tendsto hLt j
  have hb := (monotone_nat_of_le_succ fun j => (hstep j).2).ge_of_tendsto hUt j
  dsimp only [L,U,F] at ha hb
  push_cast
  rw [show (j:ℝ)+1+1 = j+2 by ring]
  constructor <;> linarith only [ha,hb]

end
end RiemannGaussian.AlpogeZetaSamples
