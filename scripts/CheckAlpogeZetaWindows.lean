import AlpogePrimeWindows
import RiemannGaussian.ZetaCenteredEulerZeroFree
import RiemannGaussian.ZetaFirstZeroCompleteness
import RiemannGaussian.AlpogeZetaPowerWindows
import RiemannGaussian.AlpogeZetaShortIntervals
import Lean.Util.CollectAxioms

/-! # Actual sign excursions of Alpöge's modulus-one function in every late power window -/

namespace RiemannGaussian.AlpogeWindow
noncomputable section
open Complex Filter Set MeasureTheory Topology Deduction

private theorem poleData_neg {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hp : PoleData g Φ Z)
    (hn : ∀ z ∈ Z, z.im ≠ 0) : PoleData (-g) (-Φ) Z := by
  refine ⟨hp.meas.neg,?_,?_,hp.pos,hp.diff.neg,hp.iso,?_⟩
  · obtain ⟨C,h⟩ := hp.growth
    exact ⟨C,fun u hu => by simpa using h u hu⟩
  · intro s hs
    simp only [Pi.neg_apply,hp.laplace s hs,Complex.ofReal_neg,neg_mul,integral_neg]
  · intro z hz
    obtain ⟨c,hc,_,f,hf,he⟩ := hp.pole z hz
    refine ⟨-c,neg_ne_zero.mpr hc,fun hi => (hn z hz hi).elim,-f,hf.neg,?_⟩
    filter_upwards [he] with s hs
    simp only [Pi.neg_apply,hs,neg_div]
    ring

private theorem zeta_nonreal {z : ℂ} (hz : z ∈ zeroSet zetaFamily) : z.im ≠ 0 := by
  obtain ⟨hr,i,h|h⟩ := hz
  all_goals
    have hzero : riemannZeta z = 0 := by
      simpa [zetaFamily,DirichletCharacter.LFunction_modOne_eq] using h
    have hlt : z.re < 1 := lt_of_not_ge fun hh => riemannZeta_ne_zero_of_one_le_re hh hzero
    have hne : z ≠ 1 := by rintro rfl; norm_num at hlt
    intro hi
    exact riemannZeta_ne_zero_of_im_sq_le_three hr hne (by rw [hi]; norm_num) hzero

private theorem eventually_excursion {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ}
    (hp : PoleData g Φ Z) {ρ : ℂ} (hρ : ρ ∈ Z) {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hθρ : θ < ρ.re) (hδ : 0 < δ) (C : ℝ) :
    ∀ᶠ U : ℝ in atTop, ∃ u ∈ Icc U ((1+δ)*U), C*Real.exp (θ*u) < g u := by
  by_contra h
  have hfail := not_eventually.mp h
  apply (not_le.mpr hθρ)
  apply landau_window hp hθ hθ1 hδ _ ρ hρ
  intro η hη U₀
  obtain ⟨Y,hY⟩ := windowHyp_of_rpow_eventually (|C| *δ) η (by positivity) hη
  obtain ⟨U,hu,hn⟩ := (frequently_atTop.mp hfail) (max U₀ (max 0 (Real.log (max 1 Y))))
  have hu0 := (le_max_left _ _).trans hu
  have hup := (le_max_left _ _).trans ((le_max_right _ _).trans hu)
  have hy := (le_max_right _ _).trans ((le_max_right _ _).trans hu)
  have hpy : 0 < max 1 Y := zero_lt_one.trans_le (le_max_left _ _)
  have hb := (hY (Real.exp U) ((le_max_right _ _).trans ((Real.log_le_iff_le_exp hpy).mp hy))).2
  rw [Real.log_exp,← Real.exp_mul,mul_comm U η] at hb
  let R := fun u => |C| *Real.exp (θ*u)
  have he : (fun u => R u*Real.exp (-θ*u)) = fun _ => |C| := by
    funext u
    dsimp [R]
    rw [mul_assoc,← Real.exp_add,show θ*u + -θ*u = 0 by ring,Real.exp_zero,mul_one]
  refine ⟨U,hu0,R,?_,?_,?_⟩
  · rw [he]; exact integrableOn_const isCompact_Icc.measure_ne_top
  · intro u hu'
    exact ⟨by dsimp [R]; positivity,(le_of_not_gt fun hh => hn ⟨u,hu',hh⟩).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)⟩
  · rw [he,setIntegral_const,Real.volume_real_Icc_of_le (by nlinarith [mul_nonneg hδ.le hup]),smul_eq_mul]
    linarith only [hb]

private theorem G_excursions_of_zero (ρ : NontrivialZetaZero) {θ δ : ℝ} (hθ : 0 < θ)
    (hθρ : θ < ρ.1.re) (hδ : 0 < δ) (C : ℝ) :
    ∀ᶠ Y : ℝ in atTop,
      (∃ y ∈ Icc Y (Y^(1+δ)), C*y^θ < Deduction.G y) ∧
      (∃ y ∈ Icc Y (Y^(1+δ)), Deduction.G y < -(C*y^θ)) := by
  have hmem : ρ.1 ∈ zeroSet zetaFamily := ⟨ρ.zero_lt_re,(),Or.inl (by
    simpa [zetaFamily,DirichletCharacter.LFunction_modOne_eq] using ρ.2.1)⟩
  obtain ⟨Φ,hp⟩ := poleData zetaFamily
  have hp' := poleData_neg hp (fun _ h => zeta_nonreal h)
  have hp1 := eventually_excursion hp hmem hθ (hθρ.trans ρ.re_lt_one) hθρ hδ C
  have hp2 := eventually_excursion hp' hmem hθ (hθρ.trans ρ.re_lt_one) hθρ hδ C
  filter_upwards [Real.tendsto_log_atTop.eventually (hp1.and hp2),eventually_gt_atTop (0:ℝ)]
    with Y hh hY
  have hmem' {u : ℝ} (hu : u ∈ Icc (Real.log Y) ((1+δ)*Real.log Y)) :
      Real.exp u ∈ Icc Y (Y^(1+δ)) := by
    refine ⟨(Real.log_le_iff_le_exp hY).mp hu.1,?_⟩
    rw [Real.rpow_def_of_pos hY,mul_comm (Real.log Y)]
    exact Real.exp_le_exp.mpr hu.2
  obtain ⟨⟨u,hu,hpu⟩,⟨v,hv,hpv⟩⟩ := hh
  refine ⟨⟨Real.exp u,hmem' hu,?_⟩,⟨Real.exp v,hmem' hv,?_⟩⟩
  · simpa only [gm,gm_zeta,← Real.exp_mul,mul_comm u θ] using hpu
  · simp only [Pi.neg_apply,gm,gm_zeta] at hpv
    rw [← Real.exp_mul,mul_comm v θ]
    linarith

/-- Both signs occur beyond any fixed multiple of `y^θ`, for `0 < θ < 1/2`, in every
sufficiently late power window, for the actual function `Deduction.G`. -/
theorem eventually_G_excursions {θ δ : ℝ} (hθ : 0 < θ) (hhalf : θ < 1/2)
    (hδ : 0 < δ) (C : ℝ) :
    ∀ᶠ Y : ℝ in atTop,
      (∃ y ∈ Icc Y (Y^(1+δ)), C*y^θ < Deduction.G y) ∧
      (∃ y ∈ Icc Y (Y^(1+δ)), Deduction.G y < -(C*y^θ)) := by
  obtain ⟨ρ,_,_,hre,_⟩ := ZetaFirstZeroCompleteness.complete_first_pair
  exact G_excursions_of_zero ρ hθ (by rwa [hre]) hδ C

/-- The polynomial parameters of Alpöge's elementary size model cannot satisfy its
thin-scale bound even at the trivial character. Here h is the host cardinality,
T = X'/3 = 4h(x+1)x² and the proposed relative error is 1/(4h(x+1)x). -/
theorem size_model_thin_scale_obstruction :
    ∀ᶠ x : ℝ in atTop, ∀ h : ℝ, x ≤ h →
      ∃ y ∈ Icc (4*h*(x+1)*x^2) ((4*h*(x+1)*x^2)^(9/8:ℝ)),
        y / (4*h*(x+1)*x) < Deduction.G y := by
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (eventually_G_excursions (θ := 1/3) (δ := 1/8)
    (by norm_num) (by norm_num) (by norm_num) 1)
  filter_upwards [eventually_ge_atTop (max 1 T₀)] with x hx
  intro h hxH
  have hx1 := (le_max_left _ _).trans hx
  have hx0 := zero_lt_one.trans_le hx1
  let D := 4*h*(x+1)*x
  let T := 4*h*(x+1)*x^2
  have hDT : T = x*D := by dsimp only [D,T]; ring
  have hD : x^3 ≤ D := by
    calc x^3 = x*x*x := by ring
         _ ≤ (4*h)*(x+1)*x := by gcongr <;> linarith
  have hD1 : 1 ≤ D := (one_le_pow₀ hx1).trans hD
  have hD0 := zero_lt_one.trans_le hD1
  have hxT : x ≤ T := by rw [hDT]; exact le_mul_of_one_le_right hx0.le hD1
  have hT0 := hx0.trans_le hxT
  obtain ⟨y,hy,hg⟩ := (hT₀ T (((le_max_right _ _).trans hx).trans hxT)).1
  have hy0 := hT0.trans_le hy.1
  have htop : y ≤ T^(9/8:ℝ) := by convert hy.2 using 1; norm_num
  have hpow := Real.rpow_le_rpow hy0.le htop (by norm_num : (0:ℝ) ≤ 2/3)
  rw [← Real.rpow_mul hT0.le,show (9/8:ℝ)*(2/3)=3/4 by norm_num] at hpow
  have hcube : T^3 ≤ D^4 := by
    rw [hDT,mul_pow,show D^4 = D*D^3 by ring]
    exact mul_le_mul_of_nonneg_right hD (by positivity)
  have hroot := Real.rpow_le_rpow (pow_nonneg hT0.le 3) hcube (by norm_num : (0:ℝ) ≤ 1/4)
  rw [← Real.rpow_natCast_mul hT0.le,← Real.rpow_natCast_mul hD0.le] at hroot
  norm_num at hroot
  rw [one_mul] at hg
  refine ⟨y,⟨hy.1,htop⟩,lt_of_le_of_lt ((div_le_iff₀ hD0).mpr ?_) hg⟩
  calc y = y^(1/3:ℝ)*y^(2/3:ℝ) := by rw [← Real.rpow_add hy0]; norm_num
       _ ≤ y^(1/3:ℝ)*D := mul_le_mul_of_nonneg_left (hpow.trans hroot) (by positivity)

/-- The native real finite sum agrees term by term with the function in the archived criterion. -/
theorem G_native (x : ℝ) : Deduction.G x = AlpogeZetaSamples.G x := by
  unfold Deduction.G Deduction.ramp AlpogeZetaSamples.G AlpogeZetaSamples.ramp
  rw [Complex.re_sum]
  simp only [mul_one,← Complex.ofReal_mul,Complex.ofReal_re]

private theorem G_nonpositive_in_windows {δ : ℝ} (hd : 0 < δ) :
    ∀ᶠ Y : ℝ in atTop, ∃ a ∈ Icc Y (Y^(1+δ)), AlpogeZetaSamples.G a ≤ 0 := by
  filter_upwards [eventually_G_excursions (θ := 1/4) (by norm_num) (by norm_num) hd 0] with Y hh
  obtain ⟨a,ha,han⟩ := hh.2
  refine ⟨a,ha,?_⟩
  simpa [G_native] using han.le

private theorem cofinal_nonpositive (A : ℝ) : ∃ b ≥ A, AlpogeZetaSamples.G b ≤ 0 := by
  obtain ⟨Y,hy,⟨b,hb,h⟩⟩ := ((eventually_ge_atTop A).and (G_nonpositive_in_windows (δ := 1) (by norm_num))).exists
  exact ⟨b,hy.trans hb.1,h⟩

/-- Any verified all-height half-plane strictly below one supplies a bound at its exact
exponent on every real argument of the original modulus-one function. -/
theorem G_le_of_zero_halfplane {B : ℝ} (hB : 0 ≤ B) (hB1 : B < 1)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → Deduction.G x ≤ C*x^B := by
  simpa only [G_native] using AlpogeZetaSamples.G_upper_of_cofinal_nonpositive hB hB1 hz cofinal_nonpositive

/-- The verified seven-eighths zero half-plane gives actual full power windows, and in fact
an upper bound on the original function at every real argument from one onwards. -/
theorem G_le_seven_eighths :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → Deduction.G x ≤ C*x^(7/8:ℝ) := by
  exact G_le_of_zero_halfplane (by norm_num) (by norm_num) suzukiLocalZero_re_le_seven_eighths

/-- At each fixed exponent, late power windows imply a uniform bound with that same exponent
on all real arguments. Specialization to zeta and the sampled normalization suffice. -/
theorem G_power_windows_iff_global {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hd : 0 < δ) :
    (∃ C : ℝ, ∀ A : ℝ, ∃ Y ≥ A, ∀ y ∈ Icc Y (Y^(1+δ)), Deduction.G y ≤ C*y^θ) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → Deduction.G x ≤ C*x^θ := by
  constructor
  · rintro ⟨C,h⟩
    have hzero := Deduction.zeroFree_of_rpow_window zetaFamily hθ hθ1 hd
      (C := C) (by simpa only [gm_zeta] using h)
    have hz (ρ : NontrivialZetaZero) : ρ.1.re ≤ θ := by
      by_contra! hr
      have hn := hzero () ρ.1 hr
      exact hn (by simpa [zetaFamily,DirichletCharacter.LFunction_modOne_eq] using ρ.2.1)
    exact G_le_of_zero_halfplane hθ.le hθ1 hz
  · rintro ⟨C,_,h⟩
    exact ⟨C,fun A => ⟨max A 1,le_max_left _ _,fun y hy => h y ((le_max_right _ _).trans hy.1)⟩⟩

/-- Every sufficiently late qualifying power window contains a whole interval of strictly
negative values of the actual modulus-one ramp, of additive length `a^α` for any fixed
`0 ≤ α < 1`. The negative excursions are taken near the actual supremum of zero real parts. -/
theorem eventually_negative_subintervals {α δ : ℝ} (hα : 0 ≤ α) (hα' : α < 1)
    (hδ : 0 < δ) : ∀ᶠ Y : ℝ in atTop,
      ∃ a : ℝ, Y ≤ a ∧ a+a^α ≤ Y^(1+δ) ∧ ∀ y ∈ Icc a (a+a^α), Deduction.G y < 0 := by
  let S := Set.range (fun ρ : NontrivialZetaZero => ρ.1.re)
  let B := sSup S
  obtain ⟨ρ₀,_,_,hre,_⟩ := ZetaFirstZeroCompleteness.complete_first_pair
  have hne : S.Nonempty := ⟨ρ₀.1.re,ρ₀,rfl⟩
  have hbd : BddAbove S := ⟨1,fun _ ⟨ρ,he⟩ => he ▸ ρ.re_lt_one.le⟩
  have hz (ρ : NontrivialZetaZero) : ρ.1.re ≤ B := le_csSup hbd ⟨ρ,rfl⟩
  have hB : 0 < B := ρ₀.zero_lt_re.trans_le (hz _)
  have hB1 : B ≤ 1 := csSup_le hne fun _ ⟨ρ,he⟩ => he ▸ ρ.re_lt_one.le
  obtain ⟨_,⟨ρ,rfl⟩,hρ⟩ := exists_lt_of_lt_csSup (s := S) hne
    (show max 0 (B+α-1) < B from max_lt hB (by linarith))
  let θ := (max 0 (B+α-1)+ρ.1.re)/2
  have hθlo : max 0 (B+α-1) < θ := by dsimp [θ]; linarith
  have hθ := (le_max_left _ _).trans_lt hθlo
  have hθρ : θ < ρ.1.re := by dsimp [θ]; linarith
  obtain ⟨C,h⟩ := AlpogeZetaSamples.negative_interval_of_sample hB.le hB1 hz hα hα'.le hθ.le
    ((le_max_right _ _).trans_lt hθlo)
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  have hd2 : 0 < δ/2 := by linarith
  filter_upwards [G_excursions_of_zero ρ hθ hθρ hd2 C,(tendsto_rpow_atTop hd2).eventually_ge_atTop 2,
    eventually_ge_atTop (max 1 N)] with Y hsign hwide hy
  obtain ⟨a,ha,hneg⟩ := hsign.2
  have hy1 := (le_max_left _ _).trans hy
  have ha1 := hy1.trans ha.1
  have hp : a^α ≤ a := (Real.rpow_le_rpow_of_exponent_le ha1 hα'.le).trans_eq (Real.rpow_one _)
  refine ⟨a,ha.1,?_,?_⟩
  · have he : Y^(1+δ/2)*Y^(δ/2) = Y^(1+δ) := by rw [← Real.rpow_add (by linarith : 0 < Y)]; ring_nf
    linarith [mul_le_mul_of_nonneg_left hwide (Real.rpow_nonneg (by linarith : 0 ≤ Y) (1+δ/2)),ha.2]
  · rw [G_native] at hneg
    intro y hyy
    rw [G_native]
    exact hN a (((le_max_right _ _).trans hy).trans ha.1) hneg y hyy

/-- Every sufficiently late power window contains a block of consecutive
fourth powers with strictly negative principal sum. Its length may grow
as any fixed sublinear power of the starting index. -/
theorem negative_polynomial_fourth_blocks {β δ : ℝ} (hβ : 0 ≤ β) (hβ₁ : β < 1) (hδ : 0 < δ) :
    ∀ᶠ Y : ℝ in atTop, ∃ M : ℕ, ∀ n ∈ Finset.Icc M (M+⌊(M:ℝ)^β⌋₊),
      (n:ℝ)^4 ∈ Icc Y (Y^(1+δ)) ∧ Deduction.G ((n:ℝ)^4) < 0 := by
  let η := (β+1)/8
  obtain ⟨A,hA⟩ := eventually_atTop.mp (AlpogeZetaSamples.polynomial_fourth_blocks_of_one_side
    (show η ≤ 1/4 by dsimp [η]; linarith) hβ (show β < 4*η by dsimp [η]; linarith) 0)
  have hN := eventually_negative_subintervals (show 0 ≤ (3:ℝ)/4+η by dsimp [η]; linarith)
    (show (3:ℝ)/4+η < 1 by dsimp [η]; linarith) hδ
  filter_upwards [hN,eventually_ge_atTop A] with Y hY hYA
  obtain ⟨a,ha,hupper,hneg⟩ := hY
  let P (x : ℝ) := x ∈ Icc Y (Y^(1+δ)) ∧ Deduction.G x < 0
  obtain ⟨M,_,h⟩ := hA a (hYA.trans ha) P (Or.inr fun y hy =>
    ⟨⟨ha.trans hy.1,hy.2.trans hupper⟩,hneg y hy⟩)
  exact ⟨M,h⟩

/-- For each admissible exponent it is enough to bound the finite string of fourth-power
observations bracketing arbitrarily late power windows. -/
theorem rh_of_fourth_power_G_windows
    (h : ∀ θ : ℝ, 1/2 < θ → θ < 1 → ∃ δ C : ℝ, 0 < δ ∧
      ∀ A : ℝ, ∃ Y ≥ A, ∀ n ∈ Finset.Icc ⌊Y^(1/4:ℝ)⌋₊ (⌊(Y^(1+δ))^(1/4:ℝ)⌋₊+1),
        Deduction.G ((n:ℝ)^4) ≤ C*((n:ℝ)^4)^θ) : RiemannHypothesis := by
  apply rh_of_smoothed_prime_windows
  intro θ hl hr
  obtain ⟨δ,C,hδ,hC⟩ := h θ hl hr
  refine ⟨δ,16*|C| +225/4,hδ,fun A => ?_⟩
  obtain ⟨Y,hY,hy⟩ := hC (max 1 A)
  refine ⟨Y,(le_max_right _ _).trans hY,fun y hh => ?_⟩
  rw [G_native]
  apply AlpogeZetaSamples.G_le_on_interval_of_fourth_samples ((le_max_left _ _).trans hY)
    (abs_nonneg C) hl.le hr.le _ hh
  intro n hn
  rw [← G_native]
  exact (hy n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))

end
end RiemannGaussian.AlpogeWindow


open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeWindow.G_native,
      ``RiemannGaussian.AlpogeWindow.eventually_G_excursions,
      ``RiemannGaussian.AlpogeWindow.size_model_thin_scale_obstruction,
      ``RiemannGaussian.AlpogeWindow.G_le_of_zero_halfplane,
      ``RiemannGaussian.AlpogeWindow.G_le_seven_eighths,
      ``RiemannGaussian.AlpogeWindow.G_power_windows_iff_global,
      ``RiemannGaussian.AlpogeWindow.eventually_negative_subintervals,
      ``RiemannGaussian.AlpogeWindow.negative_polynomial_fourth_blocks,
      ``RiemannGaussian.AlpogeWindow.rh_of_fourth_power_G_windows] do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
    logInfo m!"{decl} depends on {axioms}"
