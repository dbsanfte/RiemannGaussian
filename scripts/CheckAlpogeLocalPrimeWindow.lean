import CheckAlpogeIntegerBaseline
import CheckAlpogeZetaWindows

/-! # Fourth-power windows with the exterior prime contributions removed -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real Filter AlpogeZetaSamples
open scoped ArithmeticFunction.vonMangoldt

/-- The Green function of linear interpolation on [a,b], divided by the
denominator d. Only a < d ≤ b is used in the prime sum. -/
def chordWeight (a N b d : ℕ) : ℝ :=
  if d ≤ N then ((b:ℝ)-N)/(b-a)*(((d:ℝ)-a)/d)
  else ((N:ℝ)-a)/(b-a)*(((b:ℝ)-d)/d)

/-- The local prime-power shortfall for a single sample and two shared endpoints. -/
def chordDeficit (a N b : ℕ) : ℝ :=
  ∑ d ∈ Ioc a b, (1-Λ d)*chordWeight a N b d

private def coeffRamp (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 N, c d*((N:ℝ)/d-1)

private theorem interpolation_weights {a N b : ℕ} (ha : a ≤ N) (hb : N ≤ b) (hab : a < b) :
    let u := ((b:ℝ)-N)/(b-a)
    let v := ((N:ℝ)-a)/(b-a)
    0 ≤ u ∧ 0 ≤ v ∧ u+v=1 ∧ u*a+v*b=N := by
  have hd := sub_pos.mpr (Nat.cast_lt.mpr hab : (a:ℝ) < b)
  exact ⟨div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hb)) hd.le,
    div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr ha)) hd.le,
    by field_simp; ring,by field_simp; ring⟩

private theorem coeffRamp_chord (c : ℕ → ℝ) {a N b : ℕ} (ha : a ≤ N) (hb : N ≤ b) (hab : a < b) :
    let u := ((b:ℝ)-N)/(b-a)
    let v := ((N:ℝ)-a)/(b-a)
    u*coeffRamp c a+v*coeffRamp c b-coeffRamp c N =
      ∑ d ∈ Ioc a b, c d*chordWeight a N b d := by
  let u := ((b:ℝ)-N)/(b-a)
  let v := ((N:ℝ)-a)/(b-a)
  let f (t d : ℕ) := c d*((t:ℝ)/d-1)
  obtain ⟨_,_,hs,hx⟩ := interpolation_weights ha hb hab
  change u+v=1 at hs
  change u*a+v*b=N at hx
  have whole (d : ℕ) : u*f a d+v*f b d-f N d=0 := by
    dsimp only [f]
    linear_combination (norm := ring) (c d / d)*hx - c d*hs
  have left (d : ℕ) (hd : d ∈ Ioc a N) : v*f b d-f N d = c d*chordWeight a N b d := by
    rw [chordWeight,ite_eq_left (mem_Ioc.mp hd).2]
    change v*f b d-f N d=c d*(u*(((d:ℝ)-a)/d))
    dsimp only [f]
    have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Ioc.mp hd).1; omega)
    field_simp
    linear_combination (norm := ring) c d*hx - (c d*d)*hs
  have right (d : ℕ) (hd : d ∈ Ioc N b) : v*f b d = c d*chordWeight a N b d := by
    rw [chordWeight,ite_eq_right (not_le.mpr (mem_Ioc.mp hd).1)]
    change v*f b d=c d*(v*(((b:ℝ)-d)/d))
    dsimp only [f]
    field_simp [Nat.cast_ne_zero.mpr (show d ≠ 0 by have := (mem_Ioc.mp hd).1; omega)]
  have h0 : (∑ d ∈ Ioc 0 a, (u*f a d+v*f b d-f N d))=0 := sum_eq_zero fun d _ => whole d
  have h1 := sum_congr rfl left
  have h2 := sum_congr rfl right
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum] at h0 h1 h2
  change u*(∑ d ∈ Ioc 0 a, f a d)+v*(∑ d ∈ Ioc 0 b, f b d)-(∑ d ∈ Ioc 0 N, f N d) = _
  rw [← sum_Ioc_consecutive (f b) (Nat.zero_le N) hb,
    ← sum_Ioc_consecutive (f b) (Nat.zero_le a) ha,
    ← sum_Ioc_consecutive (f N) (Nat.zero_le a) ha,
    ← sum_Ioc_consecutive (fun d => c d * chordWeight a N b d) ha hb]
  linarith only [h0,h1,h2]

private theorem unitRamp_remainder {N : ℕ} (hN : 0 < N) :
    let r := coeffRamp (fun _ => 1) N - ((N:ℝ)*log N+(eulerMascheroniConstant-1)*N)
    0 ≤ r ∧ r ≤ 1/2 := by
  have hsum : (∑ d ∈ Ioc 0 N, (d:ℝ)⁻¹) = (harmonic N:ℝ) := by
    rw [harmonic_eq_sum_Icc,Formalism.LogFactorialMertensBounds.Icc_one_eq_Ioc]
    push_cast
    rfl
  have he : coeffRamp (fun _ => 1) N = (N:ℝ)*(harmonic N:ℝ)-N := by
    simp [coeffRamp,div_eq_mul_inv,sum_sub_distrib,← mul_sum,hsum]
  obtain ⟨hl,hu⟩ := harmonic_half_remainder hN
  have hpos : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hh := mul_le_mul_of_nonneg_left hu hpos.le
  rw [show (N:ℝ)*(1/(2*N))=1/2 by field_simp] at hh
  dsimp only
  rw [he]
  constructor <;> nlinarith only [hh,mul_nonneg hpos.le ((by positivity : 0 ≤ 1/(2*((N:ℝ)+1))).trans hl)]

private theorem G_coeffRamp (N : ℕ) :
    G N = coeffRamp (fun d => Λ d) N-(N:ℝ)*log N+(1+eulerMascheroniConstant)*N := by
  simp only [G_eq_archive (Nat.cast_nonneg N),Formalism.Gz,Formalism.Sz,Nat.floor_natCast,
    Formalism.LogFactorialMertensBounds.Icc_one_eq_Ioc,coeffRamp]

/-- The full error of replacing the centered ramp minus its endpoint chord by
the local signed sum is at most one half. This holds on every positive interval. -/
theorem chordDeficit_error {a N b : ℕ} (ha0 : 0 < a) (ha : a ≤ N) (hb : N ≤ b) (hab : a < b) :
    let u := ((b:ℝ)-N)/(b-a)
    let v := ((N:ℝ)-a)/(b-a)
    |chordDeficit a N b - (G N-u*G a-v*G b)| ≤ 1/2 := by
  let u := ((b:ℝ)-N)/(b-a)
  let v := ((N:ℝ)-a)/(b-a)
  let r (t : ℕ) := coeffRamp (fun _ => 1) t-((t:ℝ)*log t+(eulerMascheroniConstant-1)*t)
  obtain ⟨hu,hv,hs,hx⟩ := interpolation_weights ha hb hab
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  change u+v=1 at hs
  change u*a+v*b=N at hx
  have h1 := coeffRamp_chord (fun _ => 1) ha hb hab
  have hΛ := coeffRamp_chord (fun d => Λ d) ha hb hab
  have he : chordDeficit a N b - (G N-u*G a-v*G b) = u*r a+v*r b-r N := by
    unfold chordDeficit
    simp_rw [sub_mul,one_mul]
    rw [sum_sub_distrib]
    simp only [one_mul] at h1
    dsimp only at h1 hΛ
    change u*coeffRamp _ a+v*coeffRamp _ b-coeffRamp _ N = _ at h1 hΛ
    dsimp only [r]
    rw [G_coeffRamp,G_coeffRamp,G_coeffRamp]
    linear_combination (norm := ring) -h1 + hΛ + 2*eulerMascheroniConstant*hx
  have bound (t : ℕ) (ht : 0 < t) : 0 ≤ r t ∧ r t ≤ 1/2 := unitRamp_remainder ht
  obtain ⟨ra,sa⟩ := bound a ha0
  obtain ⟨rb,sb⟩ := bound b (ha0.trans_le (ha.trans hb))
  obtain ⟨rn,sn⟩ := bound N (ha0.trans_le ha)
  change |chordDeficit a N b - (G N-u*G a-v*G b)| ≤ 1/2
  rw [he]
  apply abs_le.mpr
  constructor <;> linarith only [rn,sn,mul_nonneg hu ra,mul_nonneg hv rb,
    mul_le_mul_of_nonneg_left sa hu,mul_le_mul_of_nonneg_left sb hv,hs]

/-- The actual centered ramp has a real zero in each sufficiently late power window. -/
theorem eventually_ramp_root {η : ℝ} (hη : 0 < η) :
    ∀ᶠ Y : ℝ in atTop, ∃ z ∈ Set.Icc Y (Y^(1+η)), G z = 0 := by
  filter_upwards [AlpogeWindow.eventually_G_excursions (θ := 1/4) (by norm_num) (by norm_num) hη 0,
    eventually_ge_atTop (1:ℝ)] with Y h hY
  simp only [zero_mul,neg_zero,AlpogeWindow.G_native] at h
  obtain ⟨⟨p,hp,hpos⟩,⟨q,hq,hneg⟩⟩ := h
  have cont {a b : ℝ} (ha : Y ≤ a) : ContinuousOn G (Set.Icc a b) := by
    have hL : 0 ≤ log 4+7 := by positivity
    have hLip : LipschitzOnWith ⟨_,hL⟩ G (Set.Icc a b) := by
      apply lipschitzOnWith_iff_dist_le_mul.mpr
      intro x hx y hy
      exact G_lipschitz (by linarith [hx.1]) (by linarith [hy.1])
    exact hLip.continuousOn
  rcases le_total q p with hqp | hpq
  · obtain ⟨z,hz,he⟩ := intermediate_value_Icc hqp (cont hq.1) ⟨hneg.le,hpos.le⟩
    exact ⟨z,⟨hq.1.trans hz.1,hz.2.trans hp.2⟩,he⟩
  · obtain ⟨z,hz,he⟩ := intermediate_value_Icc' hpq (cont hp.1) ⟨hneg.le,hpos.le⟩
    exact ⟨z,⟨hp.1.trans hz.1,hz.2.trans hq.2⟩,he⟩

private theorem round_root {z : ℝ} (hz : 2 ≤ z) (hg : G z = 0) :
    |G ⌊z⌋₊| ≤ 10 ∧ |G ⌈z⌉₊| ≤ 10 := by
  have hfloor := Nat.floor_le (by linarith : 0 ≤ z)
  have hs := Nat.lt_floor_add_one z
  have hceil := Nat.le_ceil z
  have ht := Nat.ceil_lt_add_one (by linarith : 0 ≤ z)
  have hf := G_lipschitz (x := (⌊z⌋₊:ℕ)) (y := z) (by linarith) (by linarith)
  have hc := G_lipschitz (x := (⌈z⌉₊:ℕ)) (y := z) (by linarith) (by linarith)
  rw [hg,sub_zero,abs_of_nonpos (sub_nonpos.mpr hfloor)] at hf
  rw [hg,sub_zero,abs_of_nonneg (sub_nonneg.mpr hceil)] at hc
  have hlog := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
  have hL : 0 ≤ log 4+7 := by positivity
  constructor <;> nlinarith only [hf,hc,hlog,mul_le_mul_of_nonneg_left
    (by linarith : -((⌊z⌋₊:ℝ)-z) ≤ 1) hL,mul_le_mul_of_nonneg_left
    (by linarith : (⌈z⌉₊:ℝ)-z ≤ 1) hL]

/-- The endpoints of an entire sample window can be placed just outside it.
The same two bounded observations serve all samples between them. -/
theorem local_prime_window_endpoints {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, ∀ {X Y : ℝ}, T ≤ X → X < Y → ∃ a b : ℕ,
      0 < a ∧ ⌊X^(1/(1+η))⌋₊ ≤ a ∧ (a:ℝ) ≤ X ∧ Y ≤ (b:ℝ) ∧ b ≤ ⌈Y^(1+η)⌉₊ ∧
        |G a| ≤ 10 ∧ |G b| ≤ 10 := by
  let t := 1/(1+η)
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨L,hL⟩ := eventually_atTop.mp (eventually_ramp_root hη)
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((tendsto_rpow_atTop ht).eventually_ge_atTop (max 2 L))
  refine ⟨max T (max 2 L),fun {X Y} hX hXY => ?_⟩
  have hx2 := (le_max_left 2 L).trans ((le_max_right _ _).trans hX)
  have hx0 : 0 < X := by linarith
  have hXt := hT X ((le_max_left _ _).trans hX)
  obtain ⟨z,hz,hgz⟩ := hL (X^t) ((le_max_right _ _).trans hXt)
  obtain ⟨w,hw,hgw⟩ := hL Y (((le_max_right 2 L).trans ((le_max_right _ _).trans hX)).trans hXY.le)
  have hend : (X^t)^(1+η)=X := by
    rw [← rpow_mul hx0.le,show t*(1+η)=1 by dsimp [t]; field_simp,rpow_one]
  rw [hend] at hz
  have hz2 := ((le_max_left _ _).trans hXt).trans hz.1
  have hw2 := (hx2.trans hXY.le).trans hw.1
  refine ⟨⌊z⌋₊,⌈w⌉₊,Nat.floor_pos.mpr (by linarith),Nat.floor_mono hz.1,
    (Nat.floor_le (by linarith)).trans hz.2,hw.1.trans (Nat.le_ceil w),Nat.ceil_mono hw.2,
    (round_root hz2 hgz).1,(round_root hw2 hgw).2⟩

/-- At bounded endpoints the local signed sum recovers each interior observation
to within eleven, uniformly in the width of the interval. -/
theorem G_chordDeficit_bounded {a N b : ℕ} (ha0 : 0 < a) (ha : a ≤ N) (hb : N ≤ b)
    (hab : a < b) (hl : |G a| ≤ 10) (hr : |G b| ≤ 10) : |G N-chordDeficit a N b| ≤ 11 := by
  obtain ⟨hu,hv,hs,_⟩ := interpolation_weights ha hb hab
  have he := abs_le.mp (chordDeficit_error ha0 ha hb hab)
  have low := add_le_add (mul_le_mul_of_nonneg_left (abs_le.mp hl).1 hu)
    (mul_le_mul_of_nonneg_left (abs_le.mp hr).1 hv)
  have high := add_le_add (mul_le_mul_of_nonneg_left (abs_le.mp hl).2 hu)
    (mul_le_mul_of_nonneg_left (abs_le.mp hr).2 hv)
  apply abs_le.mpr
  constructor <;> linarith only [he.1,he.2,low,high,hs]

/-- The ordinary-prime version of the smooth local shortfall. -/
def chordPrimeDeficit (a N b : ℕ) : ℝ :=
  ∑ d ∈ Ioc a b, (1-(if d.Prime then log d else 0))*chordWeight a N b d

private def properLog (d : ℕ) : ℝ := if d.Prime then 0 else Λ d

private theorem properLog_nonneg (d : ℕ) : 0 ≤ properLog d := by
  unfold properLog
  split <;> simp [ArithmeticFunction.vonMangoldt_nonneg]

private theorem properLog_prefix : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℕ,
    ∑ d ∈ Ioc 0 t, properLog d ≤ K*sqrt t := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨|C|,abs_nonneg _,fun t => ?_⟩
  have h := Chebyshev.psi_sub_theta_eq_sum_not_prime (t:ℝ)
  simp only [Nat.floor_natCast,sum_filter,ite_not] at h
  exact h.symm.le.trans ((hC t).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sqrt_nonneg _)))

/-- The interpolation weight lies in [0,1], and the tail decays as N/d
uniformly in both endpoints. -/
theorem chordWeight_bounds {a N b d : ℕ} (ha : a ≤ N) (hb : N ≤ b) (hab : a < b)
    (hd : d ∈ Ioc a b) :
    0 ≤ chordWeight a N b d ∧ chordWeight a N b d ≤ min 1 ((N:ℝ)/d) := by
  obtain ⟨hu,hv,hs,_⟩ := interpolation_weights ha hb hab
  obtain ⟨had,hdb⟩ := mem_Ioc.mp hd
  have hd0 : (0:ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hadR : (a:ℝ) < d := Nat.cast_lt.mpr had
  have hdbR : (d:ℝ) ≤ b := Nat.cast_le.mpr hdb
  have habR := sub_pos.mpr (Nat.cast_lt.mpr hab : (a:ℝ)<b)
  unfold chordWeight
  split_ifs with hdN
  · have hr := (div_le_one hd0).mpr (sub_le_self (d:ℝ) (Nat.cast_nonneg a))
    have h1 := (mul_le_of_le_one_right hu hr).trans
      (by linarith only [hs,hv] : ((b:ℝ)-N)/(b-a) ≤ 1)
    exact ⟨mul_nonneg hu (div_nonneg (by linarith only [hadR]) hd0.le),
      le_min h1 (h1.trans ((one_le_div hd0).mpr (Nat.cast_le.mpr hdN)))⟩
  · have h0 := mul_nonneg hv (div_nonneg (sub_nonneg.mpr hdbR) hd0.le)
    have hle : ((N:ℝ)-a)/(b-a)*(((b:ℝ)-d)/d) ≤ N/d := by
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ hd0.le
      have h := mul_le_mul_of_nonneg_left (show (b:ℝ)-d ≤ b-a by linarith) hv
      rw [div_mul_cancel₀ _ habR.ne'] at h
      exact h.trans (sub_le_self _ (Nat.cast_nonneg a))
    exact ⟨h0,le_min (hle.trans ((div_le_one hd0).mpr (Nat.cast_le.mpr (le_of_not_ge hdN)))) hle⟩

private theorem properLog_tail_bound {K : ℝ} (hK : 0 ≤ K)
    (hP : ∀ t : ℕ, ∑ d ∈ Ioc 0 t, properLog d ≤ K*sqrt t) {N : ℕ} (hN : 0 < N) (b : ℕ) :
    (∑ d ∈ Ioc N b, properLog d*((N:ℝ)/d)) ≤ 4*K*sqrt N := by
  let T (j : ℕ) := 4^j*N
  have hfour (j : ℕ) : (4:ℝ)^j=((2:ℝ)^j)^2 := by
    rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  have hs (j : ℕ) : sqrt (T j : ℝ) = (2:ℝ)^j*sqrt N := by
    dsimp only [T]; push_cast
    rw [sqrt_mul (by positivity),hfour,sqrt_sq (by positivity)]
  have hT (j : ℕ) : T j ≤ T (j+1) := by dsimp [T]; gcongr; norm_num
  have bound (j : ℕ) : (∑ d ∈ Ioc N (T j), properLog d*((N:ℝ)/d)) ≤
      4*K*sqrt N*(1-1/(2:ℝ)^j) := by
    induction j with
    | zero => simp [T]
    | succ j ih =>
      have hsmall : N ≤ T j := by dsimp [T]; exact Nat.le_mul_of_pos_left _ (by positivity)
      rw [← sum_Ioc_consecutive _ hsmall (hT j)]
      have hsum : (∑ d ∈ Ioc (T j) (T (j+1)), properLog d*((N:ℝ)/d)) ≤
          (K*sqrt (T (j+1):ℝ)) / (4:ℝ)^j := by
        calc
          _ ≤ ∑ d ∈ Ioc (T j) (T (j+1)), properLog d/(4:ℝ)^j := by
            apply sum_le_sum
            intro d hd
            rw [div_eq_mul_one_div (properLog d)]
            apply mul_le_mul_of_nonneg_left _ (properLog_nonneg d)
            have h := (mem_Ioc.mp hd).1
            have hd0 : (0:ℝ) < d := Nat.cast_pos.mpr (by omega)
            rw [div_le_div_iff₀ hd0 (by positivity)]
            simpa only [T,one_mul,mul_one,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_comm] using
              (Nat.cast_le.mpr h.le : (T j:ℝ) ≤ d)
          _ ≤ _ := by
            rw [← sum_div]
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact (sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le _))
              (fun k _ _ => properLog_nonneg k)).trans (hP _)
      apply (add_le_add ih hsum).trans_eq
      rw [hs,pow_succ (2:ℝ)]
      rw [hfour]
      field_simp
      ring
  have hmax : b ≤ T b := by
    apply (Nat.lt_pow_self (by decide : 1 < 4)).le.trans
    exact Nat.le_mul_of_pos_right _ hN
  calc
    _ ≤ ∑ d ∈ Ioc N (T b), properLog d*((N:ℝ)/d) :=
      sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hmax)
        (fun d _ _ => mul_nonneg (properLog_nonneg d) (by positivity))
    _ ≤ _ := (bound b).trans (mul_le_of_le_one_right (by positivity) (by linarith [show 0 ≤ 1/(2:ℝ)^b by positivity]))

/-- Removing every proper prime power has a square-root cost independent
of the ratio of the endpoint sizes. -/
theorem chordPrimeDeficit_proper_power_cost : ∃ K : ℝ, 0 ≤ K ∧ ∀ {a N b : ℕ}, 0 < a →
    a ≤ N → N ≤ b → a < b → 0 ≤ chordPrimeDeficit a N b-chordDeficit a N b ∧
    chordPrimeDeficit a N b-chordDeficit a N b ≤ K*sqrt N := by
  obtain ⟨C,hC,hP⟩ := properLog_prefix
  refine ⟨5*C,by positivity,fun {a N b} ha0 ha hb hab => ?_⟩
  have he : chordPrimeDeficit a N b-chordDeficit a N b =
      ∑ d ∈ Ioc a b, properLog d*chordWeight a N b d := by
    rw [chordPrimeDeficit,chordDeficit,← sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    by_cases h : d.Prime <;> simp [properLog,h,ArithmeticFunction.vonMangoldt_apply_prime]
    ring
  rw [he]
  refine ⟨sum_nonneg fun d hd => mul_nonneg (properLog_nonneg d) (chordWeight_bounds ha hb hab hd).1,?_⟩
  rw [← sum_Ioc_consecutive _ ha hb]
  have hl : (∑ d ∈ Ioc a N, properLog d*chordWeight a N b d) ≤ C*sqrt N := by
    apply le_trans _ (hP N)
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left (Nat.zero_le a))
      (fun d _ _ => properLog_nonneg d))
    exact sum_le_sum fun d hd => mul_le_of_le_one_right (properLog_nonneg d)
      ((chordWeight_bounds ha hb hab (Ioc_subset_Ioc_right hb hd)).2.trans (min_le_left _ _))
  have hr := properLog_tail_bound hC hP (ha0.trans_le ha) b
  have hu := sum_le_sum (s := Ioc N b) fun d hd => mul_le_mul_of_nonneg_left
    ((chordWeight_bounds ha hb hab (Ioc_subset_Ioc_left ha hd)).2.trans (min_le_right _ _))
    (properLog_nonneg d)
  linarith only [hl,hu,hr]

/-- Normalized positive local shortfall over a window of fourth-power indices. -/
def chordPrimeExcessOn (C : ℝ) (a b m t : ℕ) : ℝ :=
  ∑ n ∈ Icc m t, max (chordPrimeDeficit a (n^4) b-C*(n:ℝ)^2*(1+log n)^2) 0/(n:ℝ)^3

private theorem bounded_chord_prime_comparison : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {a b n : ℕ}, 0 < a → a ≤ n^4 → n^4 ≤ b → a < b → |G a| ≤ 10 → |G b| ≤ 10 →
      |chordPrimeDeficit a (n^4) b-integerPrimeDiscrepancy (n^2)| ≤ K*(n:ℝ)^2 := by
  obtain ⟨P,hP,hpp⟩ := chordPrimeDeficit_proper_power_cost
  obtain ⟨B,hB,hbase⟩ := singlePrime_central_error
  refine ⟨11+P+B,by positivity,fun {a b n} ha0 ha hb hab hl hr => ?_⟩
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at ha; omega)
  have hn2 := one_le_pow₀ (Nat.one_le_cast.mpr hn : 1 ≤ (n:ℝ)) (n := 2)
  have he := abs_le.mp (G_chordDeficit_bounded ha0 ha hb hab hl hr)
  have hp := hpp ha0 ha hb hab
  have hx := abs_le.mp (hbase n hn)
  rw [Nat.cast_pow,show (n:ℝ)^4 = ((n:ℝ)^2)^2 by ring,sqrt_sq (sq_nonneg _)] at hp
  rw [Nat.cast_pow] at he
  apply abs_le.mpr
  constructor <;> linarith only [hx.1,hx.2,he.1,he.2,hp.1,hp.2,hn2,
    mul_nonneg hP (sq_nonneg (n:ℝ))]

/-- For every sufficiently late full window, a single pair of endpoints in the two
outer buffers recovers the original prime discrepancy to square-root accuracy
at every sample simultaneously. Only primes between the endpoints occur. -/
theorem local_prime_window_comparison {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ M : ℕ, ∀ {m t : ℕ}, M ≤ m → m < t → ∃ a b : ℕ,
      ⌊((m:ℝ)^4/4)^(1/(1+η))⌋₊ ≤ a ∧ 4*a ≤ m^4 ∧ 4*t^4 ≤ b ∧ b ≤ ⌈(4*(t:ℝ)^4)^(1+η)⌉₊ ∧
      ∀ n ∈ Icc m t, |chordPrimeDeficit a (n^4) b-integerPrimeDiscrepancy (n^2)| ≤ K*(n:ℝ)^2 := by
  obtain ⟨K,hK,h⟩ := bounded_chord_prime_comparison
  obtain ⟨T,hT⟩ := local_prime_window_endpoints hη
  refine ⟨K,hK,max 2 ⌈4*T⌉₊,fun {m t} hm hmt => ?_⟩
  have hm1 : 1 ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
  have hmt4 := Nat.pow_lt_pow_left hmt (by decide : 4 ≠ 0)
  have hX : T ≤ (m:ℝ)^4/4 := by
    have h := Nat.ceil_le.mp ((le_max_right _ _).trans hm)
    linarith only [h,le_self_pow₀ hm1 (by decide : 4 ≠ 0)]
  have hY : (m:ℝ)^4/4 < 4*(t:ℝ)^4 := by
    have h : (m:ℝ)^4 < (t:ℝ)^4 := by exact_mod_cast hmt4
    linarith only [h,pow_nonneg (Nat.cast_nonneg (α := ℝ) m) 4]
  obtain ⟨a,b,ha0,hs,ha,hb,hu,hl,hr⟩ := hT hX hY
  have ha2 : 4*a ≤ m^4 := by exact_mod_cast (show 4*(a:ℝ) ≤ (m:ℝ)^4 by linarith)
  have hb2 : 4*t^4 ≤ b := by exact_mod_cast hb
  have haN : a ≤ m^4 := by omega
  have hbN : t^4 ≤ b := by omega
  refine ⟨a,b,hs,ha2,hb2,hu,fun n hn => h ha0
    (haN.trans (Nat.pow_le_pow_left (mem_Icc.mp hn).1 _))
    ((Nat.pow_le_pow_left (mem_Icc.mp hn).2 _).trans hbN) ((haN.trans_lt hmt4).trans_le hbN) hl hr⟩

/-- Uniform control of the ordinary-prime shortfall in the two outer buffers
suffices. The arithmetic hypothesis involves only finite sums of ordinary primes. -/
theorem rh_of_chordPrimeExcessOn_powerWindows {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      let t := powerWindowEnd δ m
      ∀ a b : ℕ, ⌊((m:ℝ)^4/4)^(1/(1+η))⌋₊ ≤ a → 4*a ≤ m^4 → 4*t^4 ≤ b → b ≤ ⌈(4*(t:ℝ)^4)^(1+η)⌉₊ →
        chordPrimeExcessOn C a b m t ≤ (m:ℝ)^α) : RiemannHypothesis := by
  obtain ⟨K,hK,M,hM⟩ := local_prime_window_comparison hη
  apply rh_of_singlePrimeExcessOn_powerWindows (C := C+K) (by positivity)
  intro α hα
  obtain ⟨δ,hδ,hδ₁,hw⟩ := h α hα
  refine ⟨δ,hδ,hδ₁,fun A => ?_⟩
  obtain ⟨m,hm,hh⟩ := hw (max (max 2 M) A)
  let t := powerWindowEnd δ m
  have hmb : m < t := by
    have hmr : (1:ℝ) < m := by exact_mod_cast (show 1 < m by omega)
    have hh := rpow_lt_rpow_of_exponent_lt hmr (by linarith : 1 < 1+δ)
    rw [rpow_one] at hh
    exact_mod_cast hh.trans_le (Nat.le_ceil ((m:ℝ)^(1+δ)))
  obtain ⟨a,b,h₁,h₂,h₃,h₄,hx⟩ := hM (by omega : M ≤ m) hmb
  refine ⟨m,by omega,le_trans ?_ (hh a b h₁ h₂ h₃ h₄)⟩
  apply sum_le_sum
  intro n hn
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply max_le_max_right
  have hlow := (abs_le.mp (hx n hn)).1
  have hcost := mul_le_mul_of_nonneg_left (one_le_pow₀
    (by linarith only [log_natCast_nonneg n] : 1 ≤ 1+log n) (n := 2))
    (mul_nonneg hK (sq_nonneg (n:ℝ)))
  nlinarith only [hlow,hcost]

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [
      ``RiemannGaussian.AlpogeMined.chordDeficit_error,
      ``RiemannGaussian.AlpogeMined.local_prime_window_endpoints,
      ``RiemannGaussian.AlpogeMined.G_chordDeficit_bounded,
      ``RiemannGaussian.AlpogeMined.chordPrimeDeficit_proper_power_cost,
      ``RiemannGaussian.AlpogeMined.local_prime_window_comparison,
      ``RiemannGaussian.AlpogeMined.rh_of_chordPrimeExcessOn_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
