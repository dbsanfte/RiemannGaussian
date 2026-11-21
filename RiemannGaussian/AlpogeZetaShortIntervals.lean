import RiemannGaussian.AlpogeZetaSampleBounds

/-! # One-sided intervals around small observations of the principal prime ramp -/

namespace RiemannGaussian.AlpogeZetaSamples
open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt

private noncomputable def rampSlope (a : ℝ) : ℝ :=
  ∑ n ∈ range (⌊a⌋₊+1), Λ n/(n:ℝ)

private theorem ramp_affine_error {a t b : ℝ} (ha : 1 ≤ a) (hat : a ≤ t) (htb : t ≤ b) :
    0 ≤ ramp t-ramp a-rampSlope a*(t-a) ∧
    ramp t-ramp a-rampSlope a*(t-a) ≤ (b-a+1)*Real.log b*((b-a)/a) := by
  have ha0 := zero_lt_one.trans_le ha
  have hf := Nat.floor_mono hat
  have H (n : ℕ) (hn : n ∈ range (⌊a⌋₊+1)) :
      Λ n*max (t/n-1) 0 = Λ n*max (a/n-1) 0 + (Λ n/n)*(t-a) := by
    obtain rfl|hn0 := Nat.eq_zero_or_pos n
    · simp
    have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr hn0
    have hna := (Nat.cast_le.mpr (Nat.le_of_lt_succ (mem_range.mp hn))).trans (Nat.floor_le ha0.le)
    rw [max_eq_left (sub_nonneg.mpr ((one_le_div hnpos).mpr (hna.trans hat))),
      max_eq_left (sub_nonneg.mpr ((one_le_div hnpos).mpr hna))]
    ring
  let S := Ico (⌊a⌋₊+1) (⌊t⌋₊+1)
  have he : ramp t-ramp a-rampSlope a*(t-a) = ∑ n ∈ S, Λ n*max (t/n-1) 0 := by
    unfold ramp rampSlope
    rw [← sum_range_add_sum_Ico _ (Nat.succ_le_succ hf),sum_congr rfl H,sum_add_distrib,← sum_mul]
    dsimp [S]
    ring
  rw [he]
  refine ⟨sum_nonneg (fun n _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_max_right _ _)),?_⟩
  have hlen : (S.card:ℝ) ≤ b-a+1 := by
    simp only [S,Nat.card_Ico,Nat.add_sub_add_right,Nat.cast_sub hf]
    linarith only [Nat.floor_le (ha0.le.trans hat),Nat.lt_floor_add_one a,htb]
  have hb := ha0.trans_le (hat.trans htb)
  have hlog := Real.log_nonneg (ha.trans (hat.trans htb))
  have herr : 0 ≤ (b-a)/a := div_nonneg (sub_nonneg.mpr (hat.trans htb)) ha0.le
  calc _ ≤ ∑ _n ∈ S, Real.log b*((b-a)/a) := by
         apply sum_le_sum
         intro n hn
         obtain ⟨hl,hu⟩ := mem_Ico.mp hn
         have han := (Nat.floor_lt ha0.le).mp (show ⌊a⌋₊ < n by omega)
         have hnb := (Nat.cast_le.mpr (Nat.le_of_lt_succ hu)).trans ((Nat.floor_le (ha0.le.trans hat)).trans htb)
         have h₁ : Λ n ≤ Real.log b := ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (ha0.trans han) hnb)
         have h₂ : t/(n:ℝ)-1 ≤ (b-a)/a := by
           have h := div_le_div_of_nonneg_left (ha0.le.trans hat) ha0 han.le
           have hb' := div_le_div_of_nonneg_right htb ha0.le
           linarith only [h,hb',show (b-a)/a = b/a-1 by field_simp]
         exact mul_le_mul h₁ (max_le h₂ herr) (le_max_right _ _) hlog
       _ ≤ _ := by
         simp only [sum_const,nsmul_eq_mul]
         linarith only [mul_le_mul_of_nonneg_right hlen (mul_nonneg hlog herr)]

/-- On a positive interval the centered ramp has an affine upper estimate through
any chosen observation. Its slope is shared by all points of the interval. -/
theorem G_affine_upper {a x b : ℝ} (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) :
    ∃ s : ℝ, ∀ y, a ≤ y → y ≤ b →
      G y ≤ G x + s*(y-x) + (b-a+1)*Real.log b*((b-a)/a) := by
  let s := rampSlope a + Real.eulerMascheroniConstant - Real.log x
  have hx := zero_lt_one.trans_le (ha.trans hax)
  have bound (y : ℝ) (hy : a ≤ y) (hy' : y ≤ b) :
      G y ≤ G x + s*(y-x) + (b-a+1)*Real.log b*((b-a)/a) := by
    have h := (ramp_affine_error ha hy hy').2
    have h' := (ramp_affine_error ha hax hxb).1
    have hy0 := zero_lt_one.trans_le (ha.trans hy)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hx hy0)
    rw [Real.log_div hx.ne' hy0.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hy0.le
    have he : y*(x/y-1) = x-y := by field_simp
    rw [he] at hmul
    unfold G
    dsimp [s]
    linarith only [hmul,h,h']
  exact ⟨s,bound⟩

/-- On one side of x the principal sum stays below its value at x plus the
cost of the finite prime events. The linear term from the old primes is
nonpositive in that direction. -/
theorem one_side_G_upper {a x b : ℝ} (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) :
    (∀ y ∈ Set.Icc a x, G y ≤ G x + (b-a+1)*Real.log b*((b-a)/a)) ∨
    (∀ y ∈ Set.Icc x b, G y ≤ G x + (b-a+1)*Real.log b*((b-a)/a)) := by
  obtain ⟨s,bound⟩ := G_affine_upper ha hax hxb
  by_cases hs : 0 ≤ s
  · exact Or.inl (fun y hy => by
      linarith only [bound y hy.1 (hy.2.trans hxb),mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr hy.2)])
  · exact Or.inr (fun y hy => by
      linarith only [bound y (hax.trans hy.1) hy.2,mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (sub_nonneg.mpr hy.1)])

/-- At a fourth-root observation the variation bound admits any length
z^(3/4+η) with η below both 1/4 and ε/2. -/
theorem short_intervals_with_margin {ε η : ℝ} (hε₁ : ε ≤ 1)
    (hη : 0 ≤ η) (hη₁ : η < 1/4) (hηε : 2*η < ε) :
    ∀ᶠ z : ℝ in atTop, G z ≤ z^(1/4:ℝ) →
      let H := z^((3:ℝ)/4+η)
      (∀ y ∈ Set.Icc (z-H) z, G y ≤ y^(1/2+ε)) ∨
      (∀ y ∈ Set.Icc z (z+H), G y ≤ y^(1/2+ε)) := by
  let r := (3:ℝ)/4+η
  let s := (1:ℝ)/2+ε
  let u := (ε-2*η)/2
  have hu : 0 < u := by dsimp [u]; linarith
  let t := (1:ℝ)/2+2*η+u
  let K := 1+24/u
  have hr₁ : 0 < 1-r := by dsimp [r]; linarith
  have hst : 0 < s-t := by dsimp [s,t,u]; linarith
  filter_upwards [eventually_ge_atTop (2:ℝ),
    (tendsto_rpow_atTop hr₁).eventually_ge_atTop 2,
    (tendsto_rpow_atTop hst).eventually_ge_atTop (4*K)] with z hz hz₁ hz₂
  intro hLow
  let H := z^r
  have hzpos : 0 < z := by linarith
  have hz1 : 1 ≤ z := by linarith
  have hH : 1 ≤ H := Real.one_le_rpow hz1 (by dsimp [r]; linarith)
  have hH0 := zero_lt_one.trans_le hH
  have hsmall : 2*H ≤ z := by
    have h := mul_le_mul_of_nonneg_right hz₁ hH0.le
    have he : z^(1-r)*H = z := by dsimp [H]; rw [← Real.rpow_add hzpos]; ring_nf; simp
    rwa [he] at h
  have ha : 1 ≤ z-H := by linarith
  have hb : z+H ≤ 2*z := by linarith
  have hL : Real.log (z+H) ≤ (2/u)*z^u := by
    have h₁ := Real.log_le_log (show 0 < z+H by linarith) hb
    rw [Real.log_mul (by norm_num) hzpos.ne'] at h₁
    have h₂ := Real.log_le_log (by norm_num : (0:ℝ) < 2) hz
    have h₃ := Real.log_le_rpow_div hzpos.le hu
    calc Real.log (z+H) ≤ 2*(z^u/u) := by linarith only [h₁,h₂,h₃]
         _ = _ := by ring
  have hfrac : ((z+H)-(z-H))/(z-H) ≤ 4*H/z := by
    rw [div_le_div_iff₀ (zero_lt_one.trans_le ha) hzpos]
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hH0.le]
  have hpoly : z^(u)*H*H/z = z^t := by
    dsimp [H]
    rw [div_eq_iff hzpos.ne',← Real.rpow_add hzpos,← Real.rpow_add hzpos]
    calc z^(u+r+r) = z^(t+1) := by dsimp [r,t]; congr 1; ring
         _ = z^t*z := by rw [Real.rpow_add hzpos,Real.rpow_one]
  have hmono : z^(1/4:ℝ) ≤ z^t := Real.rpow_le_rpow_of_exponent_le hz1 (by dsimp [t]; linarith)
  have hE : G z + ((z+H)-(z-H)+1)*Real.log (z+H)*(((z+H)-(z-H))/(z-H)) ≤ K*z^t := by
    have hprod := mul_le_mul
      (mul_le_mul (by linarith only [hH] : (z+H)-(z-H)+1 ≤ 3*H) hL
        (Real.log_nonneg (by linarith)) (by positivity)) hfrac
      (div_nonneg (by linarith) (by linarith)) (by positivity)
    have he : 3*H*((2/u)*z^(u))*(4*H/z) = (24/u)*z^t := by rw [← hpoly]; ring
    dsimp [K]
    linarith only [hprod,he,hLow,hmono]
  have htransfer (y : ℝ) (hy : z-H ≤ y) : K*z^t ≤ y^s := by
    have hy0 : 0 ≤ y := by linarith
    have h := Real.rpow_le_rpow hzpos.le (show z ≤ 2*y by linarith) (by dsimp [s]; linarith : 0 ≤ s)
    rw [Real.mul_rpow (by norm_num) hy0] at h
    have h₂ : (2:ℝ)^s ≤ 4 := by
      calc _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by dsimp [s]; linarith)
           _ = _ := by norm_num
    have h₃ := mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg hy0 s)
    have h₄ := mul_le_mul_of_nonneg_right hz₂ (Real.rpow_nonneg hzpos.le t)
    rw [← Real.rpow_add hzpos,sub_add_cancel] at h₄
    linarith only [h,h₃,h₄]
  rcases one_side_G_upper ha (show z-H ≤ z by linarith) (show z ≤ z+H by linarith) with h|h
  · exact Or.inl (fun y hy => ((h y hy).trans hE).trans (htransfer y hy.1))
  · exact Or.inr (fun y hy => ((h y hy).trans hE).trans (htransfer y (by linarith only [hy.1,hH0])))

/-- A convenient uniform choice of the short-interval exponent. -/
theorem short_intervals_of_low_points {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∀ᶠ z : ℝ in atTop, G z ≤ z^(1/4:ℝ) →
      let H := z^((3:ℝ)/4+ε/16)
      (∀ y ∈ Set.Icc (z-H) z, G y ≤ y^(1/2+ε)) ∨
      (∀ y ∈ Set.Icc z (z+H), G y ≤ y^(1/2+ε)) :=
  short_intervals_with_margin hε₁ (div_nonneg hε.le (by norm_num)) (by linarith) (by linarith)

private theorem fourth_block_at {z η : ℝ} (hz : 1 ≤ z) (K M₀ : ℕ)
    (hz₀ : (M₀:ℝ)+((K:ℝ)+1) ≤ z^(1/4:ℝ)) (hzη : 32*((K:ℝ)+1) ≤ z^η) :
    ∀ P : ℝ → Prop,
      ((∀ y ∈ Set.Icc (z-z^(3/4+η)) z, P y) ∨ (∀ y ∈ Set.Icc z (z+z^(3/4+η)), P y)) →
      ∃ M ≥ M₀, M ≤ ⌊z^(1/4:ℝ)⌋₊+1 ∧ ∀ n ∈ Icc M (M+K), P ((n:ℝ)^4) := by
  let v : ℝ := K+1
  intro P hP
  let a := z^(1/4:ℝ)
  let N := ⌊a⌋₊
  have hzpos := zero_lt_one.trans_le hz
  have ha : 0 ≤ a := Real.rpow_nonneg hzpos.le _
  have hN : (N:ℝ) ≤ a := Nat.floor_le ha
  have haN : a < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hNK : M₀+K ≤ N := Nat.le_floor (by push_cast; linarith only [hz₀])
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hva : v ≤ a := by linarith only [hz₀,Nat.cast_nonneg (α := ℝ) M₀]
  have he4 : a^4 = z := by
    dsimp [a]
    rw [← Real.rpow_natCast,← Real.rpow_mul hzpos.le]
    norm_num
  have he3 : a^3 = z^(3/4:ℝ) := by
    dsimp [a]
    rw [← Real.rpow_natCast,← Real.rpow_mul hzpos.le]
    norm_num
  have hwide : 32*v*a^3 ≤ z^(3/4+η) := by
    rw [Real.rpow_add hzpos,← he3,mul_comm (a^3)]
    exact mul_le_mul_of_nonneg_right hzη (pow_nonneg ha 3)
  have hdiff {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u ≤ 2*a) (hd : u-l ≤ v) :
      u^4-l^4 ≤ 32*v*a^3 := by
    have hB : u^3+u^2*l+u*l^2+l^3 ≤ 32*a^3 := by
      calc _ ≤ (2*a)^3+(2*a)^2*(2*a)+(2*a)*(2*a)^2+(2*a)^3 := by gcongr <;> linarith
           _ = _ := by ring
    calc _ = (u-l)*(u^3+u^2*l+u*l^2+l^3) := by ring
         _ ≤ v*(32*a^3) := mul_le_mul hd hB (by have := hl.trans hlu; positivity) hv
         _ = _ := by ring
  rcases hP with h|h
  · refine ⟨N-K,by omega,(Nat.sub_le N K).trans (Nat.le_succ _),?_⟩
    intro n hn
    obtain ⟨hnl,hnu⟩ := mem_Icc.mp hn
    have hnN : (n:ℝ) ≤ a := (Nat.cast_le.mpr (by omega : n ≤ N)).trans hN
    have hNn : (N:ℝ) ≤ n+K := by exact_mod_cast (by omega : N ≤ n+K)
    have hdist : a-(n:ℝ) ≤ v := by dsimp [v]; linarith
    have hbd := (hdiff (Nat.cast_nonneg n) hnN (by linarith : a ≤ 2*a) hdist).trans hwide
    rw [he4] at hbd
    exact h _ ⟨by linarith only [hbd],(pow_le_pow_left₀ (Nat.cast_nonneg n) hnN 4).trans_eq he4⟩
  · refine ⟨N+1,by omega,le_rfl,?_⟩
    intro n hn
    obtain ⟨hnl,hnu⟩ := mem_Icc.mp hn
    have han : a ≤ n := haN.le.trans (by exact_mod_cast hnl)
    have hdist : (n:ℝ)-a ≤ v := by
      have hnu' : (n:ℝ) ≤ (N:ℝ)+1+K := by exact_mod_cast hnu
      dsimp [v]
      linarith
    have hbd := (hdiff ha han (by linarith : (n:ℝ) ≤ 2*a) hdist).trans hwide
    rw [he4] at hbd
    exact h _ ⟨he4 ▸ pow_le_pow_left₀ ha han 4,by linarith only [hbd]⟩


/-- Either half of a sufficiently wide neighborhood of z contains K+1
consecutive fourth powers, starting beyond any prescribed index. -/
theorem fourth_blocks_of_one_side {η : ℝ} (hη : 0 < η) (K M₀ : ℕ) :
    ∀ᶠ z : ℝ in atTop, ∀ P : ℝ → Prop,
      ((∀ y ∈ Set.Icc (z-z^(3/4+η)) z, P y) ∨ (∀ y ∈ Set.Icc z (z+z^(3/4+η)), P y)) →
      ∃ M ≥ M₀, ∀ n ∈ Icc M (M+K), P ((n:ℝ)^4) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).eventually_ge_atTop ((M₀:ℝ)+(K+1)),
    (tendsto_rpow_atTop hη).eventually_ge_atTop (32*((K:ℝ)+1))] with z hz hz₀ hzη
  intro P hP
  obtain ⟨M,hM,_,h⟩ := fourth_block_at hz K M₀ hz₀ hzη P hP
  exact ⟨M,hM,h⟩

/-- In an interval of physical length z^(3/4+η) the number of consecutive
fourth-power samples can grow as a power of the starting index. -/
theorem polynomial_fourth_blocks_of_one_side {η β : ℝ} (hη₁ : η ≤ 1/4)
    (hβ : 0 ≤ β) (hβη : β < 4*η) (M₀ : ℕ) :
    ∀ᶠ z : ℝ in atTop, ∀ P : ℝ → Prop,
      ((∀ y ∈ Set.Icc (z-z^(3/4+η)) z, P y) ∨ (∀ y ∈ Set.Icc z (z+z^(3/4+η)), P y)) →
      ∃ M ≥ M₀, ∀ n ∈ Icc M (M+⌊(M:ℝ)^β⌋₊), P ((n:ℝ)^4) := by
  let u := (η+β/4)/2
  have hu : 0 < u := by dsimp [u]; linarith
  have h₁ : 0 < 1/4-u := by dsimp [u]; linarith
  have h₂ : 0 < η-u := by dsimp [u]; linarith
  have h₃ : 0 < u-β/4 := by dsimp [u]; linarith
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop h₁).eventually_ge_atTop ((M₀:ℝ)+2),
    (tendsto_rpow_atTop h₂).eventually_ge_atTop 64,
    (tendsto_rpow_atTop h₃).eventually_ge_atTop ((2:ℝ)^β)] with z hz hhi hwin hlo
  intro P hP
  let K := ⌊z^u⌋₊
  have hz0 := zero_lt_one.trans_le hz
  have hzu : 1 ≤ z^u := Real.one_le_rpow hz hu.le
  have hK : (K:ℝ) ≤ z^u := Nat.floor_le (by positivity)
  have hprod (v w : ℝ) : z^(v-w)*z^w = z^v := by rw [← Real.rpow_add hz0,sub_add_cancel]
  have hm := mul_le_mul_of_nonneg_right hhi (Real.rpow_nonneg hz0.le u)
  have hw := mul_le_mul_of_nonneg_right hwin (Real.rpow_nonneg hz0.le u)
  rw [hprod] at hm hw
  have hK₀ : (M₀:ℝ)+(K+1) ≤ z^(1/4:ℝ) := by
    nlinarith only [hm,hK,hzu,mul_le_mul_of_nonneg_left hzu (Nat.cast_nonneg (α := ℝ) M₀)]
  have hKη : 32*((K:ℝ)+1) ≤ z^η := by linarith only [hw,hzu,hK]
  obtain ⟨M,hM,hMq,h⟩ := fourth_block_at hz K M₀ hK₀ hKη P hP
  have hzq : 1 ≤ z^(1/4:ℝ) := Real.one_le_rpow hz (by norm_num)
  have hM' : (M:ℝ) ≤ 2*z^(1/4:ℝ) := by
    have h : (M:ℝ) ≤ ((⌊z^(1/4:ℝ)⌋₊+1:ℕ):ℝ) := Nat.cast_le.mpr hMq
    push_cast at h
    linarith only [h,hzq,Nat.floor_le (Real.rpow_nonneg hz0.le (1/4:ℝ))]
  have hpower : (M:ℝ)^β ≤ z^u := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg M) hM' hβ
    rw [Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_mul hz0.le,
      show (1/4:ℝ)*β = β/4 by ring] at h
    have he := mul_le_mul_of_nonneg_right hlo (Real.rpow_nonneg hz0.le (β/4))
    rw [hprod] at he
    exact h.trans he
  exact ⟨M,hM,fun n hn => h n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
    (mem_Icc.mp hn).2.trans (Nat.add_le_add_left (Nat.floor_mono hpower) M)⟩)⟩

end RiemannGaussian.AlpogeZetaSamples
