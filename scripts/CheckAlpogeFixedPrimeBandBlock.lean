import CheckAlpogeFixedPrimeBandCorner
import RiemannGaussian.MoebiusHarmonicCancellation

/-! # Cancellation of the Möbius form on a square of negative entries -/

noncomputable section
namespace RiemannGaussian.AlpogeMined
open Real Finset
open scoped ArithmeticFunction.Moebius

/-- The contribution from both indices in the same single-multiple interval. -/
def fixedBandMobiusBlock (t : ℕ) : ℝ :=
  ∑ a ∈ Ioc (20*t) (21*t), ∑ b ∈ Ioc (20*t) (21*t),
    ((μ a : ℝ)*(μ b : ℝ))*fixedBandProductEntry ((28*t)^2) a b

private def blockMoment (t : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Ioc (20*t) (21*t), (μ a : ℝ)*w a

private theorem block_factors (t : ℕ) :
    let u := fun a : ℕ => 28*(t:ℝ)/a
    let L := fun a : ℕ => log (u a)
    let M := blockMoment t
    fixedBandMobiusBlock t = (1-eulerMascheroniConstant)*(M u^2-M (fun _ => 1)^2)
      -2*(M u*M (fun a => u a*L a)-M (fun _ => 1)*M L) := by
  intro u L M
  let I := Ioc (20*t) (21*t)
  let p (f g : ℕ → ℝ) (a b : ℕ) := ((μ a : ℝ)*f a)*((μ b : ℝ)*g b)
  have hs (f g : ℕ → ℝ) : (∑ a ∈ I, ∑ b ∈ I, p f g a b) = M f*M g := by
    simp only [I,p,← mul_sum,← sum_mul,M,blockMoment]
  let one := fun _ : ℕ => (1:ℝ)
  let v := fun a => u a*L a
  have he (a : ℕ) (ha : a ∈ I) (b : ℕ) (hb : b ∈ I) :
      ((μ a : ℝ)*(μ b : ℝ))*fixedBandProductEntry ((28*t)^2) a b =
        (1-eulerMascheroniConstant)*(p u u a b-p one one a b)
          -(p u v a b+p v u a b-p one L a b-p L one a b) := by
    have ht : 0 < t := by by_contra! h; dsimp [I] at ha; simp [Nat.eq_zero_of_le_zero h] at ha
    have ha₀ : 0 < (a:ℝ) := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp ha).1)
    have hb₀ : 0 < (b:ℝ) := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp hb).1)
    have hy : (((28*t)^2:ℕ):ℝ)/(a*b) = u a*u b := by dsimp [u]; push_cast; ring
    rw [(fixedBand_block_entry ha hb).2.2,hy,log_mul (by dsimp [u]; positivity) (by dsimp [u]; positivity)]
    dsimp only [p,v,L,one]; ring
  unfold fixedBandMobiusBlock
  change (∑ a ∈ I, ∑ b ∈ I, _) = _
  rw [sum_congr rfl (fun a ha => sum_congr rfl (he a ha))]
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum,hs]
  dsimp only [one,v]; ring

/-- Abel summation bounds all four moments by the largest ordinary Möbius prefix
on the same interval. -/
private theorem prefix_weight {D M : ℕ} (hDM : D < M) {E : ℝ}
    (hp : ∀ j ∈ Icc D M, |moebiusFinitePrefix j| ≤ E) {w : ℕ → ℝ}
    (hw : ∀ j ∈ Icc (D+1) M, 0 ≤ w j)
    (ha : AntitoneOn w (Set.Icc (D+1) M)) :
    |∑ j ∈ Ioc D M, (μ j : ℝ)*w j| ≤ 2*E*w (D+1) := by
  have hr (j : ℕ) : (∑ a ∈ range (j+1), (μ a : ℝ)) = moebiusFinitePrefix j := by
    rw [sum_range_succ' (fun a : ℕ => (μ a : ℝ))]; simp [moebiusFinitePrefix]
  have he := sum_Ioc_by_parts w (fun a : ℕ => (μ a : ℝ)) hDM
  simp only [smul_eq_mul,hr] at he
  have hdiff (j : ℕ) (hj : j ∈ Ioc D (M-1)) : 0 ≤ w j-w (j+1) := by
    obtain ⟨hj₁,hj₂⟩ := mem_Ioc.mp hj
    exact sub_nonneg.mpr (ha ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ (by omega))
  have htel : (∑ j ∈ Ioc D (M-1), (w j-w (j+1))) = w (D+1)-w M := by
    rw [show Ioc D (M-1)=Ico (D+1) M by ext j; simp only [mem_Ioc,mem_Ico]; omega]
    have h := congrArg Neg.neg (sum_Ico_sub w (by omega : D+1 ≤ M))
    simpa only [← sum_neg_distrib,neg_sub] using h
  have hs : |∑ j ∈ Ioc D (M-1), (w (j+1)-w j)*moebiusFinitePrefix j| ≤ (w (D+1)-w M)*E := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [← htel,sum_mul]
    apply sum_le_sum
    intro j hj
    rw [abs_mul,abs_of_nonpos (by linarith only [hdiff j hj] : w (j+1)-w j ≤ 0),neg_sub]
    exact mul_le_mul_of_nonneg_left (hp j (by obtain ⟨_,_⟩ := mem_Ioc.mp hj; exact mem_Icc.mpr ⟨by omega,by omega⟩)) (hdiff j hj)
  have hend (j : ℕ) (hj : j ∈ Icc D M) {k : ℕ} (hk : k ∈ Icc (D+1) M) :
      |w k*moebiusFinitePrefix j| ≤ w k*E := by
    rw [abs_mul,abs_of_nonneg (hw k hk)]
    exact mul_le_mul_of_nonneg_left (hp j hj) (hw k hk)
  rw [sum_congr rfl (fun j _ => mul_comm _ (w j)),he]
  apply (abs_sub _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add
    (hend M (mem_Icc.mpr ⟨hDM.le,le_rfl⟩) (mem_Icc.mpr ⟨by omega,le_rfl⟩))
    (hend D (mem_Icc.mpr ⟨le_rfl,hDM.le⟩) (mem_Icc.mpr ⟨le_rfl,by omega⟩)))) hs).trans
  linarith

/-- The square of a local ordinary Möbius prefix bound controls the entire block. -/
theorem fixedBandMobiusBlock_prefix {t : ℕ} (ht : 0 < t) {E : ℝ}
    (hp : ∀ j ∈ Icc (20*t) (21*t), |moebiusFinitePrefix j| ≤ E) :
    |fixedBandMobiusBlock t| ≤ 96*E^2 := by
  let D := 20*t
  let T := 21*t
  let u := fun a : ℕ => 28*(t:ℝ)/a
  let L := fun a : ℕ => log (u a)
  let one := fun _ : ℕ => (1:ℝ)
  let M := blockMoment t
  have hDT : D < T := by dsimp [D,T]; omega
  have hE : 0 ≤ E := (abs_nonneg _).trans (hp D (mem_Icc.mpr ⟨le_rfl,hDT.le⟩))
  have hU (j : ℕ) (hj : j ∈ Set.Icc (D+1) T) : 1 ≤ u j ∧ u j ≤ 2 := by
    obtain ⟨hj₁,hj₂⟩ := hj
    have h₁ : 20*t < j := hj₁
    have h₂ : j ≤ 21*t := hj₂
    have hpos : 0 < (j:ℝ) := Nat.cast_pos.mpr (by omega)
    have hlow : 20*(t:ℝ) < j := by exact_mod_cast h₁
    have hhi : (j:ℝ) ≤ 21*t := by exact_mod_cast h₂
    exact ⟨(le_div_iff₀ hpos).mpr (by linarith), (div_le_iff₀ hpos).mpr (by linarith)⟩
  have hL (j : ℕ) (hj : j ∈ Set.Icc (D+1) T) : 0 ≤ L j ∧ L j ≤ 1 := by
    have h := hU j hj
    exact ⟨log_nonneg h.1,(log_le_sub_one_of_pos (by linarith : 0 < u j)).trans (by linarith)⟩
  have hu : AntitoneOn u (Set.Icc (D+1) T) := by
    intro i hi j _ hij
    exact div_le_div_of_nonneg_left (by positivity) (Nat.cast_pos.mpr (by have := hi.1; omega)) (by exact_mod_cast hij)
  have hl : AntitoneOn L (Set.Icc (D+1) T) := fun i hi j hj hij =>
    log_le_log (zero_lt_one.trans_le (hU j hj).1) (hu hi hj hij)
  have hmoment {w : ℕ → ℝ} (hw : ∀ j ∈ Set.Icc (D+1) T, 0 ≤ w j ∧ w j ≤ 2)
      (ha : AntitoneOn w (Set.Icc (D+1) T)) : |M w| ≤ 4*E := by
    have he := prefix_weight hDT hp (fun j hj => (hw j (mem_Icc.mp hj)).1) ha
    apply he.trans
    linarith only [mul_le_mul_of_nonneg_left (hw (D+1) ⟨le_rfl,by omega⟩).2 hE]
  have hm₀ : |M one| ≤ 4*E := hmoment (fun _ _ => ⟨by norm_num [one],by norm_num [one]⟩) (fun _ _ _ _ _ => le_rfl)
  have hm₁ := hmoment (fun j hj => ⟨zero_le_one.trans (hU j hj).1,(hU j hj).2⟩) hu
  have hm₂ := hmoment (fun j hj => ⟨(hL j hj).1,(hL j hj).2.trans (by norm_num : (1:ℝ) ≤ 2)⟩) hl
  have hm₃ : |M (fun j => u j*L j)| ≤ 4*E := by
    refine hmoment ?_ ?_
    · intro j hj
      exact ⟨mul_nonneg (zero_le_one.trans (hU j hj).1) (hL j hj).1,
        (mul_le_mul (hU j hj).2 (hL j hj).2 (hL j hj).1 (by norm_num)).trans_eq (by ring)⟩
    · intro i hi j hj hij
      exact mul_le_mul (hu hi hj hij) (hl hi hj hij) (hL j hj).1 (zero_le_one.trans (hU i hi).1)
  have hprod {a b : ℝ} (ha : |a| ≤ 4*E) (hb : |b| ≤ 4*E) : |a*b| ≤ (4*E)^2 := by
    rw [abs_mul,pow_two]; exact mul_le_mul ha hb (abs_nonneg _) (by positivity)
  have hγ : |1-eulerMascheroniConstant| ≤ 1 := abs_le.mpr
    ⟨by linarith only [eulerMascheroniConstant_lt_two_thirds],by linarith only [one_half_lt_eulerMascheroniConstant]⟩
  rw [block_factors]
  change |(1-eulerMascheroniConstant)*(M u^2-M one^2)-2*(M u*M (fun j => u j*L j)-M one*M L)| ≤ _
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_mul (2:ℝ),abs_of_pos (by norm_num : (0:ℝ)<2),pow_two,pow_two]
  have h₁ := (abs_sub _ _).trans (add_le_add (hprod hm₁ hm₁) (hprod hm₀ hm₀))
  have h₂ := (abs_sub _ _).trans (add_le_add (hprod hm₁ hm₃) (hprod hm₀ hm₂))
  linarith only [mul_le_mul hγ h₁ (abs_nonneg _) zero_le_one,h₂]

/-- The signed block is little-o of its area, unconditionally. -/
theorem fixedBandMobiusBlock_subquadratic {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, ∀ t ≥ T, |fixedBandMobiusBlock t| ≤ ε*(t:ℝ)^2 := by
  let e := sqrt (ε/96)/21
  have he : 0 < e := div_pos (sqrt_pos.mpr (by positivity)) (by norm_num)
  obtain ⟨A,hA⟩ := Metric.tendsto_atTop.mp moebiusFinitePrefix_div_tendsto_zero e he
  refine ⟨max 1 A,fun t ht => ?_⟩
  have ht₀ : 0 < t := (le_max_left 1 A).trans ht
  have hb := fixedBandMobiusBlock_prefix ht₀ (E := e*(21*t)) (fun j hj => by
    obtain ⟨hj₁,hj₂⟩ := mem_Icc.mp hj
    have hj₀ : 0 < (j:ℝ) := Nat.cast_pos.mpr (by omega)
    have hs := hA j (by have := (le_max_right 1 A).trans ht; omega)
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hj₀] at hs
    exact ((div_lt_iff₀ hj₀).mp hs).le.trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hj₂) he.le))
  apply hb.trans_eq
  dsimp only [e]
  have hr := sq_sqrt (by positivity : 0 ≤ ε/96)
  calc
    _ = 96*(sqrt (ε/96))^2*(t:ℝ)^2 := by ring
    _ = _ := by rw [hr]; ring

/-- The quantitative Möbius estimate gives an exponential saving beyond the
cubic logarithmic cutoff of the native finite-prefix theorem. -/
theorem fixedBandMobiusBlock_rate :
    ∃ H : ℝ, 22 ≤ H ∧ ∀ h ≥ H, ∀ t : ℕ,
      exp (2*moebiusFiniteContourCenter h) ≤ ((20*t:ℕ):ℝ) →
      |fixedBandMobiusBlock t| ≤ 96*(21*(moebiusFiniteCancellationConstant+1))^2*
        exp (-h)*(t:ℝ)^2 := by
  obtain ⟨H,hH,hm⟩ := exists_moebiusFinitePrefix_cubic_tail_bound
  refine ⟨H,hH,fun h hh t ht => ?_⟩
  have ht₀ : 0 < t := by by_contra! hz; simp only [Nat.eq_zero_of_le_zero hz,mul_zero,Nat.cast_zero] at ht; exact (exp_pos _).not_ge ht
  let c := moebiusFiniteCancellationConstant+1
  have hc : 0 ≤ c := by dsimp [c]; linarith only [moebiusFiniteCancellationConstant_pos]
  apply (fixedBandMobiusBlock_prefix ht₀ (E := c*exp (-h/2)*(21*t)) (fun j hj =>
    (hm h hh (20*t) ht j (mem_Icc.mp hj).1).trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast (mem_Icc.mp hj).2) (by positivity)))).trans_eq
  have he : exp (-h/2)*exp (-h/2) = exp (-h) := by rw [← exp_add]; congr 1; ring
  dsimp only [c]
  rw [← he]; ring


/-- Contribution of all pairs with a single multiple, at every square cutoff.
For a fixed positive row a the eligible columns are exactly U²/(2a) < b ≤ U. -/
def fixedBandSingleMultiple (U : ℕ) : ℝ :=
  ∑ a ∈ Ioc 0 U, (μ a : ℝ)*∑ b ∈ Ioc (U^2/(2*a)) U, (μ b : ℝ)*fixedBandProductEntry (U^2) a b

private theorem single_row {U a : ℕ} (ha : a ∈ Ioc 0 U) {E : ℝ} (hE : 0 ≤ E)
    (hp : ∀ j ∈ Icc (U/2) U, |moebiusFinitePrefix j| ≤ E) :
    |∑ b ∈ Ioc (U^2/(2*a)) U, (μ b : ℝ)*fixedBandProductEntry (U^2) a b| ≤ 4*E := by
  let D := U^2/(2*a)
  change |∑ b ∈ Ioc D U, _| ≤ _
  by_cases hd : D < U
  · obtain ⟨ha₀,haU⟩ := mem_Ioc.mp ha
    have h₂ : 0 < 2*a := by omega
    have hd₀ : U/2 ≤ D := by
      apply (Nat.le_div_iff_mul_le h₂).mpr
      calc
        U/2*(2*a) = (U/2*2)*a := by ring
        _ ≤ U*U := Nat.mul_le_mul (Nat.div_mul_le_self _ _) haU
        _ = _ := by ring
    let y (b : ℕ) := (((U^2:ℕ):ℝ)/a)/b
    let w (b : ℕ) := y b-1
    let v (b : ℕ) := w b*log (y b)
    have hentry (b : ℕ) (hb : b ∈ Set.Icc (D+1) U) :
        1 ≤ y b ∧ y b ≤ 2 ∧ fixedBandProductEntry (U^2) a b = w b*(1-eulerMascheroniConstant-log (y b)) := by
      have hb₀ : 0 < b := lt_of_le_of_lt (Nat.zero_le D) (Nat.lt_of_succ_le hb.1)
      have hab := Nat.mul_pos ha₀ hb₀
      have hlo : a*b ≤ U^2 := by simpa only [pow_two] using Nat.mul_le_mul haU hb.2
      have hhi : U^2 < 2*(a*b) := by
        have h := (Nat.div_lt_iff_lt_mul h₂).mp (show D < b from hb.1)
        nlinarith only [h]
      have hden : 0 < (a:ℝ)*b := by exact_mod_cast hab
      dsimp only [w,y]
      rw [div_div]
      exact ⟨(one_le_div hden).mpr (by exact_mod_cast hlo),
        (div_le_iff₀ hden).mpr (by exact_mod_cast hhi.le),fixedBandProductEntry_first hab hlo hhi⟩
    have hy : AntitoneOn y (Set.Icc (D+1) U) := by
      intro i hi j _ hij
      exact div_le_div_of_nonneg_left (by positivity) (Nat.cast_pos.mpr (by have := hi.1; omega)) (by exact_mod_cast hij)
    have hw : AntitoneOn w (Set.Icc (D+1) U) := fun _ hi _ hj hij => sub_le_sub_right (hy hi hj hij) _
    have hlog : AntitoneOn (fun j => log (y j)) (Set.Icc (D+1) U) := fun i hi j hj hij =>
      log_le_log (zero_lt_one.trans_le (hentry j hj).1) (hy hi hj hij)
    have hbound (b : ℕ) (hb : b ∈ Set.Icc (D+1) U) : 0 ≤ w b ∧ w b ≤ 1 ∧ 0 ≤ log (y b) ∧ log (y b) ≤ 1 := by
      obtain ⟨h₁,h₂,_⟩ := hentry b hb
      exact ⟨sub_nonneg.mpr h₁,by dsimp [w]; linarith,log_nonneg h₁,
        (log_le_sub_one_of_pos (zero_lt_one.trans_le h₁)).trans (by linarith)⟩
    let S (f : ℕ → ℝ) := ∑ b ∈ Ioc D U, (μ b : ℝ)*f b
    have hbnd {f : ℕ → ℝ} (hpos : ∀ j ∈ Set.Icc (D+1) U, 0 ≤ f j ∧ f j ≤ 1)
        (hanti : AntitoneOn f (Set.Icc (D+1) U)) : |S f| ≤ 2*E := by
      apply (prefix_weight hd (fun j hj => hp j (Icc_subset_Icc_left hd₀ hj))
        (fun j hj => (hpos j (mem_Icc.mp hj)).1) hanti).trans
      simpa using mul_le_mul_of_nonneg_left (hpos (D+1) ⟨le_rfl,hd⟩).2 (by positivity : 0 ≤ 2*E)
    have hw' := hbnd (fun j hj => ⟨(hbound j hj).1,(hbound j hj).2.1⟩) hw
    have hv' : |S v| ≤ 2*E := by
      refine hbnd ?_ ?_
      · intro j hj
        obtain ⟨h₁,h₂,h₃,h₄⟩ := hbound j hj
        exact ⟨mul_nonneg h₁ h₃,(mul_le_mul h₂ h₄ h₃ zero_le_one).trans_eq (one_mul _)⟩
      · intro i hi j hj hij
        exact mul_le_mul (hw hi hj hij) (hlog hi hj hij) (hbound j hj).2.2.1 (hbound i hi).1
    have hsplit : (∑ b ∈ Ioc D U, (μ b : ℝ)*fixedBandProductEntry (U^2) a b) =
        (1-eulerMascheroniConstant)*S w-S v := by
      dsimp only [S]
      rw [mul_sum,← sum_sub_distrib]
      apply sum_congr rfl
      intro j hj
      rw [(hentry j ⟨(mem_Ioc.mp hj).1,(mem_Ioc.mp hj).2⟩).2.2]
      dsimp [v]; ring
    rw [hsplit]
    have hγ : |1-eulerMascheroniConstant| ≤ 1 := abs_le.mpr
      ⟨by linarith only [eulerMascheroniConstant_lt_two_thirds],by linarith only [one_half_lt_eulerMascheroniConstant]⟩
    apply (abs_sub _ _).trans
    rw [abs_mul]
    linarith only [mul_le_mul hγ hw' (abs_nonneg _) zero_le_one,hv']
  · simp only [Ioc_eq_empty_of_le (by omega : U ≤ D),sum_empty,abs_zero]
    positivity

/-- All single-multiple pairs together cost at most four times the row count
times the largest ordinary Möbius prefix in the upper half. -/
theorem fixedBandSingleMultiple_prefix {U : ℕ} {E : ℝ} (hE : 0 ≤ E)
    (hp : ∀ j ∈ Icc (U/2) U, |moebiusFinitePrefix j| ≤ E) :
    |fixedBandSingleMultiple U| ≤ 4*U*E := by
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _a ∈ Ioc 0 U, 4*E := by
      apply sum_le_sum
      intro a ha
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (abs_real_moebius_le_one a) (single_row ha hE hp) (abs_nonneg _) zero_le_one
    _ = _ := by simp; ring

/-- Cancellation on the whole single-multiple region holds on every sufficiently
large scale, including all fourth-power samples. -/
theorem fixedBandSingleMultiple_subquadratic {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, ∀ U ≥ T, |fixedBandSingleMultiple U| ≤ ε*(U:ℝ)^2 := by
  obtain ⟨A,hA⟩ := Metric.tendsto_atTop.mp moebiusFinitePrefix_div_tendsto_zero (ε/4) (by positivity)
  refine ⟨2*(A+1),fun U hU => ?_⟩
  refine (fixedBandSingleMultiple_prefix (E := ε/4*U) (by positivity) (fun j hj => ?_)).trans_eq ?_
  · obtain ⟨hl,hu⟩ := mem_Icc.mp hj
    have hj₀ : 0 < (j:ℝ) := Nat.cast_pos.mpr (by omega)
    have hs := hA j (by omega)
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hj₀,div_lt_iff₀ hj₀] at hs
    exact hs.le.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hu) (by positivity))
  · ring

/-- The exponential saving applies to complete corners at all cofactor
transitions. Each of the two local Möbius sums contributes one saving. -/
theorem fixedBandCorner_rate :
    ∃ h₀ : ℝ, 22 ≤ h₀ ∧ ∀ h ≥ h₀, ∀ {D U H : ℕ}, D < U → U ≤ H*(D+1) →
      exp (2*moebiusFiniteContourCenter h) ≤ (D:ℝ) →
      |fixedBandCorner D U| ≤
        (2*log 2+6*(|fixedBandLogConstant|+log (H^2:ℕ)+2*log H))*
        (H:ℝ)^2*(1+log (H^2:ℕ))^2*(2*(moebiusFiniteCancellationConstant+1))^2*exp (-h)*(U:ℝ)^2 := by
  obtain ⟨A,hA,hm⟩ := exists_moebiusFinitePrefix_cubic_tail_bound
  refine ⟨A,hA,fun h hh D U H hDU hscale hD => ?_⟩
  let c := moebiusFiniteCancellationConstant+1
  have hc : 0 ≤ c := by dsimp [c]; linarith only [moebiusFiniteCancellationConstant_pos]
  have hpre {j : ℕ} (hj : D ≤ j) (hu : j ≤ U) : |moebiusFinitePrefix j| ≤ c*exp (-h/2)*U :=
    (hm h hh D hD j hj).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hu) (by positivity))
  have he := fixedBandCorner_local_prefix hDU hscale (E := 2*c*exp (-h/2)*U) (fun i hi => by
    have h₁ := (mem_Ioc.mp hi).1.le
    have he := moebiusFinitePrefix_sub_eq_sum h₁
    rw [← Ico_add_one_add_one_eq_Ioc]
    rw [← sum_Ico_add' (f := fun n : ℕ => (μ n : ℝ)) D i 1,← he]
    exact ((abs_sub _ _).trans (add_le_add (hpre h₁ (mem_Ioc.mp hi).2) (hpre le_rfl hDU.le))).trans_eq (by ring))
  apply he.trans_eq
  have hexp : exp (-h/2)*exp (-h/2)=exp (-h) := by rw [← exp_add]; congr 1; ring
  rw [← hexp]; dsimp only [c]; ring

end RiemannGaussian.AlpogeMined
end

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBandMobiusBlock_prefix,
      ``RiemannGaussian.AlpogeMined.fixedBandMobiusBlock_subquadratic,
      ``RiemannGaussian.AlpogeMined.fixedBandMobiusBlock_rate,
      ``RiemannGaussian.AlpogeMined.fixedBandSingleMultiple_subquadratic,
      ``RiemannGaussian.AlpogeMined.fixedBandCorner_rate] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
