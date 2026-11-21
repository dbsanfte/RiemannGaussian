import CheckAlpogeLocalPrimeWindow
import RiemannGaussian.PrimeMassFromZeroBound

/-! # A signed average of unsmoothed prime counts on long intervals -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real MeasureTheory Filter

private def rising (u : ℝ) (a d : ℕ) : ℝ := u*(((d:ℝ)-a)/d)
private def falling (v : ℝ) (b d : ℕ) : ℝ := v*(((b:ℝ)-d)/d)

private theorem rising_mono {u : ℝ} (hu : 0 ≤ u) (a : ℕ) {d e : ℕ} (hd : 0 < d) (h : d ≤ e) :
    rising u a d ≤ rising u a e := by
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have heR : (0:ℝ) < e := Nat.cast_pos.mpr (hd.trans_le h)
  have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) a) hdR (Nat.cast_le.mpr h)
  unfold rising
  rw [sub_div,sub_div,div_self hdR.ne',div_self heR.ne']
  exact mul_le_mul_of_nonneg_left (by linarith) hu

private theorem falling_anti {v : ℝ} (hv : 0 ≤ v) (b : ℕ) {d e : ℕ} (hd : 0 < d) (h : d ≤ e) :
    falling v b e ≤ falling v b d := by
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have heR : (0:ℝ) < e := Nat.cast_pos.mpr (hd.trans_le h)
  have hh := div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) b) hdR (Nat.cast_le.mpr h)
  unfold falling
  rw [sub_div,sub_div,div_self hdR.ne',div_self heR.ne']
  exact mul_le_mul_of_nonneg_left (by linarith) hv

private theorem peak_right (a N b : ℕ) :
    chordWeight a N b N = falling (((N:ℝ)-a)/(b-a)) b N := by
  simp [chordWeight,falling]
  ring

private theorem chordWeight_peak {a N b d : ℕ} (ha : a ≤ N) (hb : N ≤ b) (hab : a < b)
    (hN : 0 < N) (hd : 0 < d) : chordWeight a N b d ≤ chordWeight a N b N := by
  by_cases hx : d ≤ N
  · simp only [chordWeight,ite_eq_left hx,ite_eq_left (le_refl N)]
    exact rising_mono (div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hb))
      (sub_nonneg.mpr (Nat.cast_le.mpr hab.le))) a hd hx
  · rw [peak_right,chordWeight,ite_eq_right hx]
    exact falling_anti (div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr ha))
      (sub_nonneg.mpr (Nat.cast_le.mpr hab.le))) b hN (le_of_not_ge hx)

/-- Below the center the threshold is y. Above the center it is the peak
minus y. Both choices integrate to the original weight of each denominator. -/
def primeLevelInterval (a N b : ℕ) (y : ℝ) : Finset ℕ :=
  (Ioc a b).filter fun d =>
    (if d ≤ N then y else chordWeight a N b N-y) ≤ chordWeight a N b d

private theorem half_level_left {a N b d : ℕ} (hN : 0 < N) (ha : 4*a ≤ N) (hb : N ≤ b)
    (hd : N-N/2 ≤ d) (hdN : d ≤ N) :
    chordWeight a N b N/2 ≤ chordWeight a N b d := by
  let u := ((b:ℝ)-N)/(b-a)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hb))
    (sub_nonneg.mpr (Nat.cast_le.mpr (by omega : a ≤ b)))
  have hd0 : (0:ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hn0 : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have had : 2*(a:ℝ) ≤ d := by exact_mod_cast (show 2*a ≤ d by omega)
  have h1 : ((N:ℝ)-a)/N ≤ 1 := (div_le_one hn0).mpr (sub_le_self _ (Nat.cast_nonneg a))
  have h2 : 1/2 ≤ ((d:ℝ)-a)/d := (le_div_iff₀ hd0).mpr (by linarith)
  simp only [chordWeight,ite_eq_left hdN,ite_eq_left (le_refl N)]
  change u*_/2 ≤ u*_
  linarith only [mul_le_mul_of_nonneg_left h1 hu,mul_le_mul_of_nonneg_left h2 hu]

private theorem half_level_right {a N b d : ℕ} (hN : 0 < N) (ha : a ≤ N) (hb : 4*N ≤ b)
    (hd : N < d) (hdN : d ≤ N+N/2) :
    chordWeight a N b N/2 ≤ chordWeight a N b d := by
  let v := ((N:ℝ)-a)/(b-a)
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr ha))
    (sub_nonneg.mpr (Nat.cast_le.mpr (by omega : a ≤ b)))
  have hd0 : (0:ℝ) < d := Nat.cast_pos.mpr (hN.trans hd)
  have hn0 : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hbR : 3*(N:ℝ) ≤ b := by exact_mod_cast (show 3*N ≤ b by omega)
  have hdR : 2*(d:ℝ) ≤ 3*N := by exact_mod_cast (show 2*d ≤ 3*N by omega)
  have hratio : ((b:ℝ)-N)/N ≤ 2*(((b:ℝ)-d)/d) := by
    rw [← mul_div_assoc,div_le_div_iff₀ hn0 hd0]
    nlinarith only [mul_le_mul_of_nonneg_right hbR (by linarith : 0 ≤ 2*(N:ℝ)-d),
      mul_le_mul_of_nonneg_left hdR hn0.le]
  rw [peak_right,chordWeight,ite_eq_right (not_le.mpr hd)]
  change v*_/2 ≤ v*_
  linarith only [mul_le_mul_of_nonneg_left hratio hv]

/-- Each level is one ordinary integer interval crossing N. The opposite
thresholds ensure its cardinality exceeds floor(N/2), for every level. -/
theorem primeLevelInterval_long {a N b : ℕ} (hN : 0 < N) (ha : 4*a ≤ N) (hb : 4*N ≤ b)
    {y : ℝ} (_hy : 0 ≤ y) (hpeak : y ≤ chordWeight a N b N) :
    ∃ i j : ℕ, a ≤ i ∧ i < N ∧ N ≤ j ∧ j ≤ b ∧ N/2 < j-i ∧ primeLevelInterval a N b y = Ioc i j := by
  let S := primeLevelInterval a N b y
  have hmem : N ∈ S := mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,by simpa only [ite_eq_left (le_refl N)]⟩
  let l := S.min' ⟨N,hmem⟩
  let r := S.max' ⟨N,hmem⟩
  have hl : l ∈ S := min'_mem _ _
  have hr : r ∈ S := max'_mem _ _
  have hla := (mem_Ioc.mp (mem_filter.mp hl).1).1
  have hrb := (mem_Ioc.mp (mem_filter.mp hr).1).2
  have hln : l ≤ N := min'_le _ _ hmem
  have hnr : N ≤ r := le_max' _ _ hmem
  have lpos : 0 < l := by omega
  have hu : 0 ≤ ((b:ℝ)-N)/(b-a) := div_nonneg (sub_nonneg.mpr (by exact_mod_cast (show N ≤ b by omega)))
    (sub_nonneg.mpr (by exact_mod_cast (show a ≤ b by omega)))
  have hv : 0 ≤ ((N:ℝ)-a)/(b-a) := div_nonneg (sub_nonneg.mpr (by exact_mod_cast (show a ≤ N by omega)))
    (sub_nonneg.mpr (by exact_mod_cast (show a ≤ b by omega)))
  have hset : S = Ioc (l-1) r := by
    ext d
    constructor
    · intro hd
      have hl' : l ≤ d := min'_le _ _ hd
      exact mem_Ioc.mpr ⟨by omega,le_max' _ _ hd⟩
    · intro hd
      obtain ⟨hld,hdr⟩ := mem_Ioc.mp hd
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,?_⟩
      by_cases hdN : d ≤ N
      · have h := (mem_filter.mp hl).2
        simp only [ite_eq_left hln,chordWeight] at h
        simp only [ite_eq_left hdN,chordWeight] at h ⊢
        exact h.trans (rising_mono hu a lpos (by omega))
      · have hNr : ¬ r ≤ N := by omega
        have h := (mem_filter.mp hr).2
        simp only [ite_eq_right hNr] at h
        simp only [ite_eq_right hdN]
        apply h.trans
        rw [chordWeight,ite_eq_right hNr,chordWeight,ite_eq_right hdN]
        exact falling_anti hv b (by omega) hdr
  refine ⟨l-1,r,by omega,by omega,hnr,hrb,?_,hset⟩
  by_cases hlow : y ≤ chordWeight a N b N/2
  · have hh : N-N/2 ∈ S := mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,by
      rw [ite_eq_left (Nat.sub_le N (N/2))]
      exact hlow.trans (half_level_left hN ha (by omega) le_rfl (Nat.sub_le _ _))⟩
    have h : l ≤ N-N/2 := min'_le _ _ hh
    omega
  · by_cases hzero : N/2=0
    · omega
    have hlt : N < N+N/2 := by omega
    have hh : N+N/2 ∈ S := mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,by
      rw [ite_eq_right (not_le.mpr hlt)]
      exact (by linarith : chordWeight a N b N-y ≤ chordWeight a N b N/2).trans
        (half_level_right hN (by omega) hb hlt le_rfl)⟩
    have h : N+N/2 ≤ r := le_max' _ _ hh
    omega

private def levelAtom (a N b d : ℕ) (c : ℝ) (y : ℝ) : ℝ :=
  if (if d ≤ N then y else chordWeight a N b N-y) ≤ chordWeight a N b d then c else 0

private theorem levelAtom_integral {a N b d : ℕ} (hN : 0 < N) (ha : a ≤ N) (hb : N ≤ b)
    (hab : a < b) (hd : d ∈ Ioc a b) (c : ℝ) :
    let P := chordWeight a N b N
    IntervalIntegrable (levelAtom a N b d c) volume 0 P ∧
    (∫ y in 0..P, levelAtom a N b d c y) = c*chordWeight a N b d := by
  let P := chordWeight a N b N
  let z := chordWeight a N b d
  let f := (Set.Iic z).indicator (fun _ => c)
  have hz : z ∈ Set.Icc 0 P := ⟨(chordWeight_bounds ha hb hab hd).1,
    chordWeight_peak ha hb hab hN (by have := (mem_Ioc.mp hd).1; omega)⟩
  have hf : IntervalIntegrable f volume 0 P :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (hz.1.trans hz.2)).mpr
      ((integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by finiteness)).indicator measurableSet_Iic)
  have hi : (∫ y in 0..P, f y) = c*z := by
    have h := intervalIntegral.integral_indicator (μ := volume) (f := fun _ => c) hz
    rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] at h
    exact h
  by_cases hdN : d ≤ N
  · have he : levelAtom a N b d c = f := by funext y; simp [levelAtom,f,z,hdN,Set.indicator]
    exact ⟨he ▸ hf,he ▸ hi⟩
  · have he : levelAtom a N b d c = fun y => f (P-y) := by
      funext y; simp [levelAtom,f,z,P,hdN,Set.indicator]
    rw [he]
    exact ⟨by simpa only [sub_self,sub_zero] using (hf.comp_sub_left P).symm,by
      rw [intervalIntegral.integral_comp_sub_left,sub_self,sub_zero]; exact hi⟩

private theorem level_sum (a N b : ℕ) (c : ℕ → ℝ) (y : ℝ) :
    (∑ d ∈ primeLevelInterval a N b y, c d) = ∑ d ∈ Ioc a b, levelAtom a N b d (c d) y := by
  simp [primeLevelInterval,sum_filter,levelAtom]

/-- Opposite thresholds give the exact signed integral of ordinary interval sums
for any coefficient, including the constant and the prime log weight. -/
theorem chordWeight_level_integral {a N b : ℕ} (hN : 0 < N) (ha : a ≤ N) (hb : N ≤ b)
    (hab : a < b) (c : ℕ → ℝ) :
    let P := chordWeight a N b N
    IntervalIntegrable (fun y => ∑ d ∈ primeLevelInterval a N b y, c d) volume 0 P ∧
    (∫ y in 0..P, ∑ d ∈ primeLevelInterval a N b y, c d) = ∑ d ∈ Ioc a b, c d*chordWeight a N b d := by
  simp_rw [level_sum]
  have hint := fun (d : ℕ) (hd : d ∈ Ioc a b) => (levelAtom_integral hN ha hb hab hd (c d)).1
  constructor
  · simpa only [← Finset.sum_apply] using IntervalIntegrable.sum (Ioc a b) hint
  · rw [intervalIntegral.integral_finsetSum hint]
    exact sum_congr rfl fun d hd => (levelAtom_integral hN ha hb hab hd (c d)).2

/-- The signed ordinary-prime error for unweighted integers i < d ≤ j. -/
def primeIntervalDeficit (i j : ℕ) : ℝ :=
  ((j:ℝ)-i)-(Chebyshev.theta j-Chebyshev.theta i)

theorem primeIntervalDeficit_eq {i j : ℕ} (hij : i ≤ j) :
    ∑ d ∈ Ioc i j, (1-(if d.Prime then log d else 0)) = primeIntervalDeficit i j := by
  let p (d : ℕ) := if d.Prime then log d else 0
  have h (n : ℕ) : (∑ d ∈ Ioc 0 n, p d) = Chebyshev.theta n := by
    simp [Chebyshev.theta,p,sum_filter]
  have hs := sum_Ioc_consecutive p (Nat.zero_le i) hij
  rw [h,h] at hs
  simp only [sum_sub_distrib,sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one,Nat.cast_sub hij]
  unfold primeIntervalDeficit
  dsimp only [p] at hs
  linarith only [hs]

/-- A positive local shortfall of height greater than D forces an unweighted
prime shortfall greater than D on an interval containing N and longer than N/2. -/
theorem long_prime_deficit_of_chord {a N b : ℕ} (hN : 0 < N) (ha : 4*a ≤ N) (hb : 4*N ≤ b)
    {D : ℝ} (hD : 0 ≤ D) (hbad : D < chordPrimeDeficit a N b) :
    ∃ i j : ℕ, a ≤ i ∧ i < N ∧ N ≤ j ∧ j ≤ b ∧ N/2 < j-i ∧ D < primeIntervalDeficit i j := by
  by_contra! hn
  let P := chordWeight a N b N
  let c (d : ℕ) : ℝ := 1-(if d.Prime then log d else 0)
  have hpeak := chordWeight_bounds (a := a) (N := N) (b := b) (d := N) (by omega) (by omega)
    (by omega) (mem_Ioc.mpr ⟨by omega,by omega⟩)
  have hhi : P ≤ 1 := hpeak.2.trans (min_le_left _ _)
  have hh := chordWeight_level_integral (a := a) (b := b) hN (by omega) (by omega) (by omega) c
  have hpoint (y : ℝ) (hy : y ∈ Set.Icc 0 P) : (∑ d ∈ primeLevelInterval a N b y, c d) ≤ D := by
    obtain ⟨i,j,hai,hi,hj,hjb,hlen,he⟩ := primeLevelInterval_long hN ha hb hy.1 hy.2
    rw [he]
    exact (primeIntervalDeficit_eq (hi.le.trans hj)).le.trans (hn _ _ hai hi hj hjb hlen)
  have hu := intervalIntegral.integral_mono_on hpeak.1 hh.1 intervalIntegrable_const hpoint
  rw [hh.2,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hu
  exact hbad.not_ge (hu.trans (mul_le_of_le_one_left hD hhi))

/-- An error bound in terms of the length of each long interval transfers at
the same exponent to the central sample, independently of the endpoints. -/
theorem chordPrimeDeficit_le_length_power {a N b : ℕ} (hN : 0 < N)
    (ha : 4*a ≤ N) (hb : 4*N ≤ b) {p K : ℝ} (hp : 0 ≤ p) (hp₁ : p < 1) (hK : 0 ≤ K)
    (h : ∀ i j : ℕ, a ≤ i → i < N → N ≤ j → j ≤ b → N/2 < j-i →
      primeIntervalDeficit i j ≤ K*((j:ℝ)-i)^p) :
    chordPrimeDeficit a N b ≤ K*(N:ℝ)^p/(1-p) := by
  let P := chordWeight a N b N
  let c (d : ℕ) : ℝ := 1-(if d.Prime then log d else 0)
  have hpeak := chordWeight_bounds (a := a) (N := N) (b := b) (d := N) (by omega) (by omega)
    (by omega) (mem_Ioc.mpr ⟨by omega,by omega⟩)
  have hP : 0 ≤ P := hpeak.1
  have hP₁ : P ≤ 1 := hpeak.2.trans (min_le_left _ _)
  have hh := chordWeight_level_integral (a := a) (b := b) hN (by omega) (by omega) (by omega) c
  let f (y : ℝ) := y^(-p)
  have hf : IntervalIntegrable f volume 0 P := intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hrev : IntervalIntegrable (fun y => f (P-y)) volume 0 P := by
    simpa only [sub_self,sub_zero] using (hf.comp_sub_left P).symm
  have hpoint (y : ℝ) (hy : y ∈ Set.Ioo 0 P) :
      (∑ d ∈ primeLevelInterval a N b y, c d) ≤ (K*(N:ℝ)^p)*f (P-y) := by
    have hy0 := sub_pos.mpr hy.2
    obtain ⟨i,j,hai,hi,hj,hjb,hlen,he⟩ := primeLevelInterval_long hN ha hb hy.1.le hy.2.le
    have hJ : j ∈ primeLevelInterval a N b y := he ▸ mem_Ioc.mpr ⟨hi.trans_le hj,le_rfl⟩
    have hJ0 : (0:ℝ) < j := Nat.cast_pos.mpr (hN.trans_le hj)
    have hsize : (j:ℝ) ≤ (N:ℝ)/(P-y) := by
      apply (le_div_iff₀ hy0).mpr
      rcases eq_or_lt_of_le hj with heq | hlt
      · rw [← heq]
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) (by linarith only [hy.1,hP₁])
      · have hw := (mem_filter.mp hJ).2
        rw [ite_eq_right (not_le.mpr hlt)] at hw
        have hupper := (chordWeight_bounds (a := a) (N := N) (b := b) (by omega) (by omega)
          (by omega) (mem_filter.mp hJ).1).2.trans (min_le_right _ _)
        have hmul := (le_div_iff₀ hJ0).mp (hw.trans hupper)
        simpa only [mul_comm] using hmul
    rw [he]
    apply (primeIntervalDeficit_eq (hi.le.trans hj)).le.trans
    apply (h i j hai hi hj hjb hlen).trans
    have hpow := rpow_le_rpow (sub_nonneg.mpr (Nat.cast_le.mpr (hi.le.trans hj)))
      ((sub_le_self (j:ℝ) (Nat.cast_nonneg i)).trans hsize) hp
    dsimp only [f]
    rw [Real.div_rpow (Nat.cast_nonneg _) hy0.le] at hpow
    rw [Real.rpow_neg hy0.le]
    exact (mul_le_mul_of_nonneg_left hpow hK).trans_eq (by ring)
  have hu := intervalIntegral.integral_mono_on_of_le_Ioo hP hh.1
    (hrev.const_mul (K*(N:ℝ)^p)) hpoint
  rw [hh.2,intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_left,
    sub_self,sub_zero] at hu
  have hint : (∫ y in 0..P, f y) ≤ 1/(1-p) := by
    dsimp only [f]
    rw [integral_rpow (Or.inl (by linarith)),zero_rpow (by linarith : -p+1 ≠ 0),sub_zero,
      show -p+1=1-p by ring]
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact Real.rpow_le_one hP hP₁ (by linarith)
  exact hu.trans ((mul_le_mul_of_nonneg_left hint (by positivity)).trans_eq (by ring))

/-- On a power window, test the logarithmic ordinary-prime mass of each
macroscopic interval in the buffers that crosses a sampled fourth power. -/
def longIntervalWindowBound (η K : ℝ) (m t : ℕ) : Prop :=
  ∀ n ∈ Icc m t, ∀ i j : ℕ, ⌊((m:ℝ)^4/4)^(1/(1+η))⌋₊ ≤ i → i < n^4 → n^4 ≤ j →
    j ≤ ⌈(4*(t:ℝ)^4)^(1+η)⌉₊ → n^4/2 < j-i →
      primeIntervalDeficit i j ≤ K*sqrt ((j:ℝ)-i)*(1+log ((j:ℝ)-i))^2

/-- A single fixed relative window width and one ordinary-prime lower bound
on arbitrarily late windows suffice for RH. -/
theorem rh_of_longIntervalWindowBound {η δ K : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hK : 0 ≤ K)
    (h : ∀ A : ℕ, ∃ m ≥ A, longIntervalWindowBound η K m (powerWindowEnd δ m)) :
    RiemannHypothesis := by
  apply rh_of_chordPrimeExcessOn_powerWindows (C := 512*K) hη (by positivity)
  intro α _
  refine ⟨δ,hδ,hδ₁,fun A => ?_⟩
  obtain ⟨m,hm,hh⟩ := h (max 2 A)
  let t := powerWindowEnd δ m
  obtain ⟨hmt,ht⟩ := powerWindowEnd_bounds (by omega : 1 ≤ m) hδ.le hδ₁
  change t ≤ m^2 at ht
  change m ≤ t at hmt
  have ht1 : 1 ≤ (t:ℝ) := by exact_mod_cast (show 1 ≤ t by omega)
  refine ⟨m,by omega,fun a b h₁ h₂ h₃ h₄ => ?_⟩
  change 4*t^4 ≤ b at h₃
  change b ≤ ⌈(4*(t:ℝ)^4)^(1+η)⌉₊ at h₄
  have hb₀ : b ≤ (4*t^4)^2 := by
    apply h₄.trans (Nat.ceil_le.mpr _)
    push_cast
    rw [← Real.rpow_natCast (4*(t:ℝ)^4) 2]
    apply rpow_le_rpow_of_exponent_le _ (by norm_num; linarith)
    linarith only [one_le_pow₀ ht1 (n := 4)]
  have zero_mass : chordPrimeExcessOn (512*K) a b m t = 0 := by
    apply sum_eq_zero
    intro n hn
    obtain ⟨hmn,hnt⟩ := mem_Icc.mp hn
    have hn1 : 1 ≤ n := by omega
    have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn1
    have hn4 := Nat.pow_le_pow_left hmn 4
    have ht4 := Nat.pow_le_pow_left hnt 4
    have hb : (b:ℝ) ≤ 16*(n:ℝ)^16 := by
      have ht' := ht.trans (Nat.pow_le_pow_left hmn 2)
      have htR : (t:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast ht'
      have hs := pow_le_pow_left₀ (Nat.cast_nonneg t) htR 8
      have hb' : (b:ℝ) ≤ ((4*t^4)^2:ℕ) := Nat.cast_le.mpr hb₀
      push_cast at hb'
      nlinarith only [hs,hb']
    have hlog : 1+log b ≤ 16*(1+log n) := by
      have hlog := log_le_log (Nat.cast_pos.mpr (show 0 < b by
        have := Nat.one_le_pow 4 t (by omega); omega)) hb
      rw [log_mul (by norm_num) (by positivity),log_pow,Nat.cast_ofNat] at hlog
      linarith only [hlog,log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 16)]
    let B := K*(1+log b)^2
    have hlen (i j : ℕ) (hai : a ≤ i) (hi : i < n^4) (hj : n^4 ≤ j) (hjb : j ≤ b)
        (hl : n^4/2 < j-i) : primeIntervalDeficit i j ≤ B*((j:ℝ)-i)^(1/2:ℝ) := by
      have H := hh n hn i j (h₁.trans hai) hi hj (hjb.trans h₄) hl
      have hL : 1 ≤ (j:ℝ)-i := by
        have hij : (i:ℝ)+1 ≤ j := by exact_mod_cast (show i+1 ≤ j by omega)
        linarith
      have hu : (j:ℝ)-i ≤ b := by linarith only [(Nat.cast_le.mpr hjb : (j:ℝ) ≤ b),Nat.cast_nonneg (α := ℝ) i]
      have hsq := pow_le_pow_left₀ (by linarith only [log_nonneg hL] : 0 ≤ 1+log ((j:ℝ)-i))
        (add_le_add_right (log_le_log (zero_lt_one.trans_le hL) hu) 1) 2
      rw [← sqrt_eq_rpow]
      exact H.trans ((mul_le_mul_of_nonneg_left hsq (by positivity)).trans_eq (by dsimp [B]; ring))
    have hc := chordPrimeDeficit_le_length_power (N := n^4) (Nat.one_le_pow 4 n hn1)
      (h₂.trans hn4) ((Nat.mul_le_mul_left 4 ht4).trans h₃) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num) (by dsimp only [B]; positivity) hlen
    rw [← sqrt_eq_rpow,Nat.cast_pow,show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,sqrt_sq (sq_nonneg _)] at hc
    dsimp only [B] at hc
    have hsq := pow_le_pow_left₀ (by positivity [log_natCast_nonneg b] : 0 ≤ 1+log b) hlog 2
    have hupper : chordPrimeDeficit a (n^4) b ≤ 512*K*(n:ℝ)^2*(1+log n)^2 := by
      apply hc.trans
      calc
        _ = 2*(K*(n:ℝ)^2)*(1+log b)^2 := by ring
        _ ≤ 2*(K*(n:ℝ)^2)*(16*(1+log n))^2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = _ := by ring
    rw [max_eq_right (sub_nonpos.mpr hupper),zero_div]
  exact zero_mass.le.trans (by positivity)

/-- A zero half-plane controls the *length* error on any long interval crossing
the center. The constant is uniform in the center and in both endpoints. -/
theorem long_prime_interval_error_of_zero_bound {B : ℝ} (hB : 1/2 ≤ B) (hB₁ : B ≤ 1)
    (hz : ∀ ρ : NontrivialZetaZero, ρ.1.re ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {i N j : ℕ}, 4 ≤ i → i < N → N ≤ j → N/2 < j-i →
      |primeIntervalDeficit i j| ≤ K*((j:ℝ)-i)^B*(1+log ((j:ℝ)-i))^2 := by
  obtain ⟨C,hC,h⟩ := PrimeMassFromZeroBound.theta_error hB hB₁ hz
  refine ⟨216*C,by positivity,fun {i N j} hi hiN hNj hlen => ?_⟩
  let L : ℝ := j-i
  have hL : 1 ≤ L := by
    have ht : (i:ℝ)+1 ≤ j := by exact_mod_cast (show i+1 ≤ j by omega)
    dsimp [L]; linarith
  have hjL : (j:ℝ) ≤ 3*L := by
    have ht : j ≤ 3*(j-i) := by omega
    simpa only [L,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (hiN.le.trans hNj)] using
      (Nat.cast_le.mpr ht : (j:ℝ) ≤ ((3*(j-i):ℕ):ℝ))
  have hend (k : ℕ) (hk : 4 ≤ k) (hkj : k ≤ j) :
      |Chebyshev.theta k-k| ≤ 108*C*L^B*(1+log L)^2 := by
    have hk4 : (4:ℝ) ≤ k := by exact_mod_cast hk
    have hk1 : (1:ℝ) ≤ k := by linarith
    have hk0 := zero_lt_one.trans_le hk1
    have hsize := (Nat.cast_le.mpr hkj : (k:ℝ) ≤ j).trans hjL
    have hpow : (k:ℝ)^B ≤ 3*L^B := calc
      _ ≤ (3*L)^B := rpow_le_rpow hk0.le hsize (by linarith)
      _ = (3:ℝ)^B * L^B := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hB₁).trans_eq (rpow_one _)) (by positivity)
    have hlog := log_le_log hk0 hsize
    rw [log_mul (by norm_num) (by linarith : L ≠ 0)] at hlog
    have hlogk := log_nonneg hk1
    have hlogL := log_nonneg hL
    have htwo : (1/2:ℝ) ≤ log 2 := by linarith only [Real.log_two_gt_d9]
    have hd : log k/log 2 ≤ 2*log k := (div_le_iff₀ (by linarith : 0 < log 2)).mpr
      (by nlinarith only [mul_le_mul_of_nonneg_right htwo hlogk])
    have hlog' : 1+log k/log 2 ≤ 6*(1+log L) := by
      linarith only [hd,hlog,hlogL,log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)]
    have hs := pow_le_pow_left₀ (by positivity [Real.log_two_gt_d9] : 0 ≤ 1+log k/log 2) hlog' 2
    apply (h k hk4).trans
    exact (mul_le_mul_of_nonneg_left (mul_le_mul hpow hs (sq_nonneg _) (by positivity)) hC).trans_eq (by ring)
  have hx := hend i hi (hiN.le.trans hNj)
  have hy := hend j (hi.trans (hiN.le.trans hNj)) le_rfl
  have he : primeIntervalDeficit i j = (Chebyshev.theta i-i)-(Chebyshev.theta j-j) := by
    unfold primeIntervalDeficit; ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hx hy).trans_eq (by dsimp only [L]; ring))

/-- The current unconditional zero bound gives a two-sided interval error with exponent 7/8. -/
theorem long_prime_interval_seven_eighths :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {i N j : ℕ}, 4 ≤ i → i < N → N ≤ j → N/2 < j-i →
      |primeIntervalDeficit i j| ≤ K*((j:ℝ)-i)^(7/8:ℝ)*(1+log ((j:ℝ)-i))^2 :=
  long_prime_interval_error_of_zero_bound (by norm_num) (by norm_num) suzukiLocalZero_re_le_seven_eighths

/-- For each fixed buffer exponent and fixed window width, the cofinal one-sided
ordinary-prime condition is exactly equivalent to Mathlib's RH. -/
theorem rh_iff_long_prime_intervals {η δ : ℝ} (hη : 0 < η) (hη₁ : η ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    RiemannHypothesis ↔ ∃ K : ℝ, 0 ≤ K ∧ ∀ A : ℕ, ∃ m ≥ A,
      longIntervalWindowBound η K m (powerWindowEnd δ m) := by
  refine ⟨fun hr => ?_, fun ⟨K,hK,h⟩ => rh_of_longIntervalWindowBound hη hη₁ hδ hδ₁ hK h⟩
  obtain ⟨K,hK,h⟩ := long_prime_interval_error_of_zero_bound (B := 1/2) le_rfl (by norm_num)
    (fun ρ => (hr ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2).le)
  refine ⟨K,hK,fun A => ?_⟩
  let m := max 4 A
  have hm : (4:ℝ) ≤ m := by exact_mod_cast (le_max_left 4 A)
  have hbase : 16 ≤ (m:ℝ)^4/4 := by
    linarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hm 4]
  have hlow : 4 ≤ ⌊((m:ℝ)^4/4)^(1/(1+η))⌋₊ := by
    apply Nat.le_floor
    change (4:ℝ) ≤ _
    calc (4:ℝ) = sqrt 16 := by norm_num
         _ ≤ sqrt ((m:ℝ)^4/4) := sqrt_le_sqrt hbase
         _ ≤ _ := by
           rw [sqrt_eq_rpow]
           apply rpow_le_rpow_of_exponent_le (by linarith)
           exact (le_div_iff₀ (by linarith : 0 < 1+η)).mpr (by linarith)
  refine ⟨m,le_max_right _ _,fun n _ i j hi hiN hNj _ hlen => ?_⟩
  simpa only [← sqrt_eq_rpow] using
    (le_abs_self (primeIntervalDeficit i j)).trans (h (hlow.trans hi) hiN hNj hlen)

/-- If the signed average is at most D, at least one long interval already
has ordinary-prime shortfall at most 2D+1. -/
theorem exists_long_prime_interval_of_chord_le {a N b : ℕ} (hN : 0 < N)
    (ha : 4*a ≤ N) (hb : 4*N ≤ b) {D : ℝ} (hD : 0 ≤ D) (h : chordPrimeDeficit a N b ≤ D) :
    ∃ i j : ℕ, a ≤ i ∧ i < N ∧ N ≤ j ∧ j ≤ b ∧ N/2 < j-i ∧ primeIntervalDeficit i j ≤ 2*D+1 := by
  let P := chordWeight a N b N
  have hN0 : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hab : (a:ℝ) < b := Nat.cast_lt.mpr (by omega)
  have ha' : 4*(a:ℝ) ≤ N := by exact_mod_cast ha
  have hb' : 4*(N:ℝ) ≤ b := by exact_mod_cast hb
  have hu : 3/4 ≤ ((b:ℝ)-N)/(b-a) := (le_div_iff₀ (sub_pos.mpr hab)).mpr
    (by linarith only [hb',Nat.cast_nonneg (α := ℝ) a])
  have hv : 3/4 ≤ ((N:ℝ)-a)/N := (le_div_iff₀ hN0).mpr (by linarith only [ha'])
  have hP : 1/2 ≤ P := by
    simp only [P,chordWeight,ite_eq_left (le_refl N)]
    exact (by norm_num : (1/2:ℝ) ≤ (3/4)*(3/4)).trans
      (mul_le_mul hu hv (by norm_num) (by linarith))
  by_contra! hbad
  let c (d : ℕ) : ℝ := 1-(if d.Prime then log d else 0)
  have hh := chordWeight_level_integral (a := a) (b := b) hN (by omega) (by omega) (by omega) c
  have hpoint (y : ℝ) (hy : y ∈ Set.Icc 0 P) : 2*D+1 ≤ ∑ d ∈ primeLevelInterval a N b y, c d := by
    obtain ⟨i,j,hai,hi,hj,hjb,hlen,he⟩ := primeLevelInterval_long hN ha hb hy.1 hy.2
    rw [he]
    exact (hbad i j hai hi hj hjb hlen).le.trans (primeIntervalDeficit_eq (hi.le.trans hj)).ge
  have ht := intervalIntegral.integral_mono_on (by linarith : 0 ≤ P) intervalIntegrable_const hh.1 hpoint
  rw [hh.2,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at ht
  change P*(2*D+1) ≤ chordPrimeDeficit a N b at ht
  linarith only [h,ht,mul_le_mul_of_nonneg_right hP (show 0 ≤ 2*D+1 by positivity)]

/-- Every sufficiently late power window contains a polynomial block of fourth
powers on which one long interval per sample has square-root shortfall. The
two outer buffers contain all witnesses for the block. -/
theorem long_prime_square_root_blocks {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {β δ : ℝ}, 0 ≤ β → β < 1 → 0 < δ →
      ∀ᶠ Y : ℝ in Filter.atTop, ∃ M : ℕ,
        let t := M+⌊(M:ℝ)^β⌋₊
        Y ≤ (M:ℝ)^4 ∧ (t:ℝ)^4 ≤ Y^(1+δ) ∧ ∀ n ∈ Icc M t, ∃ i j : ℕ,
          ⌊((M:ℝ)^4/4)^(1/(1+η))⌋₊ ≤ i ∧ i < n^4 ∧ n^4 ≤ j ∧ j ≤ ⌈(4*(t:ℝ)^4)^(1+η)⌉₊ ∧
          n^4/2 < j-i ∧ primeIntervalDeficit i j ≤ C*(n:ℝ)^2 := by
  obtain ⟨K,hK,M₀,hM₀⟩ := local_prime_window_comparison hη
  obtain ⟨B,hB,hbase⟩ := singlePrime_central_error
  refine ⟨2*(K+B)+1,by positivity,fun {β δ} hβ hβ₁ hδ => ?_⟩
  filter_upwards [AlpogeWindow.negative_polynomial_fourth_blocks hβ hβ₁ hδ,
    Filter.eventually_ge_atTop (((max 1 M₀:ℕ):ℝ)^4)] with Y hY hY₀
  obtain ⟨M,hw⟩ := hY
  let t := M+⌊(M:ℝ)^β⌋₊
  have hMt : M ≤ t := Nat.le_add_right _ _
  have hleft := (hw M (mem_Icc.mpr ⟨le_rfl,hMt⟩)).1.1
  have hright := (hw t (mem_Icc.mpr ⟨hMt,le_rfl⟩)).1.2
  have hm : max 1 M₀ ≤ M := by
    by_contra! hlt
    exact (not_lt_of_ge (hY₀.trans hleft)) (pow_lt_pow_left₀ (Nat.cast_lt.mpr hlt)
      (Nat.cast_nonneg M) (by decide : 4 ≠ 0))
  have h1 : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hfloor : 1 ≤ ⌊(M:ℝ)^β⌋₊ := Nat.le_floor (by simpa using Real.one_le_rpow h1 hβ)
  obtain ⟨a,b,hal,ha,hb,hbu,hcomp⟩ := hM₀ (show M₀ ≤ M by omega) (show M < t by dsimp [t]; omega)
  refine ⟨M,hleft,hright,fun n hn => ?_⟩
  obtain ⟨hmn,hnt⟩ := mem_Icc.mp hn
  have hn1 : 1 ≤ n := by omega
  have hneg := (hw n hn).2
  rw [AlpogeWindow.G_native] at hneg
  have hs := (abs_le.mp (hbase n hn1)).1
  have hc := (abs_le.mp (hcomp n hn)).2
  have hd : chordPrimeDeficit a (n^4) b ≤ (K+B)*(n:ℝ)^2 := by nlinarith only [hs,hc,hneg]
  obtain ⟨i,j,hai,hi,hj,hjb,hlen,he⟩ := exists_long_prime_interval_of_chord_le
    (Nat.one_le_pow 4 n hn1) (ha.trans (Nat.pow_le_pow_left hmn 4))
    ((Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hnt 4)).trans hb) (by positivity) hd
  refine ⟨i,j,hal.trans hai,hi,hj,hjb.trans hbu,hlen,?_⟩
  nlinarith only [he,one_le_pow₀ (Nat.one_le_cast.mpr hn1 : 1 ≤ (n:ℝ)) (n := 2)]

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [
      ``RiemannGaussian.AlpogeMined.primeLevelInterval_long,
      ``RiemannGaussian.AlpogeMined.chordWeight_level_integral,
      ``RiemannGaussian.AlpogeMined.primeIntervalDeficit_eq,
      ``RiemannGaussian.AlpogeMined.long_prime_deficit_of_chord,
      ``RiemannGaussian.AlpogeMined.chordPrimeDeficit_le_length_power,
      ``RiemannGaussian.AlpogeMined.rh_of_longIntervalWindowBound,
      ``RiemannGaussian.AlpogeMined.long_prime_interval_seven_eighths,
      ``RiemannGaussian.AlpogeMined.rh_iff_long_prime_intervals,
      ``RiemannGaussian.AlpogeMined.long_prime_square_root_blocks] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
