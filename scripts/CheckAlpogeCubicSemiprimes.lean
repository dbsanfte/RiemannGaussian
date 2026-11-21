import CheckAlpogeCubicSmallPrimes

/-! # Pairing rough semiprimes with positive terms in the moving upper sum -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real
open scoped Classical ArithmeticFunction.Omega ArithmeticFunction.vonMangoldt

def cubicSampleStart (n : ℕ) := n^4-(Nat.log 2 n+1)*n^3

/-- The entire averaging interval is in the first half of one period modulo t. -/
def cubicHalfPeriod (n t : ℕ) : Prop := ∃ j : ℕ, 0<j ∧ j*t ≤ cubicSampleStart n ∧
  2*cubicSampleEnd n ≤ (2*j+1)*t

theorem weight_ge_half_of_halfPeriod {n t M : ℕ} (ht : 0<t) (hp : cubicHalfPeriod n t)
    (hlo : cubicSampleStart n ≤ M) (hhi : M ≤ cubicSampleEnd n) : 1/2 ≤ weight M t := by
  obtain ⟨j,_,hj,he⟩ := hp
  have hMt := hj.trans hlo
  rw [show (2*j+1)*t=2*(j*t)+t by ring] at he
  have hrem : M-j*t<t := by omega
  have hmod : M%t=M-j*t := by
    conv_lhs => rw [← Nat.sub_add_cancel hMt]
    simp [Nat.mod_eq_of_lt hrem]
  have ha : 2*(M%t) ≤ t := by omega
  have hreal : (2:ℝ)*(M%t:ℕ) ≤ t := by exact_mod_cast ha
  have hh : ((M%t:ℕ):ℝ)/t ≤ 1/2 :=
    (div_le_iff₀ (Nat.cast_pos.mpr ht)).mpr (by linarith only [hreal])
  unfold weight
  linarith only [hh]

/-- Rough losses in the fixed half-weight range with a positive partner
in a certified half-period above the frozen cutoff. -/
def movingSemiprimes (n : ℕ) := (Ioc n (3*n^3)).filter (fun r =>
  r.Coprime n.factorial ∧ Ω r=2 ∧ 3*n^3 < 2*crossingPrime n*r ∧
    cubicHalfPeriod n (2*crossingPrime n*r))

private theorem moving_bounds {n r : ℕ} (hr : r ∈ movingSemiprimes n) :
    r ≤ 3*n^3 ∧ 3*n^3 < 2*crossingPrime n*r ∧ 2*crossingPrime n*r ≤ cubicSampleStart n := by
  obtain ⟨hi,_,_,hR,j,hj,ht,_⟩ := mem_filter.mp hr
  exact ⟨(mem_Ioc.mp hi).2,hR,(Nat.le_mul_of_pos_left _ hj).trans ht⟩

private theorem cubicWidth_eighth {n : ℕ} (hn : 64 ≤ n) :
    8*((Nat.log 2 n+1)*n^3) ≤ n^4 := by
  let k := Nat.log 2 n+1
  have hlog : 6 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega : n≠0)).mpr hn
  have hpow (j : ℕ) (hj : 6 ≤ j) : 8*(j+1) ≤ 2^j := by
    induction j, hj using Nat.le_induction with
    | base => decide
    | succ j _ ih => rw [pow_succ]; omega
  have hk : 8*k ≤ n := (hpow _ hlog).trans (Nat.pow_log_le_self 2 (by omega))
  have hw := Nat.mul_le_mul_right (n^3) hk
  simpa only [show 8*k*n^3=8*(k*n^3) by ring,show n*n^3=n^4 by ring] using hw

/-- A full interval of products near the central fourth power satisfies the
period condition, for every n from 64 onward. -/
theorem movingSemiprimes_of_top_band {n r : ℕ} (hn : 64 ≤ n) (hnr : n<r)
    (hc : r.Coprime n.factorial) (hΩ : Ω r=2)
    (hlo : 3*n^4 ≤ 4*(2*crossingPrime n*r)) (hhi : 8*(2*crossingPrime n*r) ≤ 7*n^4) :
    r ∈ movingSemiprimes n := by
  let k := Nat.log 2 n+1
  have hw : 8*(k*n^3) ≤ n^4 := cubicWidth_eighth hn
  let t := 2*crossingPrime n*r
  change 3*n^4 ≤ 4*t at hlo
  change 8*t ≤ 7*n^4 at hhi
  have ht : t ≤ n^4 := by omega
  have hnq := (crossingPrime_spec (by omega : 8≤n)).2.2.2.le
  have hrn := Nat.mul_le_mul_right r hnq
  have hr3 : r ≤ n^3 := by
    apply Nat.le_of_mul_le_mul_left _ (by omega : 0<n)
    exact hrn.trans (ht.trans_eq (by ring))
  have hscale := Nat.mul_le_mul_right (n^3) (show 8 ≤ n by omega)
  rw [show n*n^3=n^4 by ring] at hscale
  refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨hnr,by omega⟩,hc,hΩ,?_,1,by decide,?_,?_⟩
  · change 3*n^3 < t
    omega
  · change 1*t ≤ n^4-k*n^3
    omega
  · change 2*(n^4+k*n^3) ≤ (2*1+1)*t
    omega

private def movingPartners (n : ℕ) := (movingSemiprimes n).image (fun r => 2*crossingPrime n*r)

/-- Shifting log r from each upper partner back to its rough semiprime
keeps the diagonal at r and removes the partner's coefficient. -/
def semiprimeTransfer (n t : ℕ) : ℝ :=
  (if t ∈ movingPartners n then log (t/(2*crossingPrime n):ℕ) else 0) -
    (if t ∈ movingSemiprimes n then log t else 0)

def cubicCompensatedCoefficient (n t : ℕ) : ℝ :=
  cubicMatchedCoefficient n t - semiprimeTransfer n t

private theorem sum_members {S U : Finset ℕ} (h : S ⊆ U) (f : ℕ → ℝ) :
    (∑ t ∈ U, if t ∈ S then f t else 0) = ∑ t ∈ S, f t := by
  rw [← sum_filter]
  congr 1
  ext t
  simp only [mem_filter]
  exact ⟨And.right,fun ht => ⟨h ht,ht⟩⟩

theorem cubicMean_le_on {n : ℕ} (hn : 8 ≤ n) {f g : ℕ → ℝ}
    (h : ∀ M, cubicSampleStart n ≤ M → M ≤ cubicSampleEnd n → f M ≤ g M) :
    cubicMean n f ≤ cubicMean n g := by
  let k := Nat.log 2 n+1
  let D := n^3
  have hk : k ≤ n := by have := (cubic_tail_parameters hn).1; dsimp [k]; omega
  have hh : k*D ≤ n^4 := (Nat.mul_le_mul_right D hk).trans_eq (by dsimp [D]; ring)
  change repeatedMean (2*D+1) k f (n^4-k*D) ≤ repeatedMean (2*D+1) k g (n^4-k*D)
  apply repeat_mono
  intro M hlo hhi
  apply h M hlo
  change M ≤ n^4+k*D
  change M ≤ n^4-k*D+k*(2*D) at hhi
  rw [show k*(2*D)=2*(k*D) by ring] at hhi
  omega

theorem cubicMean_const (n : ℕ) (c : ℝ) : cubicMean n (fun _ => c) = c :=
  repeat_const (by omega : 0 < 2*n^3+1) (Nat.log 2 n+1) _ _

theorem cubicMean_first_moment {n : ℕ} (hn : 8 ≤ n) :
    cubicMean n (fun M => (M:ℝ)) = (n:ℝ)^4 := by
  have hk := (cubic_tail_parameters hn).1
  have hw := (Nat.mul_le_mul_right (n^3) (show Nat.log 2 n+1 ≤ n by omega)).trans_eq
    (show n*n^3=n^4 by ring)
  change repeatedMean (2*n^3+1) (Nat.log 2 n+1) (fun M => (M:ℝ)) (cubicSampleStart n) = _
  rw [repeat_first_moment,cubicSampleStart,Nat.cast_sub hw]
  push_cast
  ring

/-- The precise surplus of the actual moving weights above the matching
half weight, summed over all the selected partners. -/
def movingSemiprimeSurplus (n : ℕ) := cubicMean n (fun M => ∑ r ∈ movingSemiprimes n,
  log r * weight M (2*crossingPrime n*r)) - (∑ r ∈ movingSemiprimes n, log r)/2

theorem movingSemiprimeSurplus_nonneg {n : ℕ} (hn : 8 ≤ n) : 0 ≤ movingSemiprimeSurplus n := by
  apply sub_nonneg.mpr
  rw [← cubicMean_const n ((∑ r ∈ movingSemiprimes n, log r)/2)]
  apply cubicMean_le_on hn
  intro M hlo hhi
  rw [sum_div]
  apply sum_le_sum
  intro r hr
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (log_natCast_nonneg _)
  simpa only [one_div] using (weight_ge_half_of_halfPeriod
    ((Nat.zero_le _).trans_lt (moving_bounds hr).2.1) (mem_filter.mp hr).2.2.2.2 hlo hhi)

private theorem interior_mod {n M t : ℕ} (hn : 64 ≤ n)
    (hl : 4*n^4 ≤ 5*t) (hu : 8*t ≤ 7*n^4)
    (hlo : cubicSampleStart n ≤ M) (hhi : M ≤ cubicSampleEnd n) : t ≤ M ∧ M%t = M-t := by
  have hw := cubicWidth_eighth hn
  have hpos : 0 < n^4 := by positivity
  unfold cubicSampleStart at hlo
  unfold cubicSampleEnd at hhi
  have hMt : t ≤ M := by omega
  have hrem : M-t < t := by omega
  refine ⟨hMt,?_⟩
  conv_lhs => rw [← Nat.sub_add_cancel hMt]
  simp [Nat.mod_eq_of_lt hrem]

private theorem weight_interior {n M t : ℕ} (hn : 64 ≤ n) (ht : 0<t)
    (hl : 4*n^4 ≤ 5*t) (hu : 8*t ≤ 7*n^4)
    (hlo : cubicSampleStart n ≤ M) (hhi : M ≤ cubicSampleEnd n) : 19/32 ≤ weight M t := by
  obtain ⟨_,hmod⟩ := interior_mod hn hl hu hlo hhi
  have hw := cubicWidth_eighth hn
  unfold cubicSampleEnd at hhi
  have ha : 32*(M%t) ≤ 13*t := by omega
  have hreal : (32:ℝ)*(M%t:ℕ) ≤ 13*t := by exact_mod_cast ha
  have hh : ((M%t:ℕ):ℝ)/t ≤ 13/32 := (div_le_iff₀ (Nat.cast_pos.mpr ht)).mpr (by linarith)
  unfold weight
  linarith only [hh]

/-- On the inner band each rough loss is overcompensated by at least
three thirty-seconds of its logarithm, throughout the full repeated mean. -/
theorem movingSemiprimeSurplus_lower {n : ℕ} (hn : 64 ≤ n) :
    (3/32:ℝ)*(∑ r ∈ (movingSemiprimes n).filter (fun r =>
      4*n^4 ≤ 5*(2*crossingPrime n*r) ∧ 8*(2*crossingPrime n*r) ≤ 7*n^4), log r) ≤
      movingSemiprimeSurplus n := by
  unfold movingSemiprimeSurplus
  rw [le_sub_iff_add_le]
  nth_rw 1 [← cubicMean_const n (_+_)]
  apply cubicMean_le_on (by omega)
  intro M hlo hhi
  rw [sum_filter,mul_sum,sum_div,← sum_add_distrib]
  apply sum_le_sum
  intro r hr
  have ht := (Nat.zero_le _).trans_lt (moving_bounds hr).2.1
  split_ifs with hb
  · have h := mul_le_mul_of_nonneg_left (weight_interior hn ht hb.1 hb.2 hlo hhi) (log_natCast_nonneg r)
    linarith only [h]
  · have h := mul_le_mul_of_nonneg_left (weight_ge_half_of_halfPeriod ht
      (mem_filter.mp hr).2.2.2.2 hlo hhi) (log_natCast_nonneg r)
    linarith only [h]

theorem semiprimeTransfer_response {n : ℕ} (hn : 8 ≤ n) :
    cubicWeightedResponse n (semiprimeTransfer n) = movingSemiprimeSurplus n := by
  let S := movingSemiprimes n
  let P := movingPartners n
  let R := 3*n^3
  let K := 2*crossingPrime n
  have hK : 0<K := by have := (crossingPrime_spec hn).2.1; dsimp [K]; omega
  have hlow : (∑ t ∈ Icc 0 R, semiprimeTransfer n t) = -(∑ r ∈ S, log r) := by
    rw [← sum_members (U := Icc 0 R) (fun r hr => mem_Icc.mpr ⟨Nat.zero_le _,(moving_bounds hr).1⟩)
      (fun r => log r),←sum_neg_distrib]
    apply sum_congr rfl
    intro t ht
    have hP : t ∉ P := by
      rintro hp
      obtain ⟨r,hr,rfl⟩ := mem_image.mp hp
      exact (not_le.mpr (moving_bounds hr).2.1) (mem_Icc.mp ht).2
    unfold semiprimeTransfer
    rw [ite_eq_right hP,zero_sub]
  have hupper (M : ℕ) (hAM : cubicSampleStart n ≤ M) :
      (∑ t ∈ Ioc R M, semiprimeTransfer n t*weight M t) =
        ∑ r ∈ S, log r * weight M (K*r) := by
    have hP : P ⊆ Ioc R M := by
      intro t ht
      obtain ⟨r,hr,rfl⟩ := mem_image.mp ht
      obtain ⟨_,hR,he⟩ := moving_bounds hr
      exact mem_Ioc.mpr ⟨hR,he.trans hAM⟩
    calc
      _ = ∑ t ∈ Ioc R M, if t ∈ P then log (t/K:ℕ)*weight M t else 0 := by
        apply sum_congr rfl
        intro t ht
        have hS : t ∉ S := fun h => (not_le.mpr (mem_Ioc.mp ht).1) (moving_bounds h).1
        unfold semiprimeTransfer
        rw [ite_eq_right hS,sub_zero]
        change (if t ∈ P then log (t/K:ℕ) else 0)*weight M t = _
        split_ifs <;> simp
      _ = ∑ t ∈ P, log (t/K:ℕ)*weight M t := sum_members hP _
      _ = _ := by
        unfold P movingPartners
        rw [sum_image (fun a _ b _ he => Nat.eq_of_mul_eq_mul_left hK he)]
        apply sum_congr rfl
        intro r _
        rw [Nat.mul_div_cancel_left r hK]
  have hmean : cubicMean n (fun M => ∑ t ∈ Ioc R M, semiprimeTransfer n t*weight M t) =
      cubicMean n (fun M => ∑ r ∈ S, log r * weight M (K*r)) :=
    le_antisymm (cubicMean_le_on hn (fun M ha _ => (hupper M ha).le))
      (cubicMean_le_on hn (fun M ha _ => (hupper M ha).ge))
  unfold cubicWeightedResponse movingSemiprimeSurplus
  rw [hlow,hmean]
  change _ = cubicMean n (fun M => ∑ r ∈ S, log r * weight M (K*r)) - (∑ r ∈ S, log r)/2
  ring

theorem movingSemiprime_compensated_values {n r : ℕ} (hn : 8 ≤ n) (hr : r ∈ movingSemiprimes n) :
    cubicCompensatedCoefficient n r = Λ r ∧
      cubicCompensatedCoefficient n (2*crossingPrime n*r) = 0 := by
  let K := 2*crossingPrime n
  obtain ⟨hq,hq2,hqn,hcross⟩ := crossingPrime_spec hn
  have hK : 0<K := by dsimp [K]; omega
  obtain ⟨hi,hc,hΩ,_,_⟩ := mem_filter.mp hr
  obtain ⟨hlo,hhi,hstart⟩ := moving_bounds hr
  have hnr := (mem_Ioc.mp hi).1
  have hnot : ∀ s : ℕ, K*s ≠ r := by
    intro s he
    have hd : 2 ∣ r := ⟨crossingPrime n*s,by rw [← he]; dsimp [K]; ring⟩
    have := Nat.eq_one_of_dvd_coprimes hc hd (Nat.dvd_factorial (by decide) (by omega))
    omega
  have hraw := cubicMatchedCoefficient_eq_outside
    (fun hs => (not_le.mpr hhi) (matchedSemiprime_bounds hn hs).2) (fun s _ => hnot s)
  have hpartner : cubicMatchedCoefficient n (K*r) = log r := by
    rw [cubicMatchedCoefficient_eq_outside
      (fun hs => (not_le.mpr hhi) (matchedSemiprime_bounds hn hs).1)
      (fun s hs he => (not_le.mpr hhi) (he ▸ (matchedSemiprime_bounds hn hs).2))]
    exact cubicThreeFactorCoefficient_crossing_pair (by omega) (by omega) hc Nat.prime_two hq
      (by omega) (by omega) hqn hcross (no_four_of_le_fourth (hstart.trans (Nat.sub_le _ _)))
  have hP : r ∉ movingPartners n := fun h => by
    obtain ⟨s,_,he⟩ := mem_image.mp h
    exact hnot s he
  have hKr : K*r ∈ movingPartners n := mem_image_of_mem _ hr
  have hout : K*r ∉ movingSemiprimes n := fun h => (not_le.mpr hhi) (moving_bounds h).1
  constructor
  · rw [cubicCompensatedCoefficient,hraw,cubicThreeFactorCoefficient_rough_eq (by omega) hnr hc,
      ite_eq_left (Or.inl hΩ),semiprimeTransfer,ite_eq_right hP,ite_eq_left hr]
    ring
  · change cubicCompensatedCoefficient n (K*r)=0
    rw [cubicCompensatedCoefficient,hpartner,semiprimeTransfer,ite_eq_left hKr,ite_eq_right hout]
    change log r - (log (K*r/K:ℕ)-0)=0
    rw [Nat.mul_div_cancel_left r hK]; ring

/-- Both matching steps leave every odd upper coefficient available. -/
theorem cubicCompensatedCoefficient_of_odd_upper {n t : ℕ} (hn : 8 ≤ n)
    (ht : 3*n^3 < t) (ho : ¬2 ∣ t) :
    cubicCompensatedCoefficient n t = cubicThreeFactorCoefficient n t := by
  have hnot (r : ℕ) : 2*crossingPrime n*r ≠ t := by
    rintro rfl
    exact ho ⟨crossingPrime n*r,by ring⟩
  have hmatched := cubicMatchedCoefficient_eq_outside
    (fun h => (not_le.mpr ht) (matchedSemiprime_bounds hn h).1) (fun r _ => hnot r)
  have hP : t ∉ movingPartners n := by
    rintro h
    obtain ⟨r,_,he⟩ := mem_image.mp h
    exact hnot r he
  have hS : t ∉ movingSemiprimes n := fun h => (not_le.mpr ht) (moving_bounds h).1
  simp only [cubicCompensatedCoefficient,semiprimeTransfer,hmatched,ite_eq_right hP,
    ite_eq_right hS,sub_zero]

/-- Throughout this band the remainder is M-t. Averaging the resulting
affine weight replaces M by its exact first moment n⁴, even for signed c. -/
theorem cubicWeightedResponse_interior_eq {n : ℕ} (hn : 64 ≤ n) (s : Finset ℕ) (c : ℕ → ℝ)
    (hband : ∀ t ∈ s, 4*n^4 ≤ 5*t ∧ 8*t ≤ 7*n^4) :
    cubicWeightedResponse n (fun t => if t ∈ s then c t else 0) =
      ∑ t ∈ s, c t*(2-(n:ℝ)^4/t) := by
  have hw := cubicWidth_eighth hn
  have hscale : 64*n^3 ≤ n^4 := (Nat.mul_le_mul_right (n^3) hn).trans_eq (by ring)
  have hloc {t : ℕ} (ht : t ∈ s) : 3*n^3 < t ∧ t ≤ cubicSampleStart n := by
    obtain ⟨hl,hu⟩ := hband t ht
    unfold cubicSampleStart
    have hpos : 0 < n^3 := by positivity
    omega
  have hlow : ∑ t ∈ Icc 0 (3*n^3), (if t ∈ s then c t else 0) = 0 := by
    apply sum_eq_zero
    intro t ht
    exact ite_eq_right (fun hm => (not_le.mpr (hloc hm).1) (mem_Icc.mp ht).2)
  let L := ∑ t ∈ s, c t/(t:ℝ)
  let U := ∑ t ∈ s, c t*2
  let F := fun M => ∑ t ∈ Ioc (3*n^3) M, (if t ∈ s then c t else 0)*weight M t
  let G : ℕ → ℝ := (fun _ => U) - L • (fun M : ℕ => (M:ℝ))
  have he (M : ℕ) (hstart : cubicSampleStart n ≤ M) (hend : M ≤ cubicSampleEnd n) : F M = G M := by
    have hsub : s ⊆ Ioc (3*n^3) M := fun t ht => mem_Ioc.mpr ⟨(hloc ht).1,(hloc ht).2.trans hstart⟩
    dsimp only [F,G,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,U,L]
    simp_rw [ite_mul,zero_mul]
    rw [sum_members hsub,sum_mul,← sum_sub_distrib]
    apply sum_congr rfl
    intro t ht
    obtain ⟨htM,hmod⟩ := interior_mod hn (hband t ht).1 (hband t ht).2 hstart hend
    have ht0 : 0 < (t:ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt (hloc ht).1)
    rw [weight,hmod,Nat.cast_sub htM]
    field_simp
    ring
  have hmean : cubicMean n F = cubicMean n G := le_antisymm
    (cubicMean_le_on (by omega) fun M hl hu => (he M hl hu).le)
    (cubicMean_le_on (by omega) fun M hl hu => (he M hl hu).ge)
  unfold cubicWeightedResponse
  rw [hlow,zero_div,zero_add]
  change cubicMean n F = _
  rw [hmean]
  dsimp only [G]
  rw [map_sub,map_smul,cubicMean_const,cubicMean_first_moment (by omega : 8 ≤ n),smul_eq_mul]
  dsimp only [U,L]
  rw [sum_mul,← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  ring

/-- Retaining the explicit surplus makes the compensated response exact. -/
theorem cubicCompensatedResponse_eq {n : ℕ} (hn : 8 ≤ n) :
    cubicWeightedResponse n (cubicCompensatedCoefficient n) + movingSemiprimeSurplus n =
      cubicWeightedResponse n (cubicThreeFactorCoefficient n) := by
  change cubicWeightedResponse n (cubicMatchedCoefficient n-semiprimeTransfer n) + _ = _
  rw [← cubicWeightedResponse_sub,semiprimeTransfer_response hn,cubicMatchedResponse_eq hn]
  ring

def cubicCompensatedMassOn (m b : ℕ) : ℝ := ∑ n ∈ Icc m b, max
  (cubicSmoothMoments n - cubicWeightedResponse n (cubicCompensatedCoefficient n) -
    movingSemiprimeSurplus n) 0 / (n:ℝ)^3

theorem cubicCompensatedMassOn_eq {m b : ℕ} (hm : 8 ≤ m) :
    cubicCompensatedMassOn m b = cubicThreeFactorMassOn m b := by
  apply sum_congr rfl
  intro n hn
  rw [sub_sub,cubicCompensatedResponse_eq (hm.trans (mem_Icc.mp hn).1)]

theorem rh_of_cubicCompensatedMassOn_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicCompensatedMassOn m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicThreeFactorMassOn_powerWindows
  intro α hα
  obtain ⟨δ,hδ,hδ1,hw⟩ := h α hα
  refine ⟨δ,hδ,hδ1,fun A => ?_⟩
  obtain ⟨m,hm,he⟩ := hw (max A 8)
  exact ⟨m,by omega,(cubicCompensatedMassOn_eq (by omega : 8 ≤ m)).ge.trans he⟩

/-- Only count the excess above the exact surplus and a quadratic allowance. -/
def cubicExceptionalMassOn (C : ℝ) (m b : ℕ) : ℝ := ∑ n ∈ Icc m b, max
  (cubicSmoothMoments n - cubicWeightedResponse n (cubicCompensatedCoefficient n) -
    movingSemiprimeSurplus n - C*(n:ℝ)^2*(1+log n)^2) 0 / (n:ℝ)^3

/-- Discarding this allowance at every sample costs at most a cubic logarithm
over the entire window, uniformly in its starting point. -/
theorem cubicExceptionalMassOn_bounds {C : ℝ} (hC : 0 ≤ C) {m b : ℕ} (hm : 1 ≤ m) :
    cubicExceptionalMassOn C m b ≤ cubicCompensatedMassOn m b ∧
    cubicCompensatedMassOn m b ≤ cubicExceptionalMassOn C m b + C*(1+log b)^3 :=
  cubicAllowance_bounds (fun n => cubicSmoothMoments n - cubicWeightedResponse n (cubicCompensatedCoefficient n) -
    movingSemiprimeSurplus n) hC hm

theorem rh_of_cubicExceptionalMassOn_powerWindows {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ A : ℕ, ∃ m ≥ A, cubicExceptionalMassOn C m (powerWindowEnd δ m) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_cubicCompensatedMassOn_powerWindows
  exact subpowerWindows_of_log_cube_error hC
    (fun hm => (cubicExceptionalMassOn_bounds hC (by omega : 1 ≤ _)).2) h

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.cubicRadicalCoefficient_pos_requires_radical,
      ``RiemannGaussian.AlpogeMined.cubicRadicalCoefficient_of_pair,
      ``RiemannGaussian.AlpogeMined.movingSemiprimes_of_top_band,
      ``RiemannGaussian.AlpogeMined.movingSemiprime_compensated_values,
      ``RiemannGaussian.AlpogeMined.movingSemiprimeSurplus_nonneg,
      ``RiemannGaussian.AlpogeMined.movingSemiprimeSurplus_lower,
      ``RiemannGaussian.AlpogeMined.cubicCompensatedMassOn_eq,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicCompensatedMassOn_powerWindows,
      ``RiemannGaussian.AlpogeMined.cubicExceptionalMassOn_bounds,
      ``RiemannGaussian.AlpogeMined.rh_of_cubicExceptionalMassOn_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
