import CheckAlpogeFixedPrimeBandCentered

/-! # Off-diagonal Möbius pairs by reduced ratio

For indices ga < gb with coprime a and b, the decay of the centered kernel
pays for the entire region a³ ≤ b in absolute value. The same window budget
covers H ⌊n⁴/l⌋² partners per larger index l, for each fixed H.
-/

noncomputable section
namespace RiemannGaussian.AlpogeMined
open Finset Real

private def fixedBandKernelCap : ℝ := 72+60*|fixedBandLogConstant|

private theorem fixedBandKernelCap_nonneg : 0 ≤ fixedBandKernelCap := by
  unfold fixedBandKernelCap; positivity

private theorem fixedBand_kernel_decay {y : ℝ} (hy : 1 ≤ y) :
    |fixedBandCenteredKernel y| ≤ 5*fixedBandKernelCap*y^(-(3/4):ℝ) := by
  have hy₀ := zero_lt_one.trans_le hy
  have hpow := one_le_rpow hy (by norm_num : (0:ℝ) ≤ 1/4)
  by_cases h : 2 ≤ y
  · apply (fixedBandCenteredKernel_bound h).trans
    have hl := log_le_rpow_div hy₀.le (by norm_num : (0:ℝ)<1/4)
    have hsum : 1+log y ≤ 5*y^(1/4:ℝ) := by linarith
    calc
      _ ≤ fixedBandKernelCap*(5*y^(1/4:ℝ))/y :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum fixedBandKernelCap_nonneg) hy₀.le
      _ = _ := by
        rw [show (-(3/4):ℝ)=1/4-1 by norm_num,rpow_sub hy₀,rpow_one]
        ring
  · apply (fixedBandCenteredKernel_uniform hy).trans
    change fixedBandKernelCap ≤ _
    rw [rpow_neg hy₀.le,← div_eq_mul_inv,le_div_iff₀ (rpow_pos_of_pos hy₀ _)]
    have hpow' : y^(3/4:ℝ) ≤ y := by
      simpa using rpow_le_rpow_of_exponent_le hy (by norm_num : (3/4:ℝ) ≤ 1)
    nlinarith only [mul_le_mul_of_nonneg_left (hpow'.trans (lt_of_not_ge h).le) fixedBandKernelCap_nonneg,
      fixedBandKernelCap_nonneg]

/-- Increasing pairs whose larger reduced coordinate is at least the cube of the smaller. -/
def fixedBandWidePairs (n : ℕ) : Finset (ℕ × ℕ) :=
  let S := Ioc (fixedBandMultipleCutoff n) (n^4)
  (S ×ˢ S).filter fun p => p.1<p.2 ∧
    (p.1/p.1.gcd p.2)^3 ≤ p.2/p.1.gcd p.2

private def ratioIndex (p : ℕ × ℕ) : Σ _b : ℕ, ℕ × ℕ :=
  ⟨p.2/p.1.gcd p.2,p.1/p.1.gcd p.2,p.1.gcd p.2⟩

private theorem ratioIndex_recovers (p : ℕ × ℕ) :
    (ratioIndex p).2.1*(ratioIndex p).2.2 = p.1 ∧ (ratioIndex p).1*(ratioIndex p).2.2 = p.2 :=
  ⟨Nat.div_mul_cancel (Nat.gcd_dvd_left _ _),Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)⟩

private theorem ratioIndex_injective : Function.Injective ratioIndex := by
  intro p q h
  have hp := ratioIndex_recovers p
  rw [h] at hp
  exact Prod.ext (hp.1.symm.trans (ratioIndex_recovers q).1) (hp.2.symm.trans (ratioIndex_recovers q).2)

private theorem widePair_data {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ fixedBandWidePairs n) :
    let r := ratioIndex p
    0 < p.1 ∧ 0 < r.1 ∧ 0 < r.2.1 ∧ 0 < r.2.2 ∧
      r.1 ≤ n^4 ∧ r.2.2 ≤ n^4/r.1 ∧ (r.2.1:ℝ) ≤ (r.1:ℝ)^(1/3:ℝ) := by
  obtain ⟨hS,hlt,hcube⟩ := mem_filter.mp hp
  obtain ⟨hk,hl⟩ := mem_product.mp hS
  have hk₀ := (Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1
  have hl₀ := hk₀.trans hlt
  obtain ⟨hka,hlb⟩ := ratioIndex_recovers p
  let r := ratioIndex p
  change r.2.1*r.2.2=p.1 at hka
  change r.1*r.2.2=p.2 at hlb
  change r.2.1^3 ≤ r.1 at hcube
  have ha₀ : 0 < r.2.1 := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hka; omega
  have hb₀ : 0 < r.1 := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hlb; omega
  have hg₀ : 0 < r.2.2 := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hlb; omega
  have hprod := hlb.le.trans (mem_Ioc.mp hl).2
  refine ⟨hk₀,hb₀,ha₀,hg₀,(Nat.le_mul_of_pos_right _ hg₀).trans hprod,
    (Nat.le_div_iff_mul_le hb₀).mpr (by simpa [Nat.mul_comm] using hprod),?_⟩
  rw [one_div,le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num),rpow_ofNat]
  exact_mod_cast hcube

private theorem fixedBandTerm_abs_le (n k : ℕ) :
    |fixedBandTailTerm n k| ≤ |fixedBandCenteredKernel (((n^4:ℕ):ℝ)/k)| := by
  rw [fixedBandTailTerm,abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k))

private theorem widePair_product_bound {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ fixedBandWidePairs n) :
    |fixedBandTailTerm n p.1*fixedBandTailTerm n p.2| ≤
      5*fixedBandKernelCap^2*((ratioIndex p).1:ℝ)^(-(1/2):ℝ) := by
  let r := ratioIndex p
  obtain ⟨hk,hb,ha,_,_,_,hroot⟩ := widePair_data hp
  have hS := mem_product.mp (mem_filter.mp hp).1
  have hl := (mem_Ioc.mp hS.2).2
  let y := ((n^4:ℕ):ℝ)/p.1
  have hkR : 0 < (p.1:ℝ) := Nat.cast_pos.mpr hk
  have haR : 0 < (r.2.1:ℝ) := Nat.cast_pos.mpr ha
  have hbR : 0 < (r.1:ℝ) := Nat.cast_pos.mpr hb
  have hsize : (r.1:ℝ) ≤ y*r.2.1 := by
    dsimp only [y]
    rw [div_mul_eq_mul_div, le_div_iff₀ hkR]
    have he : r.1*p.1 = p.2*r.2.1 := by
      obtain ⟨h₁,h₂⟩ := ratioIndex_recovers p
      change r.2.1*r.2.2=p.1 at h₁
      change r.1*r.2.2=p.2 at h₂
      rw [← h₁,← h₂]; ring
    exact_mod_cast he.le.trans (Nat.mul_le_mul_right _ hl)
  have hemi : (r.1:ℝ)^(2/3:ℝ) ≤ y := by
    apply le_of_mul_le_mul_right _ haR
    apply le_trans (mul_le_mul_of_nonneg_left hroot (rpow_nonneg hbR.le (2/3:ℝ))) _
    rw [← rpow_add hbR,show (2/3:ℝ)+1/3=1 by norm_num,rpow_one]
    exact hsize
  have hy : 1 ≤ y := (one_le_rpow (by exact_mod_cast hb : 1 ≤ (r.1:ℝ)) (by norm_num)).trans hemi
  have hdec := rpow_le_rpow_of_nonpos (rpow_pos_of_pos hbR (2/3:ℝ)) hemi (by norm_num : (-(3/4):ℝ) ≤ 0)
  rw [← rpow_mul hbR.le,show (2/3:ℝ)* -(3/4) = -(1/2) by norm_num] at hdec
  have hw := ((fixedBandTerm_abs_le n p.1).trans (fixedBand_kernel_decay hy)).trans
    (mul_le_mul_of_nonneg_left hdec (by positivity [fixedBandKernelCap_nonneg]))
  have hlpos : 0 < (p.2:ℝ) := Nat.cast_pos.mpr (hk.trans (mem_filter.mp hp).2.1)
  have hv := (fixedBandTerm_abs_le n p.2).trans (fixedBandCenteredKernel_uniform
    ((one_le_div hlpos).mpr (Nat.cast_le.mpr hl)))
  rw [abs_mul]
  apply (mul_le_mul hw hv (abs_nonneg _) (by positivity [fixedBandKernelCap_nonneg])).trans_eq
  change 5*fixedBandKernelCap*(r.1:ℝ)^(-(1/2):ℝ)*fixedBandKernelCap = _
  ring

/-- The convergent majorant after summing over reduced directions. -/
def fixedBandWidePairConstant : ℝ :=
  (5*fixedBandKernelCap^2)*∑' b : ℕ, (b:ℝ)^(-(7/6):ℝ)

/-- After dividing out the common factor, all ordered directions with
the larger coordinate at least the cube of the smaller one have total
absolute mass O(n⁴), uniformly in the sample. -/
theorem fixedBandWidePairs_abs_le (n : ℕ) :
    (∑ p ∈ fixedBandWidePairs n, |fixedBandTailTerm n p.1*fixedBandTailTerm n p.2|) ≤
      fixedBandWidePairConstant*(n:ℝ)^4 := by
  let N := n^4
  let C := 5*fixedBandKernelCap^2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let fiber (b : ℕ) := Ioc 0 ⌊(b:ℝ)^(1/3:ℝ)⌋₊ ×ˢ Ioc 0 (N/b)
  let W := fun (r : Σ _b : ℕ, ℕ × ℕ) => C*(r.1:ℝ)^(-(1/2):ℝ)
  have hsub : image ratioIndex (fixedBandWidePairs n) ⊆ (Ioc 0 N).sigma fiber := by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hr
    obtain ⟨_,hb,ha,hg,hN,hgN,haN⟩ := widePair_data hp
    exact mem_sigma.mpr ⟨mem_Ioc.mpr ⟨hb,hN⟩,mem_product.mpr
      ⟨mem_Ioc.mpr ⟨ha,Nat.le_floor haN⟩,mem_Ioc.mpr ⟨hg,hgN⟩⟩⟩
  refine (sum_le_sum_of_injOn (g := W) ratioIndex ratioIndex_injective.injOn hsub
    (fun _ hp => widePair_product_bound hp) (fun _ _ _ => by dsimp [W]; positivity)).trans ?_
  rw [sum_sigma]
  have hrow (b : ℕ) (hb : b ∈ Ioc 0 N) :
      (∑ j ∈ fiber b, W ⟨b,j⟩) ≤ (C*N)*(b:ℝ)^(-(7/6):ℝ) := by
    have hb₀ := Nat.cast_pos (α := ℝ).mpr (mem_Ioc.mp hb).1
    have hdiv : ((N/b:ℕ):ℝ) ≤ (N:ℝ)/b :=
      (le_div_iff₀ hb₀).mpr (by exact_mod_cast Nat.div_mul_le_self N b)
    dsimp only [W,fiber]
    rw [sum_const,card_product,Nat.card_Ioc,Nat.card_Ioc,Nat.sub_zero,Nat.sub_zero,nsmul_eq_mul,Nat.cast_mul]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul (Nat.floor_le (by positivity)) hdiv
      (by positivity) (by positivity)) (by positivity)).trans_eq ?_
    rw [div_eq_mul_inv]
    calc
      _ = (C*N)*(((b:ℝ)^(1/3:ℝ)*(b:ℝ)^(-1:ℝ))*(b:ℝ)^(-(1/2):ℝ)) := by rw [rpow_neg_one]; ring
      _ = _ := by rw [← rpow_add hb₀,← rpow_add hb₀]; norm_num
  refine (sum_le_sum hrow).trans ?_
  rw [← mul_sum]
  have hs : Summable (fun b : ℕ => (b:ℝ)^(-(7/6):ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
  have hsum := hs.sum_le_tsum (Ioc 0 N) (fun b _ => rpow_nonneg (Nat.cast_nonneg b) _)
  refine (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ C*N)).trans_eq ?_
  dsimp only [fixedBandWidePairConstant,N,C]
  push_cast
  ring

private theorem fixedBandTailOffDiagonal_upperPairs (n : ℕ) :
    let S := Ioc (fixedBandMultipleCutoff n) (n^4)
    fixedBandTailOffDiagonal n = 2*(∑ p ∈ (S ×ˢ S).filter (fun p => p.1<p.2),
      fixedBandTailTerm n p.1*fixedBandTailTerm n p.2) := by
  intro S
  let a := fixedBandTailTerm n
  let v (i j : ℕ) := if i<j then a i*a j else 0
  have row (i : ℕ) (hi : i ∈ S) :
      (∑ j ∈ S.erase i, a i*a j) = ∑ j ∈ S, (v i j+v j i) := by
    rw [← sum_erase_add S (fun j => v i j+v j i) hi]
    simp only [v,lt_irrefl,ite_false,add_zero]
    apply sum_congr rfl
    intro j hj
    rcases lt_or_gt_of_ne (ne_of_mem_erase hj) with h | h
    · simp [h,not_lt_of_ge h.le,mul_comm]
    · simp [h,not_lt_of_ge h.le]
  change (∑ i ∈ S, ∑ j ∈ S.erase i, a i*a j) = _
  rw [sum_congr rfl row]
  simp only [sum_add_distrib]
  rw [sum_comm (f := fun i j => v j i),sum_filter,sum_product]
  change _ = 2*(∑ i ∈ S, ∑ j ∈ S, v i j)
  ring

private def fixedBandRatioPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  let S := Ioc (fixedBandMultipleCutoff n) (n^4)
  (S ×ˢ S).filter fun p => p.1<p.2 ∧ p.2/p.1.gcd p.2 < (p.1/p.1.gcd p.2)^3

/-- Only pairs with reduced coordinates a < b < a³ remain. Both
orientations have the same weight and are counted together. -/
def fixedBandRatioMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, (2*∑ p ∈ fixedBandRatioPairs n,
    fixedBandTailTerm n p.1*fixedBandTailTerm n p.2)/(n:ℝ)^5

private theorem weighted_harmonic_window {C : ℝ} (hC : 0 ≤ C) {m b : ℕ} (hm : 2 ≤ m) :
    (∑ n ∈ Icc m b, C*(n:ℝ)⁻¹) ≤ C*(1+log b) := by
  rw [← mul_sum]
  have hi := harmonic_le_one_add_log b
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hi
  exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg
    (Icc_subset_Icc_left (by omega : 1 ≤ m)) (fun n _ _ => inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) n))).trans hi) hC

theorem fixedBandRatioMass_error {m b : ℕ} (hm : 2 ≤ m) :
    |fixedBandOffDiagonalMass m b-fixedBandRatioMass m b| ≤
      2*fixedBandWidePairConstant*(1+log b) := by
  let C := 2*fixedBandWidePairConstant
  have hC : 0 ≤ C := by unfold C fixedBandWidePairConstant; positivity
  unfold fixedBandOffDiagonalMass fixedBandRatioMass
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc m b, C*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      let S := Ioc (fixedBandMultipleCutoff n) (n^4)
      let P := (S ×ˢ S).filter fun p => p.1<p.2
      let w := fun p : ℕ × ℕ => fixedBandTailTerm n p.1*fixedBandTailTerm n p.2
      let far := fun p : ℕ × ℕ => (p.1/p.1.gcd p.2)^3 ≤ p.2/p.1.gcd p.2
      have hsplit := sum_filter_add_sum_filter_not P far w
      have hfar : P.filter far = fixedBandWidePairs n := by
        ext p; simp [P,S,far,fixedBandWidePairs,and_assoc]
      have hrest : P.filter (fun p => ¬far p) =
          (S ×ˢ S).filter (fun p => p.1<p.2 ∧ p.2/p.1.gcd p.2 < (p.1/p.1.gcd p.2)^3) := by
        ext p; simp [P,far,and_assoc]
      rw [fixedBandTailOffDiagonal_upperPairs]
      change |(2*∑ p ∈ P, w p)/(n:ℝ)^5 -
        (2*∑ p ∈ (S ×ˢ S).filter (fun p => p.1<p.2 ∧ p.2/p.1.gcd p.2 < (p.1/p.1.gcd p.2)^3), w p)/(n:ℝ)^5| ≤ _
      rw [← hrest,← sub_div]
      change |(2*(∑ p ∈ P, w p)-2*(∑ p ∈ P.filter (fun p => ¬far p), w p))/(n:ℝ)^5| ≤ _
      rw [← hsplit,← mul_sub,add_sub_cancel_right,hfar,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by have := (mem_Icc.mp hn).1; omega)
      rw [abs_of_pos (pow_pos hn₀ _)]
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((abs_sum_le_sum_abs _ _).trans (fixedBandWidePairs_abs_le n)) (by norm_num : (0:ℝ) ≤ 2))
          (pow_nonneg hn₀.le 5)).trans_eq
      dsimp only [C]; field_simp
    _ ≤ _ := weighted_harmonic_window hC hm

/-- The logarithmic estimate for these remaining reduced directions supplies RH. -/
theorem rh_of_fixedBandRatioMass_log_squareWindows
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandRatioMass m (m^2) ≤ C*(1+2*log m)) : RiemannHypothesis := by
  apply rh_of_fixedBandOffDiagonalMass_log_squareWindows
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C+2*fixedBandWidePairConstant,by unfold fixedBandWidePairConstant; positivity,fun A => ?_⟩
  obtain ⟨m,hm,hw⟩ := h (max 2 A)
  have he := (abs_le.mp (fixedBandRatioMass_error (b := m^2) ((le_max_left 2 A).trans hm))).2
  rw [Nat.cast_pow,log_pow,Nat.cast_ofNat] at he
  exact ⟨m,(le_max_right 2 A).trans hm,by linarith only [hw,he]⟩

private theorem sum_inv_sqrt_Ioc (N : ℕ) :
    (∑ l ∈ Ioc 0 N, (l:ℝ)^(-(1/2):ℝ)) ≤ 2*sqrt N := by
  let f (x : ℝ) := x^(-(1/2):ℝ)
  have ha : AntitoneOn f (Set.Ioc 0 (0+(N:ℝ))) := fun _ hx _ _ h =>
    rpow_le_rpow_of_nonpos hx.1 h (by norm_num)
  have hi := ha.sum_le_integral_of_integrableOn
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity) (by simp)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(1/2))))
  have hset : Ioc 0 N = Ico 1 (N+1) := by ext l; simp; omega
  rw [hset,sum_Ico_eq_sum_range]
  simp only [Nat.add_one_sub_one]
  dsimp only [f] at hi
  rw [zero_add,integral_rpow (Or.inl (by norm_num))] at hi
  norm_num [← sqrt_eq_rpow,add_comm,div_eq_mul_inv] at hi ⊢
  simpa [mul_comm] using hi

/-- Per-sample coefficient for the absolute contribution of sparse rows. -/
def fixedBandSparseRowConstant (H : ℕ) : ℝ := 2*H*(5*fixedBandKernelCap)^2

/-- A set of earlier partners for each larger index can be discarded in
absolute value at cost proportional to H n⁴ when its row at l contains at
most H ⌊n⁴/l⌋² indices. The partners may depend on both n and l. -/
theorem fixedBandSparseRows_abs_le (n H : ℕ) (row : ℕ → Finset ℕ)
    (hrow : ∀ l ∈ Ioc 0 (n^4), row l ⊆ Ioc 0 l)
    (hcard : ∀ l ∈ Ioc 0 (n^4), (row l).card ≤ H*(n^4/l)^2) :
    (∑ l ∈ Ioc 0 (n^4), ∑ k ∈ row l, |fixedBandTailTerm n k*fixedBandTailTerm n l|) ≤
      fixedBandSparseRowConstant H*(n:ℝ)^4 := by
  let N := n^4
  let D := 5*fixedBandKernelCap
  have hD : 0 ≤ D := by dsimp [D]; positivity [fixedBandKernelCap_nonneg]
  have estimate (l : ℕ) (hl : l ∈ Ioc 0 N) :
      (∑ k ∈ row l, |fixedBandTailTerm n k*fixedBandTailTerm n l|) ≤
        ((H:ℝ)*D^2*sqrt N)*(l:ℝ)^(-(1/2):ℝ) := by
    have hl₀ := Nat.cast_pos (α := ℝ).mpr (mem_Ioc.mp hl).1
    let y := (N:ℝ)/l
    have hy : 1 ≤ y := (one_le_div hl₀).mpr (by exact_mod_cast (mem_Ioc.mp hl).2)
    have hy₀ := zero_lt_one.trans_le hy
    have term (k : ℕ) (hk : k ∈ Ioc 0 l) : |fixedBandTailTerm n k| ≤ D*y^(-(3/4):ℝ) := by
      have hk₀ := Nat.cast_pos (α := ℝ).mpr (mem_Ioc.mp hk).1
      have hxy : y ≤ (N:ℝ)/k := div_le_div_of_nonneg_left (by positivity) hk₀ (by exact_mod_cast (mem_Ioc.mp hk).2)
      exact ((fixedBandTerm_abs_le n k).trans (fixedBand_kernel_decay (hy.trans hxy))).trans
        (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_nonpos hy₀ hxy (by norm_num)) hD)
    have hdiv : ((N/l:ℕ):ℝ) ≤ y :=
      (le_div_iff₀ hl₀).mpr (by exact_mod_cast Nat.div_mul_le_self N l)
    have hc : ((row l).card:ℝ) ≤ H*y^2 := by
      have hcast : ((row l).card:ℝ) ≤ H*((N/l:ℕ):ℝ)^2 := by exact_mod_cast hcard l hl
      exact hcast.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hdiv 2) (by positivity))
    calc
      _ ≤ ∑ _k ∈ row l, (D*y^(-(3/4):ℝ))^2 := by
        apply sum_le_sum
        intro k hk
        rw [abs_mul,pow_two]
        exact mul_le_mul (term k (hrow l hl hk)) (term l (mem_Ioc.mpr ⟨(mem_Ioc.mp hl).1,le_rfl⟩))
          (abs_nonneg _) (by positivity)
      _ ≤ H*y^2*(D*y^(-(3/4):ℝ))^2 := by
        rw [sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = ((H:ℝ)*D^2)*(y^(1/2:ℝ)) := by
        rw [mul_pow,← rpow_two (y^(-(3/4):ℝ)),← rpow_mul hy₀.le,← rpow_two y]
        rw [show (1/2:ℝ) = 2 + -(3/4)*2 by norm_num,rpow_add hy₀]
        ring
      _ = _ := by
        dsimp only [y]
        rw [← sqrt_eq_rpow,sqrt_div (by positivity),rpow_neg hl₀.le,← sqrt_eq_rpow]
        ring
  refine (sum_le_sum estimate).trans ?_
  rw [← mul_sum]
  refine (mul_le_mul_of_nonneg_left (sum_inv_sqrt_Ioc N) (by positivity : 0 ≤ (H:ℝ)*D^2*sqrt N)).trans_eq ?_
  calc
    _ = 2*H*D^2*(sqrt N)^2 := by ring
    _ = _ := by rw [sq_sqrt (by positivity)]; simp [N,D,fixedBandSparseRowConstant]

private def fixedBandNearby (n H : ℕ) (p : ℕ × ℕ) : Prop :=
  p.2-p.1 ≤ H*(n^4/p.2)^2

private instance (n H : ℕ) : DecidablePred (fixedBandNearby n H) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

private theorem fixedBandNearby_abs_le (n H : ℕ) (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n^4) :
    (∑ p ∈ P.filter (fixedBandNearby n H), |fixedBandTailTerm n p.1*fixedBandTailTerm n p.2|) ≤
      fixedBandSparseRowConstant H*(n:ℝ)^4 := by
  let row (l : ℕ) := (Ico (l-H*(n^4/l)^2) l).filter fun k => (k,l) ∈ P
  have hrow (l : ℕ) (_ : l ∈ Ioc 0 (n^4)) : row l ⊆ Ioc 0 l := by
    intro k hk
    have hp := hP (k,l) (mem_filter.mp hk).2
    exact mem_Ioc.mpr ⟨hp.1,hp.2.1.le⟩
  have hc (l : ℕ) (_ : l ∈ Ioc 0 (n^4)) : (row l).card ≤ H*(n^4/l)^2 := by
    apply (card_le_card (filter_subset _ _)).trans
    rw [Nat.card_Ico]
    omega
  rw [sum_finset_product_right _ (Ioc 0 (n^4)) row]
  · exact fixedBandSparseRows_abs_le n H row hrow hc
  · rintro ⟨k,l⟩
    simp only [mem_filter, fixedBandNearby, row, mem_Ico, mem_Ioc]
    constructor
    · rintro ⟨hp,hd⟩
      obtain ⟨hk,hkl,hl⟩ := hP (k,l) hp
      exact ⟨⟨hk.trans hkl,hl⟩,⟨by omega,hkl⟩,hp⟩
    · rintro ⟨_,⟨hk,_⟩,hp⟩
      exact ⟨hp,by omega⟩

/-- Signed increasing pairs left after the reduced-ratio and nearby-pair estimates.
The factor of two includes the reverse orientation. -/
def fixedBandSeparatedRatioMass (H m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, (2*∑ p ∈ (fixedBandRatioPairs n).filter (fun p => ¬fixedBandNearby n H p),
    fixedBandTailTerm n p.1*fixedBandTailTerm n p.2)/(n:ℝ)^5

theorem fixedBandSeparatedRatioMass_error (H : ℕ) {m b : ℕ} (hm : 2 ≤ m) :
    |fixedBandRatioMass m b-fixedBandSeparatedRatioMass H m b| ≤
      2*fixedBandSparseRowConstant H*(1+log b) := by
  let C := 2*fixedBandSparseRowConstant H
  have hC : 0 ≤ C := by dsimp [C,fixedBandSparseRowConstant]; positivity
  unfold fixedBandRatioMass fixedBandSeparatedRatioMass
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Icc m b, C*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      let P := fixedBandRatioPairs n
      let w := fun p : ℕ × ℕ => fixedBandTailTerm n p.1*fixedBandTailTerm n p.2
      have hs := sum_filter_add_sum_filter_not P (fixedBandNearby n H) w
      have hp := fixedBandNearby_abs_le n H P (by
        intro p hp
        obtain ⟨hs,hlt,_⟩ := mem_filter.mp hp
        obtain ⟨hk,hl⟩ := mem_product.mp hs
        exact ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hk).1,hlt,(mem_Ioc.mp hl).2⟩)
      have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by have := (mem_Icc.mp hn).1; omega)
      change |(2*∑ p ∈ P, w p)/(n:ℝ)^5 - (2*∑ p ∈ P.filter (fun p => ¬fixedBandNearby n H p), w p)/(n:ℝ)^5| ≤ _
      rw [← sub_div,← mul_sub,← hs,add_sub_cancel_right,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
        abs_of_pos (pow_pos hn₀ _)]
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((abs_sum_le_sum_abs _ _).trans hp) (by norm_num : (0:ℝ) ≤ 2)) (pow_nonneg hn₀.le 5)).trans_eq
      dsimp only [C]; field_simp
    _ ≤ _ := weighted_harmonic_window hC hm

/-- For any fixed H, only pairs outside both discarded regions need a signed window bound. -/
theorem rh_of_fixedBandSeparatedRatioMass_log_squareWindows (H : ℕ)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandSeparatedRatioMass H m (m^2) ≤ C*(1+2*log m)) : RiemannHypothesis := by
  apply rh_of_fixedBandRatioMass_log_squareWindows
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C+2*fixedBandSparseRowConstant H,by unfold fixedBandSparseRowConstant; positivity,fun A => ?_⟩
  obtain ⟨m,hm,hw⟩ := h (max 2 A)
  have he := (abs_le.mp (fixedBandSeparatedRatioMass_error H (b := m^2) ((le_max_left 2 A).trans hm))).2
  rw [Nat.cast_pow,log_pow,Nat.cast_ofNat] at he
  exact ⟨m,(le_max_right 2 A).trans hm,by linarith only [hw,he]⟩

end RiemannGaussian.AlpogeMined
end

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBandWidePairs_abs_le,
      ``RiemannGaussian.AlpogeMined.fixedBandRatioMass_error,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandRatioMass_log_squareWindows,
      ``RiemannGaussian.AlpogeMined.fixedBandSparseRows_abs_le,
      ``RiemannGaussian.AlpogeMined.fixedBandSeparatedRatioMass_error,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandSeparatedRatioMass_log_squareWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  let imports := (← getEnv).header.moduleNames
  logInfo m!"Reduced-ratio implication uses {imports.size + 1} Lean modules including this module."
