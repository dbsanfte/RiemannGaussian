import CheckAlpogeFixedPrimeBandCentered

/-! # Quotient moments and a rational test for the fixed-band window -/

namespace RiemannGaussian.AlpogeMined

open Finset Real
open scoped ArithmeticFunction.Moebius

private def cellRamp {𝕜 : Type*} [Field 𝕜] (j : ℕ) (y : 𝕜) : 𝕜 := y*(harmonic j:𝕜)-j

private def cellLattice {𝕜 : Type*} [Field 𝕜] (j : ℕ) (y : 𝕜) : 𝕜 :=
  cellRamp j y-3*cellRamp (j/2) (y/2)+2*cellRamp (j/4) (y/4)

private def positiveLogSeries {𝕜 : Type*} [Field 𝕜] (p : ℕ) (z : 𝕜) : 𝕜 :=
  ∑ i ∈ range p, z^(i+1)/((i:𝕜)+1)

private noncomputable def cofactorBase (j : ℕ) (y : ℝ) : ℝ :=
  log 2*(cellRamp j y-cellRamp (j/2) (y/2))-(log j+fixedBandLogConstant)*cellLattice j y

/-- For quotient j, expand the variable part of log y in powers of 1-j/y. -/
noncomputable def fixedBandPolynomialKernel (p j : ℕ) (y : ℝ) : ℝ :=
  cofactorBase j y-positiveLogSeries p (1-(j:ℝ)/y)*cellLattice j y

private theorem abs_lattice_le_twice {y : ℝ} (hy : 1 ≤ y) :
    |fixedBandLattice y| ≤ 2*y := by
  have hy₀ := zero_lt_one.trans_le hy
  have he : |fixedBandLattice y-y*log 2/2| ≤ 1 := by
    rw [abs_sub_comm]
    exact fixedBand_lattice_error hy₀
  have hl : log (2:ℝ) ≤ 1 := by linarith only [log_le_sub_one_of_pos (show 0 < (2:ℝ) by norm_num)]
  have hp := mul_le_mul_of_nonneg_left hl hy₀.le
  calc
    _ = |(fixedBandLattice y-y*log 2/2)+y*log 2/2| := by ring_nf
    _ ≤ 1+|y*log 2/2| := (abs_add_le _ _).trans (add_le_add he le_rfl)
    _ ≤ 2*y := by
      rw [abs_of_nonneg (by positivity)]
      linarith only [hp, hy]

private theorem cellLattice_eq {j : ℕ} {y : ℝ} (hy : 0 ≤ y) (hq : ⌊y⌋₊ = j) :
    cellLattice j y = fixedBandLattice y := by
  rw [fixedBandLattice_ramps hy]
  have hR (d : ℕ) : fixedBandUnitRamp (y/d) = cellRamp (j/d) (y/d) := by
    simp only [fixedBandUnitRamp,cellRamp,Nat.floor_div_natCast,hq]
  have hRd : fixedBandUnitRamp y = cellRamp j y := by
    simp only [fixedBandUnitRamp,cellRamp,hq]
  rw [hRd,show fixedBandUnitRamp (y/2)=cellRamp (j/2) (y/2) by simpa using hR 2,
    show fixedBandUnitRamp (y/4)=cellRamp (j/4) (y/4) by simpa using hR 4]
  rfl

/-- The first p terms give a remainder decaying geometrically with the quotient. -/
theorem fixedBandPolynomialKernel_error {p j : ℕ} {y : ℝ} (hj : 0 < j)
    (hq : ⌊y⌋₊ = j) :
    |fixedBandCenteredKernel y-fixedBandPolynomialKernel p j y| ≤
      4/((j:ℝ)+1)^p := by
  let z := 1-(j:ℝ)/y
  have hj₀ : 0 < (j:ℝ) := Nat.cast_pos.mpr hj
  have h1j : 1 ≤ (j:ℝ) := by exact_mod_cast hj
  have hy₁ : (j:ℝ) ≤ y := by
    have hn : 0 ≤ y := by
      by_contra! h
      rw [Nat.floor_of_nonpos h.le] at hq
      omega
    rw [← hq]
    exact Nat.floor_le hn
  have hy₀ := hj₀.trans_le hy₁
  have hy₂ : y ≤ (j:ℝ)+1 := by
    have he := (Nat.lt_floor_add_one y).le
    rwa [hq] at he
  have hzy : 1-z = (j:ℝ)/y := by dsimp [z]; ring
  have hz₀ : 0 ≤ z := sub_nonneg.mpr ((div_le_one hy₀).mpr hy₁)
  have hz : z ≤ 1/((j:ℝ)+1) := by
    have he := div_le_div_of_nonneg_left hj₀.le hy₀ hy₂
    have hl : 1-(j:ℝ)/((j:ℝ)+1) = 1/((j:ℝ)+1) := by field_simp; ring
    exact (sub_le_sub_left he 1).trans_eq hl
  have hz₁ : z < 1 := hz.trans_lt ((div_lt_one (by positivity)).mpr (by linarith))
  have hg := abs_log_sub_add_sum_range_le (by rwa [abs_of_nonneg hz₀]) p
  rw [abs_of_nonneg hz₀,hzy,log_div hj₀.ne' hy₀.ne'] at hg
  change |positiveLogSeries p z + (log j-log y)| ≤ z^(p+1)/((j:ℝ)/y) at hg
  have hlog : |log y-(log j+positiveLogSeries p z)| ≤ z^(p+1)/((j:ℝ)/y) := by
    rw [show log y-(log j+positiveLogSeries p z) =
      -(positiveLogSeries p z+(log j-log y)) by ring,abs_neg]
    exact hg
  have hB := abs_lattice_le_twice (h1j.trans hy₁)
  have hR (d : ℕ) : fixedBandUnitRamp (y/d) = cellRamp (j/d) (y/d) := by
    simp only [fixedBandUnitRamp,cellRamp,Nat.floor_div_natCast,hq]
  have hRd : fixedBandUnitRamp y = cellRamp j y := by
    simp only [fixedBandUnitRamp,cellRamp,hq]
  have hR₂ : fixedBandUnitRamp (y/2) = cellRamp (j/2) (y/2) := by simpa using hR 2
  have hL : fixedBandLattice y = cellLattice j y := (cellLattice_eq hy₀.le hq).symm
  have hdiff : fixedBandCenteredKernel y-fixedBandPolynomialKernel p j y =
      -(log y-(log j+positiveLogSeries p z))*fixedBandLattice y := by
    unfold fixedBandCenteredKernel fixedBandPolynomialKernel cofactorBase
    rw [hRd,hR₂,← hL]
    dsimp only [z]
    ring
  rw [hdiff,abs_mul,abs_neg]
  have hD : 0 < (j:ℝ)/y := div_pos hj₀ hy₀
  have hscale : (2*y)/((j:ℝ)/y) ≤ 4*((j:ℝ)+1) := by
    apply (div_le_iff₀ hD).mpr
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hy₀).mpr
    have hyy := mul_le_mul hy₂ hy₂ hy₀.le (by positivity : 0 ≤ (j:ℝ)+1)
    nlinarith only [hyy, sq_nonneg (j:ℝ), h1j]
  calc
    _ ≤ (z^(p+1)/((j:ℝ)/y))*(2*y) := mul_le_mul hlog hB (abs_nonneg _) (by positivity)
    _ = z^(p+1)*((2*y)/((j:ℝ)/y)) := by ring
    _ ≤ (1/((j:ℝ)+1))^(p+1)*(4*((j:ℝ)+1)) :=
      mul_le_mul (pow_le_pow_left₀ hz₀ hz _) hscale (by positivity) (by positivity)
    _ = 4/((j:ℝ)+1)^p := by rw [div_pow,pow_succ,one_pow]; field_simp; ring

private theorem binaryWindowBudget {m : ℕ} (hm : 1 ≤ m) :
    1+(Nat.log 2 m:ℝ) ≤ 1+2*log m ∧ 1+2*log m ≤ 3*(1+(Nat.log 2 m:ℝ)) := by
  let r := Nat.log 2 m
  have hm₀ : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hr1 : (2:ℝ)^r ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
  have hr2 : (m:ℝ) ≤ (2:ℝ)^(r+1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) m).le
  have h₁ := Real.log_le_log (by positivity) hr1
  have h₂ := Real.log_le_log hm₀ hr2
  rw [log_pow] at h₁ h₂
  push_cast at h₂
  have hhalf : 1/2 ≤ log (2:ℝ) := by
    have h := log_le_sub_one_of_pos (show 0 < (1/2:ℝ) by norm_num)
    rw [one_div,log_inv] at h
    linarith only [h]
  have hlog2 : log (2:ℝ) ≤ 1 := by
    linarith only [log_le_sub_one_of_pos (show 0 < (2:ℝ) by norm_num)]
  constructor
  · nlinarith only [h₁,mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (α := ℝ) r)]
  · nlinarith only [h₂,mul_le_mul_of_nonneg_left hlog2
      (show 0 ≤ (r:ℝ)+1 by positivity),Nat.cast_nonneg (α := ℝ) r]

/-- The largest discarded multiple, computed entirely with integers. -/
def fixedBandIntegerMultipleCutoff (n : ℕ) : ℕ :=
  n^3 / (Nat.sqrt (Nat.log 2 n+1)+1)

private theorem integer_multiple_cutoff_error {n : ℕ} (hn : 2 ≤ n) :
    |dyadicContrast ((n:ℝ)^4)-fixedBandCenteredTail (n^4) (fixedBandIntegerMultipleCutoff n)| ≤
      6*(72+60*|fixedBandLogConstant|)*(n:ℝ)^2 := by
  let K := fixedBandIntegerMultipleCutoff n
  let L := Nat.log 2 n+1
  let q := Nat.sqrt L+1
  let C := 72+60*|fixedBandLogConstant|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hq : (L:ℝ) ≤ (q:ℝ)^2 := by
    exact_mod_cast (show L ≤ q^2 by simpa [q,Nat.pow_two] using (Nat.lt_succ_sqrt L).le)
  have hL : 1+4*log (n:ℝ) ≤ 6*(L:ℝ) := by
    have h := (binaryWindowBudget (show 1 ≤ n by omega)).2
    dsimp [L]
    push_cast
    linarith only [h]
  have hKn : (K:ℝ)*(q:ℝ) ≤ (n:ℝ)^3 := by
    exact_mod_cast Nat.div_mul_le_self (n^3) q
  have hKn' := pow_le_pow_left₀ (by positivity : 0 ≤ (K:ℝ)*(q:ℝ)) hKn 2
  rw [mul_pow] at hKn'
  have hE : (K:ℝ)^2*(1+4*log (n:ℝ)) ≤ 6*(n:ℝ)^6 := by
    have h := (mul_le_mul_of_nonneg_left hq (sq_nonneg (K:ℝ))).trans hKn'
    have h' := mul_le_mul_of_nonneg_left hL (sq_nonneg (K:ℝ))
    nlinarith only [h,h']
  have hN : 4 ≤ n^4 := (by decide : 4 ≤ 2^4).trans (Nat.pow_le_pow_left hn 4)
  have hKN : 2*K ≤ n^4 := by
    rw [pow_succ n 3,mul_comm (n^3)]
    exact (Nat.mul_le_mul_left 2 (Nat.div_le_self _ _)).trans (Nat.mul_le_mul_right _ hn)
  have h := fixedBandCenteredTail_error hN hKN
  rw [Nat.cast_pow,log_pow,Nat.cast_ofNat] at h
  refine h.trans ?_
  calc
    C*(K:ℝ)^2*(1+4*log n)/(n:ℝ)^4 ≤ C*(6*(n:ℝ)^6)/(n:ℝ)^4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hE hC
    _ = 6*C*(n:ℝ)^2 := by field_simp [hn₀.ne']

/-- Select enough terms at this quotient to pay the error at scale n². -/
def fixedBandPolynomialOrder (n j : ℕ) : ℕ := Nat.log (j+1) (n^2)+1

/-- The critical tail with the variable logarithm replaced on each quotient. -/
noncomputable def fixedBandPolynomialTail (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc (fixedBandIntegerMultipleCutoff n) (n^4),
    (μ k:ℝ)*fixedBandPolynomialKernel (fixedBandPolynomialOrder n (n^4/k)) (n^4/k)
      (((n^4:ℕ):ℝ)/k)

/-- The variable logarithms of the tail can all be replaced at cost O(n²). -/
theorem fixedBandPolynomialTail_error {n : ℕ} (hn : 2 ≤ n) :
    |fixedBandCenteredTail (n^4) (fixedBandIntegerMultipleCutoff n)-fixedBandPolynomialTail n| ≤
      4*(n:ℝ)^2 := by
  let N := n^4
  let K := fixedBandIntegerMultipleCutoff n
  have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  rw [fixedBandCenteredTail,fixedBandPolynomialTail,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k ∈ Ioc K N, 4/(n:ℝ)^2 := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hK,hN⟩ := mem_Ioc.mp hk
      have hk₀ : 0 < k := (Nat.zero_le K).trans_lt hK
      let j := N/k
      have hj : 0 < j := Nat.div_pos hN hk₀
      have hf : ⌊(N:ℝ)/k⌋₊ = j := by
        rw [Nat.floor_div_natCast,Nat.floor_natCast]
      have hp : (n:ℝ)^2 ≤ ((j:ℝ)+1)^(fixedBandPolynomialOrder n j) := by
        have h := (Nat.lt_pow_succ_log_self (show 1 < j+1 by omega) (n^2)).le
        exact_mod_cast h
      have hμ : |(μ k:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
      rw [← mul_sub,abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hμ).trans
        ((fixedBandPolynomialKernel_error hj hf).trans
          (div_le_div_of_nonneg_left (by norm_num) (by positivity) hp))
    _ ≤ (n:ℝ)^4*(4/(n:ℝ)^2) := by
      simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [← Nat.cast_pow]
      exact_mod_cast Nat.sub_le N K
    _ = 4*(n:ℝ)^2 := by field_simp [hn₀.ne']

/-- The clipped interval of indices with quotient j. -/
def fixedBandCofactorBlock (N K j : ℕ) : Finset ℕ :=
  Ioc (max K (N/(j+1))) (N/j)

private theorem cofactor_fiber {N K j : ℕ} (hj : 0 < j) :
    (Ioc K N).filter (fun k => N/k=j) = fixedBandCofactorBlock N K j := by
  ext k
  simp only [mem_filter,mem_Ioc,fixedBandCofactorBlock,max_lt_iff]
  constructor
  · rintro ⟨⟨hK,hN⟩,h⟩
    have hk : 0 < k := (Nat.zero_le K).trans_lt hK
    have hl := (Nat.div_lt_iff_lt_mul hk).mp (show N/k < j+1 by omega)
    have hu := (Nat.le_div_iff_mul_le hk).mp (show j ≤ N/k by omega)
    exact ⟨⟨hK,(Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mpr (by rwa [Nat.mul_comm])⟩,
      (Nat.le_div_iff_mul_le hj).mpr (by rwa [Nat.mul_comm])⟩
  · rintro ⟨⟨hK,hl⟩,hu⟩
    have hk : 0 < k := (Nat.zero_le K).trans_lt hK
    have hlo := (Nat.le_div_iff_mul_le hj).mp hu
    have hhi := (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mp hl
    have hlow : j ≤ N/k := (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hlo)
    have hhigh : N/k < j+1 := (Nat.div_lt_iff_lt_mul hk).mpr (by simpa only [Nat.mul_comm k (j+1)] using hhi)
    exact ⟨⟨hK,(Nat.le_mul_of_pos_right _ hj).trans hlo⟩,by omega⟩

private theorem sum_by_cofactor {M : Type*} [AddCommMonoid M] (N K : ℕ) (f : ℕ → ℕ → M) :
    (∑ k ∈ Ioc K N, f (N/k) k) =
      ∑ j ∈ Icc 1 (N/(K+1)), ∑ k ∈ fixedBandCofactorBlock N K j, f j k := by
  have hmap (k : ℕ) (hk : k ∈ Ioc K N) : N/k ∈ Icc 1 (N/(K+1)) := by
    obtain ⟨hK,hN⟩ := mem_Ioc.mp hk
    exact mem_Icc.mpr ⟨Nat.div_pos hN (by omega),Nat.div_le_div_left hK (Nat.succ_pos K)⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro j hj
  have hj₀ : 0 < j := (mem_Icc.mp hj).1
  rw [← cofactor_fiber hj₀]
  apply sum_congr rfl
  intro k hk
  rw [(mem_filter.mp hk).2]

/-- The polynomial tail groups into disjoint clipped quotient intervals. -/
theorem fixedBandPolynomialTail_by_cofactor (n : ℕ) :
    fixedBandPolynomialTail n =
      ∑ j ∈ Icc 1 (n^4/(fixedBandIntegerMultipleCutoff n+1)),
        ∑ k ∈ fixedBandCofactorBlock (n^4) (fixedBandIntegerMultipleCutoff n) j,
          (μ k:ℝ)*fixedBandPolynomialKernel (fixedBandPolynomialOrder n j) j (((n^4:ℕ):ℝ)/k) :=
  sum_by_cofactor (n^4) (fixedBandIntegerMultipleCutoff n)
    (fun j k => (μ k:ℝ)*fixedBandPolynomialKernel (fixedBandPolynomialOrder n j) j (((n^4:ℕ):ℝ)/k))

/-- A Möbius moment in the affine variable 1-jk/N on one quotient interval. -/
def fixedBandCofactorMoment {𝕜 : Type*} [Field 𝕜] (N K j r : ℕ) (weight : ℕ → 𝕜) : 𝕜 :=
  ∑ k ∈ fixedBandCofactorBlock N K j, (μ k:𝕜)*weight k*(1-(j:𝕜)*k/N)^r

private def affineCofactorSum {𝕜 : Type*} [Field 𝕜] (N K j r : ℕ) (w : 𝕜 → 𝕜) : 𝕜 :=
  (w 1-w 0)*N*fixedBandCofactorMoment N K j r (fun k => (k:𝕜)⁻¹) +
    w 0*fixedBandCofactorMoment N K j r (fun _ => 1)

private theorem affineCofactorSum_eq {𝕜 : Type*} [Field 𝕜] (N K j r : ℕ) {w : 𝕜 → 𝕜}
    (hw : ∀ y, w y = (w 1-w 0)*y+w 0) :
    affineCofactorSum N K j r w =
      ∑ k ∈ fixedBandCofactorBlock N K j, (μ k:𝕜)*w ((N:𝕜)/k)*(1-(j:𝕜)*k/N)^r := by
  unfold affineCofactorSum fixedBandCofactorMoment
  rw [mul_sum,mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro k _
  rw [hw ((N:𝕜)/k),div_eq_mul_inv (N:𝕜) (k:𝕜)]
  ring

private theorem cellLattice_affine {𝕜 : Type*} [Field 𝕜] (j : ℕ) (y : 𝕜) :
    cellLattice j y=(cellLattice j 1-cellLattice j 0)*y+cellLattice j 0 := by
  unfold cellLattice cellRamp
  ring

private theorem cofactorBase_affine (j : ℕ) (y : ℝ) :
    cofactorBase j y=(cofactorBase j 1-cofactorBase j 0)*y+cofactorBase j 0 := by
  unfold cofactorBase cellLattice cellRamp
  ring

private def polynomialCofactorScore {𝕜 : Type*} [Field 𝕜] (N K j p : ℕ) (base : 𝕜 → 𝕜) : 𝕜 :=
  affineCofactorSum N K j 0 base -
    ∑ i ∈ range p, affineCofactorSum N K j (i+1) (cellLattice j)/((i:𝕜)+1)

private theorem polynomialCofactorScore_eq {𝕜 : Type*} [Field 𝕜] (N K j p : ℕ)
    {base : 𝕜 → 𝕜} (h : ∀ y, base y = (base 1-base 0)*y+base 0) :
    polynomialCofactorScore N K j p base =
      ∑ k ∈ fixedBandCofactorBlock N K j, (μ k:𝕜)*
        (base ((N:𝕜)/k)-positiveLogSeries p (1-(j:𝕜)/((N:𝕜)/k))*cellLattice j ((N:𝕜)/k)) := by
  unfold polynomialCofactorScore
  rw [affineCofactorSum_eq _ _ _ _ h]
  simp only [affineCofactorSum_eq _ _ _ _ (cellLattice_affine j),pow_zero,mul_one,sum_div]
  rw [sum_comm,← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  unfold positiveLogSeries
  rw [show (j:𝕜)/((N:𝕜)/k)=(j:𝕜)*k/N by rw [div_div_eq_mul_div]]
  rw [mul_sub,sum_mul,mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

/-- Only ordinary and reciprocal power moments are needed in a quotient block. -/
noncomputable def fixedBandPolynomialCofactorScore (N K j p : ℕ) : ℝ :=
  polynomialCofactorScore N K j p (cofactorBase j)

theorem fixedBandPolynomialCofactorScore_eq (N K j p : ℕ) :
    fixedBandPolynomialCofactorScore N K j p =
      ∑ k ∈ fixedBandCofactorBlock N K j,
        (μ k:ℝ)*fixedBandPolynomialKernel p j ((N:ℝ)/k) :=
  polynomialCofactorScore_eq _ _ _ _ (cofactorBase_affine j)

/-- Evaluation of the whole tail by the two families of quotient moments. -/
theorem fixedBandPolynomialTail_eq_moments (n : ℕ) :
    fixedBandPolynomialTail n =
      ∑ j ∈ Icc 1 (n^4/(fixedBandIntegerMultipleCutoff n+1)),
        fixedBandPolynomialCofactorScore (n^4) (fixedBandIntegerMultipleCutoff n) j
          (fixedBandPolynomialOrder n j) := by
  rw [fixedBandPolynomialTail_by_cofactor]
  exact sum_congr rfl fun j _ => (fixedBandPolynomialCofactorScore_eq _ _ _ _).symm

/-- The positive window mass of the polynomial moment scores. -/
noncomputable def fixedBandPolynomialMass (m b : ℕ) : ℝ :=
  ∑ n ∈ Icc m b, max (fixedBandPolynomialTail n) 0/(n:ℝ)^3

theorem fixedBandPolynomialMass_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-fixedBandPolynomialMass m b| ≤ C*(1+log b) := by
  obtain ⟨C,hC,h⟩ := dyadicPrimeDeficit_power_cost
  let D := 6*(72+60*|fixedBandLogConstant|)+4
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C+D,by positivity,fun {m b} hm => fixedBand_mass_sqrt_error
    (x := fun n => dyadicPrimeDeficit ((n:ℝ)^4)) (y := fixedBandPolynomialTail)
    (by positivity) (fun {n} hn => ?_) hm⟩
  have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨hlo,hhi⟩ := h (pow_pos hn₀ 4)
  rw [show sqrt ((n:ℝ)^4)=(n:ℝ)^2 by rw [show (n:ℝ)^4=((n:ℝ)^2)^2 by ring,
    Real.sqrt_sq (sq_nonneg (n:ℝ))]] at hhi
  apply (abs_sub_le _ (dyadicContrast ((n:ℝ)^4)) _).trans
  rw [abs_of_nonneg hlo]
  have he := (abs_sub_le _ (fixedBandCenteredTail (n^4) (fixedBandIntegerMultipleCutoff n)) _).trans
    (add_le_add (integer_multiple_cutoff_error hn) (fixedBandPolynomialTail_error hn))
  exact (add_le_add hhi he).trans_eq (by dsimp [D]; ring)

/-- A logarithmic estimate for the moment scores suffices for RH. -/
theorem rh_of_fixedBandPolynomial_log_squareWindows
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      fixedBandPolynomialMass m (m^2) ≤ C*(1+2*log m)) : RiemannHypothesis := by
  apply rh_of_fixedBand_upper_log_squareWindows _ _ h
  obtain ⟨C,hC,herr⟩ := fixedBandPolynomialMass_error
  exact ⟨C,hC,fun {_ _} hm => (abs_le.mp (herr hm)).2⟩

private theorem cast_cellRamp (j : ℕ) (y : ℚ) :
    ((cellRamp j y : ℚ) : ℝ)=cellRamp j (y:ℝ) := by
  simp [cellRamp]

private theorem cast_cellLattice (j : ℕ) (y : ℚ) :
    ((cellLattice j y : ℚ) : ℝ)=cellLattice j (y:ℝ) := by
  simp only [cellLattice,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,
    Rat.cast_ofNat,cast_cellRamp]

private theorem cast_positiveLogSeries (p : ℕ) (z : ℚ) :
    ((positiveLogSeries p z : ℚ) : ℝ)=positiveLogSeries p (z:ℝ) := by
  simp only [positiveLogSeries,Rat.cast_sum,Rat.cast_pow,Rat.cast_add,Rat.cast_div,
    Rat.cast_natCast,Rat.cast_one]

private def harmonicScaleExponent (n : ℕ) : ℕ := Nat.log 2 (n^2)+1

private def rationalLogTwo (n : ℕ) : ℚ := positiveLogSeries (5*harmonicScaleExponent n) (1/2:ℚ)

private def rationalCofactorBase (n j : ℕ) (y : ℚ) : ℚ :=
  let r := harmonicScaleExponent n
  let l := rationalLogTwo n
  l*(cellRamp j y-cellRamp (j/2) (y/2))-
    (harmonic (2^r*j)-1-((r:ℚ)-1)*l)*cellLattice j y

/-- All the coefficients in the quotient polynomial can be chosen rationally. -/
def fixedBandRationalKernel (n j : ℕ) (y : ℚ) : ℚ :=
  rationalCofactorBase n j y-
    positiveLogSeries (fixedBandPolynomialOrder n j) (1-(j:ℚ)/y)*cellLattice j y

private theorem rationalCofactorBase_affine (n j : ℕ) (y : ℚ) :
    rationalCofactorBase n j y =
      (rationalCofactorBase n j 1-rationalCofactorBase n j 0)*y+rationalCofactorBase n j 0 := by
  unfold rationalCofactorBase cellLattice cellRamp
  ring

private theorem abs_logTwo_rational_error (n : ℕ) :
    |log 2-(rationalLogTwo n:ℝ)| ≤ 1/(2:ℝ)^(5*harmonicScaleExponent n) := by
  unfold rationalLogTwo
  rw [cast_positiveLogSeries,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  have h := abs_log_sub_add_sum_range_le (x := (1/2:ℝ)) (by norm_num) (5*harmonicScaleExponent n)
  rw [abs_of_nonneg (by norm_num : 0 ≤ (1/2:ℝ)),
    show 1-(1/2:ℝ)=1/2 by norm_num,one_div,log_inv] at h
  rw [abs_sub_comm]
  have hh : (2:ℝ)⁻¹ ^ (5*harmonicScaleExponent n+1) / (2:ℝ)⁻¹ =
      1/(2:ℝ)^(5*harmonicScaleExponent n) := by
    rw [pow_succ, mul_div_cancel_right₀ _ (by norm_num : (2:ℝ)⁻¹ ≠ 0), inv_pow, one_div]
  simpa only [positiveLogSeries,one_div,sub_eq_add_neg,hh] using h

private theorem harmonic_scaled_error {r j : ℕ} (hj : 0 < j) :
    |(harmonic (2^r*j):ℝ)-(log j+eulerMascheroniConstant+(r:ℝ)*log 2)| ≤
      1/(2*((2:ℝ)^r*(j:ℝ))) := by
  have hM : 0 < 2^r*j := Nat.mul_pos (by positivity) hj
  obtain ⟨hl,hu⟩ := AlpogeZetaSamples.harmonic_half_bounds hM
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    log_mul (by positivity : ((2:ℝ)^r) ≠ 0) (Nat.cast_ne_zero.mpr hj.ne'),
    log_pow] at hl hu
  rw [abs_of_nonneg (by linarith only [hl, show 0 ≤ 1/(2*((2:ℝ)^r*(j:ℝ)+1)) by positivity])]
  linarith only [hu]

private theorem abs_harmonic_le_index (j : ℕ) : |(harmonic j:ℝ)| ≤ j := by
  have h₀ : 0 ≤ (harmonic j:ℝ) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    exact sum_nonneg fun _ _ => by positivity
  rw [abs_of_nonneg h₀]
  by_cases hj : j=0
  · simp [hj]
  · have h := log_le_sub_one_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj) : 0 < (j:ℝ))
    exact (harmonic_le_one_add_log j).trans (by linarith)

private theorem abs_cellRamp_le {j : ℕ} {y t : ℝ} (hy : 0 ≤ y) (hyt : y ≤ t)
    (hjt : (j:ℝ) ≤ t) (ht : 1 ≤ t) : |cellRamp j y| ≤ 2*t^2 := by
  unfold cellRamp
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg hy,show |(j:ℝ)|=(j:ℝ) from abs_of_nonneg (Nat.cast_nonneg j)]
  have h₀ : y*|(harmonic j:ℝ)| ≤ t*t :=
    mul_le_mul hyt ((abs_harmonic_le_index j).trans hjt) (abs_nonneg _) (by linarith)
  nlinarith only [h₀,hjt, mul_nonneg (show 0 ≤ t by linarith) (show 0 ≤ t-1 by linarith)]

private theorem abs_cellRampDifference_le {j : ℕ} {y : ℝ} (hy : 1 ≤ y) (hj : (j:ℝ) ≤ y) :
    |cellRamp j y-cellRamp (j/2) (y/2)| ≤ 4*y^2 := by
  have hj' : ((j/2:ℕ):ℝ) ≤ y := (Nat.cast_le.mpr (Nat.div_le_self j 2)).trans hj
  exact (abs_sub _ _).trans ((add_le_add
    (abs_cellRamp_le (by linarith) le_rfl hj hy)
    (abs_cellRamp_le (by linarith) (by linarith) hj' hy)).trans_eq (by ring))

private theorem rationalKernel_error {n j : ℕ} {v : ℚ} (hn : 2 ≤ n) (hj : 0 < j)
    (hq : ⌊(v:ℝ)⌋₊ = j) (h1 : 1 ≤ (v:ℝ)) (hN : (v:ℝ) ≤ (n:ℝ)^4) :
    |fixedBandPolynomialKernel (fixedBandPolynomialOrder n j) j v-
      (fixedBandRationalKernel n j v:ℝ)| ≤ 8/(n:ℝ)^2 := by
  let y := (v:ℝ)
  let r := harmonicScaleExponent n
  let l := (rationalLogTwo n:ℝ)
  let A := cellRamp j y-cellRamp (j/2) (y/2)
  let B := cellLattice j y
  have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hj₀ : 0 < (j:ℝ) := Nat.cast_pos.mpr hj
  have h1j : 1 ≤ (j:ℝ) := by exact_mod_cast hj
  have hlow : (j:ℝ) ≤ y := by rw [← hq]; exact Nat.floor_le (by linarith)
  have hhi : y ≤ (j:ℝ)+1 := by
    have h := (Nat.lt_floor_add_one y).le
    rwa [hq] at h
  have hB : |B| ≤ 2*y := by
    dsimp only [B]
    rw [cellLattice_eq (by linarith : 0 ≤ y) hq]
    exact abs_lattice_le_twice h1
  have hL : (n:ℝ)^2 ≤ (2:ℝ)^r := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n^2)).le
  have hlogN : |log 2-l| ≤ 1/(n:ℝ)^10 := by
    apply (abs_logTwo_rational_error n).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h := pow_le_pow_left₀ (sq_nonneg (n:ℝ)) hL 5
    simpa only [← pow_mul,show 2*5=10 by decide,mul_comm r 5] using h
  have hGauss := harmonic_scaled_error (r := r) hj
  have hGam :
      |(harmonic (2^r*j):ℝ)-(log j+eulerMascheroniConstant+(r:ℝ)*log 2)| * |B| ≤
        2/(n:ℝ)^2 := by
    apply (mul_le_mul hGauss hB (abs_nonneg _) (by positivity)).trans
    calc
      _ = (y/(j:ℝ))/(2:ℝ)^r := by field_simp
      _ ≤ 2/(2:ℝ)^r := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact (div_le_iff₀ hj₀).mpr (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) hL
  have hr0 : 0 ≤ (r:ℝ)-1 := by
    simp [r,harmonicScaleExponent, Nat.cast_add]
  have hrN : (r:ℝ)-1 ≤ (n:ℝ)^4 := by
    have h := Nat.log_le_self 2 (n^2)
    have h' : (Nat.log 2 (n^2):ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast h
    dsimp only [r,harmonicScaleExponent]
    push_cast
    simpa only [add_sub_cancel_right] using h'.trans
      (pow_le_pow_right₀ (show 1 ≤ (n:ℝ) by exact_mod_cast (show 1 ≤ n by omega)) (by decide : 2 ≤ 4))
  have hcoef : |A+((r:ℝ)-1)*B| ≤ 6*(n:ℝ)^8 := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg hr0]
    have hA := (abs_cellRampDifference_le h1 hlow).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ y) hN 2)
        (by norm_num : (0:ℝ) ≤ 4))
    have hBB := mul_le_mul hrN (hB.trans (mul_le_mul_of_nonneg_left hN (by norm_num)))
      (abs_nonneg _) (by positivity : 0 ≤ (n:ℝ)^4)
    exact (add_le_add hA hBB).trans_eq (by ring)
  have hdiff : fixedBandPolynomialKernel (fixedBandPolynomialOrder n j) j v-
      (fixedBandRationalKernel n j v:ℝ) =
        (log 2-l)*(A+((r:ℝ)-1)*B) +
          ((harmonic (2^r*j):ℝ)-(log j+eulerMascheroniConstant+(r:ℝ)*log 2))*B := by
    unfold fixedBandPolynomialKernel cofactorBase fixedBandRationalKernel rationalCofactorBase
    simp only [Rat.cast_sub,Rat.cast_mul,Rat.cast_one,Rat.cast_div,
      Rat.cast_ofNat,Rat.cast_natCast,cast_cellLattice,cast_cellRamp,cast_positiveLogSeries]
    dsimp [A,B,y,l,r,fixedBandLogConstant]
    ring
  rw [hdiff]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  have hlog := mul_le_mul hlogN hcoef (abs_nonneg _) (by positivity)
  exact (add_le_add hlog hGam).trans_eq (by field_simp [hn₀.ne']; norm_num)

/-- The quotient score evaluated by the two families of exact rational moments. -/
def fixedBandRationalCofactorScore (n N K j : ℕ) : ℚ :=
  polynomialCofactorScore N K j (fixedBandPolynomialOrder n j) (rationalCofactorBase n j)

/-- The rational weight of an actual multiple k at the fourth-power sample. -/
def fixedBandRationalWeight (n k : ℕ) : ℚ :=
  fixedBandRationalKernel n (n^4/k) (((n^4:ℕ):ℚ)/k)

/-- Pointwise rationalization at critical accuracy, including all the multiples
in the quadratic form. -/
theorem fixedBandRationalWeight_error {n k : ℕ} (hn : 2 ≤ n) (hk : k ∈ Ioc 0 (n^4)) :
    |fixedBandCenteredKernel (((n^4:ℕ):ℝ)/k)-(fixedBandRationalWeight n k:ℝ)| ≤
      12/(n:ℝ)^2 := by
  let N := n^4
  let j := N/k
  let y : ℚ := (N:ℚ)/k
  obtain ⟨hk₀,hkN⟩ := mem_Ioc.mp hk
  have hkR : 0 < (k:ℝ) := Nat.cast_pos.mpr hk₀
  have hj : 0 < j := Nat.div_pos hkN hk₀
  have hy : (y:ℝ) = (N:ℝ)/k := by simp [y]
  have hq : ⌊(y:ℝ)⌋₊ = j := by rw [hy,Nat.floor_div_natCast,Nat.floor_natCast]
  have h1 : 1 ≤ (y:ℝ) := by
    rw [hy]
    exact (one_le_div hkR).mpr (by exact_mod_cast hkN)
  have hN : (y:ℝ) ≤ (n:ℝ)^4 := by
    rw [hy,← Nat.cast_pow]
    exact div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hk₀)
  have hp : (n:ℝ)^2 ≤ ((j:ℝ)+1)^(fixedBandPolynomialOrder n j) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (show 1 < j+1 by omega) (n^2)).le
  have he : |fixedBandCenteredKernel y-fixedBandPolynomialKernel (fixedBandPolynomialOrder n j) j y| ≤
      4/(n:ℝ)^2 := (fixedBandPolynomialKernel_error hj hq).trans
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) hp)
  rw [← hy]
  change |fixedBandCenteredKernel y-(fixedBandRationalKernel n j y:ℝ)| ≤ _
  exact (abs_sub_le _ (fixedBandPolynomialKernel (fixedBandPolynomialOrder n j) j y) _).trans
    ((add_le_add he (rationalKernel_error hn hj hq h1 hN)).trans_eq (by ring))

/-- The rational tail can be evaluated one clipped quotient block at a time. -/
def fixedBandRationalTail (n : ℕ) : ℚ :=
  ∑ j ∈ Icc 1 (n^4/(fixedBandIntegerMultipleCutoff n+1)),
    fixedBandRationalCofactorScore n (n^4) (fixedBandIntegerMultipleCutoff n) j

theorem fixedBandRationalTail_eq_sum (n : ℕ) :
    fixedBandRationalTail n =
      ∑ k ∈ Ioc (fixedBandIntegerMultipleCutoff n) (n^4),
        (μ k:ℚ)*fixedBandRationalKernel n (n^4/k) (((n^4:ℕ):ℚ)/k) := by
  rw [sum_by_cofactor (n^4) (fixedBandIntegerMultipleCutoff n)
    (fun j k => (μ k:ℚ)*fixedBandRationalKernel n j (((n^4:ℕ):ℚ)/k))]
  unfold fixedBandRationalTail
  exact sum_congr rfl fun j _ => polynomialCofactorScore_eq _ _ _ _ (rationalCofactorBase_affine n j)

theorem fixedBandRationalTail_error {n : ℕ} (hn : 2 ≤ n) :
    |fixedBandPolynomialTail n-(fixedBandRationalTail n:ℝ)| ≤ 8*(n:ℝ)^2 := by
  let N := n^4
  let K := fixedBandIntegerMultipleCutoff n
  have hn₀ : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  simp only [fixedBandRationalTail_eq_sum,Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast,
    fixedBandPolynomialTail,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _k ∈ Ioc K N, 8/(n:ℝ)^2 := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hK,hN⟩ := mem_Ioc.mp hk
      have hk₀ : 0 < k := (Nat.zero_le K).trans_lt hK
      have hkR : 0 < (k:ℝ) := Nat.cast_pos.mpr hk₀
      let y : ℚ := (N:ℚ)/k
      let j := N/k
      have hj : 0 < j := Nat.div_pos hN hk₀
      have hy : (y:ℝ) = (N:ℝ)/k := by simp [y]
      have hq : ⌊(y:ℝ)⌋₊ = j := by
        rw [hy,Nat.floor_div_natCast,Nat.floor_natCast]
      have h1 : 1 ≤ (y:ℝ) := by
        rw [hy]
        exact (one_le_div hkR).mpr (by exact_mod_cast hN)
      have hN' : (y:ℝ) ≤ (n:ℝ)^4 := by
        rw [hy,← Nat.cast_pow]
        exact div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hk₀)
      have hμ : |(μ k:ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
      rw [← mul_sub,abs_mul]
      apply (mul_le_of_le_one_left (abs_nonneg _) hμ).trans
      have h := rationalKernel_error hn hj hq h1 hN'
      rw [hy] at h
      exact h
    _ ≤ (n:ℝ)^4*(8/(n:ℝ)^2) := by
      simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [← Nat.cast_pow]
      exact_mod_cast Nat.sub_le N K
    _ = 8*(n:ℝ)^2 := by field_simp [hn₀.ne']

/-- Positive-part mass formed with exact rational arithmetic. -/
def fixedBandRationalMass (m b : ℕ) : ℚ :=
  ∑ n ∈ Icc m b, max (fixedBandRationalTail n) 0/(n:ℚ)^3

theorem fixedBandRationalMass_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-(fixedBandRationalMass m b:ℝ)| ≤ C*(1+log b) := by
  obtain ⟨C,hC,h⟩ := fixedBandPolynomialMass_error
  refine ⟨C+8,by positivity,fun {m b} hm => ?_⟩
  have hr : |fixedBandPolynomialMass m b-(fixedBandRationalMass m b:ℝ)| ≤ 8*(1+log b) := by
    simpa only [fixedBandPolynomialMass,fixedBandRationalMass,Rat.cast_sum,Rat.cast_div,
      Rat.cast_max,Rat.cast_zero,Rat.cast_pow,Rat.cast_natCast] using
        (fixedBand_mass_sqrt_error (C := 8) (by norm_num) fixedBandRationalTail_error (b := b) hm)
  exact (abs_sub_le _ (fixedBandPolynomialMass m b) _).trans
    ((add_le_add (h hm) hr).trans_eq (by ring))

/-- A single integer pays the rational masses on arbitrarily late square windows. -/
def fixedBandIntegerWindowBound (mass : ℕ → ℕ → ℚ) : Prop :=
  ∃ C : ℕ, ∀ A : ℕ, ∃ m ≥ A, 2 ≤ m ∧
    mass m (m^2) ≤ (C:ℚ)*(1+(Nat.log 2 m:ℚ))

def fixedBandRationalWindowBound : Prop := fixedBandIntegerWindowBound fixedBandRationalMass

theorem fixedBandIntegerWindowBound_iff_log (mass : ℕ → ℕ → ℚ) : fixedBandIntegerWindowBound mass ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      (mass m (m^2):ℝ) ≤ C*(1+2*log m) := by
  constructor
  · rintro ⟨C,h⟩
    refine ⟨C,by positivity,fun A => ?_⟩
    obtain ⟨m,hm,hm₂,hM⟩ := h A
    refine ⟨m,hm,?_⟩
    have h' : (mass m (m^2):ℝ) ≤ (C:ℝ)*(1+(Nat.log 2 m:ℝ)) := by
      exact_mod_cast hM
    exact h'.trans (mul_le_mul_of_nonneg_left (binaryWindowBudget (by omega)).1 (Nat.cast_nonneg C))
  · rintro ⟨C,hC,h⟩
    refine ⟨⌈3*C⌉₊,fun A => ?_⟩
    obtain ⟨m,hm,hM⟩ := h (max 2 A)
    have hm₂ : 2 ≤ m := (le_max_left 2 A).trans hm
    refine ⟨m,(le_max_right 2 A).trans hm,hm₂,?_⟩
    have h' : (mass m (m^2):ℝ) ≤ (⌈3*C⌉₊:ℝ)*(1+(Nat.log 2 m:ℝ)) := by
      calc
        _ ≤ C*(1+2*log m) := hM
        _ ≤ C*(3*(1+(Nat.log 2 m:ℝ))) :=
          mul_le_mul_of_nonneg_left (binaryWindowBudget (by omega)).2 hC
        _ = (3*C)*(1+(Nat.log 2 m:ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
    exact_mod_cast h'

theorem fixedBandRationalWindowBound_iff_log : fixedBandRationalWindowBound ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A,
      (fixedBandRationalMass m (m^2):ℝ) ≤ C*(1+2*log m) :=
  fixedBandIntegerWindowBound_iff_log fixedBandRationalMass

/-- An additive logarithmic error preserves the rational cofinal window test. -/
theorem fixedBandIntegerWindowBound_iff_prime (mass : ℕ → ℕ → ℚ)
    (herr : ∃ K : ℝ, 0 ≤ K ∧ ∀ {m b : ℕ}, 2 ≤ m →
      |fixedBandMass m b-(mass m b:ℝ)| ≤ K*(1+log b)) :
    fixedBandIntegerWindowBound mass ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℕ, ∃ m ≥ A, fixedBandMass m (m^2) ≤ C*(1+2*log m) := by
  rw [fixedBandIntegerWindowBound_iff_log]
  obtain ⟨K,hK,he⟩ := herr
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C+K,by positivity,fun A => ?_⟩ <;>
    obtain ⟨m,hm,hM⟩ := h (max 2 A)
  all_goals
    have hdiff := abs_le.mp (he (b := m^2) ((le_max_left _ _).trans hm))
    rw [Nat.cast_pow,log_pow,Nat.cast_ofNat] at hdiff
    exact ⟨m,(le_max_right _ _).trans hm,by linarith only [hdiff.1,hdiff.2,hM]⟩

/-- The complete rational cofinal window estimate implies RH. -/
theorem rh_of_fixedBandRationalWindowBound (h : fixedBandRationalWindowBound) :
    RiemannHypothesis := by
  apply rh_of_fixedBand_upper_log_squareWindows (fun m b => (fixedBandRationalMass m b:ℝ)) _
    (fixedBandRationalWindowBound_iff_log.mp h)
  obtain ⟨C,hC,herr⟩ := fixedBandRationalMass_error
  exact ⟨C,hC,fun {_ _} hm => (abs_le.mp (herr hm)).2⟩

end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBandPolynomialTail_eq_moments,
      ``RiemannGaussian.AlpogeMined.fixedBandRationalTail_eq_sum,
      ``RiemannGaussian.AlpogeMined.fixedBandRationalTail_error,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandRationalWindowBound] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  let imports := (← getEnv).header.moduleNames
  logInfo m!"Rational arithmetic implication uses {imports.size + 1} Lean modules including this module."
