/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszFewBinCoverFloor
import RiemannGaussian.ZetaRieszCycleCorrelation
import RiemannGaussian.ZetaRieszAdaptiveRateAudit
import RiemannGaussian.TrigonometricLinearEnclosure

set_option autoImplicit false

/-!
# Cofactor bins do not supply orthogonal owner-period phases

The owner log compensates the cofactor log inside the actual phase. This
audit retains signed cross terms across all counts and occupied patterns.
It gives a lower bound on coherent quadratic cost, a signed tangent bound
for literal atoms, and an exact nonzero complete-period model. None is a
source-scale payment or an estimate for the numerical floor.
-/

noncomputable section
open Real MeasureTheory Set
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszManyBinPhaseAudit
open ZetaArithmeticBandCorrelation ZetaRieszPairMidpoint

/-- Moving the owner centre with its literal cofactor leaves one common
total-log phase, regardless of that cofactor's occupied bins or count. -/
theorem recentered_owner_phase (v y b t : ℝ) :
    unitPhase (-y*((v-b+t)+b))=unitPhase (-y*(v+t)) := by
  congr 1
  ring

/-- On an actual owner-prime fibre the offset is the TOTAL-log offset.
There is no independent cofactor-bin frequency on the right. -/
theorem literal_owner_phase (v y : ℝ) (a p : ℕ) :
    unitPhase (-y*(log p+log a))=
      unitPhase (-y*(v+(log p+log a-v))) := by
  congr 1
  ring

/-- The full allocation and original Riesz coefficient retain the same
exact phase factor as the original factorial kernel. -/
theorem residual_atom_phase (A : Finset ℕ) (L y : ℝ) (N n : ℕ) :
    ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n =
      (ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2) n)*unitPhase (-y*log n) := by
  have hk : zetaPrimeLogKernel N (3/2+Complex.I*y) n =
      zetaPrimeLogKernel N (3/2) n*unitPhase (-y*log n) := by
    rw [← ZetaRieszJointAllocation.filter_one_eq,
      ← ZetaRieszJointAllocation.filter_one_eq]
    exact filterKernel_phase 1 N y n
  rw [hk,mul_assoc]

/-- The unchanged atom is one SIGNED real amplitude times its original
cosine. In particular, count and bin masks need not be relaxed. -/
theorem re_residual_atom (A : Finset ℕ) (L y : ℝ) (N n : ℕ) :
    (ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re =
      ((1-ZetaRieszJointAllocation.boundedShare A N n)*
        (SquarefreeVaughanLogSource.coefficient L n).re*
        (exp (-(3/2 : ℝ)*log n)*log n^N/N.factorial))*cos (y*log n) := by
  rw [ZetaRieszJointAllocation.residualCoefficient,mul_assoc,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    ← ZetaRieszJointAllocation.filter_one_eq,
    ZetaRieszCosineCarrier.re_coefficient_filter_one]
  ring

/-- Near a cosine peak the literal joined real sum keeps its SIGNED
zero-height sum; only the quadratic angular error is charged. This holds
for every finite original selection, including all counts and bin patterns. -/
theorem literal_signed_peak_bounds (S A : Finset ℕ) (L y v : ℝ)
    (N : ℕ) (hv : sin (y*v)=0) :
    let b := fun n => (1-ZetaRieszJointAllocation.boundedShare A N n)*
      (SquarefreeVaughanLogSource.coefficient L n).re*
      (exp (-(3/2 : ℝ)*log n)*log n^N/N.factorial)
    let J := (∑ n∈S,ZetaRieszJointAllocation.residualCoefficient A L N n*
      zetaPrimeLogKernel N (3/2+Complex.I*y) n).re
    let D := ∑ n∈S, |b n| * (y*(log n-v))^2/2
    cos (y*v)*(∑ n∈S,b n)-D≤J ∧ J≤cos (y*v)*(∑ n∈S,b n)+D := by
  dsimp only
  let b := fun n => (1-ZetaRieszJointAllocation.boundedShare A N n)*
      (SquarefreeVaughanLogSource.coefficient L n).re*
      (exp (-(3/2 : ℝ)*log n)*log n^N/N.factorial)
  have hb n : |b n*(cos (y*log n)-cos (y*v))|≤
      |b n| * (y*(log n-v))^2/2 := by
    have h := TrigonometricLinearEnclosure.cos_tangent_error (y*log n) (y*v)
    rw [hv,zero_mul,add_zero] at h
    rw [abs_mul]
    simpa only [mul_sub,mul_div_assoc] using
      mul_le_mul_of_nonneg_left h (abs_nonneg (b n))
  have hsum := (Finset.abs_sum_le_sum_abs (fun n =>
    b n*(cos (y*log n)-cos (y*v))) S).trans (Finset.sum_le_sum (fun n _ => hb n))
  have he : (∑ n∈S,b n*(cos (y*log n)-cos (y*v))) =
      (∑ n∈S,ZetaRieszJointAllocation.residualCoefficient A L N n*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n).re-cos (y*v)*(∑ n∈S,b n) := by
    rw [Complex.re_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by rw [re_residual_atom]; dsimp [b]; ring)
  rw [he] at hsum
  have hh := abs_le.mp hsum
  constructor <;> linarith only [hh.1,hh.2]

/-- A common phase preserves the full signed sum and every cross term. -/
theorem common_phase_norm {ι : Type*} (S : Finset ι) (b : ι → ℝ) (t : ℝ) :
    ‖∑ i∈S,(b i : ℂ)*unitPhase t‖=|∑ i∈S,b i| := by
  rw [← Finset.sum_mul,← Complex.ofReal_sum,norm_mul,norm_unitPhase,mul_one,
    Complex.norm_real,Real.norm_eq_abs]

/-- For nonnegative coherent bin columns, the squared cost contains all
off-diagonal products. Counting occupied bins does not diagonalize it. -/
theorem coherent_energy {ι : Type*} (S : Finset ι) (b : ι → ℝ) (t : ℝ) :
    ‖∑ i∈S,(b i : ℂ)*unitPhase t‖^2=(∑ i∈S,b i)^2 := by
  rw [common_phase_norm,sq_abs]

/-- With m identical columns, the joint cost is m times its diagonal
cost, rather than reduced by a square-root orthogonality factor. -/
theorem unit_columns_energy {ι : Type*} (S : Finset ι) (t : ℝ) :
    ‖∑ _i∈S,unitPhase t‖^2=
      (S.card : ℝ)*(∑ _i∈S,‖unitPhase t‖^2) := by
  have h := coherent_energy S (fun _ => 1) t
  simpa only [Complex.ofReal_one,one_mul,Finset.sum_const,nsmul_eq_mul,
    mul_one,norm_unitPhase,one_pow,pow_two] using h

/-- Slightly different total logs can still have uniformly positive
cross terms. This estimate is independent of all cofactor bin locations. -/
theorem cos_small_lower {x : ℝ} (hx : |x|≤1/4) : 31/32≤cos x := by
  have h := (abs_le.mp (TrigonometricLinearEnclosure.cos_tangent_error x 0)).1
  simp only [cos_zero,sin_zero,zero_mul,add_zero,sub_zero] at h
  have hsq := pow_le_pow_left₀ (abs_nonneg x) hx 2
  rw [sq_abs] at hsq
  nlinarith only [h,hsq]

/-- Demodulation keeps the common SIGNED amplitude. It does not replace
individual bins or count classes by their absolute values. -/
theorem demodulated_sum_re {ι : Type*} (S : Finset ι) (b φ : ι → ℝ) (v : ℝ) :
    (unitPhase (-v)*(∑ i∈S,(b i : ℂ)*unitPhase (φ i))).re =
      ∑ i∈S,b i*cos (φ i-v) := by
  rw [Finset.mul_sum,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : unitPhase (-v)*((b i : ℂ)*unitPhase (φ i))=
      (b i : ℂ)*unitPhase (φ i-v) := by
    rw [sub_eq_add_neg,unitPhase_add]
    ring
  rw [he,unitPhase_eq_cos_sin]
  simp only [Complex.mul_re,Complex.add_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,zero_mul,mul_zero,
    sub_zero,add_zero]

/-- Coherent signed layers in a common phase cell retain at least31/32
of their total mass, however many occupied cofactor bins they have. -/
theorem coherent_cell_lower {ι : Type*} (S : Finset ι) (b φ : ι → ℝ) (v : ℝ)
    (hb : ∀ i∈S,0≤b i) (hφ : ∀ i∈S,|φ i-v|≤1/4) :
    (31/32 : ℝ)*(∑ i∈S,b i)≤‖∑ i∈S,(b i : ℂ)*unitPhase (φ i)‖ := by
  have hr : (31/32 : ℝ)*(∑ i∈S,b i)≤
      (unitPhase (-v)*(∑ i∈S,(b i : ℂ)*unitPhase (φ i))).re := by
    rw [demodulated_sum_re,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (cos_small_lower (hφ i hi)) (hb i hi)
  apply hr.trans
  simpa only [norm_mul,norm_unitPhase,one_mul] using
    Complex.re_le_norm (unitPhase (-v)*(∑ i∈S,(b i : ℂ)*unitPhase (φ i)))

/-- Even a factor one-half PER occupied bin gives only a polynomial
discount on the literal at-most2log(N+1)+1 bin grid. This is a rate
comparison, not a lower bound for the actual arithmetic cost. -/
theorem binary_bin_discount_lower (N b : ℕ)
    (hb : (b : ℝ)≤2*log ((N : ℝ)+1)+1) :
    exp (-1 : ℝ)/((N : ℝ)+1)^2≤(1/2 : ℝ)^b := by
  have hx : (0 : ℝ)<(N : ℝ)+1 := by positivity
  have hl : log (2 : ℝ)≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith only [h]
  have hmul : (b : ℝ)*log 2≤2*log ((N : ℝ)+1)+1 :=
    (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg b)).trans (by simpa using hb)
  have hp : (2 : ℝ)^b≤exp 1*((N : ℝ)+1)^2 := by
    calc
      _ = exp ((b : ℝ)*log 2) := by rw [exp_nat_mul,exp_log (by norm_num)]
      _ ≤ exp (2*log ((N : ℝ)+1)+1) := exp_le_exp.mpr hmul
      _ = _ := by
        rw [exp_add,show (2 : ℝ)*log ((N : ℝ)+1)=((2 : ℕ) : ℝ)*log ((N : ℝ)+1) by norm_num,
          exp_nat_mul,exp_log hx]
        ring
  have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ)<(2 : ℝ)^b) hp
  calc
    _ = 1/(exp 1*((N : ℝ)+1)^2) := by rw [exp_neg]; field_simp
    _ ≤ 1/(2 : ℝ)^b := h
    _ = _ := by rw [one_div_pow,one_div]

/-- Halving each possible occupied-bin contribution cannot pay the
source-growing common period envelope. This assertion concerns THAT
envelope only, not the signed prime sum or its true population measure. -/
theorem binary_bin_discount_source_tendsto {u : ℝ} (hu : 1/2<u) (b : ℕ → ℕ)
    (hb : ∀ N,(b N : ℝ)≤2*log ((N : ℝ)+1)+1) :
    Filter.Tendsto (fun N : ℕ => (1/2 : ℝ)^(b N)*(2*u)^N/((N : ℝ)+1)^5)
      Filter.atTop Filter.atTop := by
  have ht := (ZetaRieszShiftedCenter.polynomial_source_ratio_tendsto hu 7).const_mul_atTop
    (exp_pos (-1 : ℝ))
  apply Filter.tendsto_atTop_mono' Filter.atTop ?_ ht
  filter_upwards [] with N
  have hm := mul_le_mul_of_nonneg_right (binary_bin_discount_lower N (b N) (hb N))
    (by positivity : 0≤(2*u)^N/((N : ℝ)+1)^5)
  convert hm using 1 <;> field_simp

/-- Odd log-grid indices force EVERY active subset at one grid index
to have the same parity, even when those indices occupy many scales. -/
theorem odd_grid_subset_sign {ι : Type*} (S : Finset ι) (w : ι → ℕ)
    (hw : ∀ i∈S,Odd (w i)) :
    (-1 : ℝ)^S.card=(-1 : ℝ)^(∑ i∈S,w i) := by
  calc
    (-1 : ℝ)^S.card = ∏ _i∈S,(-1 : ℝ) := by simp
    _ = ∏ i∈S,(-1 : ℝ)^(w i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (hw i hi).neg_one_pow.symm
    _ = _ := Finset.prod_pow_eq_pow_sum S w (-1)

/-- In a single odd-grid active layer, nonnegative hinge weights all
reinforce. The assertion holds for arbitrary finite selected subsets. -/
theorem odd_grid_layer_no_cancellation {ι : Type*} (S : Finset ι)
    (w : ι → ℕ) (U : Finset (Finset ι)) (k : ℕ) (b : Finset ι → ℝ)
    (hw : ∀ i∈S,Odd (w i)) (hU : ∀ V∈U,V⊆S ∧ ∑ i∈V,w i=k)
    (hb : ∀ V∈U,0≤b V) :
    |∑ V∈U,(-1 : ℝ)^V.card*b V|=∑ V∈U,b V := by
  have he : (∑ V∈U,(-1 : ℝ)^V.card*b V)=(-1 : ℝ)^k*(∑ V∈U,b V) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro V hV
    rw [odd_grid_subset_sign V w (fun i hi => hw i ((hU V hV).1 hi)),(hU V hV).2]
  rw [he,abs_mul,abs_pow]
  norm_num only [abs_neg,abs_one,one_pow,one_mul]
  exact abs_of_nonneg (Finset.sum_nonneg hb)

/-- Deleting ANY cofactor prime expands the same joined two-hinge
response into four hinges. No new arithmetic observation is produced. -/
theorem two_hinge_delete {a r : ℕ} (ha : Squarefree a) (hr : r∈a.primeFactors)
    (x L : ℝ) :
    VaughanLogAverage.riesz x a-VaughanLogAverage.riesz L a =
      (VaughanLogAverage.riesz x (a/r)-VaughanLogAverage.riesz (x-log r) (a/r))-
        (VaughanLogAverage.riesz L (a/r)-VaughanLogAverage.riesz (L-log r) (a/r)) := by
  have hp := Nat.prime_of_mem_primeFactors hr
  have hfac : r*(a/r)=a := Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hr)
  have hs : Squarefree (r*(a/r)) := hfac.symm ▸ ha
  have hn : ¬r∣a/r := hp.coprime_iff_not_dvd.mp (Nat.squarefree_mul_iff.mp hs).1
  have he t := ZetaSquarefreeRieszWindows.riesz_prime_mul t hp hn
  rw [hfac] at he
  rw [he x,he L]

/-- Retaining the complete common original weight makes every marked
cofactor incidence have exactly the same squared cost as the original. -/
theorem weighted_deletion_energy {a r : ℕ} (ha : Squarefree a) (hr : r∈a.primeFactors)
    (x L : ℝ) (w : ℂ) :
    ‖w*((VaughanLogAverage.riesz x (a/r)-VaughanLogAverage.riesz (x-log r) (a/r)-
      (VaughanLogAverage.riesz L (a/r)-VaughanLogAverage.riesz (L-log r) (a/r)) : ℝ) : ℂ)‖^2 =
      ‖w*((VaughanLogAverage.riesz x a-VaughanLogAverage.riesz L a : ℝ) : ℂ)‖^2 := by
  rw [← two_hinge_delete ha hr]

/-- For ACTUAL squarefree cofactors, averaging complete deletion energies
first within bins and then over occupied bins costs exactly the original
two-hinge energy. Thus a Cauchy step on these literal incidences has no
automatic bin saving. Arbitrary common masks, phase and factorial weight
are retained in w; cancellation across different labels is not excluded. -/
theorem bin_deletion_energy_exact (N : ℕ) {a : ℕ} (ha : Squarefree a)
    (hB : (ZetaRieszFewBinCoverFloor.cofactorBins N a).Nonempty) (x L : ℝ) (w : ℂ) :
    let B := ZetaRieszFewBinCoverFloor.cofactorBins N a
    let P := fun i : ℕ => a.primeFactors.filter (fun r : ℕ =>
      ZetaRieszFewBinCoverFloor.binHead N<log r ∧ ZetaRieszFewBinCoverFloor.primeBin N r=i)
    (∑ i∈B,(∑ r∈P i,
      ‖w*((VaughanLogAverage.riesz x (a/r)-VaughanLogAverage.riesz (x-log r) (a/r)-
        (VaughanLogAverage.riesz L (a/r)-VaughanLogAverage.riesz (L-log r) (a/r)) : ℝ) : ℂ)‖^2)/
      ((P i).card : ℝ))/(B.card : ℝ) =
        ‖w*((VaughanLogAverage.riesz x a-VaughanLogAverage.riesz L a : ℝ) : ℂ)‖^2 := by
  dsimp only
  let B := ZetaRieszFewBinCoverFloor.cofactorBins N a
  let P := fun i : ℕ => a.primeFactors.filter (fun r : ℕ =>
    ZetaRieszFewBinCoverFloor.binHead N<log r ∧ ZetaRieszFewBinCoverFloor.primeBin N r=i)
  let C := ‖w*((VaughanLogAverage.riesz x a-VaughanLogAverage.riesz L a : ℝ) : ℂ)‖^2
  have hP i (hi : i∈B) : (P i).Nonempty := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hi
    obtain ⟨hra,hrhead⟩ := Finset.mem_filter.mp hr
    exact ⟨r,Finset.mem_filter.mpr ⟨hra,hrhead,he⟩⟩
  have he i (hi : i∈B) : (∑ r∈P i,
      ‖w*((VaughanLogAverage.riesz x (a/r)-VaughanLogAverage.riesz (x-log r) (a/r)-
        (VaughanLogAverage.riesz L (a/r)-VaughanLogAverage.riesz (L-log r) (a/r)) : ℝ) : ℂ)‖^2)/
        ((P i).card : ℝ)=C := by
    have hc : ((P i).card : ℝ)≠0 := Nat.cast_ne_zero.mpr (hP i hi).card_ne_zero
    have hh : (∑ r∈P i,
      ‖w*((VaughanLogAverage.riesz x (a/r)-VaughanLogAverage.riesz (x-log r) (a/r)-
        (VaughanLogAverage.riesz L (a/r)-VaughanLogAverage.riesz (L-log r) (a/r)) : ℝ) : ℂ)‖^2)=
        ((P i).card : ℝ)*C := by
      rw [← nsmul_eq_mul,← Finset.sum_const]
      exact Finset.sum_congr rfl (fun r hr =>
        weighted_deletion_energy ha (Finset.mem_filter.mp hr).1 x L w)
    rw [hh]
    field_simp
  change (∑ i∈B,_)/(B.card : ℝ)=C
  rw [Finset.sum_congr rfl he,Finset.sum_const,nsmul_eq_mul]
  have hc : (B.card : ℝ)≠0 := Nat.cast_ne_zero.mpr hB.card_ne_zero
  field_simp

/-- A complete phase period with a nonzero smooth exponential tilt is
not zero. This exact real-space model keeps BOTH half-periods. -/
theorem exponential_full_period {k y : ℝ} (hy : 0<y) :
    (∫ t in -Real.pi/y..Real.pi/y,exp (k*t)*cos (y*t)) =
      -k*(exp (k*(Real.pi/y))-exp (k*(-Real.pi/y)))/(k^2+y^2) := by
  have hden : k^2+y^2≠0 := by nlinarith only [sq_nonneg k,sq_pos_of_pos hy]
  let F := fun t => exp (k*t)*(k*cos (y*t)+y*sin (y*t))/(k^2+y^2)
  have hF (t : ℝ) : HasDerivAt F (exp (k*t)*cos (y*t)) t := by
    have he := (((hasDerivAt_id t).const_mul k).exp.mul
      ((((hasDerivAt_id t).const_mul y).cos.const_mul k).add
        (((hasDerivAt_id t).const_mul y).sin.const_mul y))).div_const (k^2+y^2)
    apply he.congr_deriv
    simp only [id_eq,mul_one,Pi.add_apply]
    field_simp
    ring
  have hi : IntervalIntegrable (fun t => exp (k*t)*cos (y*t)) volume
      (-Real.pi/y) (Real.pi/y) := (by fun_prop :
        Continuous (fun t : ℝ => exp (k*t)*cos (y*t))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) hi]
  dsimp only [F]
  have hleft : y*(-Real.pi/y)=-Real.pi := by field_simp
  have hright : y*(Real.pi/y)=Real.pi := by field_simp
  rw [hleft,hright]
  simp only [cos_neg,cos_pi,sin_neg,sin_pi,mul_neg,mul_zero,add_zero]
  ring

/-- The coherent complete-period model has a strictly NEGATIVE signed
residual at every positive tilt, irrespective of the number of bins. -/
theorem exponential_full_period_neg {k y : ℝ} (hk : 0<k) (hy : 0<y) :
    (∫ t in -Real.pi/y..Real.pi/y,exp (k*t)*cos (y*t))<0 := by
  rw [exponential_full_period hy]
  have ht : 0<Real.pi/y := div_pos Real.pi_pos hy
  have hex : exp (k*(-Real.pi/y))<exp (k*(Real.pi/y)) := by
    apply exp_lt_exp.mpr
    rw [neg_div,mul_neg]
    linarith only [mul_pos hk ht]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hk) (sub_pos.mpr hex))
    (by nlinarith only [sq_nonneg k,sq_pos_of_pos hy])

end RiemannGaussian.ZetaRieszManyBinPhaseAudit
