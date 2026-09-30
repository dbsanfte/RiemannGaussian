/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCofactorDiscrepancy
import RiemannGaussian.ZetaRieszOwnerMaximal
import RiemannGaussian.ZetaRieszSignedDensityMain

/-!
# Signed counting comparison with the exact smooth owner weight

Squarefreeness belongs in the counting measure, not in a zero extension of
the test weight. On a full cofactor shell the exact owner allocation has
bounded variation. The result below keeps the signed density main and the
ordinary-prime cofactor correction together. It does not estimate that main
or remove additional arithmetic masks from the original core.
-/

noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszSmoothOwnerDiscrepancy
open Real ZetaRieszOwnerMaximal ZetaRieszCofactorDiscrepancy

/-- The original total-order radial factor, including the successor log. -/
def radial (N : ℕ) (T : ℝ) : ℝ := exp (-T/2)*T^(N+1)/(N.factorial : ℝ)

/-- A uniform cap before source normalization; only the COUNTING ERROR
will use this cap. The signed main is not bounded by it. -/
def radialCap (N : ℕ) : ℝ := ((N : ℝ)+1)*2^(N+1)

theorem radialCap_nonneg (N : ℕ) : 0 ≤ radialCap N := by
  unfold radialCap
  positivity

private theorem exp_monomial_bound (k : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    exp (-T/2)*T^k/(k.factorial : ℝ) ≤ (2 : ℝ)^k := by
  have h := Real.pow_div_factorial_le_exp (T/2) (show 0 ≤ T/2 by positivity) k
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ exp (-T/2)*(2 : ℝ)^k by positivity)
  have he : exp (-T/2)*exp (T/2)=1 := by
    rw [← exp_add,show -T/2+T/2=0 by ring,exp_zero]
  have hp : (2 : ℝ)^k*(T/2)^k=T^k := by rw [← mul_pow]; congr 1; ring
  calc
    _ = (exp (-T/2)*(2 : ℝ)^k)*((T/2)^k/(k.factorial : ℝ)) := by
      rw [← hp]
      ring
    _ ≤ (exp (-T/2)*(2 : ℝ)^k)*exp (T/2) := hh
    _ = (2 : ℝ)^k*(exp (-T/2)*exp (T/2)) := by ring
    _ = _ := by rw [he,mul_one]

theorem radial_bounds (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ radial N T ∧ radial N T ≤ radialCap N := by
  refine ⟨by unfold radial; positivity,?_⟩
  have h := mul_le_mul_of_nonneg_left (exp_monomial_bound (N+1) hT)
    (show 0 ≤ (N : ℝ)+1 by positivity)
  have hf : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hN : (N : ℝ)+1 ≠ 0 := by positivity
  have he : radial N T = ((N : ℝ)+1)*
      (exp (-T/2)*T^(N+1)/((N+1).factorial : ℝ)) := by
    rw [radial,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    field_simp
  rw [he]
  exact h

theorem radial_deriv (N : ℕ) (T : ℝ) :
    HasDerivAt (radial N)
      (exp (-T/2)*(((N : ℝ)+1)*T^N-T^(N+1)/2)/(N.factorial : ℝ)) T := by
  have h := ((((hasDerivAt_id T).neg.div_const 2).exp).mul
    ((hasDerivAt_id T).pow (N+1))).div_const (N.factorial : ℝ)
  apply h.congr_deriv
  simp only [Pi.neg_apply,id_eq,Pi.pow_apply,
    Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_one]
  ring

theorem radial_deriv_bound (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    |exp (-T/2)*(((N : ℝ)+1)*T^N-T^(N+1)/2)/(N.factorial : ℝ)| ≤ radialCap N := by
  have ha := exp_monomial_bound N hT
  have hb := (radial_bounds N hT).2
  have hn : 0 ≤ (N : ℝ)+1 := by positivity
  have hleft : |((N : ℝ)+1)*(exp (-T/2)*T^N/(N.factorial : ℝ))| ≤
      ((N : ℝ)+1)*2^N := by
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left ha hn
  have hright : |radial N T/2| ≤ radialCap N/2 := by
    rw [abs_of_nonneg (by unfold radial; positivity)]
    exact div_le_div_of_nonneg_right hb (by norm_num)
  calc
    _ = |((N : ℝ)+1)*(exp (-T/2)*T^N/(N.factorial : ℝ))-radial N T/2| := by
      congr 1
      unfold radial
      ring
    _ ≤ ((N : ℝ)+1)*2^N+radialCap N/2 :=
      (abs_sub _ _).trans (add_le_add hleft hright)
    _ = radialCap N := by unfold radialCap; rw [pow_succ]; ring

theorem radial_lipschitz (N : ℕ) {T U : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U) :
    |radial N T-radial N U| ≤ radialCap N*|T-U| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t (_ht : t ∈ Set.Ici (0 : ℝ)) => (radial_deriv N t).hasDerivWithinAt)
      (fun t (ht : t ∈ Set.Ici (0 : ℝ)) => by
        simpa only [Real.norm_eq_abs] using radial_deriv_bound N ht)
      (convex_Ici (0 : ℝ)) hU hT

/-- The exact binomial owner weight also has total variation at most two
when the cofactor share increases. No small-order allocation is dropped. -/
theorem ownerWeight_increasing_variation {N : ℕ} (hN : 32 ≤ N) (m : ℕ)
    (x : ℕ → ℝ) (hx : ∀ i ≤ m, x i ∈ Set.Icc (0 : ℝ) 1)
    (hinc : ∀ i < m, x i ≤ x (i+1)) :
    (∑ i ∈ Finset.range m, |ownerWeight N (x i)-ownerWeight N (x (i+1))|) ≤ 2 := by
  let H := fun i => lowerMass (N+1) (13*N/32) (x i)
  let L := fun i => lowerMass (N+1) (N/5+1) (x i)
  have hH i (hi : i < m) : H (i+1) ≤ H i :=
    lowerMass_antitone _ _ (hx i (by omega)) (hx (i+1) (by omega)) (hinc i hi)
  have hL i (hi : i < m) : L (i+1) ≤ L i :=
    lowerMass_antitone _ _ (hx i (by omega)) (hx (i+1) (by omega)) (hinc i hi)
  have he i : ownerWeight N (x i)=1-H i+L i := by
    rw [ownerWeight,ownerMass_eq_difference hN]
    dsimp [H,L]
    ring
  have hp i (hi : i ∈ Finset.range m) :
      |ownerWeight N (x i)-ownerWeight N (x (i+1))| ≤
        (H i-H (i+1))+(L i-L (i+1)) := by
    rw [he i,he (i+1)]
    have hh := hH i (Finset.mem_range.mp hi)
    have hl := hL i (Finset.mem_range.mp hi)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    _ ≤ ∑ i ∈ Finset.range m, ((H i-H (i+1))+(L i-L (i+1))) := Finset.sum_le_sum hp
    _ = (H 0-H m)+(L 0-L m) := by
      rw [Finset.sum_add_distrib,Finset.sum_range_sub',Finset.sum_range_sub']
    _ ≤ 2 := by
      have hH0 := lowerMass_bounds (N+1) (13*N/32) (hx 0 (by omega)).1 (hx 0 (by omega)).2
      have hHm := lowerMass_bounds (N+1) (13*N/32) (hx m le_rfl).1 (hx m le_rfl).2
      have hL0 := lowerMass_bounds (N+1) (N/5+1) (hx 0 (by omega)).1 (hx 0 (by omega)).2
      have hLm := lowerMass_bounds (N+1) (N/5+1) (hx m le_rfl).1 (hx m le_rfl).2
      dsimp [H,L]
      linarith only [hH0.2,hHm.1,hL0.2,hLm.1]

/-- Smooth extension of the literal owner amplitude. Squarefreeness is
left in `compositePrefix`; the extension does not set nonsquarefree rows to zero. -/
def ownerAmplitude (N : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  ownerWeight N (log n/(c+log n))*radial N (c+log n)

theorem ownerAmplitude_bounds (N : ℕ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 ≤ ownerAmplitude N c n ∧ ownerAmplitude N c n ≤ radialCap N := by
  have hlog := log_natCast_nonneg n
  have hT : 0 < c+log n := by linarith
  have hs : log n/(c+log n) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hlog hT.le,(div_le_one hT).mpr (by linarith)⟩
  have ho := ownerWeight_bounds N hs.1 hs.2
  have hr := radial_bounds N hT.le
  exact ⟨mul_nonneg ho.1 hr.1,(mul_le_of_le_one_left hr.1 ho.2).trans hr.2⟩

private theorem owner_radial_variation {N : ℕ} (hN : 32 ≤ N) (m : ℕ)
    (x T : ℕ → ℝ) (hx : ∀ i ≤ m, x i ∈ Set.Icc (0 : ℝ) 1)
    (hinc : ∀ i < m, x i ≤ x (i+1))
    (hT : ∀ i ≤ m, 0 ≤ T i) (hTi : ∀ i < m, T i ≤ T (i+1))
    (hlen : T m-T 0 ≤ 1) :
    (∑ i ∈ Finset.range m,
      |ownerWeight N (x i)*radial N (T i)-
        ownerWeight N (x (i+1))*radial N (T (i+1))|) ≤ 3*radialCap N := by
  have hp i (hi : i ∈ Finset.range m) :
      |ownerWeight N (x i)*radial N (T i)-
        ownerWeight N (x (i+1))*radial N (T (i+1))| ≤
      radialCap N*(|ownerWeight N (x i)-ownerWeight N (x (i+1))|+
        (T (i+1)-T i)) := by
    have hi' := Finset.mem_range.mp hi
    have hw := ownerWeight_bounds N (hx (i+1) (by omega)).1 (hx (i+1) (by omega)).2
    have hr := radial_bounds N (hT i (by omega))
    have hdiff := radial_lipschitz N (hT i (by omega)) (hT (i+1) (by omega))
    rw [abs_of_nonpos (sub_nonpos.mpr (hTi i hi')),neg_sub] at hdiff
    calc
      _ = |(ownerWeight N (x i)-ownerWeight N (x (i+1)))*radial N (T i)+
          ownerWeight N (x (i+1))*(radial N (T i)-radial N (T (i+1)))| := by
        congr 1
        ring
      _ ≤ |ownerWeight N (x i)-ownerWeight N (x (i+1))| *radialCap N+
          radialCap N*(T (i+1)-T i) := by
        apply (abs_add_le _ _).trans
        rw [abs_mul,abs_mul,abs_of_nonneg hr.1,abs_of_nonneg hw.1]
        apply add_le_add (mul_le_mul_of_nonneg_left hr.2 (abs_nonneg _))
        exact (mul_le_of_le_one_left (abs_nonneg _) hw.2).trans hdiff
      _ = _ := by ring
  have hv := ownerWeight_increasing_variation hN m x hx hinc
  calc
    _ ≤ ∑ i ∈ Finset.range m, radialCap N*
        (|ownerWeight N (x i)-ownerWeight N (x (i+1))|+(T (i+1)-T i)) :=
      Finset.sum_le_sum hp
    _ = radialCap N*((∑ i ∈ Finset.range m,
        |ownerWeight N (x i)-ownerWeight N (x (i+1))|)+(T m-T 0)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_range_sub]
    _ ≤ _ := by nlinarith only [radialCap_nonneg N,hv,hlen]

private theorem log_share_monotone {c a b : ℝ} (hc : 0 < c)
    (ha : 0 ≤ a) (hab : a ≤ b) : a/(c+a) ≤ b/(c+b) := by
  rw [div_le_div_iff₀ (by linarith : 0 < c+a) (by linarith : 0 < c+b)]
  nlinarith [mul_le_mul_of_nonneg_left hab hc.le]

/-- The amplitude's variation on a whole dyadic integer shell is at most
three radial caps. This pays the actual finite-order owner selector. -/
theorem ownerAmplitude_variation {N M X : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M) {c : ℝ} (hc : 0 < c) :
    (∑ k ∈ Finset.Ico (M+1) X,
      |ownerAmplitude N c k-ownerAmplitude N c (k+1)|) ≤ 3*radialCap N := by
  let m := X-(M+1)
  let v := fun i : ℕ => log (M+1+i : ℕ)
  let x := fun i => v i/(c+v i)
  let T := fun i => c+v i
  have hv i : 0 ≤ v i := log_natCast_nonneg _
  have hvi i : v i ≤ v (i+1) := log_le_log (by positivity)
    (by exact_mod_cast (show M+1+i ≤ M+1+(i+1) by omega))
  have hx i (_hi : i ≤ m) : x i ∈ Set.Icc (0 : ℝ) 1 := by
    have hT0 : 0 < c+v i := by linarith [hv i]
    exact ⟨div_nonneg (hv i) hT0.le,(div_le_one hT0).mpr (by linarith)⟩
  have hlen : T m-T 0 ≤ 1 := by
    have hem : M+1+m=X := by dsimp [m]; omega
    have hMl : (0 : ℝ)<M+1 := by positivity
    have hX : (0 : ℝ)<X := by exact_mod_cast (show 0 < X by omega)
    have hr : (X : ℝ)/(M+1) ≤ 2 := by
      apply (div_le_iff₀ hMl).mpr
      have h := (show (X : ℝ) ≤ 2*M by exact_mod_cast hXM)
      linarith
    have hb := log_le_sub_one_of_pos (div_pos hX hMl)
    rw [log_div hX.ne' hMl.ne'] at hb
    dsimp [T,v]
    rw [hem,Nat.add_zero,Nat.cast_add,Nat.cast_one]
    linarith
  have hb := owner_radial_variation hN m x T hx
    (fun i _ => log_share_monotone hc (hv i) (hvi i))
    (fun i _ => by dsimp [T]; linarith [hv i])
    (fun i _ => by dsimp [T]; linarith [hvi i]) hlen
  rw [Finset.sum_Ico_eq_sum_range]
  convert hb using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [ownerAmplitude,x,T,v]
  congr 2

/-- All integer-count cancellation is performed before the absolute value.
The signed density and prime subtraction remain one main expression. -/
theorem owner_shell_error {N M X D : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hD : 0 < D) (hDM : D^2 ≤ M) (hlarge : exp ((N : ℝ)/2) ≤ M)
    {c : ℝ} (hc : 0 < c) (y : ℝ) :
    |ZetaRieszCofactorPhaseEnergy.correlation (compositePrefix X)
        (shellWeight M X (ownerAmplitude N c) y c) D-
      compositeModel X D (shellWeight M X (ownerAmplitude N c) y c)| ≤
      countingConstant*exp (-(N : ℝ)/32)*(6+|y|)*radialCap N := by
  have hconstant := countingConstant_pos
  have hb := shell_composite_error hM hMX hXM hD hDM N hlarge
    (ownerAmplitude N c) y c (radialCap N) (radialCap_nonneg N)
    (fun n _ => by
      rw [abs_of_nonneg (ownerAmplitude_bounds N hc n).1]
      exact (ownerAmplitude_bounds N hc n).2)
  apply hb.trans
  have hv := ownerAmplitude_variation hN hM hMX hXM hc
  have h := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ countingConstant*exp (-(N : ℝ)/32) by positivity)
  nlinarith only [h]

/-- This is a genuine geometric error after the original source scaling,
not a polynomial improvement to a growing positive main bound. -/
theorem normalized_owner_shell_error {N M X D : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hD : 0 < D) (hDM : D^2 ≤ M) (hlarge : exp ((N : ℝ)/2) ≤ M)
    {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    |u^(N+1)*(ZetaRieszCofactorPhaseEnergy.correlation (compositePrefix X)
        (shellWeight M X (ownerAmplitude N c) y c) D-
      compositeModel X D (shellWeight M X (ownerAmplitude N c) y c))| ≤
      2*u*countingConstant*(6+|y|)*((N : ℝ)+1)*exp (-(3/100 : ℝ)*N) := by
  have hconstant := countingConstant_pos
  rw [abs_mul,abs_of_nonneg (pow_nonneg hu _)]
  apply (mul_le_mul_of_nonneg_left
    (owner_shell_error hN hM hMX hXM hD hDM hlarge hc y) (pow_nonneg hu _)).trans
  have hr := mul_le_mul_of_nonneg_left (source_rate_bound hu hU N)
    (show 0 ≤ 2*u*countingConstant*(6+|y|)*((N : ℝ)+1) by positivity)
  convert hr using 1
  simp only [radialCap,mul_pow,pow_succ]
  ring

private theorem sum_profile_steps {R : ℕ} (_hR : 0 < R) (f : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 R, (f d-f (d+1)))=f 1-f (R+1) := by
  have he : Finset.Icc 1 R=Finset.Ico 1 (R+1) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  rw [he,Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_sub_cancel,Nat.add_zero,Nat.zero_add,Nat.add_comm,Nat.add_left_comm,
    Nat.add_assoc] using Finset.sum_range_sub' (fun i => f (i+1)) R

/-- The exact finite profile is summed with its signs before comparison.
Only its explicit variation appears in the counting-error allowance. -/
theorem normalized_owner_profile_error {N M X R : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (_hR : 0 < R) (hRM : R^2 ≤ M) (hlarge : exp ((N : ℝ)/2) ≤ M)
    {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (f : ℕ → ℝ) (hf : f (R+1)=0) :
    |u^(N+1)*((∑ n ∈ compositePrefix X,
        shellWeight M X (ownerAmplitude N c) y c n *
          (∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0)))-
      ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*
        compositeModel X D (shellWeight M X (ownerAmplitude N c) y c))| ≤
      (2*u*countingConstant*(6+|y|)*((N : ℝ)+1)*exp (-(3/100 : ℝ)*N))*
        ∑ D ∈ Finset.Icc 1 R, |f D-f (D+1)| := by
  let w := shellWeight M X (ownerAmplitude N c) y c
  have he : (∑ n ∈ compositePrefix X, w n*
      (∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0))) =
      ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*
        ZetaRieszCofactorPhaseEnergy.correlation (compositePrefix X) w D := by
    simp_rw [ZetaRieszSignedCutoffEnergy.abel_profile R f _ hf,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro D _
    simp only [ZetaRieszCofactorPhaseEnergy.correlation,
      ZetaRieszCofactorPhaseEnergy.sharp,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring_nf)
  change |u^(N+1)*((∑ n ∈ compositePrefix X, w n*
      (∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0)))-_)| ≤ _
  rw [he,← Finset.sum_sub_distrib,Finset.mul_sum,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro D hD
  have hb := normalized_owner_shell_error hN hM hMX hXM (Finset.mem_Icc.mp hD).1
    ((Nat.pow_le_pow_left (Finset.mem_Icc.mp hD).2 2).trans hRM) hlarge hc hu hU y
  have hmul := mul_le_mul_of_nonneg_left hb (abs_nonneg (f D-f (D+1)))
  calc
    _ = |f D-f (D+1)| *|u^(N+1)*
        (ZetaRieszCofactorPhaseEnergy.correlation (compositePrefix X) w D-
          compositeModel X D w)| := by rw [← abs_mul]; congr 1; ring
    _ ≤ _ := hmul.trans_eq (by ring)

private theorem shell_model {M X D : ℕ} (hM : 0 < M) (hDM : D ≤ M)
    (a : ℕ → ℝ) (y c : ℝ) :
    compositeModel X D (shellWeight M X a y c) =
      densityPrefix D*(∑ n ∈ Finset.Icc 1 X, shellWeight M X a y c n)-
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, shellWeight M X a y c p := by
  have h1 : shellWeight M X a y c 1=0 := by simp [shellWeight,show ¬M<1 by omega]
  have he : (∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ D<p),
      shellWeight M X a y c p) =
      ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, shellWeight M X a y c p := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : p.Prime <;> by_cases hd : D<p
    · simp [hp,hd]
    · simp [hp,hd,shellWeight,show ¬M<p by omega]
    · simp [hp]
    · simp [hp]
  rw [compositeModel,h1,sub_zero,he]

private theorem hinge_steps {R : ℕ} (hR : 0 < R) {b : ℝ} (hb : 0 ≤ b)
    (hend : b ≤ log (R+1 : ℕ)) :
    (∑ d ∈ Finset.Icc 1 R,
      |max 0 (b-log d)-max 0 (b-log (d+1 : ℕ))|)=b := by
  have hdiff d (hd : d ∈ Finset.Icc 1 R) :
      0 ≤ max 0 (b-log d)-max 0 (b-log (d+1 : ℕ)) := by
    have hlog : log d ≤ log (d+1 : ℕ) := log_le_log
      (by exact_mod_cast (Finset.mem_Icc.mp hd).1) (by exact_mod_cast Nat.le_succ d)
    exact sub_nonneg.mpr (max_le_max_left 0 (by linarith))
  rw [Finset.sum_congr rfl (fun d hd => abs_of_nonneg (hdiff d hd)),
    sum_profile_steps hR]
  rw [max_eq_left (sub_nonpos.mpr hend)]
  simp only [Nat.cast_one,log_one,sub_zero,max_eq_right hb]

/-- The positive logarithmic profile pays exactly its length, while the
signed density scalar and ordinary-prime subtraction remain coupled. -/
theorem normalized_owner_riesz_error {N M X R : ℕ} (hN : 32 ≤ N)
    (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hR : 0 < R) (hRM : R^2 ≤ M) (hlarge : exp ((N : ℝ)/2) ≤ M)
    {c u b : ℝ} (hc : 0 < c) (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (hb : 0 ≤ b)
    (hRcut : ⌊exp b⌋₊ ≤ R) (hend : b ≤ log (R+1 : ℕ)) (y : ℝ) :
    let w := shellWeight M X (ownerAmplitude N c) y c;
    |u^(N+1)*((∑ n ∈ compositePrefix X, w n*VaughanLogAverage.riesz b n)-
      (ZetaRieszSignedDensityMain.densityRiesz b*(∑ n ∈ Finset.Icc 1 X, w n)-
        b*(∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p)))| ≤
      2*u*countingConstant*(6+|y|)*((N : ℝ)+1)*b*exp (-(3/100 : ℝ)*N) := by
  dsimp only
  let w := shellWeight M X (ownerAmplitude N c) y c
  let f := fun d : ℕ => max 0 (b-log d)
  have hf : f (R+1)=0 := max_eq_left (sub_nonpos.mpr hend)
  have hRM' : R ≤ M := by nlinarith
  have hmain : (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*compositeModel X D w) =
      ZetaRieszSignedDensityMain.densityRiesz b*(∑ n ∈ Finset.Icc 1 X, w n)-
        b*(∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p) := by
    have hmodel D (hD : D ∈ Finset.Icc 1 R) := shell_model (X := X) hM
      ((Finset.mem_Icc.mp hD).2.trans hRM')
      (ownerAmplitude N c) y c
    have hden : (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*densityPrefix D) =
        ZetaRieszSignedDensityMain.densityRiesz b := by
      simp only [densityPrefix]
      rw [← ZetaRieszSignedCutoffEnergy.abel_profile R f
        (fun d => (μ d : ℝ)*SquarefreeCounting.density d.primeFactors) hf,
        ZetaRieszSignedDensityMain.densityRiesz_eq_hinge b hRcut]
      exact Finset.sum_congr rfl (fun _ _ => by dsimp [f]; ring)
    calc
      _ = ∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*
          (densityPrefix D*(∑ n ∈ Finset.Icc 1 X, w n)-
            ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p) :=
        Finset.sum_congr rfl (fun D hD => congrArg (fun z : ℝ => (f D-f (D+1))*z)
          (hmodel D hD))
      _ = (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1))*densityPrefix D)*
          (∑ n ∈ Finset.Icc 1 X, w n)-
          (∑ D ∈ Finset.Icc 1 R, (f D-f (D+1)))*
            (∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, w p) := by
        simp only [mul_sub,← mul_assoc,Finset.sum_sub_distrib,← Finset.sum_mul]
      _ = _ := by
        rw [hden,sum_profile_steps hR,hf]
        simp only [f,Nat.cast_one,log_one,sub_zero,max_eq_right hb]
  have hlit : (∑ n ∈ compositePrefix X, w n*VaughanLogAverage.riesz b n) =
      ∑ n ∈ compositePrefix X, w n*
        (∑ d ∈ Finset.Icc 1 R, f d*(if d ∣ n then (μ d : ℝ) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1; omega
    rw [ZetaSquarefreeRieszCompletion.riesz_eq_finite_divisor_cutoff b hend hn0]
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d∣n <;> simp [hd,f,mul_comm]
  have h := normalized_owner_profile_error hN hM hMX hXM hR hRM hlarge hc hu hU y f hf
  change |u^(N+1)*((∑ n ∈ compositePrefix X, w n*_)-_)| ≤ _
  rw [hlit,← hmain]
  exact h.trans_eq (by rw [hinge_steps hR hb hend]; ring)

private theorem composite_count {a : ℕ} (ha : Squarefree a)
    (ha1 : 1 < a) (hap : ¬a.Prime) : 2 ≤ a.primeFactors.card := by
  by_contra h
  have hc : a.primeFactors.card ≤ 1 := by omega
  have hp := Nat.minFac_prime ha1.ne'
  have hm : a.minFac ∈ a.primeFactors :=
    hp.mem_primeFactors (Nat.minFac_dvd a) ha.ne_zero
  have he : a.primeFactors={a.minFac} := by
    ext q
    simp only [Finset.mem_singleton]
    constructor
    · exact fun hq => Finset.card_le_one.mp hc q hq a.minFac hm
    · exact fun hq => hq ▸ hm
  have hprod := Nat.prod_primeFactors_of_squarefree ha
  rw [he,Finset.prod_singleton] at hprod
  exact hap (hprod ▸ hp)

/-- On this geometric sector the smooth extension agrees pointwise with
the actual retained owner atom. Its whole complex product phase is taken
to the real part only after the exact Riesz difference is evaluated. -/
theorem owner_atom_eq (A : Finset ℕ) (N : ℕ) {a p : ℕ} (ha : Squarefree a)
    (ha1 : 1 < a) (hap : ¬a.Prime) (hp : p.Prime) (haplt : a < p) (hpA : p ∈ A)
    {L : ℝ} (hpL : log p ≤ L) (y : ℝ) :
    (ZetaRieszJointAllocation.residualCoefficient
      (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
        zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re =
      (ownerAmplitude N (log p) a*cos (y*(log p+log a))/(a : ℝ)*
        VaughanLogAverage.riesz (L-log p) a)/(L*p) := by
  have hc := composite_count ha ha1 hap
  have hn0 : 0 < a := by omega
  have hpd : ¬p∣a := by
    intro hd
    exact (Nat.le_of_dvd hn0 hd).not_gt haplt
  have hmax : ∀ q ∈ a.primeFactors, q<p := fun q hq =>
    (Nat.le_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hq)).trans_lt haplt
  have hlog : log (p*a : ℕ)=log p+log a := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero)]
  have haL : log a ≤ L := (log_le_log (by exact_mod_cast hn0)
    (by exact_mod_cast haplt.le)).trans hpL
  have hw := ownerWeight_eq_fibre A N ha hc hp hmax hpA
  rw [hlog] at hw
  have hh : ZetaRieszJointPrimeEnergy.divisorResponse
      (ZetaRieszJointPrimeEnergy.hinge L p) a = -VaughanLogAverage.riesz (L-log p) a := by
    simp only [ZetaRieszJointPrimeEnergy.divisorResponse,ZetaRieszJointPrimeEnergy.hinge,
      mul_sub,Finset.sum_sub_distrib]
    change VaughanLogAverage.riesz L a - VaughanLogAverage.riesz (L-log p) a = _
    rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1.ne' hap haL,zero_sub]
  rw [ZetaRieszJointPrimeEnergy.atom_eq _ L y N ha hc hp hpd,hh]
  dsimp only [ZetaRieszJointPrimeEnergy.primeWeight,ownerAmplitude,radial]
  rw [← hw]
  ring

/-- Literal squarefree composite cofactors in a complete integer shell.
This is an equality of the original owner atoms, not a prime-density model. -/
theorem literal_owner_shell_eq (A : Finset ℕ) (N M X : ℕ) (hM : 0 < M)
    {p : ℕ} (hp : p.Prime) (hXp : X < p) (hpA : p ∈ A)
    {L : ℝ} (hpL : log p ≤ L) (y : ℝ) :
    (∑ a ∈ (Finset.Ioc M X).filter (fun a => Squarefree a ∧ ¬a.Prime),
      (ZetaRieszJointAllocation.residualCoefficient
        (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
          zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re) =
      (∑ a ∈ compositePrefix X,
        shellWeight M X (ownerAmplitude N (log p)) y (log p) a*
          VaughanLogAverage.riesz (L-log p) a)/(L*p) := by
  let S := (Finset.Ioc M X).filter (fun a => Squarefree a ∧ ¬a.Prime)
  have hs : S ⊆ compositePrefix X := by
    intro a ha
    obtain ⟨haI,hs,hnp⟩ := Finset.mem_filter.mp ha
    have hi := Finset.mem_Ioc.mp haI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,hi.2⟩,hs,hnp⟩
  have hrestrict : (∑ a ∈ compositePrefix X,
      shellWeight M X (ownerAmplitude N (log p)) y (log p) a*
        VaughanLogAverage.riesz (L-log p) a) =
      ∑ a ∈ S, shellWeight M X (ownerAmplitude N (log p)) y (log p) a*
        VaughanLogAverage.riesz (L-log p) a := by
    symm
    apply Finset.sum_subset hs
    intro a ha hnot
    obtain ⟨haI,hs,hap⟩ := Finset.mem_filter.mp ha
    have hlow : ¬M<a := by
      intro h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
        ⟨h,(Finset.mem_Ioc.mp haI).2⟩,hs,hap⟩)
    simp [shellWeight,hlow]
  rw [hrestrict,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨haI,hs,hap⟩ := Finset.mem_filter.mp ha
  have hi := Finset.mem_Ioc.mp haI
  rw [owner_atom_eq A N hs (by omega) hap hp (hi.2.trans_lt hXp) hpA hpL y]
  simp only [shellWeight,hi.1,hi.2,and_self,ite_true]

/-- Both signs of the literal owner-shell discrepancy are geometrically
bounded. The full signed density main minus its ordinary-prime correction
is retained as one expression. Additional core masks are NOT assumed paid. -/
theorem normalized_literal_owner_error (A : Finset ℕ) {N M X R p : ℕ}
    (hN : 32 ≤ N) (hM : 0 < M) (hMX : M < X) (hXM : X ≤ 2*M)
    (hp : p.Prime) (hXp : X < p) (hpA : p ∈ A) {L : ℝ} (hpL : log p ≤ L)
    (hR : 0 < R) (hRM : R^2 ≤ M) (hlarge : exp ((N : ℝ)/2) ≤ M)
    (hRcut : ⌊exp (L-log p)⌋₊ ≤ R) (hend : L-log p ≤ log (R+1 : ℕ))
    {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    let w := shellWeight M X (ownerAmplitude N (log p)) y (log p);
    |u^(N+1)*((∑ a ∈ (Finset.Ioc M X).filter (fun a => Squarefree a ∧ ¬a.Prime),
        (ZetaRieszJointAllocation.residualCoefficient
          (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re)-
      (ZetaRieszSignedDensityMain.densityRiesz (L-log p)*(∑ a ∈ Finset.Icc 1 X, w a)-
        (L-log p)*(∑ q ∈ (Finset.Icc 1 X).filter Nat.Prime, w q))/(L*p))| ≤
      (2*u*countingConstant*(6+|y|)*((N : ℝ)+1)/(p : ℝ))*exp (-(3/100 : ℝ)*N) := by
  dsimp only
  have hlogp : 0 < log p := log_pos (by exact_mod_cast hp.one_lt)
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have hL : 0 < L := hlogp.trans_le hpL
  have hconstant := countingConstant_pos
  have hb := normalized_owner_riesz_error hN hM hMX hXM hR hRM hlarge
    hlogp hu hU (sub_nonneg.mpr hpL) hRcut hend y
  dsimp only at hb
  rw [literal_owner_shell_eq A N M X hM hp hXp hpA hpL y,
    ← sub_div,← mul_div_assoc,abs_div,abs_of_pos (mul_pos hL hp0)]
  apply (div_le_div_of_nonneg_right hb (mul_pos hL hp0).le).trans
  have hnon : 0 ≤ 2*u*countingConstant*(6+|y|)*((N : ℝ)+1)*exp (-(3/100 : ℝ)*N) :=
    by positivity
  have hratio : (L-log p)/L ≤ 1 := (div_le_one hL).mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_left hratio (div_nonneg hnon hp0.le)
  convert hh using 1 <;> ring

/-- Sum every marked prime BEFORE estimating the signed density main and
its prime-cofactor correction. Only the already cancelled counting errors
are summed absolutely. The prime cardinality is replaced by a harmonic cost. -/
theorem normalized_joint_owner_error (A P : Finset ℕ) (M X R : ℕ → ℕ)
    {N : ℕ} (hN : 32 ≤ N) {L u : ℝ} (hu : 0 ≤ u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ∈ A ∧ log p ≤ L)
    (hshell : ∀ p ∈ P, 0 < M p ∧ M p < X p ∧ X p ≤ 2*M p ∧ X p < p)
    (hcut : ∀ p ∈ P, 0 < R p ∧ (R p)^2 ≤ M p ∧
      exp ((N : ℝ)/2) ≤ M p ∧ ⌊exp (L-log p)⌋₊ ≤ R p ∧
        L-log p ≤ log (R p+1 : ℕ)) :
    let w := fun p => shellWeight (M p) (X p) (ownerAmplitude N (log p)) y (log p);
    |u^(N+1)*((∑ p ∈ P,
      ∑ a ∈ (Finset.Ioc (M p) (X p)).filter (fun a => Squarefree a ∧ ¬a.Prime),
        (ZetaRieszJointAllocation.residualCoefficient
          (A ∩ {ZetaRieszPrimeEndpoint.largestPrime (p*a)}) L N (p*a)*
            zetaPrimeLogKernel N (3/2+Complex.I*y) (p*a)).re)-
      ∑ p ∈ P, (ZetaRieszSignedDensityMain.densityRiesz (L-log p)*
        (∑ a ∈ Finset.Icc 1 (X p), w p a)-
          (L-log p)*(∑ q ∈ (Finset.Icc 1 (X p)).filter Nat.Prime, w p q))/(L*p))| ≤
      (2*u*countingConstant*(6+|y|)*((N : ℝ)+1)*exp (-(3/100 : ℝ)*N))*
        ∑ p ∈ P, (p : ℝ)⁻¹ := by
  dsimp only
  rw [← Finset.sum_sub_distrib,Finset.mul_sum,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpP,hpA,hpL⟩ := hP p hp
  obtain ⟨hM,hMX,hXM,hXp⟩ := hshell p hp
  obtain ⟨hR,hRM,hlarge,hRcut,hend⟩ := hcut p hp
  exact (normalized_literal_owner_error A hN hM hMX hXM hpP hXp hpA hpL
    hR hRM hlarge hRcut hend hu hU y).trans_eq (by ring)

/-- The outer marked-prime aggregation is only logarithmic, so it does
not consume the new geometric saving even at an exponential physical cutoff. -/
theorem marked_harmonic_bound (P : Finset ℕ) {Q : ℕ}
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ Q) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 1+log Q := by
  have hs : P ⊆ Finset.Icc 1 Q := fun p hp =>
    Finset.mem_Icc.mpr ⟨(hP p hp).1.pos,(hP p hp).2⟩
  have hh : (∑ n ∈ Finset.Icc 1 Q, (n : ℝ)⁻¹) ≤ 1+log Q := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using
      harmonic_le_one_add_log Q
  exact (Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; positivity)).trans hh

end RiemannGaussian.ZetaRieszSmoothOwnerDiscrepancy
