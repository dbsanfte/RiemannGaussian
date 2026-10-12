import OAI.NumberTheory.DirichletL.Detector.PrincipalProduct
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-! Native-toolchain review of the pinned OpenAI principal Euler factor.

Run with the isolated Lean 4.34.1 review project. These theorems retain
the actual angular and target-character phases. They extend an analytic
correction, not the arithmetic low estimate or any zero-free region.
The extracted angular Euler channel is not assumed to be nonvanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical
namespace OpenAIReview.PrincipalEuler
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeEuler OAI.SmoothMobiusCorrection
local notation "O" => OAI.ActualEisensteinCubic.O
local notation "Id" => Ideal O

/-- The exact residual after extracting the angular Euler denominator. -/
def residualFactor (q R D : ℂ) : ℂ :=
  (1-q^2)*(1-q*(R-D)/(1-D))

theorem principal_algebra (q R D : ℂ)
    (hq : 1-q≠0) (hR : 1-R≠0) (hD : 1-D≠0) :
    ProbeLocal.continuedCorrection q q D
      (markedFactor R q q (D*(1-q)) (-D+q*R) 1) =
        residualFactor q R D/(1-R) := by
  unfold ProbeLocal.continuedCorrection markedFactor residualFactor
  field_simp
  ring

theorem coordV_principal (Q : ℝ) :
    coordV Q (1/6)=(Q:ℂ)⁻¹ := by
  unfold coordV
  norm_num [Complex.cpow_neg]

theorem coordW_principal (Q : ℝ) :
    coordW Q 1 1=(Q:ℂ)⁻¹ := by
  unfold coordW
  norm_num [Complex.cpow_neg]

theorem coordK_principal (Q : ℝ) (hQ : 0<Q) (eta s : ℂ) :
    coordK Q eta s 1=coordD Q eta 1 s*(1-(Q:ℂ)⁻¹) := by
  have hQn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  have hpow : (Q:ℂ)^(-s-1)=(Q:ℂ)^(-s)*(Q:ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hQn]
    simp [div_eq_mul_inv]
  simp only [coordK,coordD,star_one,mul_one,hpow]
  field_simp

/-- The extracted residual at an actual ordinary prime ideal. -/
def residualLocal (eta : HeckeFamily.Character) (P : PrimeIdeal) (s : ℂ) : ℂ :=
  residualFactor (Ideal.absNorm P.val:ℂ)⁻¹
    (coordR (Ideal.absNorm P.val) (actualAPhase eta (CompletedGauss.primaryGenerator P.val)) s (1/6))
    (coordD (Ideal.absNorm P.val) (HeckeFamily.elementCoeff eta (CompletedGauss.primaryGenerator P.val)) 1 s)

theorem unramified_principal_factorization
    (Q : ℝ) (hQ : 0<Q) (A eta s : ℂ)
    (hq : 1-(Q:ℂ)⁻¹≠0) (hR : 1-coordR Q A s (1/6)≠0)
    (hD : 1-coordD Q eta 1 s≠0) :
    unramifiedClosed Q A eta 1 s 1 (1/6)=
      residualFactor (Q:ℂ)⁻¹ (coordR Q A s (1/6)) (coordD Q eta 1 s)/
        (1-coordR Q A s (1/6)) := by
  unfold unramifiedClosed
  dsimp only
  rw [coordV_principal,coordW_principal,coordK_principal Q hQ]
  exact principal_algebra _ _ _ hq hR hD

theorem residualFactor_sub_one (q R D : ℂ) :
    residualFactor q R D-1=
      -q^2-(1-q^2)*q*(R-D)/(1-D) := by
  unfold residualFactor
  ring

theorem residualFactor_defect_bound (q R D : ℂ)
    (hq : ‖q‖≤1) (hD : ‖D‖≤1/2) :
    ‖residualFactor q R D-1‖≤‖q‖^2+4*‖q‖*(‖R‖+‖D‖) := by
  have hinv := ProbeLocal.inv_one_sub_norm_le_two D hD
  have hq2 : ‖q‖^2≤1 := pow_le_one₀ (norm_nonneg _) hq
  have hleft : ‖1-q^2‖≤2 := by
    calc
      _≤‖(1:ℂ)‖+‖q^2‖ := norm_sub_le _ _
      _≤2 := by rw [norm_one,norm_pow]; linarith
  rw [residualFactor_sub_one]
  calc
    _≤‖-q^2‖+‖(1-q^2)*q*(R-D)/(1-D)‖ := norm_sub_le _ _
    _≤‖q‖^2+(2*‖q‖*(‖R‖+‖D‖))*2 := by
      simp only [norm_neg,norm_pow,norm_mul,div_eq_mul_inv]
      gcongr
      exact norm_sub_le _ _
    _=_ := by ring

/-- Summable residual exponent at any fixed positive distance from 1/2. -/
def residualExponent (sigma : ℝ) : ℝ := min 2 (min (6*sigma-2) (sigma+1))

theorem residualExponent_gt_one {sigma : ℝ} (hsigma : 1/2<sigma) :
    1<residualExponent sigma := by
  unfold residualExponent
  exact lt_min (by norm_num) (lt_min (by linarith) (by linarith))

theorem residual_principal_bound (Q : ℝ) (hQ : 4≤Q) (A eta s : ℂ)
    (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (sigma : ℝ)
    (hsigma : 1/2<sigma) (hs : sigma<s.re) :
    ‖residualFactor (Q:ℂ)⁻¹ (coordR Q A s (1/6)) (coordD Q eta 1 s)-1‖≤
      9*Q^(-residualExponent sigma) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hqi : ‖(Q:ℂ)⁻¹‖=Q^(-1:ℝ) := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,
      Real.rpow_neg hQ0.le,Real.rpow_one]
  have hq : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [hqi]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : (-1:ℝ)≤0)).trans_eq
      (Real.rpow_zero Q)
  have hR : ‖coordR Q A s (1/6)‖≤Q^(3-6*sigma) := by
    apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    norm_num
    linarith
  have hD : ‖coordD Q eta 1 s‖≤Q^(-sigma) :=
    (coordD_norm_le Q hQ0 eta 1 s heta (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hDh : ‖coordD Q eta 1 s‖≤1/2 :=
    hD.trans (rpow_le_half Q _ hQ (by linarith))
  let E := residualExponent sigma
  let T := Q^(-E)
  have hT : 0≤T := Real.rpow_nonneg hQ0.le _
  have he2 : E≤2 := min_le_left _ _
  have heR : E≤6*sigma-2 := (min_le_right _ _).trans (min_le_left _ _)
  have heD : E≤sigma+1 := (min_le_right _ _).trans (min_le_right _ _)
  have hqq : ‖(Q:ℂ)⁻¹‖^2≤T := by
    calc
      _=Q^(-1:ℝ)*Q^(-1:ℝ) := by rw [hqi,pow_two]
      _=Q^(-2:ℝ) := by rw [←Real.rpow_add hQ0]; norm_num
      _≤T := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hqR : ‖(Q:ℂ)⁻¹‖*‖coordR Q A s (1/6)‖≤T := by
    calc
      _≤Q^(-1:ℝ)*Q^(3-6*sigma) := by rw [hqi]; gcongr
      _=Q^(2-6*sigma) := by rw [←Real.rpow_add hQ0]; congr 1; ring
      _≤T := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hqD : ‖(Q:ℂ)⁻¹‖*‖coordD Q eta 1 s‖≤T := by
    calc
      _≤Q^(-1:ℝ)*Q^(-sigma) := by rw [hqi]; gcongr
      _=Q^(-1-sigma) := by rw [←Real.rpow_add hQ0]; congr 1
      _≤T := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hb := residualFactor_defect_bound (Q:ℂ)⁻¹ (coordR Q A s (1/6))
    (coordD Q eta 1 s) hq hDh
  change _≤9*T
  nlinarith

theorem residual_principal_analytic (Q : ℝ) (hQ : 4≤Q) (A eta : ℂ)
    (heta : ‖eta‖≤1) :
    AnalyticOnNhd ℂ (fun s : ℂ=>
      residualFactor (Q:ℂ)⁻¹ (coordR Q A s (1/6)) (coordD Q eta 1 s))
      {s : ℂ | 1/2<s.re} := by
  have hQ0 : 0<Q := by linarith
  have hdif : DifferentiableOn ℂ (fun s : ℂ=>
      residualFactor (Q:ℂ)⁻¹ (coordR Q A s (1/6)) (coordD Q eta 1 s))
      {s : ℂ | 1/2<s.re} := by
    intro s hs
    have hd : 1-coordD Q eta 1 s≠0 := by
      apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordD_norm_le Q hQ0 eta 1 s heta (by simp)).trans
      exact rpow_le_half Q _ hQ (by change (1/2:ℝ)<s.re at hs; linarith)
    have hR : DifferentiableAt ℂ (fun x=>coordR Q A x (1/6)) s :=
      (coordR_differentiable Q hQ0 A (1/6)).differentiableAt
    have hD : DifferentiableAt ℂ (fun x=>coordD Q eta 1 x) s :=
      (coordD_differentiable Q hQ0 eta 1).differentiableAt
    apply DifferentiableAt.differentiableWithinAt
    unfold residualFactor
    fun_prop (disch := assumption)
  exact hdif.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

theorem residualLocal_bound (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (sigma : ℝ) (hsigma : 1/2<sigma)
    (s : ℂ) (hs : sigma<s.re) :
    ‖residualLocal eta P s-1‖≤
      9*(Ideal.absNorm P.val:ℝ)^(-residualExponent sigma) := by
  apply residual_principal_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one eta _
  · exact ProbeRow.targetMonoid_norm_le_one eta _
  · exact hsigma
  · exact hs

theorem residualLocal_analytic (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) :
    AnalyticOnNhd ℂ (residualLocal eta P) {s : ℂ | 1/2<s.re} := by
  apply residual_principal_analytic
  · exact_mod_cast hP
  · exact ProbeRow.targetMonoid_norm_le_one eta _

/-- Product of the residual factors outside the same frozen prime set. -/
def residualCorrection (eta : HeckeFamily.Character) (S : Finset Id) (s : ℂ) : ℂ :=
  ∏'P : {P : PrimeIdeal // P.val∉S},residualLocal eta P.val s

/-- A uniform, summable bound for the actual residual defect. -/
def residualMajorant (sigma : ℝ) (P : PrimeIdeal) : ℝ :=
  9*(Ideal.absNorm P.val:ℝ)^(-residualExponent sigma)

theorem residualMajorant_summable {sigma : ℝ} (hsigma : 1/2<sigma) :
    Summable (residualMajorant sigma) := by
  have hs : 1<residualExponent sigma := residualExponent_gt_one hsigma
  have h : Summable (fun P : PrimeIdeal=>
      ‖CubicEisenstein.fullIdealWeight ((residualExponent sigma:ℝ):ℂ) P.val‖) :=
    (CubicEisenstein.fullIdealWeight_summable_norm ((residualExponent sigma:ℝ):ℂ)
      (by simpa using hs)).comp_injective Subtype.val_injective
  apply (h.mul_left 9).congr
  intro P
  unfold residualMajorant CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp

/-- Uniform tail-product lemma, used only with the actual principal factors. -/
theorem exists_tail_cutoff
    (F : HeckeFamily.Character→PrimeIdeal→ℂ→ℂ) (b : PrimeIdeal→ℝ) (sigma : ℝ)
    (hb0 : ∀P,0≤b P) (hb : Summable b)
    (hFa : ∀eta P,4≤Ideal.absNorm P.val→
      AnalyticOnNhd ℂ (F eta P) {s : ℂ | sigma<s.re})
    (hFb : ∀eta P,4≤Ideal.absNorm P.val→∀s : ℂ,sigma<s.re→‖F eta P s-1‖≤b P) :
    ∃N : ℕ,4≤N ∧ ∀S : Finset Id,
      (∀P : PrimeIdeal,Ideal.absNorm P.val≤N→P.val∈S)→
      ∀eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (fun s=>∏'P : {P : PrimeIdeal // P.val∉S},F eta P.val s)
          {s : ℂ | sigma<s.re} ∧
        ∀s : ℂ,sigma<s.re→‖(∏'P : {P : PrimeIdeal // P.val∉S},F eta P.val s)-1‖≤1/2 := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero b)).2 (1/6:ℝ) (by norm_num)
  obtain ⟨E,hE⟩ := ht.exists
  let N := max 4 (E.sup (fun P=>Ideal.absNorm P.val))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS eta
  let T := {P : PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉E := by
    intro hm
    apply P.property
    apply hS P.val
    exact (Finset.le_sup (f:=fun Q : PrimeIdeal=>Ideal.absNorm Q.val) hm).trans
      (le_max_right _ _)
  let inc : T→{P : PrimeIdeal // P∉E} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun t : {P : PrimeIdeal // P∉E}=>t.val) h
  have hnorm (P : T) : 4≤Ideal.absNorm P.val.val := by
    have hh : ¬Ideal.absNorm P.val.val≤N := fun h=>P.property (hS P.val h)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hh))
  have hsum : Summable (fun P : T=>b P.val) := hb.subtype _
  have hsmall : (∑'P : T,b P.val)≤1/6 := by
    apply le_trans ?_ hE.le
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _=>hb0 P.val) (fun _=>le_rfl)
      hsum (hb.subtype _)
  have hhalf (P : T) : b P.val≤1/2 := by
    have hterm := Summable.le_tsum hsum P (fun Q _=>hb0 Q.val)
    linarith
  constructor
  · exact normalProduct_analytic (fun P : T=>F eta P.val) (fun P : T=>b P.val) _
      (Complex.isOpen_re_gt _) hsum (fun P=>hFa eta P.val (hnorm P))
      (fun P s hs=>hFb eta P.val (hnorm P) s hs) hhalf
  · intro s hs
    exact product_defect_le (fun P : T=>F eta P.val s) (fun P : T=>b P.val) hsum
      (fun P=>hFb eta P.val (hnorm P) s hs) hhalf hsmall

theorem exists_residual_cutoff {sigma : ℝ} (hsigma : 1/2<sigma) :
    ∃N : ℕ,4≤N ∧ ∀S : Finset Id,
      (∀P : PrimeIdeal,Ideal.absNorm P.val≤N→P.val∈S)→
      ∀eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (residualCorrection eta S) {s : ℂ | sigma<s.re} ∧
        ∀s : ℂ,sigma<s.re→‖residualCorrection eta S s-1‖≤1/2 := by
  apply exists_tail_cutoff residualLocal (residualMajorant sigma) sigma
  · intro P; unfold residualMajorant; positivity
  · exact residualMajorant_summable hsigma
  · intro eta P hP
    exact (residualLocal_analytic eta P hP).mono
      (fun s hs=>lt_trans hsigma hs)
  · intro eta P hP s hs
    exact residualLocal_bound eta P hP sigma hsigma s hs

/-- Defect exponent for the original correction, including its angular channel. -/
def principalExponent (sigma : ℝ) : ℝ := min (residualExponent sigma) (6*sigma-3)

theorem principalExponent_gt_one {sigma : ℝ} (hsigma : 2/3<sigma) :
    1<principalExponent sigma := by
  unfold principalExponent
  exact lt_min (residualExponent_gt_one (by linarith)) (by linarith)

theorem unramified_principal_bound (Q : ℝ) (hQ : 4≤Q) (A eta s : ℂ)
    (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (sigma : ℝ)
    (hsigma : 2/3<sigma) (hs : sigma<s.re) :
    ‖unramifiedClosed Q A eta 1 s 1 (1/6)-1‖≤20*Q^(-principalExponent sigma) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hR : ‖coordR Q A s (1/6)‖≤Q^(3-6*sigma) := by
    apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    norm_num
    linarith
  have hRh : ‖coordR Q A s (1/6)‖≤1/2 :=
    hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hDh : ‖coordD Q eta 1 s‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta 1 s heta (by simp)).trans
    exact rpow_le_half Q _ hQ (by linarith)
  have hqh : ‖(Q:ℂ)⁻¹‖≤1/2 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    rw [div_le_iff₀ hQ0]
    linarith
  have hRn := ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hRh
  have hDn := ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hDh
  have hqn := ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hqh
  let G := residualFactor (Q:ℂ)⁻¹ (coordR Q A s (1/6)) (coordD Q eta 1 s)
  let T := Q^(-principalExponent sigma)
  have hT : 0≤T := Real.rpow_nonneg hQ0.le _
  have hGT : ‖G-1‖≤9*T := by
    apply (residual_principal_bound Q hQ A eta s hA heta sigma (by linarith) hs).trans
    gcongr
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (neg_le_neg (min_le_left _ _))
  have hRT : ‖coordR Q A s (1/6)‖≤T :=
    hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1
      (by have hh : principalExponent sigma≤6*sigma-3 := min_le_right _ _; linarith))
  rw [unramified_principal_factorization Q hQ0 A eta s hqn hRn hDn]
  change ‖G/(1-coordR Q A s (1/6))-1‖≤20*T
  have heq : G/(1-coordR Q A s (1/6))-1=
      ((G-1)+coordR Q A s (1/6))/(1-coordR Q A s (1/6)) := by
    field_simp
    ring
  rw [heq,div_eq_mul_inv,norm_mul]
  have hnum : ‖G-1+coordR Q A s (1/6)‖≤10*T :=
    (norm_add_le _ _).trans (by linarith)
  have hinv := ProbeLocal.inv_one_sub_norm_le_two _ hRh
  calc
    _≤(10*T)*2 := mul_le_mul hnum hinv (norm_nonneg _) (by positivity)
    _=_ := by ring

theorem principalLocal_extended_analytic (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) :
    AnalyticOnNhd ℂ (principalLocal eta P) {s : ℂ | 2/3<s.re} := by
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4≤Q := by dsimp [Q]; exact_mod_cast hP
  have hQ0 : 0<Q := by linarith
  have hA := actualAPhase_norm_le_one eta (CompletedGauss.primaryGenerator P.val)
  have he := ProbeRow.targetMonoid_norm_le_one eta (CompletedGauss.primaryGenerator P.val)
  have hv : 1-coordV Q (1/6)≠0 := by
    apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by norm_num)
  have hdif : DifferentiableOn ℂ (principalLocal eta P) {s : ℂ | 2/3<s.re} := by
    intro s hs
    apply (unramifiedClosed_differentiableAt Q hQ0
      (actualAPhase eta (CompletedGauss.primaryGenerator P.val))
      (HeckeFamily.elementCoeff eta (CompletedGauss.primaryGenerator P.val))
      1 s 1 (1/6) ?_ hv ?_).differentiableWithinAt
    · apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordR_norm_le Q hQ0 _ s (1/6) hA).trans
      apply rpow_le_half Q _ hQ
      norm_num
      change (2/3:ℝ)<s.re at hs
      linarith
    · apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordD_norm_le Q hQ0 _ 1 s he (by simp)).trans
      exact rpow_le_half Q _ hQ (by change (2/3:ℝ)<s.re at hs; linarith)
  exact hdif.analyticOnNhd (Complex.isOpen_re_gt _)

/-- A summable original-factor bound when the reference real part exceeds 2/3. -/
def extendedMajorant (sigma : ℝ) (P : PrimeIdeal) : ℝ :=
  20*(Ideal.absNorm P.val:ℝ)^(-principalExponent sigma)

theorem extendedMajorant_summable {sigma : ℝ} (hsigma : 2/3<sigma) :
    Summable (extendedMajorant sigma) := by
  have hs := principalExponent_gt_one hsigma
  have h : Summable (fun P : PrimeIdeal=>
      ‖CubicEisenstein.fullIdealWeight ((principalExponent sigma:ℝ):ℂ) P.val‖) :=
    (CubicEisenstein.fullIdealWeight_summable_norm ((principalExponent sigma:ℝ):ℂ)
      (by simpa using hs)).comp_injective Subtype.val_injective
  apply (h.mul_left 20).congr
  intro P
  unfold extendedMajorant CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp

/-- The original, unmodified principal correction is holomorphic and close
to one on any fixed half-plane strictly to the right of 2/3, after deleting
finitely many small primes. This is not a zero-free region theorem. -/
theorem exists_extended_principal_cutoff {sigma : ℝ} (hsigma : 2/3<sigma) :
    ∃N : ℕ,4≤N ∧ ∀S : Finset Id,
      (∀P : PrimeIdeal,Ideal.absNorm P.val≤N→P.val∈S)→
      ∀eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection eta S) {s : ℂ | sigma<s.re} ∧
        ∀s : ℂ,sigma<s.re→‖principalCorrection eta S s-1‖≤1/2 := by
  apply exists_tail_cutoff principalLocal (extendedMajorant sigma) sigma
  · intro P; unfold extendedMajorant; positivity
  · exact extendedMajorant_summable hsigma
  · intro eta P hP
    exact (principalLocal_extended_analytic eta P hP).mono
      (fun s hs=>lt_trans hsigma hs)
  · intro eta P hP s hs
    apply unramified_principal_bound
    · exact_mod_cast hP
    · exact actualAPhase_norm_le_one eta _
    · exact ProbeRow.targetMonoid_norm_le_one eta _
    · exact hsigma
    · exact hs

theorem principal_R_eq (Q : ℝ) (A s : ℂ) :
    coordR Q A s (1/6)=A*(Q:ℂ)^(3-6*s) := by
  unfold coordR
  congr 2
  ring

theorem residualLocal_eq_angular_mul (eta : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (s : ℂ) (hs : 2/3<s.re) :
    residualLocal eta P s=
      (1-coordR (Ideal.absNorm P.val)
        (actualAPhase eta (CompletedGauss.primaryGenerator P.val)) s (1/6))*
        principalLocal eta P s := by
  let Q : ℝ := Ideal.absNorm P.val
  let A := actualAPhase eta (CompletedGauss.primaryGenerator P.val)
  let e := HeckeFamily.elementCoeff eta (CompletedGauss.primaryGenerator P.val)
  have hQ : 4≤Q := by dsimp [Q]; exact_mod_cast hP
  have hQ0 : 0<Q := by linarith
  have hA : ‖A‖≤1 := actualAPhase_norm_le_one eta _
  have he : ‖e‖≤1 := ProbeRow.targetMonoid_norm_le_one eta _
  have hRn : 1-coordR Q A s (1/6)≠0 := by
    apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
    apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
    apply rpow_le_half Q _ hQ
    norm_num
    linarith
  have hDn : 1-coordD Q e 1 s≠0 := by
    apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
    apply (coordD_norm_le Q hQ0 e 1 s he (by simp)).trans
    exact rpow_le_half Q _ hQ (by linarith)
  have hqn : 1-(Q:ℂ)⁻¹≠0 := by
    apply ProbeLocal.one_sub_ne_zero_of_norm_le_half
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    rw [div_le_iff₀ hQ0]
    linarith
  change residualFactor (Q:ℂ)⁻¹ (coordR Q A s (1/6)) (coordD Q e 1 s)=
    (1-coordR Q A s (1/6))*unramifiedClosed Q A e 1 s 1 (1/6)
  rw [unramified_principal_factorization Q hQ0 A e s hqn hRn hDn]
  field_simp

/-- Exact finite extraction, with actual phases and every prime unchanged. -/
theorem finite_angular_factorization (eta : HeckeFamily.Character) (F : Finset PrimeIdeal)
    (hF : ∀P∈F,4≤Ideal.absNorm P.val) (s : ℂ) (hs : 2/3<s.re) :
    (∏P∈F,residualLocal eta P s)=
      (∏P∈F,(1-actualAPhase eta (CompletedGauss.primaryGenerator P.val)*
        (Ideal.absNorm P.val:ℂ)^(3-6*s)))*(∏P∈F,principalLocal eta P s) := by
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rw [residualLocal_eq_angular_mul eta P (hF P hP) s hs,principal_R_eq]
  norm_cast

theorem actualAPhase_ideal_mul (eta : HeckeFamily.Character) (I J : Id) :
    actualAPhase eta (CompletedGauss.primaryGenerator (I*J))=
      actualAPhase eta (CompletedGauss.primaryGenerator I)*
        actualAPhase eta (CompletedGauss.primaryGenerator J) := by
  rw [CompletedGauss.primaryGenerator_mul]
  simp only [actualAPhase,CompletedGauss.angularFactor_mul,HeckeFamily.elementCoeff_mul,
    star_mul,mul_pow]
  ring

/-- The actual angular/finite-target character of the extracted ideal channel. -/
def angularCharacter (eta : HeckeFamily.Character) : Id→*ℂ where
  toFun I:=actualAPhase eta (CompletedGauss.primaryGenerator I)
  map_one' := by
    simp only [actualAPhase,CompletedGauss.primaryGenerator_one,FiniteGaussPhase.angularFactor,
      map_one,norm_one,Complex.ofReal_one,div_one,star_one,one_pow,
      HeckeFamily.elementCoeff_one,one_mul]
  map_mul' := actualAPhase_ideal_mul eta

theorem actual_R_eq_angular_character (eta : HeckeFamily.Character) (P : PrimeIdeal) (s : ℂ) :
    coordR (Ideal.absNorm P.val)
      (actualAPhase eta (CompletedGauss.primaryGenerator P.val)) s (1/6)=
        angularCharacter eta P.val*(Ideal.absNorm P.val:ℂ)^(-(6*s-3)) := by
  rw [principal_R_eq]
  change _=actualAPhase eta (CompletedGauss.primaryGenerator P.val)*
    (Ideal.absNorm P.val:ℂ)^(-(6*s-3))
  push_cast
  congr 2
  ring

theorem angular_channel_euler_domain (s : ℂ) :
    1<(6*s-3).re ↔ 2/3<s.re := by
  simp only [Complex.sub_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,sub_zero]
  constructor <;> intro h <;> linarith

theorem prime_norm_power_summable {r : ℝ} (hr : 1<r) :
    Summable (fun P : PrimeIdeal=>(Ideal.absNorm P.val:ℝ)^(-r)) := by
  have h : Summable (fun P : PrimeIdeal=>
      ‖CubicEisenstein.fullIdealWeight (r:ℂ) P.val‖) :=
    (CubicEisenstein.fullIdealWeight_summable_norm (r:ℂ)
      (by simpa using hr)).comp_injective Subtype.val_injective
  apply h.congr
  intro P
  unfold CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  simp

theorem principalLocal_multipliable (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P : PrimeIdeal,P.val∉S→4≤Ideal.absNorm P.val)
    (s : ℂ) (hs : 2/3<s.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>principalLocal eta P.val s) := by
  let sigma := ((2/3:ℝ)+s.re)/2
  have hsigma : 2/3<sigma := by dsimp [sigma]; linarith
  have hss : sigma<s.re := by dsimp [sigma]; linarith
  have hb := (extendedMajorant_summable hsigma).subtype (fun P : PrimeIdeal=>P.val∉S)
  have he : Summable (fun P : {P : PrimeIdeal // P.val∉S}=>‖principalLocal eta P.val s-1‖) := by
    apply hb.of_nonneg_of_le (fun _=>norm_nonneg _)
    intro P
    apply unramified_principal_bound
    · exact_mod_cast hS P.val P.property
    · exact actualAPhase_norm_le_one eta _
    · exact ProbeRow.targetMonoid_norm_le_one eta _
    · exact hsigma
    · exact hss
  exact (multipliable_one_add_of_summable he).congr (fun _=>by simp)

theorem angularFactor_multipliable (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P : PrimeIdeal,P.val∉S→4≤Ideal.absNorm P.val)
    (s : ℂ) (hs : 2/3<s.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>
      1-coordR (Ideal.absNorm P.val.val)
        (actualAPhase eta (CompletedGauss.primaryGenerator P.val.val)) s (1/6)) := by
  let r := 6*s.re-3
  have hr : 1<r := by dsimp [r]; linarith
  have hb := (prime_norm_power_summable hr).subtype (fun P : PrimeIdeal=>P.val∉S)
  have he : Summable (fun P : {P : PrimeIdeal // P.val∉S}=>
      ‖-coordR (Ideal.absNorm P.val.val)
        (actualAPhase eta (CompletedGauss.primaryGenerator P.val.val)) s (1/6)‖) := by
    apply hb.of_nonneg_of_le (fun _=>norm_nonneg _)
    intro P
    rw [norm_neg]
    have hQ0 : 0<(Ideal.absNorm P.val.val:ℝ) :=
      lt_of_lt_of_le (by norm_num : (0:ℝ)<4) (by exact_mod_cast hS P.val P.property)
    have hn := coordR_norm_le (Ideal.absNorm P.val.val) hQ0
      (actualAPhase eta (CompletedGauss.primaryGenerator P.val.val)) s (1/6)
      (actualAPhase_norm_le_one eta _)
    have hexp : 4-6*s.re-6*(1/6:ℂ).re = -r := by
      dsimp [r]
      norm_num
      ring
    rw [hexp] at hn
    exact hn
  exact (multipliable_one_add_of_summable he).congr (fun _=>by simp only [sub_eq_add_neg])

/-- The infinite extraction is justified only in its convergent Euler domain. -/
theorem correction_factorization (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P : PrimeIdeal,P.val∉S→4≤Ideal.absNorm P.val)
    (s : ℂ) (hs : 2/3<s.re) :
    residualCorrection eta S s=
      (∏'P : {P : PrimeIdeal // P.val∉S},
        (1-angularCharacter eta P.val.val*(Ideal.absNorm P.val.val:ℂ)^(-(6*s-3))))*
        principalCorrection eta S s := by
  have hA := angularFactor_multipliable eta S hS s hs
  have hP := principalLocal_multipliable eta S hS s hs
  have heq (P : {P : PrimeIdeal // P.val∉S}) :=
    residualLocal_eq_angular_mul eta P.val (hS P.val P.property) s hs
  unfold residualCorrection principalCorrection
  calc
    _=(∏'P : {P : PrimeIdeal // P.val∉S},
        ((1-coordR (Ideal.absNorm P.val.val)
          (actualAPhase eta (CompletedGauss.primaryGenerator P.val.val)) s (1/6))*
          principalLocal eta P.val s)) := tprod_congr heq
    _=(∏'P : {P : PrimeIdeal // P.val∉S},
        (1-coordR (Ideal.absNorm P.val.val)
          (actualAPhase eta (CompletedGauss.primaryGenerator P.val.val)) s (1/6)))*
          (∏'P : {P : PrimeIdeal // P.val∉S},principalLocal eta P.val s) := hA.tprod_mul hP
    _=_ := by simp only [actual_R_eq_angular_character]

end OpenAIReview.PrincipalEuler

#lint+ in OpenAIReview.PrincipalEuler

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    unless (n.toString.splitOn "OpenAIReview.PrincipalEuler").length > 1 do continue
    declarations := declarations + 1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems + 1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations > 0 do throwError "Empty principal Euler audit."
  logInfo m!"Principal Euler audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.writeFile "principal-euler-axioms.json"
    (Json.mkObj [("scope",toJson "actual principal Euler factor; no zero-free claim"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
