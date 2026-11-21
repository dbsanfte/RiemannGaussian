import CheckAlpogeCubicTypeI

/-! # Averaging the constant divisor rows in the cubic window -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real MeasureTheory
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

/-- The positive multiples of a stride in the arithmetic coefficient. -/
def strideUnit (e p : ℕ) : ℝ := if e ∣ p then if p/e = 0 then 0 else 1 else 0

theorem strideUnit_prefix {e : ℕ} (he : 0 < e) (x : ℝ) :
    coefficientPrefix (strideUnit e) x = (⌊x/(e:ℝ)⌋₊:ℝ) := by
  unfold coefficientPrefix strideUnit
  rw [← sum_filter, sum_stride (fun k => if k = 0 then (0:ℝ) else 1) _ he,
    Nat.floor_div_natCast]
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le (⌊x⌋₊/e))]
  have hs : ∑ k ∈ Ioc 0 (⌊x⌋₊/e), (if k=0 then (0:ℝ) else 1) =
      ∑ _k ∈ Ioc 0 (⌊x⌋₊/e), (1:ℝ) := by
    apply sum_congr rfl
    intro k hk
    simp [(mem_Ioc.mp hk).1.ne']
  rw [hs]
  simp [Nat.card_Ioc]

private theorem strideUnit_reciprocal_prefix {e : ℕ} (he : 0 < e) (X : ℕ) :
    coefficientPrefix (fun p => strideUnit e p / p) (X:ℝ) =
      (harmonic (X/e):ℝ)/e := by
  unfold coefficientPrefix
  rw [Nat.floor_natCast]
  have hterm (p : ℕ) :
      strideUnit e p / p = if e ∣ p then (e:ℝ)⁻¹*((p/e:ℕ):ℝ)⁻¹ else 0 := by
    by_cases hp : e ∣ p
    · obtain ⟨k,rfl⟩ := hp
      rw [strideUnit, ite_eq_left (dvd_mul_right e k), ite_eq_left (dvd_mul_right e k),
        Nat.mul_div_cancel_left k he]
      by_cases hk : k=0
      · simp [hk]
      · simp [hk,Nat.cast_mul,div_eq_mul_inv,mul_comm]
    · simp [strideUnit,hp]
  simp_rw [hterm]
  rw [← sum_filter, sum_stride (fun k => (e:ℝ)⁻¹*(k:ℝ)⁻¹) _ he, ← mul_sum,
    harmonic_eq_sum_Icc, Rat.cast_sum]
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le (X/e)), Nat.cast_zero, inv_zero, zero_add,
    show Ioc 0 (X/e) = Icc 1 (X/e) by ext k; simp only [mem_Ioc,mem_Icc]; omega]
  simp only [Rat.cast_inv,Rat.cast_natCast,div_eq_mul_inv,mul_comm]

/-- Fractional remainder along a real progression with spacing e. -/
def strideFraction (e : ℕ) (x : ℝ) : ℝ :=
  x/(e:ℝ)-(⌊x/(e:ℝ)⌋₊:ℝ)

theorem strideFraction_integral_exact {M D e : ℕ} (he : 0 < e) (heD : e ≤ D) (hDM : D ≤ M) :
    (∫ x in (D:ℝ)..(M:ℝ), strideFraction e x/x^2) -
        (1/2:ℝ)*((D:ℝ)⁻¹-(M:ℝ)⁻¹) =
      (tailQuadrature D e id/(D:ℝ)-tailQuadrature M e id/(M:ℝ))/(e:ℝ) := by
  have hD := he.trans_le heD
  have hd : 0 < (D:ℝ) := by exact_mod_cast hD
  have hb : (D:ℝ) ≤ M := by exact_mod_cast hDM
  have hM := hd.trans_le hb
  have hE : 0 < (e:ℝ) := by exact_mod_cast he
  have hrecip := coefficient_reciprocal_sum (strideUnit e) hD hDM
  rw [← coefficientPrefix_sub (fun p => strideUnit e p / p) hDM,
    strideUnit_reciprocal_prefix he M,strideUnit_reciprocal_prefix he D] at hrecip
  simp_rw [strideUnit_prefix he,Nat.floor_div_natCast,Nat.floor_natCast] at hrecip
  simp_rw [← Nat.floor_div_natCast] at hrecip
  have hdiv : IntervalIntegrable (fun x : ℝ => (x/e)/x^2) volume D M := by
    have hc : ContinuousOn (fun x : ℝ => (x/e)/x^2) (Set.Icc (D:ℝ) M) :=
      (continuousOn_id.div_const _).div (continuousOn_id.pow 2) fun _ hx =>
        pow_ne_zero _ (hd.trans_le hx.1).ne'
    exact hc.intervalIntegrable_of_Icc hb
  have hfloor : IntervalIntegrable (fun x => (⌊x/(e:ℝ)⌋₊:ℝ)/x^2) volume D M := by
    simpa only [strideUnit_prefix he] using coefficient_kernel_integrable (strideUnit e) hd hb
  have hmodel : (∫ x in (D:ℝ)..(M:ℝ), (x/e)/x^2) = log ((M:ℝ)/D)/e := by
    simp_rw [show ∀ x : ℝ, (x/(e:ℝ))/x^2 = (e:ℝ)⁻¹*(x/x^2) by
      intro x; simp only [div_eq_mul_inv]; ring]
    rw [intervalIntegral.integral_const_mul, id_kernel_integral hd hb]
    ring
  have hlog : log ((M:ℝ)/D) = log ((M:ℝ)/e)-log ((D:ℝ)/e) := by
    rw [log_div hM.ne' hd.ne', log_div hM.ne' hE.ne', log_div hd.ne' hE.ne']
    ring
  simp only [strideFraction,sub_div]
  rw [intervalIntegral.integral_sub hdiv hfloor,hmodel,hlog,
    id_tailQuadrature_formula he heD,id_tailQuadrature_formula he (heD.trans hDM)]
  have hval : (∫ x in (D:ℝ)..(M:ℝ), (↑⌊x/(e:ℝ)⌋₊:ℝ)/x^2) =
      (harmonic (M/e):ℝ)/e-(harmonic (D/e):ℝ)/e -
        ((M/e:ℕ):ℝ)/M+((D/e:ℕ):ℝ)/D := by linarith only [hrecip]
  rw [hval]
  field_simp
  ring

/-- Replacing the fractional remainder by one half in the integral
costs only one stride times the inverse squares of the endpoints. -/
theorem strideFraction_integral_error {M D e : ℕ} (he : 0 < e) (heD : e ≤ D) (hDM : D ≤ M) :
    |(∫ x in (D:ℝ)..(M:ℝ), strideFraction e x/x^2) -
        (1/2:ℝ)*((D:ℝ)⁻¹-(M:ℝ)⁻¹)| ≤
      8*(e:ℝ)/D^2+8*(e:ℝ)/M^2 := by
  have hd : 0 < (D:ℝ) := by exact_mod_cast he.trans_le heD
  have hm : 0 < (M:ℝ) := by exact_mod_cast he.trans_le (heD.trans hDM)
  have hE : 0 < (e:ℝ) := by exact_mod_cast he
  have ha (X : ℕ) (hX : e ≤ X) :
      |tailQuadrature X e id/(X:ℝ)-eulerMascheroniConstant| ≤ 8*(e:ℝ)^2/X^2 := by
    have hx : 0 < (X:ℝ) := by exact_mod_cast he.trans_le hX
    rw [show tailQuadrature X e id/(X:ℝ)-eulerMascheroniConstant =
        (tailQuadrature X e id-eulerMascheroniConstant*X)/X by field_simp,
      abs_div,abs_of_pos hx]
    exact (div_le_div_of_nonneg_right (id_tailQuadrature_error he hX) hx.le).trans_eq (by ring)
  rw [strideFraction_integral_exact he heD hDM,abs_div,abs_of_pos hE]
  rw [show tailQuadrature D e id/(D:ℝ)-tailQuadrature M e id/(M:ℝ) =
    (tailQuadrature D e id/(D:ℝ)-eulerMascheroniConstant) -
      (tailQuadrature M e id/(M:ℝ)-eulerMascheroniConstant) by ring]
  have h := (abs_sub _ _).trans (add_le_add (ha D heD) (ha M (heD.trans hDM)))
  exact (div_le_div_of_nonneg_right h hE.le).trans_eq (by field_simp)

private theorem strideFraction_nat (M : ℕ) {e j : ℕ} (he : 0 < e) (hj : 0 < j) :
    strideFraction e ((M:ℝ)/j) = 1-weight M (e*j) := by
  have hP : 0 < (e*j:ℕ) := Nat.mul_pos he hj
  have hP0 : (↑(e*j:ℕ):ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have heq : ((M:ℝ)/(j:ℝ))/(e:ℝ) = (M:ℝ)/((e*j:ℕ):ℝ) := by
    have he0 : (e:ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have hj0 : (j:ℝ) ≠ 0 := by exact_mod_cast hj.ne'
    rw [Nat.cast_mul]
    field_simp
  rw [strideFraction,heq,Nat.floor_div_natCast,Nat.floor_natCast,weight]
  have hmod : ((M%(e*j):ℕ):ℝ)+((e*j:ℕ):ℝ)*(M/(e*j):ℕ) = M := by
    exact_mod_cast Nat.mod_add_div M (e*j)
  field_simp
  nlinarith only [hmod]

/-- The constant-density approximation error for one progression. -/
def strideUnitError (M D e : ℕ) : ℝ :=
  tailQuadratureSumIntegral M D (coefficientPrefix (strideUnit e)) -
    tailQuadratureSumIntegral M D (fun x => x/(e:ℝ))

theorem strideUnitError_eq {M D e : ℕ} (he : 0 < e) (heD : e ≤ D) (hDM : D ≤ M) :
    strideUnitError M D e =
      (M:ℝ)*(∫ x in (D:ℝ)..(M:ℝ), strideFraction e x/x^2) -
        ∑ j ∈ Icc 1 (M/D), strideFraction e ((M:ℝ)/j) := by
  have hd : 0 < (D:ℝ) := by exact_mod_cast he.trans_le heD
  have hab : (D:ℝ) ≤ M := by exact_mod_cast hDM
  have hcont : ContinuousOn (fun x : ℝ => (x/e)/x^2) (Set.Icc (D:ℝ) M) :=
    (continuousOn_id.div_const _).div (continuousOn_id.pow 2) fun _ hx =>
      pow_ne_zero _ (hd.trans_le hx.1).ne'
  have hdiv : IntervalIntegrable (fun x : ℝ => (x/e)/x^2) volume D M :=
    hcont.intervalIntegrable_of_Icc hab
  have hfloor : IntervalIntegrable (fun x => (⌊x/(e:ℝ)⌋₊:ℝ)/x^2) volume D M := by
    simpa only [strideUnit_prefix he] using coefficient_kernel_integrable (strideUnit e) hd hab
  simp only [strideUnitError,tailQuadratureSumIntegral,strideUnit_prefix he,strideFraction,sub_div,
    intervalIntegral.integral_sub hdiv hfloor,sum_sub_distrib]
  ring

private theorem repeated_abs_bound {W k A : ℕ} (hW : 0 < W)
    {f : ℕ → ℝ} {B : ℝ} (h : ∀ M, A ≤ M → M ≤ A+k*(W-1) → |f M| ≤ B) :
    |repeatedMean W k f A| ≤ B := by
  have hhi := repeat_mono W k A (f := f) (g := fun _ => B) fun M hAM hM =>
    (abs_le.mp (h M hAM hM)).2
  have hlo := repeat_mono W k A (f := fun _ => -B) (g := f) fun M hAM hM =>
    (abs_le.mp (h M hAM hM)).1
  exact abs_le.mpr ⟨by simpa only [repeat_const hW k A] using hlo,
    by simpa only [repeat_const hW k A] using hhi⟩

private theorem strideFraction_sample_error {M D e n : ℕ}
    (hn : 1 ≤ n) (hDe : D = n^3) (he : 0 < e) (hen : e ≤ n^2)
    (hDM : D ≤ M) (hM : M ≤ 2*n^4) :
    |(M:ℝ)*(∫ x in (D:ℝ)..(M:ℝ), strideFraction e x/x^2) -
      ((M:ℝ)/(2*(D:ℝ))-1/2)| ≤ 24 := by
  have heD : e ≤ D := by
    rw [hDe, pow_succ]
    exact hen.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hm0 : 0 < (M:ℝ) := by exact_mod_cast he.trans_le (heD.trans hDM)
  have hd0 : 0 < (D:ℝ) := by exact_mod_cast he.trans_le heD
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hr : (M:ℝ) ≤ 2*(n:ℝ)^4 := by exact_mod_cast hM
  have heR : (e:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hen
  have hcost1 : 8*(e:ℝ)*M/(D:ℝ)^2 ≤ 16 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd0)).mpr
    rw [hDe, Nat.cast_pow]
    have hh := mul_le_mul heR hr hm0.le (sq_nonneg (n:ℝ))
    nlinarith only [hh]
  have hcost2 : 8*(e:ℝ)/M ≤ 8 := by
    apply (div_le_iff₀ hm0).mpr
    have hh : (e:ℝ) ≤ M := by exact_mod_cast heD.trans hDM
    linarith only [hh]
  have hterm : (M:ℝ)*((1/2:ℝ)*((D:ℝ)⁻¹-(M:ℝ)⁻¹)) =
      (M:ℝ)/(2*(D:ℝ))-1/2 := by field_simp
  rw [← hterm, ← mul_sub, abs_mul, abs_of_pos hm0]
  calc
    _ ≤ (M:ℝ)*(8*(e:ℝ)/D^2+8*(e:ℝ)/M^2) :=
      mul_le_mul_of_nonneg_left (strideFraction_integral_error he heD hDM) hm0.le
    _ = 8*(e:ℝ)*M/(D:ℝ)^2+8*(e:ℝ)/M := by field_simp
    _ ≤ _ := by linarith only [hcost1,hcost2]

private theorem fixed_stride_rows_error {n e R A : ℕ} (hn : 1 ≤ n) (he : 0 < e)
    (hen : e ≤ n^2) (hR : 1 ≤ R) (hRn : R ≤ n) :
    |repeatedMean (2*n^3+1) (Nat.log 2 n+1)
      (fun M => ∑ j ∈ Icc 1 R, strideFraction e ((M:ℝ)/j)) A - (R:ℝ)/2| ≤
        (1+log n)/2+1 := by
  let W := 2*n^3+1
  let k := Nat.log 2 n+1
  let L := repeatedMean W k
  have hw : 0 < W := by dsimp [W]; omega
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hpow : (1/2:ℝ)^k ≤ (n:ℝ)⁻¹ := by
    rw [div_pow,one_pow]
    have hb : (n:ℝ) ≤ 2^k := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
    exact (one_div_le_one_div_of_le hn0 hb).trans_eq (one_div _)
  have hrow (j : ℕ) (hj : j ∈ Icc 1 R) :
      |L (fun M => strideFraction e ((M:ℝ)/j)) A-1/2| ≤ 1/(2*(j:ℝ))+(n:ℝ)⁻¹ := by
    have hj0 : 0 < j := (mem_Icc.mp hj).1
    have hp := Nat.mul_pos he hj0
    have hpD : e*j ≤ n^3 := by
      have hh := Nat.mul_le_mul hen ((mem_Icc.mp hj).2.trans hRn)
      simpa only [pow_succ] using hh
    have hjR : 0 < (j:ℝ) := by exact_mod_cast hj0
    have hpR : (j:ℝ) ≤ ((e*j:ℕ):ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left j he
    have hratio : (((e*j:ℕ):ℝ)/(W:ℝ)) ≤ 1/2 := by
      apply (div_le_iff₀ (Nat.cast_pos.mpr hw)).mpr
      have hb : ((e*j:ℕ):ℝ) ≤ (n:ℝ)^3 := by exact_mod_cast hpD
      push_cast at hb
      dsimp only [W]
      push_cast
      linarith only [hb]
    have hper := repeated_weight_error hp hw k A
    have hc : (fun M : ℕ => strideFraction e ((M:ℝ)/j)) =
        (fun _ : ℕ => (1:ℝ))-(fun M : ℕ => weight M (e*j)) := by
      funext M
      exact strideFraction_nat M he hj0
    rw [hc,map_sub,Pi.sub_apply,show L (fun _ => (1:ℝ)) A=1 from repeat_const hw k A 1]
    rw [show 1-L (fun M => weight M (e*j)) A-1/2 =
      -(L (fun M => weight M (e*j)) A-(1/2+1/(2*((e*j:ℕ):ℝ)))) -
        1/(2*((e*j:ℕ):ℝ)) by ring]
    apply (abs_sub _ _).trans
    rw [abs_neg,abs_of_nonneg (by positivity : 0 ≤ 1/(2*((e*j:ℕ):ℝ)))]
    have hp1 := pow_le_pow_left₀
      (by positivity : 0 ≤ (((e*j:ℕ):ℝ)/(W:ℝ))) hratio k
    have hinv : 1/(2*((e*j:ℕ):ℝ)) ≤ 1/(2*(j:ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith only [hpR])
    linarith only [hper,hp1,hpow,hinv]
  have hsum : (fun M : ℕ => ∑ j ∈ Icc 1 R, strideFraction e ((M:ℝ)/j)) =
      ∑ j ∈ Icc 1 R, (fun M : ℕ => strideFraction e ((M:ℝ)/j)) := by
    funext M
    rw [Finset.sum_apply]
  have hhalf : ∑ _j ∈ Icc 1 R, (1/2:ℝ) = (R:ℝ)/2 := by
    simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  change |L (fun M => ∑ j ∈ Icc 1 R, strideFraction e ((M:ℝ)/j)) A-(R:ℝ)/2| ≤ _
  rw [hsum,map_sum,Finset.sum_apply,← hhalf,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  refine (sum_le_sum hrow).trans ?_
  simp only [show ∀ j : ℕ, 1/(2*(j:ℝ)) = (1/2:ℝ)*(j:ℝ)⁻¹ by intro j; rw [div_eq_mul_inv, mul_inv]; ring,
    sum_add_distrib,← mul_sum,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
  have hharm := primeWindow_harmonic_le (b := R) (by decide : 1 ≤ 1)
  have hlog := log_le_log (show 0 < (R:ℝ) by exact_mod_cast hR)
    (show (R:ℝ) ≤ n by exact_mod_cast hRn)
  have hmass : (R:ℝ)*(n:ℝ)⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (show (R:ℝ) ≤ n by exact_mod_cast hRn) (by positivity : 0 ≤ (n:ℝ)⁻¹)
    rwa [mul_inv_cancel₀ hn0.ne'] at h
  linarith only [hharm,hlog,hmass]

/-- Averaging matches the discrete fractional remainders to the half-density
integral, with only a logarithmic error for every stride through n squared. -/
theorem averaged_strideUnitError {n e : ℕ} (hn : 8 ≤ n) (he : 0 < e) (hen : e ≤ n^2) :
    |repeatedMean (2*n^3+1) (Nat.log 2 n+1) (fun M => strideUnitError M (n^3) e)
      (n^4-(Nat.log 2 n+1)*n^3)| ≤ 27+3*((Nat.log 2 n+1:ℕ):ℝ)+log n := by
  let k := Nat.log 2 n+1
  let D := n^3
  let W := 2*D+1
  let R := n-k
  let A := n^4-k*D
  let L := repeatedMean W k
  let S (M : ℕ) := ∑ j ∈ Icc 1 (M/D), strideFraction e ((M:ℝ)/j)
  let P (M : ℕ) := ∑ j ∈ Icc 1 R, strideFraction e ((M:ℝ)/j)
  let I (M : ℕ) := (M:ℝ)*(∫ x in (D:ℝ)..(M:ℝ), strideFraction e x/x^2)
  let J (M : ℕ) := (M:ℝ)/(2*(D:ℝ))-1/2
  obtain ⟨hk,_⟩ := cubic_tail_parameters hn
  have hn1 : 1 ≤ n := by omega
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hRn : R ≤ n := Nat.sub_le _ _
  have hRk : R+k=n := Nat.sub_add_cancel (by omega)
  have hD : 0 < D := by dsimp [D]; positivity
  have hd : 0 < (D:ℝ) := by exact_mod_cast hD
  have hW : 0 < W := by dsimp [W]; omega
  have heD : e ≤ D := by
    dsimp only [D]
    rw [pow_succ]
    exact hen.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hN : n*D=n^4 := by dsimp [D]; ring
  have hAeq : A=R*D := by
    have h := congrArg (fun t : ℕ => t*D) hRk
    rw [Nat.add_mul,hN] at h
    dsimp [A]
    omega
  have hDA : D ≤ A := by
    rw [hAeq]
    exact Nat.le_mul_of_pos_left D (by omega)
  have hmid : A+k*D=n^4 := by
    rw [hAeq,← Nat.add_mul,hRk,hN]
  have hmax : A+k*(W-1) = (n+k)*D := by
    have hw : W-1=2*D := by dsimp [W]
    rw [hw,show k*(2*D)=k*D+k*D by ring,← Nat.add_assoc,hmid]
    calc n^4+k*D = n*D+k*D := by rw [hN]
         _ = (n+k)*D := (Nat.add_mul _ _ _).symm
  have hI : |L I A-L J A| ≤ 24 := by
    rw [← Pi.sub_apply,← map_sub]
    apply repeated_abs_bound hW
    intro M hm hM
    have hM2 : M ≤ 2*n^4 := by
      have h := Nat.mul_le_mul_right D (show n+k ≤ 2*n by omega)
      rw [Nat.mul_assoc,hN] at h
      exact (hM.trans_eq hmax).trans h
    exact strideFraction_sample_error hn1 rfl he hen (hDA.trans hm) hM2
  have hJ : L J A=(n:ℝ)/2-1/2 := by
    have heq : J = (1/(2*(D:ℝ))) • (fun M : ℕ => (M:ℝ))-(fun _ => (1/2:ℝ)) := by
      funext M
      simp only [J,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
      ring
    rw [heq,map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      show L (fun _ => (1/2:ℝ)) A=1/2 from repeat_const hW k A _]
    have hfirst : L (fun M : ℕ => (M:ℝ)) A=(n:ℝ)^4 :=
      (repeat_first_moment D k A).trans (by exact_mod_cast hmid)
    rw [hfirst]
    dsimp only [D]
    push_cast
    field_simp
  have hfixed : |L P A-(R:ℝ)/2| ≤ (1+log n)/2+1 :=
    fixed_stride_rows_error hn1 he hen hR hRn
  have hmoving : |L S A-L P A| ≤ 2*(k:ℝ) := by
    rw [← Pi.sub_apply,← map_sub]
    apply repeated_abs_bound hW
    intro M hm hM
    have hRq : R ≤ M/D := (Nat.le_div_iff_mul_le hD).mpr (by rwa [← hAeq])
    have hq : M/D ≤ n+k := by
      have h := Nat.div_le_div_right (hM.trans_eq hmax) (c := D)
      simpa only [Nat.mul_div_cancel _ hD] using h
    have heq : S M-P M = ∑ j ∈ Ioc R (M/D), strideFraction e ((M:ℝ)/j) := by
      dsimp only [S,P]
      have he (t : ℕ) : Icc 1 t = Ioc 0 t := by ext j; simp only [mem_Icc,mem_Ioc]; omega
      have hsplit := sum_Ioc_consecutive
        (f := fun j : ℕ => strideFraction e ((M:ℝ)/j)) (Nat.zero_le R) hRq
      rw [he (M/D),he R,← hsplit]
      ring
    rw [show (S-P) M=S M-P M from rfl,heq]
    have hterm (j : ℕ) (hj : j ∈ Ioc R (M/D)) :
        0 ≤ strideFraction e ((M:ℝ)/j) ∧ strideFraction e ((M:ℝ)/j) ≤ 1 := by
      have hj0 := (mem_Ioc.mp hj).1.trans_le' (Nat.zero_le R)
      rw [strideFraction_nat M he hj0]
      have hh := weight_mem (N := M) (Nat.mul_pos he hj0)
      constructor <;> linarith only [hh.1,hh.2]
    rw [abs_of_nonneg (sum_nonneg fun j hj => (hterm j hj).1)]
    apply (sum_le_sum (g := fun _ => (1:ℝ)) fun j hj => (hterm j hj).2).trans
    simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one]
    exact_mod_cast (show M/D-R ≤ 2*k by omega)
  have heq : L (fun M => strideUnitError M D e) A=L I A-L S A := by
    rw [← Pi.sub_apply,← map_sub]
    apply le_antisymm
    · apply repeat_mono
      intro M hm _
      exact (strideUnitError_eq he heD (hDA.trans hm)).le
    · apply repeat_mono
      intro M hm _
      exact (strideUnitError_eq he heD (hDA.trans hm)).ge
  change |L (fun M => strideUnitError M D e) A| ≤ _
  rw [heq]
  obtain ⟨hIL,hIU⟩ := abs_le.mp hI
  obtain ⟨hPL,hPU⟩ := abs_le.mp hfixed
  obtain ⟨hSL,hSU⟩ := abs_le.mp hmoving
  have hRreal : (R:ℝ)+(k:ℝ)=n := by exact_mod_cast hRk
  rw [hJ] at hIL hIU
  apply abs_le.mpr
  constructor <;> linarith only [hIL,hIU,hPL,hPU,hSL,hSU,hRreal,
    Nat.cast_nonneg (α := ℝ) k,log_nonneg hnR]

/-- Sampling error for the convolution of the two small-factor truncations with one. -/
def averagedCubicCrossError (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n, ∑ v ∈ Ioc 0 n, (μ d : ℝ)*Λ v*
    repeatedMean (2*n^3+1) (Nat.log 2 n+1) (fun M => strideUnitError M (n^3) (d*v))
      (n^4-(Nat.log 2 n+1)*n^3)

theorem averagedCubicCrossError_bound {n : ℕ} (hn : 8 ≤ n) :
    |averagedCubicCrossError n| ≤
      (log 4+4)*(n:ℝ)^2*(27+3*((Nat.log 2 n+1:ℕ):ℝ)+log n) := by
  let B := 27+3*((Nat.log 2 n+1:ℕ):ℝ)+log n
  let L := repeatedMean (2*n^3+1) (Nat.log 2 n+1)
  let A := n^4-(Nat.log 2 n+1)*n^3
  have hB : 0 ≤ B := by dsimp [B]; positivity [log_natCast_nonneg n]
  have hpsi : ∑ v ∈ Ioc 0 n, Λ v ≤ (log 4+4)*(n:ℝ) := by
    simpa [Chebyshev.psi] using Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
  change |∑ d ∈ Ioc 0 n, ∑ v ∈ Ioc 0 n,
    (μ d : ℝ)*Λ v*L (fun M => strideUnitError M (n^3) (d*v)) A| ≤ _
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _d ∈ Ioc 0 n, ∑ v ∈ Ioc 0 n, Λ v*B := by
      apply sum_le_sum
      intro d hd
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro v hv
      obtain ⟨hd0,hdn⟩ := mem_Ioc.mp hd
      obtain ⟨hv0,hvn⟩ := mem_Ioc.mp hv
      have h := averaged_strideUnitError hn (Nat.mul_pos hd0 hv0)
        (by simpa only [pow_two] using Nat.mul_le_mul hdn hvn)
      have hmu : |(μ d:ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hv0' : 0 ≤ Λ v := ArithmeticFunction.vonMangoldt_nonneg
      rw [abs_mul,abs_mul,abs_of_nonneg hv0']
      calc
        _ ≤ |(μ d:ℝ)| * Λ v * B :=
          mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg _) hv0')
        _ ≤ Λ v*B := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmu hv0') hB
    _ ≤ _ := by
      rw [← sum_mul,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]
      calc
        _ ≤ (n:ℝ)*(((log 4+4)*(n:ℝ))*B) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpsi hB) (Nat.cast_nonneg n)
        _ = _ := by ring

/-- The complete cubic-window sampling error of the small cross convolution
is bounded by a squared logarithm. -/
theorem cubicCross_window_error {m b : ℕ} (hm : 8 ≤ m) :
    ∑ n ∈ Icc m b, |averagedCubicCrossError n|/(n:ℝ)^3 ≤
      ((log 4+4)*(31+3/log 2))*(1+log b)^2 := by
  let C := (log 4+4)*(31+3/log 2)
  have hl2 : 0 < log (2:ℝ) := log_pos (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity [log_pos (by norm_num : (1:ℝ)<4)]
  have hb : 0 ≤ log (b:ℝ) := log_natCast_nonneg b
  calc
    _ ≤ ∑ n ∈ Icc m b, C*(1+log b)*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hn8 := hm.trans (mem_Icc.mp hn).1
      have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hlog := log_le_log hn0 (show (n:ℝ) ≤ b by exact_mod_cast (mem_Icc.mp hn).2)
      have hk := Real.natLog_le_logb n 2
      rw [← Real.log_div_log] at hk
      have hk' := hk.trans (div_le_div_of_nonneg_right hlog hl2.le)
      have hB : 27+3*((Nat.log 2 n+1:ℕ):ℝ)+log n ≤ (31+3/log 2)*(1+log b) := by
        push_cast
        rw [div_eq_mul_inv] at hk' ⊢
        nlinarith only [hk',hlog,hb,inv_nonneg.mpr hl2.le]
      have hp : 0 ≤ log (4:ℝ)+4 := by positivity [log_pos (by norm_num : (1:ℝ)<4)]
      apply (div_le_iff₀ (pow_pos hn0 3)).mpr
      have he : C*(1+log b)*(n:ℝ)⁻¹*(n:ℝ)^3 =
          (log 4+4)*(n:ℝ)^2*((31+3/log 2)*(1+log b)) := by
        dsimp [C]
        field_simp
      rw [he]
      exact (averagedCubicCrossError_bound hn8).trans
        (mul_le_mul_of_nonneg_left hB (mul_nonneg hp (sq_nonneg _)))
    _ ≤ _ := by
      rw [← mul_sum]
      exact (mul_le_mul_of_nonneg_left (primeWindow_harmonic_le (by omega : 1 ≤ m))
        (mul_nonneg hC (by linarith))).trans_eq (by dsimp [C]; ring)

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.strideFraction_integral_error,
      ``RiemannGaussian.AlpogeMined.averaged_strideUnitError,
      ``RiemannGaussian.AlpogeMined.cubicCross_window_error] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
