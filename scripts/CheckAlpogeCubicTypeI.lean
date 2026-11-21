import CheckAlpogeCubicQuadrature

/-! # Small-divisor control for the arithmetic window -/

namespace RiemannGaussian.AlpogeMined
noncomputable section
open Finset Real MeasureTheory
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt

/-- The logarithmic coefficient on the multiples of one positive divisor. -/
def strideLog (d p : ℕ) : ℝ := if d ∣ p then log (p/d:ℕ) else 0

/-- The divisor rows reconstruct the literal von Mangoldt coefficient. -/
theorem vonMangoldt_eq_moebius_strideLog (p : ℕ) :
    Λ p = ∑ d ∈ Ioc 0 p, (μ d:ℝ)*strideLog d p := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f p)
    ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
  rw [ArithmeticFunction.mul_apply] at h
  simp only [ArithmeticFunction.log_apply,ArithmeticFunction.intCoe_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (fun i j => (μ i:ℝ)*log (j:ℝ))] at h
  rw [← h]
  have hset : p.divisors = (Ioc 0 p).filter fun d => d ∣ p := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hp),Nat.le_of_dvd
        (Nat.pos_of_ne_zero hp) hd⟩,hd⟩
    · exact fun h => ⟨h.2,hp⟩
  rw [hset,sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : d ∣ p <;> simp [strideLog,hd]

/-- Reindexing a finite progression by its quotient. -/
theorem sum_stride (f : ℕ → ℝ) (X : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ p ∈ (Icc 0 X).filter (fun p => d ∣ p), f (p/d)) =
      ∑ k ∈ Icc 0 (X/d), f k := by
  classical
  symm
  refine sum_bij (fun k _ => d*k) ?_ ?_ ?_ ?_
  · intro k hk
    exact mem_filter.mpr
      ⟨mem_Icc.mpr ⟨Nat.zero_le _,by
        rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hd).mp (mem_Icc.mp hk).2⟩,dvd_mul_right d k⟩
  · intro k _ l _ hkl
    exact Nat.eq_of_mul_eq_mul_left hd hkl
  · intro p hp
    obtain ⟨hpX, hpd⟩ := mem_filter.mp hp
    exact ⟨p/d,mem_Icc.mpr ⟨Nat.zero_le _,Nat.div_le_div_right (mem_Icc.mp hpX).2⟩,
      Nat.mul_div_cancel' hpd⟩
  · intro k _
    rw [Nat.mul_div_cancel_left k hd]

theorem strideLog_prefix {d : ℕ} (hd : 0 < d) (x : ℝ) :
    coefficientPrefix (strideLog d) x = log (⌊x/(d:ℝ)⌋₊.factorial:ℕ) := by
  rw [Nat.floor_div_natCast]
  unfold coefficientPrefix strideLog
  rw [← sum_filter, sum_stride (fun k => log (k:ℝ)) _ hd]
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le (⌊x⌋₊/d)), Nat.cast_zero, log_zero, zero_add,
    show Ioc 0 (⌊x⌋₊/d) = Icc 1 (⌊x⌋₊/d) by ext k; simp only [mem_Ioc,mem_Icc]; omega]
  exact Formalism.LogFactorialMertensBounds.sum_log_eq_log_factorial _

/-- Continuous logarithmic density along a divisor row. -/
def strideLogMain (d : ℕ) (x : ℝ) : ℝ :=
  let t := x/(d:ℝ)
  t * log t-t

private theorem log_scaled_lower {s q : ℝ} (hq : 0 < q) (hs : 0 < s) :
    s-q ≤ s*log (s/q) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hq hs)
  rw [log_div hq.ne' hs.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h hs.le
  rw [show s*(q/s-1)=q-s by field_simp] at hm
  rw [log_div hs.ne' hq.ne']
  linarith only [hm]

theorem strideLog_prefix_error {d : ℕ} (hd : 0 < d) {x : ℝ} (hdx : (d:ℝ) ≤ x) :
    |coefficientPrefix (strideLog d) x-strideLogMain d x| ≤ 1+log x := by
  let s : ℝ := x/d
  let q := ⌊s⌋₊
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd
  have hd1 : 1 ≤ (d:ℝ) := by exact_mod_cast hd
  have hs1 : 1 ≤ s := (one_le_div hd0).mpr hdx
  have hs := zero_lt_one.trans_le hs1
  have hq1 : 1 ≤ q := (Nat.le_floor_iff hs.le).mpr (by simpa using hs1)
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast hq1
  have hqR : 1 ≤ (q:ℝ) := by exact_mod_cast hq1
  have hqs : (q:ℝ) ≤ s := Nat.floor_le hs.le
  have hsQ : s ≤ (q:ℝ)+1 := (Nat.lt_floor_add_one s).le
  have hsx : s ≤ x := div_le_self (hd0.le.trans hdx) hd1
  have hls := log_nonneg hs1
  have hlq := log_nonneg hqR
  have hu : (q:ℝ)*log (s/q) ≤ s-q := by
    have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hs hq0)) hq0.le
    exact h.trans_eq (by field_simp)
  have hL := log_scaled_lower hq0 hs
  rw [log_div hs.ne' hq0.ne'] at hu hL
  have hΔlo : 0 ≤ (s*log s-s)-((q:ℝ)*log q-q) := by
    nlinarith only [hL,mul_nonneg (sub_nonneg.mpr hqs) hlq]
  have hΔhi : (s*log s-s)-((q:ℝ)*log q-q) ≤ log s := by
    nlinarith only [hu,mul_le_mul_of_nonneg_right (show s-q≤1 by linarith only [hsQ]) hls]
  obtain ⟨hlo,hhi⟩ := factorial_remainder hq1
  rw [strideLog_prefix hd]
  change |log (q.factorial:ℝ)-(s*log s-s)| ≤ _
  have hlog := log_le_log hs hsx
  have hle := log_le_log hq0 (hqs.trans hsx)
  apply abs_le.mpr
  constructor <;> linarith only [hΔlo,hΔhi,hlo,hhi,hlog,hle,log_nonneg (hd1.trans hdx)]

/-- One stride can be replaced by its smooth density at one logarithmic
error per quotient row. -/
theorem strideLog_quadrature_error {M D d : ℕ} (hd : 0 < d) (hdD : d ≤ D) (hDM : D ≤ M) :
    |tailQuadratureSumIntegral M D (coefficientPrefix (strideLog d)) -
      tailQuadratureSumIntegral M D (strideLogMain d)| ≤
        2*(1+log M)*((M:ℝ)/D) := by
  have hD := hd.trans_le hdD
  have ha : 0 < (D:ℝ) := by exact_mod_cast hD
  have hab : (D:ℝ) ≤ M := by exact_mod_cast hDM
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hscaled : ContinuousOn (fun x : ℝ => x/d) (Set.Icc (D:ℝ) M) :=
    continuousOn_id.div_const _
  have hmodel : ContinuousOn (strideLogMain d) (Set.Icc (D:ℝ) M) :=
    (hscaled.mul (hscaled.log fun x hx => (div_pos (ha.trans_le hx.1) hdR).ne')).sub hscaled
  have hmain : IntervalIntegrable (fun x => strideLogMain d x/x^2) volume D M :=
    (hmodel.div (continuousOn_id.pow 2) fun _ hx =>
      pow_ne_zero _ (ha.trans_le hx.1).ne').intervalIntegrable_of_Icc hab
  have hrow := coefficient_kernel_integrable (strideLog d) ha hab
  rw [← tailQuadratureSumIntegral_sub M D hrow hmain]
  apply tailQuadratureSumIntegral_abs_le hD hDM
    (by linarith only [log_nonneg (by exact_mod_cast (show 1 ≤ M by omega) : 1 ≤ (M:ℝ))])
  · simp only [sub_div]
    exact hrow.sub hmain
  · intro x hx
    have hdx : (d:ℝ) ≤ x := (by exact_mod_cast hdD : (d:ℝ) ≤ D).trans hx.1
    exact (strideLog_prefix_error hd hdx).trans
      (by linarith only [log_le_log (ha.trans_le hx.1) hx.2])

/-- The small Möbius-divisor part of the logarithmic convolution keeps
its signed continuous main term, with an explicit total sampling cost. -/
theorem smallDivisor_log_quadrature_error {M D U : ℕ} (hD : 0 < D) (hUD : U ≤ D) (hDM : D ≤ M) :
    |∑ d ∈ Ioc 0 U, (μ d:ℝ) *
      (tailQuadratureSumIntegral M D (coefficientPrefix (strideLog d)) -
        tailQuadratureSumIntegral M D (strideLogMain d))| ≤
          (U:ℝ)*(2*(1+log M)*((M:ℝ)/D)) := by
  have hcost : 0 ≤ 2*(1+log M)*((M:ℝ)/D) :=
    by positivity [log_nonneg (by exact_mod_cast (show 1 ≤ M by omega) : 1 ≤ (M:ℝ))]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _d ∈ Ioc 0 U, 2*(1+log M)*((M:ℝ)/D) := by
      apply sum_le_sum
      intro d hd
      have hd1 := mem_Ioc.mp hd
      rw [abs_mul]
      have hμ : |(μ d:ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      exact (mul_le_mul hμ (strideLog_quadrature_error hd1.1 (hd1.2.trans hUD) hDM)
        (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = _ := by simp [Nat.card_Ioc,nsmul_eq_mul]

/-- At the cubic cutoff, all logarithmic rows with divisor at most n
can be sampled together at square-root cost times one logarithm. -/
theorem smallDivisor_log_quadrature_error_cubic {n M : ℕ}
    (hn : 1 ≤ n) (hlo : n^3 ≤ M) (hhi : M ≤ 2*n^4) :
    |∑ d ∈ Ioc 0 n, (μ d:ℝ) *
      (tailQuadratureSumIntegral M (n^3) (coefficientPrefix (strideLog d)) -
        tailQuadratureSumIntegral M (n^3) (strideLogMain d))| ≤
          4*(n:ℝ)^2*(1+log (2*(n:ℝ)^4)) := by
  have hD : 0 < n^3 := pow_pos (by omega) _
  have h := smallDivisor_log_quadrature_error hD (Nat.le_self_pow (by decide : 3 ≠ 0) n) hlo
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hM0 : 0 < (M:ℝ) := by exact_mod_cast hD.trans_le hlo
  have hM1 : 1 ≤ (M:ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
  have hM := show (M:ℝ) ≤ 2*(n:ℝ)^4 by exact_mod_cast hhi
  have hlog := log_le_log hM0 hM
  have hfrac : (M:ℝ)/((n^3:ℕ):ℝ) ≤ 2*(n:ℝ) := by
    push_cast
    apply (div_le_iff₀ (pow_pos hn0 3)).mpr
    nlinarith only [hM]
  apply h.trans
  calc
    _ ≤ (n:ℝ)*(2*(1+log (2*(n:ℝ)^4))*(2*(n:ℝ))) := by
      have h0 : 0 ≤ 1+log M := by linarith only [log_nonneg hM1]
      have h0' : 0 ≤ 2*(1+log (2*(n:ℝ)^4)) := by linarith only [h0,hlog]
      gcongr
    _ = _ := by ring

/-- The sampling discrepancy of the small logarithmic divisor rows under
the same repeated mean as the original cubic tail. -/
def averagedSmallDivisorLogError (n : ℕ) : ℝ :=
  let k := Nat.log 2 n+1
  repeatedMean (2*n^3+1) k (fun M =>
    ∑ d ∈ Ioc 0 n, (μ d:ℝ) *
      (tailQuadratureSumIntegral M (n^3) (coefficientPrefix (strideLog d)) -
        tailQuadratureSumIntegral M (n^3) (strideLogMain d))) (n^4-k*n^3)

theorem averagedSmallDivisorLogError_bound {n : ℕ} (hn : 8 ≤ n) :
    |averagedSmallDivisorLogError n| ≤ 4*(n:ℝ)^2*(1+log (2*(n:ℝ)^4)) := by
  let k := Nat.log 2 n+1
  let D := n^3
  let A := n^4-k*D
  let W := 2*D+1
  let F (M : ℕ) := ∑ d ∈ Ioc 0 n, (μ d:ℝ) *
    (tailQuadratureSumIntegral M D (coefficientPrefix (strideLog d)) -
      tailQuadratureSumIntegral M D (strideLogMain d))
  let B := 4*(n:ℝ)^2*(1+log (2*(n:ℝ)^4))
  obtain ⟨hk,_⟩ := cubic_tail_parameters hn
  have hW : 0 < W := by dsimp [W]; omega
  have hhalf : 2*(k*D) ≤ n^4 := by
    simpa only [D,← Nat.mul_assoc,show n^4=n*n^3 by ring] using Nat.mul_le_mul_right (n^3) hk
  have hD2 : 2*D ≤ n^4 :=
    (Nat.mul_le_mul_right D (by omega : 2 ≤ n)).trans_eq (by dsimp [D]; ring)
  have hDA : D ≤ A := by dsimp [A]; omega
  have hmax : A+k*(W-1) ≤ 2*n^4 := by
    dsimp [A,W]
    rw [show k*(2*D)=2*(k*D) by ring]
    omega
  have hd (M : ℕ) (hAM : A ≤ M) (hM : M ≤ A+k*(W-1)) : |F M| ≤ B :=
    smallDivisor_log_quadrature_error_cubic (by omega) (hDA.trans hAM) (hM.trans hmax)
  have hhi := repeat_mono W k A (f := F) (g := fun _ => B) fun M hAM hM =>
    (abs_le.mp (hd M hAM hM)).2
  have hlo := repeat_mono W k A (f := fun _ => -B) (g := F) fun M hAM hM =>
    (abs_le.mp (hd M hAM hM)).1
  change |repeatedMean W k F A| ≤ B
  exact abs_le.mpr ⟨by simpa only [repeat_const hW k A] using hlo,
    by simpa only [repeat_const hW k A] using hhi⟩

/-- The error on every complete fourth-power window is polylogarithmic. -/
theorem smallDivisor_log_window_error {m b : ℕ} (hm : 8 ≤ m) :
    ∑ n ∈ Icc m b, |averagedSmallDivisorLogError n|/(n:ℝ)^3 ≤ 16*(1+log b)^2 := by
  have hcoeff : 0 ≤ 16*(1+log b) := by positivity [log_natCast_nonneg b]
  calc
    _ ≤ ∑ n ∈ Icc m b, (16*(1+log b))*(n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hn8 := hm.trans (mem_Icc.mp hn).1
      have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hlog := log_le_log hn0 (show (n:ℝ) ≤ b by exact_mod_cast (mem_Icc.mp hn).2)
      have h4 : log (2*(n:ℝ)^4) ≤ 1+4*log b := by
        rw [log_mul (by norm_num) (pow_ne_zero _ hn0.ne'),log_pow,Nat.cast_ofNat]
        linarith only [hlog,log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
      have hh : 4*(1+log (2*(n:ℝ)^4)) ≤ 16*(1+log b) := by linarith only [h4]
      apply (div_le_iff₀ (pow_pos hn0 3)).mpr
      have hhpow := mul_le_mul_of_nonneg_right hh (sq_nonneg (n:ℝ))
      have he : (16*(1+log b)*(n:ℝ)⁻¹)*(n:ℝ)^3 = 16*(1+log b)*(n:ℝ)^2 := by field_simp
      rw [he]
      exact (averagedSmallDivisorLogError_bound hn8).trans (by
        nlinarith only [hhpow])
    _ ≤ _ := by
      rw [← mul_sum]
      exact (mul_le_mul_of_nonneg_left (primeWindow_harmonic_le (by omega : 1 ≤ m)) hcoeff).trans_eq
        (by ring)

end
end RiemannGaussian.AlpogeMined

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.vonMangoldt_eq_moebius_strideLog,
      ``RiemannGaussian.AlpogeMined.smallDivisor_log_window_error] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
