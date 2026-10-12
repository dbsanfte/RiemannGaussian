/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorCofactorParityAudit
import RiemannGaussian.ArithmeticOperatorIncidenceFreedom

/-!
# Complete phased Gamma data followed by Möbius inversion

This is the inverse-convolution escape not covered by the source-blind
complete-Gamma hierarchy. Exact Möbius inversion restores the original
prime coefficients with their phase. With the source-retaining cofactor
code it also inherits the exact density cancellation, but still joins to
the SAME arbitrary-weight scalar test. Inversion supplies no independent
signed estimate. Norm-paying its literal Gamma fibers has a cofinally
divergent source-normalized debit, even at actual integer logarithms.

No free-weight countermodel is asserted to satisfy every actual Gamma
observation. Mixed-height inverses, nonlinear masks and distinct-column
prime correlations are outside this scoped audit.
-/

namespace RiemannGaussian.ArithmeticOperatorGammaInverseAudit
noncomputable section
open Complex Filter ArithmeticOperatorKummerCutoff
open ArithmeticOperatorCommutatorAudit ArithmeticOperatorDilationAudit
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- The complete cofactor-compatible phased divisor row. -/
def phasedRow (w : ℕ → ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  primePhase y n*divisorObservation w n

/-- Same-phase Möbius inverse, with every ordinary integer fiber. -/
def decoded (w : ℕ → ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  ∑ da ∈ n.divisorsAntidiagonal,
    (ArithmeticFunction.moebius da.1 : ℂ)*primePhase y da.1*phasedRow w y da.2

/-- First gate: inversion restores ANY original integer array, not
only prime weights. No phase, proper power or positive endpoint is lost. -/
theorem decoded_eq_phased {n : ℕ} (hn : 0 < n) (w : ℕ → ℂ) (y : ℝ) :
    decoded w y n = w n*primePhase y n := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := w) (g := divisorObservation w)).mp (fun _ _ => rfl) n hn
  calc
    _ = primePhase y n*(∑ da ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius da.1 : ℂ)*divisorObservation w da.2) := by
      rw [Finset.mul_sum]
      unfold decoded phasedRow
      apply Finset.sum_congr rfl
      intro da hda
      have hp := (Nat.mem_divisorsAntidiagonal.mp hda).1
      have hphase : primePhase y da.1*primePhase y da.2 = primePhase y n := by
        rw [← primePhase_mul y (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hda |>.bot_lt)
          (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hda |>.bot_lt), hp]
      calc
        _ = (primePhase y da.1*primePhase y da.2)*
            ((ArithmeticFunction.moebius da.1 : ℂ)*divisorObservation w da.2) := by ring
        _ = _ := by rw [hphase]
    _ = _ := by rw [hinv]; ring

/-- At actual coefficients the forward row is exactly the literal
phased integer logarithm, so every complete Gamma datum is retained. -/
theorem actual_phasedRow (y : ℝ) (n : ℕ) :
    phasedRow (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) y n =
      primePhase y n*(Real.log n : ℂ) := by
  simp only [phasedRow, divisorObservation, ← Complex.ofReal_sum,
    ArithmeticFunction.vonMangoldt_sum]

theorem actual_decoded {n : ℕ} (hn : 0 < n) (y : ℝ) :
    decoded (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) y n =
      (ArithmeticFunction.vonMangoldt n : ℂ)*primePhase y n :=
  decoded_eq_phased hn _ y

/-- No restriction to physical cutoff precedes either inversion or the
cofactor code. The quotient prefix keeps its literal endpoint. -/
def codedCutoff (w : ℕ → ℂ) (y : ℝ) (X : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 X, decoded w y d*
    prefixSum (ArithmeticOperatorCofactorParityAudit.cofactor y) (X/d)

/-- The entire inverse-Gamma candidate is EXACTLY the previously
audited source-sensitive cofactor packet, for arbitrary arrays. -/
theorem codedCutoff_eq_packet (w : ℕ → ℂ) (y : ℝ) (X : ℕ) :
    codedCutoff w y X = ArithmeticOperatorCofactorParityAudit.packet w y X := by
  rw [ArithmeticOperatorCofactorParityAudit.packet_eq_scalar]
  unfold codedCutoff ArithmeticOperatorCofactorParityAudit.kernel
  apply Finset.sum_congr rfl
  intro d hd
  rw [decoded_eq_phased (Finset.mem_Icc.mp hd).1]
  ring

/-- Genuine convergent coefficient series, before meromorphic
continuation. No reflected or hypothetical spectral mode is inserted. -/
theorem actual_euler_response (y : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (divisorConvolution
      (decoded (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) y)
      (ArithmeticOperatorCofactorParityAudit.cofactor y)) s =
      ArithmeticOperatorCofactorParityAudit.response y (s+I*y) := by
  have he : decoded (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) y =
      fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d := by
    funext d
    by_cases hd : d = 0
    · simp [hd, decoded]
    · exact actual_decoded (Nat.pos_of_ne_zero hd) y
  rw [he]
  exact ArithmeticOperatorCofactorParityAudit.packet_euler_response y hs

/-- Source preflight survives with exact actual multiplicity. It is
not a new literal cutoff asymptotic or an independent prime estimate. -/
theorem retained_matched_source (rho : NontrivialZetaZero) :
    Tendsto (fun z : ℂ => (z-rho.1)*ArithmeticOperatorCofactorParityAudit.response rho.1.im z)
      (𝓝[≠] rho.1) (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*
        ArithmeticOperatorCofactorParityAudit.cofactorResponse rho.1.im (rho.1.re : ℂ))) ∧
      -(analyticZetaZeroMultiplicity rho : ℂ)*
        ArithmeticOperatorCofactorParityAudit.cofactorResponse rho.1.im (rho.1.re : ℂ) ≠ 0 :=
  ⟨ArithmeticOperatorCofactorParityAudit.tendsto_matched_source rho,
    ArithmeticOperatorCofactorParityAudit.matched_source_ne_zero rho⟩

/-- Both density residues disappear in the exact joined response; this
does not turn the inverse into a source-small arithmetic operator. -/
theorem density_residues_zero {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun z : ℂ => (z-1)*ArithmeticOperatorCofactorParityAudit.response y z)
      (𝓝[≠] 1) (𝓝 0) ∧
    Tendsto (fun z : ℂ => (z-(1+I*y))*ArithmeticOperatorCofactorParityAudit.response y z)
      (𝓝[≠] (1+I*y)) (𝓝 0) :=
  ⟨ArithmeticOperatorCofactorParityAudit.tendsto_density_pole_zero hy,
    ArithmeticOperatorCofactorParityAudit.tendsto_integer_density_zero hy⟩

/-- Fourth gate fails: composing exact forward Gamma and inverse
Möbius operators imposes no extra bound on the original scalar data. -/
theorem no_free_weight_bound {X : ℕ} (hX : 0 < X) (y : ℝ) (B : ℝ) :
    ¬ (∀ w : ℕ → ℂ, ‖codedCutoff w y X‖ ≤ B) := by
  simp only [codedCutoff_eq_packet]
  exact ArithmeticOperatorCofactorParityAudit.no_free_weight_bound hX y B

/-- Literal norm debit of inverse-Gamma fibers at actual logarithmic
rows. Every signed Möbius divisor and both multiplicative phases occur. -/
def fiberDebit (n : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ n.divisors,
    ‖(ArithmeticFunction.moebius d : ℂ)*primePhase y d*primePhase y (n/d)*
      (Real.log ((n/d : ℕ) : ℝ) : ℂ)‖

/-- Full literal cutoff debit from taking norms on every inverse Möbius fiber. -/
def fullDebit (X : ℕ) (y : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 X, fiberDebit n y

/-- The unit Möbius fiber alone already pays at least `log(n)`; the
true joined inverse is NOT bounded by this debit at source scale. -/
theorem log_le_fiberDebit {n : ℕ} (hn : 0 < n) (y : ℝ) :
    Real.log n ≤ fiberDebit n y := by
  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n,hn.ne'⟩
  have hh := Finset.single_le_sum
    (fun d (_ : d ∈ n.divisors) => norm_nonneg
      ((ArithmeticFunction.moebius d : ℂ)*primePhase y d*primePhase y (n/d)*
        (Real.log ((n/d : ℕ) : ℝ) : ℂ))) h1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ n from hn))
  simpa only [fiberDebit, ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul,
    Nat.div_one, norm_mul, norm_primePhase, mul_one, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog] using hh

theorem fullDebit_lower {H : ℕ} (hH : 0 < H) (y : ℝ) :
    (H : ℝ)*Real.log 2 ≤ fullDebit (4*H) y := by
  have hsub : Finset.Icc 2 (H+1) ⊆ Finset.Icc 1 (4*H) := by
    intro n hn
    have hh := Finset.mem_Icc.mp hn
    apply Finset.mem_Icc.mpr
    omega
  have hcard : (Finset.Icc 2 (H+1)).card = H := by rw [Nat.card_Icc]; omega
  calc
    _ = ∑ n ∈ Finset.Icc 2 (H+1), Real.log 2 := by simp [hcard]
    _ ≤ ∑ n ∈ Finset.Icc 2 (H+1), fiberDebit n y := by
      apply Finset.sum_le_sum
      intro n hn
      have hn2 := (Finset.mem_Icc.mp hn).1
      exact (Real.log_le_log (by norm_num) (by exact_mod_cast hn2)).trans
        (log_le_fiberDebit (by omega) y)
    _ ≤ fullDebit (4*H) y :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ =>
        Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- Actual integer Gamma inverse norm payment diverges relative to
EVERY strip power source, independently of height and zero hypotheses. -/
theorem tendsto_scaled_fullDebit_atTop {beta : ℝ} (hb : beta < 1) (y : ℝ) :
    Tendsto (fun J : ℕ => (Real.exp (-beta*Real.log 2))^J*fullDebit (4*2^J) y)
      atTop atTop := by
  have hr : 1 < 2*Real.exp (-beta*Real.log 2) := by
    have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have he : 2*Real.exp (-beta*Real.log 2) = Real.exp ((1-beta)*Real.log 2) := by
      rw [show (1-beta)*Real.log 2 = Real.log 2+(-beta*Real.log 2) by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [he]
    exact Real.one_lt_exp_iff.mpr (mul_pos (by linarith) hl)
  have ht := (tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  apply tendsto_atTop_mono' atTop ?_ ht
  filter_upwards [] with J
  have hh := mul_le_mul_of_nonneg_left
    (fullDebit_lower (by positivity : 0 < (2 : ℕ)^J) y)
    (pow_nonneg (Real.exp_pos (-beta*Real.log 2)).le J)
  convert hh using 1
  push_cast
  rw [mul_pow]
  ring

end
end RiemannGaussian.ArithmeticOperatorGammaInverseAudit
