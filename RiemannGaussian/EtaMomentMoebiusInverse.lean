import RiemannGaussian.EtaMomentMoebiusTransform

/-!
# Exact inverse reconstruction of all completed eta moment orders

Finite divisor inversion acts on the physical cutoff and logarithmic center
together. The inverse below preserves both translations before regrouping
the two Mellin weights. It recovers the original completed finite moments,
with no restriction to simple zeros or order zero.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Finite Möbius inversion with a translated logarithmic center. The
two center shifts and divided cutoffs combine at their exact product. -/
theorem sum_divided_moebius_inverse_centered (s : ℂ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ a, f 0 a = 0) (M : ℕ) (a : ℝ) :
    (∑ d ∈ Finset.Icc 1 M, (d : ℂ) ^ (-s) *
      ∑ e ∈ Finset.Icc 1 (M / d), (μ e : ℂ) * (e : ℂ) ^ (-s) *
        f ((M / d) / e) ((a - Real.log d) - Real.log e)) = f M a := by
  have he : (∑ d ∈ Finset.Icc 1 M, (d : ℂ) ^ (-s) *
      ∑ e ∈ Finset.Icc 1 (M / d), (μ e : ℂ) * (e : ℂ) ^ (-s) *
        f ((M / d) / e) ((a - Real.log d) - Real.log e)) =
      ∑ d ∈ Finset.Icc 1 M, ∑ e ∈ Finset.Icc 1 (M / d),
        (μ e : ℂ) * (((d * e : ℕ) : ℂ) ^ (-s) *
          f (M / (d * e)) (a - Real.log (d * e : ℕ))) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hdpos := (Finset.mem_Icc.mp hd).1
    have hepos := (Finset.mem_Icc.mp he).1
    rw [Nat.div_div_eq_div_mul, Nat.cast_mul, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow,
      Real.log_mul (by positivity : (d : ℝ) ≠ 0) (by positivity : (e : ℝ) ≠ 0),
      show a - Real.log d - Real.log e = a - (Real.log d + Real.log e) by ring]
    ring
  rw [he, ← sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix]
  calc
    _ = ∑ n ∈ Finset.Icc 1 M, (if n = 1 then 1 else 0) *
        ((n : ℂ) ^ (-s) * f (M / n) (a - Real.log n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hmu : (∑ p ∈ n.divisorsAntidiagonal, (μ p.2 : ℂ)) = if n = 1 then 1 else 0 := by
        rw [Nat.sum_divisorsAntidiagonal' (fun _ k ↦ (μ k : ℂ))]
        simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.intCoe_apply,
          ArithmeticFunction.one_apply] using
            congrArg (fun g : ArithmeticFunction ℂ ↦ g n)
              (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ))
      calc
        _ = (∑ p ∈ n.divisorsAntidiagonal, (μ p.2 : ℂ)) *
            ((n : ℂ) ^ (-s) * f (M / n) (a - Real.log n)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
        _ = _ := by rw [hmu]
    _ = f M a := by
      by_cases hM : M = 0
      · simp [hM, hf]
      · simp [ite_mul, Finset.sum_ite_eq', Finset.mem_Icc, Nat.one_le_iff_ne_zero.mpr hM]

/-- One inverse feature retains the actual completed moment aggregate,
its divided physical cutoff, and the divisor's translated center. -/
def pairedEtaCompletedMomentInverseTerm
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M d : ℕ) : ℂ :=
  (d : ℂ) ^ (-rho.1) * pairedEtaCompletedMomentMoebiusAggregate rho k (a - Real.log d) (M / d)

/-- Inverse-weighted whole aggregates recover the complete unpaired
moment endpoint prefix at its original center. -/
theorem sum_pairedEtaCompletedMomentInverseTerm
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, pairedEtaCompletedMomentInverseTerm rho k a M d) =
      (pairedEtaXiCompletionFactor rho.1 * rho.1) *
        pairedEtaUnpairedCenteredMomentPrefix k rho.1 a M := by
  simp only [pairedEtaCompletedMomentInverseTerm, pairedEtaCompletedMomentMoebiusAggregate,
    pairedEtaCompletedMomentMoebiusTerm]
  exact sum_divided_moebius_inverse_centered rho.1
    (fun n b ↦ (pairedEtaXiCompletionFactor rho.1 * rho.1) *
      pairedEtaUnpairedCenteredMomentPrefix k rho.1 b n)
    (by intro b; simp [pairedEtaUnpairedCenteredMomentPrefix]) M a

/-- Every original finite completed moment is exactly reconstructed
from whole Möbius aggregates, at its literal physical center and cutoff. -/
theorem pairedEtaFiniteCompletedMoment_eq_momentInverse
    (rho : NontrivialZetaZero) (N k : ℕ) :
    pairedEtaFiniteCompletedMoment rho N k =
      ∑ d ∈ Finset.Icc 1 (2 * N), pairedEtaCompletedMomentInverseTerm rho k
        (pairedEtaLogTailCutoff N) (2 * N) d := by
  rw [sum_pairedEtaCompletedMomentInverseTerm,
    pairedEtaUnpairedCenteredMomentPrefix_even k (NontrivialZetaZero.coe_ne_zero rho)]
  rfl

end

end RiemannGaussian
