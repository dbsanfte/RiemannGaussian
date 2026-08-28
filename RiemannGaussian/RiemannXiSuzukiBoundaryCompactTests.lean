import RiemannGaussian.RiemannXiSuzukiArithmeticBoundaryIdentification
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Compactly supported boundary tests for the Suzuki meeting problem

The abstract boundary-identification criterion only asks for weak convergence
on a dense family of `L²(ℝ)` test vectors.  This file supplies a concrete
family suited to future contour arguments: continuous compactly supported
complex functions.

Each such function is packaged as an actual `L²` vector.  Mathlib's regular-
measure approximation theorem is specialized to prove that these vectors
have dense range in `L²(ℝ, ℂ)`.  Their Hilbert pairings with both the finite
spectral windows and the complete arithmetic signal are then identified with
literal Lebesgue integrals.  Consequently the desired strong arithmetic
boundary identification is exactly equivalent to tail-Gram vanishing plus
convergence of those compact-test integrals.

The integral convergence is named as a proposition and is not asserted here.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- A continuous compactly supported complex test function on the real
spectral boundary. -/
def SuzukiXiBoundaryCompactTest :=
  {g : ℝ → ℂ // Continuous g ∧ HasCompactSupport g}

/-- A compactly supported continuous test function as an actual boundary
`L²` vector. -/
def suzukiXiBoundaryCompactTestLp
    (g : SuzukiXiBoundaryCompactTest) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (g.2.1.memLp_of_hasCompactSupport g.2.2).toLp g.1

/-- The packaged test vector has the literal continuous function as a
representative almost everywhere. -/
theorem suzukiXiBoundaryCompactTestLp_ae
    (g : SuzukiXiBoundaryCompactTest) :
    suzukiXiBoundaryCompactTestLp g =ᵐ[volume] g.1 :=
  MemLp.coeFn_toLp (g.2.1.memLp_of_hasCompactSupport g.2.2)

/-- Continuous compactly supported boundary tests have dense range in the
complete Hilbert space `L²(ℝ, ℂ)`. -/
theorem denseRange_suzukiXiBoundaryCompactTestLp :
    DenseRange suzukiXiBoundaryCompactTestLp := by
  rw [Metric.denseRange_iff]
  intro f epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  obtain ⟨g, hcompact, hbound, hcontinuous, _hmem⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      ((ENNReal.ofReal_pos.2 hhalf).ne')
  let test : SuzukiXiBoundaryCompactTest :=
    ⟨g, hcontinuous, hcompact⟩
  refine ⟨test, ?_⟩
  have hedistance :
      edist f (suzukiXiBoundaryCompactTestLp test) ≤
        ENNReal.ofReal (epsilon / 2) := by
    change edist f
      ((hcontinuous.memLp_of_hasCompactSupport hcompact).toLp g) ≤ _
    rw [← Lp.toLp_coeFn f (Lp.memLp f), Lp.edist_toLp_toLp]
    exact hbound
  have hdistance :
      dist f (suzukiXiBoundaryCompactTestLp test) ≤ epsilon / 2 := by
    rw [Lp.edist_dist] at hedistance
    exact (ENNReal.ofReal_le_ofReal_iff hhalf.le).1 hedistance
  exact hdistance.trans_lt (half_lt_self hepsilon)

/-- The literal product of a compact test with a finite spectral window is
Lebesgue integrable. -/
theorem integrable_conj_compactTest_mul_signalWindow
    (g : SuzukiXiBoundaryCompactTest) (t T : ℝ) :
    Integrable (fun x : ℝ ↦ starRingEnd ℂ (g.1 x) *
      suzukiRealAxisSignalWindow t T x) := by
  apply (L2.integrable_inner (suzukiXiBoundaryCompactTestLp g)
    (suzukiRealAxisSignalWindowLp t T)).congr
  filter_upwards [suzukiXiBoundaryCompactTestLp_ae g,
    suzukiRealAxisSignalWindowLp_ae t T] with x htest hwindow
  rw [htest, hwindow, RCLike.inner_apply']

/-- At positive time, the literal product of a compact test with the complete
arithmetic signal is Lebesgue integrable. -/
theorem integrable_conj_compactTest_mul_arithmeticSignal
    (g : SuzukiXiBoundaryCompactTest) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ℝ ↦ starRingEnd ℂ (g.1 x) *
      suzukiRealAxisArithmeticSignalPositive t x) := by
  apply (L2.integrable_inner (suzukiXiBoundaryCompactTestLp g)
    (suzukiRealAxisArithmeticSignalPositiveLp t ht)).congr
  filter_upwards [suzukiXiBoundaryCompactTestLp_ae g,
    suzukiRealAxisArithmeticSignalPositiveLp_ae t ht]
      with x htest harithmetic
  rw [htest, harithmetic, RCLike.inner_apply']

/-- Pairing a compact test with a finite spectral window is its literal
Lebesgue integral against that window. -/
theorem inner_suzukiXiBoundaryCompactTestLp_signalWindow
    (g : SuzukiXiBoundaryCompactTest) (t T : ℝ) :
    inner ℂ (suzukiXiBoundaryCompactTestLp g)
        (suzukiRealAxisSignalWindowLp t T) =
      ∫ x : ℝ, starRingEnd ℂ (g.1 x) *
        suzukiRealAxisSignalWindow t T x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [suzukiXiBoundaryCompactTestLp_ae g,
    suzukiRealAxisSignalWindowLp_ae t T] with x htest hwindow
  rw [htest, hwindow, RCLike.inner_apply']

/-- Pairing a compact test with the complete arithmetic `L²` signal is the
corresponding literal arithmetic integral. -/
theorem inner_suzukiXiBoundaryCompactTestLp_arithmeticSignal
    (g : SuzukiXiBoundaryCompactTest) (t : ℝ) (ht : 0 < t) :
    inner ℂ (suzukiXiBoundaryCompactTestLp g)
        (suzukiRealAxisArithmeticSignalPositiveLp t ht) =
      ∫ x : ℝ, starRingEnd ℂ (g.1 x) *
        suzukiRealAxisArithmeticSignalPositive t x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [suzukiXiBoundaryCompactTestLp_ae g,
    suzukiRealAxisArithmeticSignalPositiveLp_ae t ht]
      with x htest harithmetic
  rw [htest, harithmetic, RCLike.inner_apply']

/-- Convergence of all compactly supported continuous boundary-test
integrals.  This declaration names the analytic target but does not assert
it. -/
def SuzukiXiArithmeticBoundaryCompactTestIdentification
    (t : ℝ) : Prop :=
  ∀ g : SuzukiXiBoundaryCompactTest,
    Tendsto (fun T : ℝ ↦
      ∫ x : ℝ, starRingEnd ℂ (g.1 x) *
        suzukiRealAxisSignalWindow t T x) atTop
      (nhds (∫ x : ℝ, starRingEnd ℂ (g.1 x) *
        suzukiRealAxisArithmeticSignalPositive t x))

/-- Compact-test integral convergence is exactly weak arithmetic boundary
identification on the dense range of packaged compact tests. -/
theorem compactTestIdentification_iff_weakOn_range
    (t : ℝ) (ht : 0 < t) :
    SuzukiXiArithmeticBoundaryCompactTestIdentification t ↔
      SuzukiXiArithmeticBoundaryWeakIdentificationOn t ht
        (range suzukiXiBoundaryCompactTestLp) := by
  constructor
  · intro hcompact _g hg
    obtain ⟨g, rfl⟩ := hg
    simpa only [inner_suzukiXiBoundaryCompactTestLp_signalWindow,
      inner_suzukiXiBoundaryCompactTestLp_arithmeticSignal] using hcompact g
  · intro hweak g
    have h := hweak (suzukiXiBoundaryCompactTestLp g) ⟨g, rfl⟩
    simpa only [inner_suzukiXiBoundaryCompactTestLp_signalWindow,
      inner_suzukiXiBoundaryCompactTestLp_arithmeticSignal] using h

/-- The exact concrete meeting criterion: the finite spectral windows
converge strongly to the arithmetic `L²` signal iff their tail Gram vanishes
and all continuous compact-support test integrals converge to the literal
arithmetic integrals. -/
theorem arithmeticBoundaryIdentification_iff_tailGramVanishing_and_compactTests
    (t : ℝ) (ht : 0 < t) :
    SuzukiXiArithmeticBoundaryIdentification t ht ↔
      SuzukiXiCoefficientTailGramVanishing t ∧
        SuzukiXiArithmeticBoundaryCompactTestIdentification t := by
  rw [arithmeticBoundaryIdentification_iff_tailGramVanishing_and_weakOn
    t ht denseRange_suzukiXiBoundaryCompactTestLp]
  exact and_congr_right fun _hvanish ↦
    (compactTestIdentification_iff_weakOn_range t ht).symm

end

end RiemannGaussian
