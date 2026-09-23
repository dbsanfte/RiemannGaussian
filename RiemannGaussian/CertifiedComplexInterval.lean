/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertifiedIntervalProgram
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Checked complex rectangles for finite analytic evaluation

Both signed coordinates are retained. Rational arithmetic uses outward
dyadic rounding, while exponentials, trigonometric functions, logarithms
and reciprocal domain checks use the existing checked LeanCert evaluator.
No successful interval computation is asserted without a proof of its
result. The intended application is the finite Euler--Maclaurin evaluator.
-/

namespace RiemannGaussian.CertifiedComplexInterval
open LeanCert.Core LeanCert.Engine

/-- A complex rectangle with finite dyadic endpoints. -/
structure Box where
  /-- Real-coordinate enclosure. -/
  re : IntervalDyadic
  /-- Imaginary-coordinate enclosure. -/
  im : IntervalDyadic
  deriving Repr

/-- Literal containment of both signed coordinates. -/
def Mem (z : ℂ) (B : Box) : Prop := z.re ∈ B.re ∧ z.im ∈ B.im

/-- Enclose an exact rational complex number by outward rounding. -/
def rational (prec : ℤ) (a b : ℚ) : Box :=
  ⟨IntervalDyadic.ofIntervalRat (IntervalRat.singleton a) prec,
    IntervalDyadic.ofIntervalRat (IntervalRat.singleton b) prec⟩

/-- The rational constructor encloses the exact complex value. -/
theorem mem_rational {prec : ℤ} (hp : prec ≤ 0) (a b : ℚ) :
    Mem ((a : ℂ) + (b : ℂ) * Complex.I) (rational prec a b) := by
  constructor <;> simpa [rational] using
    (IntervalDyadic.mem_ofIntervalRat (IntervalRat.mem_singleton _) prec hp)

/-- Complex negation preserves both exact sign changes. -/
def neg (B : Box) : Box := ⟨B.re.neg, B.im.neg⟩

/-- Soundness of complex negation. -/
theorem mem_neg {z : ℂ} {B : Box} (h : Mem z B) : Mem (-z) (neg B) :=
  ⟨IntervalDyadic.mem_neg h.1, IntervalDyadic.mem_neg h.2⟩

/-- Rounded complex addition. -/
def add (prec : ℤ) (A B : Box) : Box :=
  ⟨A.re.addRounded B.re prec, A.im.addRounded B.im prec⟩

private theorem mem_addRounded {x y : ℝ} {A B : IntervalDyadic}
    (hx : x ∈ A) (hy : y ∈ B) (prec : ℤ) : x + y ∈ A.addRounded B prec :=
  IntervalDyadic.roundOut_contains (IntervalDyadic.mem_add hx hy) prec

private theorem mem_mulRounded {x y : ℝ} {A B : IntervalDyadic}
    (hx : x ∈ A) (hy : y ∈ B) (prec : ℤ) : x * y ∈ A.mulRounded B prec :=
  IntervalDyadic.roundOut_contains (IntervalDyadic.mem_mul hx hy) prec

/-- Soundness of rounded complex addition. -/
theorem mem_add {z w : ℂ} {A B : Box} (hz : Mem z A) (hw : Mem w B) (prec : ℤ) :
    Mem (z + w) (add prec A B) :=
  ⟨mem_addRounded hz.1 hw.1 prec, mem_addRounded hz.2 hw.2 prec⟩

/-- Rounded multiplication retains the real subtraction and both mixed terms. -/
def mul (prec : ℤ) (A B : Box) : Box :=
  ⟨(A.re.mulRounded B.re prec).addRounded (A.im.mulRounded B.im prec).neg prec,
    (A.re.mulRounded B.im prec).addRounded (A.im.mulRounded B.re prec) prec⟩

/-- Soundness of rounded multiplication, before any norm is taken. -/
theorem mem_mul {z w : ℂ} {A B : Box} (hz : Mem z A) (hw : Mem w B) (prec : ℤ) :
    Mem (z * w) (mul prec A B) := by
  constructor
  · simpa only [mul, Complex.mul_re, sub_eq_add_neg] using
      mem_addRounded (mem_mulRounded hz.1 hw.1 prec)
        (IntervalDyadic.mem_neg (mem_mulRounded hz.2 hw.2 prec)) prec
  · exact mem_addRounded (mem_mulRounded hz.1 hw.2 prec)
      (mem_mulRounded hz.2 hw.1 prec) prec

/-- A two-coordinate environment; unused indices have the imaginary interval. -/
def environment (B : Box) : IntervalDyadicEnv := fun i ↦ if i = 0 then B.re else B.im

/-- Exact real environment matching a complex input. -/
noncomputable def realEnvironment (z : ℂ) : ℕ → ℝ := fun i ↦ if i = 0 then z.re else z.im

/-- Both coordinate enclosures give the engine's full environment premise. -/
theorem env_mem {z : ℂ} {B : Box} (h : Mem z B) :
    envMemDyadic (realEnvironment z) (environment B) := by
  intro i
  by_cases hi : i = 0 <;> simp [realEnvironment, environment, hi, h.1, h.2]

/-- Keep the checked scalar engine opaque during algebraic elaboration;
explicit computations and the soundness theorem still use its full definition. -/
@[irreducible] def scalarEval (e : Expr) (ρ : IntervalDyadicEnv) (cfg : DyadicConfig) :
    EvalResult IntervalDyadic := evalIntervalDyadicChecked e ρ cfg

private theorem scalarEval_correct (e : Expr) (ρ_real : Nat → ℝ)
    (ρ_dyad : IntervalDyadicEnv) (hρ : envMemDyadic ρ_real ρ_dyad)
    (cfg : DyadicConfig) (hp : cfg.precision ≤ 0) (I : IntervalDyadic)
    (h : scalarEval e ρ_dyad cfg = .ok I) : Expr.eval ρ_real e ∈ I :=
  evalIntervalDyadicChecked_correct e ρ_real ρ_dyad hρ cfg hp I
    (by simpa only [scalarEval] using h)

private def reciprocalNorm : Expr :=
  .inv (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))

/-- Complex reciprocal. Failure of the real norm-square domain check
propagates as failure rather than becoming a spurious enclosure. -/
def inv (cfg : DyadicConfig) (B : Box) : EvalResult Box :=
  match scalarEval reciprocalNorm (environment B) cfg with
  | .error err => .error err
  | .ok d => .ok ⟨B.re.mulRounded d cfg.precision, (B.im.mulRounded d cfg.precision).neg⟩

/-- Every successful reciprocal encloses the actual complex reciprocal. -/
theorem mem_inv {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {z : ℂ} {A B : Box} (hz : Mem z A) (h : inv cfg A = .ok B) : Mem z⁻¹ B := by
  cases hd : scalarEval reciprocalNorm (environment A) cfg with
  | error err => rw [inv, hd] at h; cases h
  | ok d =>
    have he := scalarEval_correct reciprocalNorm (realEnvironment z)
      (environment A) (env_mem hz) cfg hp d hd
    simp only [reciprocalNorm, Expr.eval, realEnvironment, Nat.one_ne_zero, ↓reduceIte] at he
    simp only [inv, hd, Except.ok.injEq] at h
    subst B
    constructor
    · simpa only [Complex.inv_re, Complex.normSq_apply, div_eq_mul_inv] using
        mem_mulRounded hz.1 he cfg.precision
    · simpa only [Complex.inv_im, Complex.normSq_apply, div_eq_mul_inv, neg_mul] using
        IntervalDyadic.mem_neg (mem_mulRounded hz.2 he cfg.precision)

/-- The existing proved twenty-decimal enclosure of pi. -/
def piBounds : IntervalRat :=
  ⟨3.14159265358979323846, 3.14159265358979323847, by norm_num⟩

private theorem mem_piBounds : Real.pi ∈ piBounds := by
  exact ⟨Real.pi_gt_d20.le, Real.pi_lt_d20.le⟩

/-- Choose a nearby full period. This integer is only a computational
choice: soundness holds for every shift, even for a wide input interval. -/
def angleShift (I : IntervalDyadic) : ℤ :=
  ((I.lo.toRat + I.hi.toRat) / (2 * (piBounds.lo + piBounds.hi)) + 1 / 2).floor

/-- Subtract the same integer multiple of two pi from every enclosed angle. -/
def reduceAngle (cfg : DyadicConfig) (I : IntervalDyadic) : IntervalDyadic :=
  I.addRounded
    ((IntervalDyadic.ofIntervalRat (IntervalRat.singleton (angleShift I)) cfg.precision).mulRounded
      (IntervalDyadic.ofIntervalRat (IntervalRat.mul (IntervalRat.singleton 2) piBounds)
        cfg.precision) cfg.precision).neg cfg.precision

/-- Period reduction encloses the actual shifted angle using proved pi bounds. -/
theorem mem_reduceAngle {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {x : ℝ} {I : IntervalDyadic} (hx : x ∈ I) :
    x - (angleShift I : ℝ) * (2 * Real.pi) ∈ reduceAngle cfg I := by
  have hk := IntervalDyadic.mem_ofIntervalRat
    (IntervalRat.mem_singleton (angleShift I)) cfg.precision hp
  have hpi := IntervalDyadic.mem_ofIntervalRat
    (IntervalRat.mem_mul (IntervalRat.mem_singleton 2) mem_piBounds) cfg.precision hp
  simpa only [reduceAngle, Rat.cast_intCast, Rat.cast_ofNat, sub_eq_add_neg] using
    mem_addRounded hx (IntervalDyadic.mem_neg (mem_mulRounded hk hpi cfg.precision)) cfg.precision

/-- Complex exponential with certified periodic reduction of the angle. -/
def exp (cfg : DyadicConfig) (B : Box) : EvalResult Box :=
  match scalarEval (.exp (.var 0)) (environment B) cfg with
  | .error err => .error err
  | .ok r =>
    match scalarEval (.cos (.var 0)) (fun _ => reduceAngle cfg B.im) cfg with
    | .error err => .error err
    | .ok c =>
      match scalarEval (.sin (.var 0)) (fun _ => reduceAngle cfg B.im) cfg with
      | .error err => .error err
      | .ok s => .ok ⟨r.mulRounded c cfg.precision, r.mulRounded s cfg.precision⟩

/-- Every successful exponential encloses both exact oscillatory coordinates;
periodicity pays the full angle shift, without an approximation of the phase. -/
theorem mem_exp {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {z : ℂ} {A B : Box} (hz : Mem z A) (h : exp cfg A = .ok B) :
    Mem (Complex.exp z) B := by
  cases hr : scalarEval (.exp (.var 0)) (environment A) cfg with
  | error err => simp [exp, hr] at h
  | ok r =>
    cases hc : scalarEval (.cos (.var 0)) (fun _ => reduceAngle cfg A.im) cfg with
    | error err => simp [exp, hr, hc] at h
    | ok c =>
      cases hs : scalarEval (.sin (.var 0)) (fun _ => reduceAngle cfg A.im) cfg with
      | error err => simp [exp, hr, hc, hs] at h
      | ok s =>
        have hreal := scalarEval_correct _ _ _ (env_mem hz) cfg hp r hr
        have hcos := scalarEval_correct _
          (fun _ => z.im - (angleShift A.im : ℝ) * (2 * Real.pi)) _
          (fun _ => mem_reduceAngle hp hz.2) cfg hp c hc
        have hsin := scalarEval_correct _
          (fun _ => z.im - (angleShift A.im : ℝ) * (2 * Real.pi)) _
          (fun _ => mem_reduceAngle hp hz.2) cfg hp s hs
        simp only [Expr.eval, realEnvironment, ↓reduceIte] at hreal
        simp only [Expr.eval, Real.cos_sub_int_mul_two_pi] at hcos
        simp only [Expr.eval, Real.sin_sub_int_mul_two_pi] at hsin
        simp only [exp, hr, hc, hs, Except.ok.injEq] at h
        subst B
        constructor
        · simpa only [Complex.exp_re] using mem_mulRounded hreal hcos cfg.precision
        · simpa only [Complex.exp_im] using mem_mulRounded hreal hsin cfg.precision

/-- A positive integer base raised to a complex power, through its checked
real logarithm. Invalid logarithm inputs cause an explicit failure. -/
def natPower (cfg : DyadicConfig) (n : ℕ) (B : Box) : EvalResult Box :=
  match scalarEval (.log (.const n)) (environment B) cfg with
  | .error err => .error err
  | .ok l => exp cfg (mul cfg.precision ⟨l, (rational cfg.precision 0 0).im⟩ B)

/-- Successful integer-base powers enclose the literal complex power;
the positive-base branch of the complex logarithm is proved explicitly. -/
theorem mem_natPower {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {n : ℕ} (hn : 0 < n) {z : ℂ} {A B : Box} (hz : Mem z A)
    (h : natPower cfg n A = .ok B) : Mem ((n : ℂ) ^ z) B := by
  cases hl : scalarEval (.log (.const n)) (environment A) cfg with
  | error err => simp [natPower, hl] at h
  | ok l =>
    have he := scalarEval_correct _ _ _ (env_mem hz) cfg hp l hl
    simp only [Expr.eval, Rat.cast_natCast] at he
    have hz0 := (mem_rational hp 0 0).2
    have hL : Mem (Complex.ofReal (_root_.Real.log (n : ℝ)))
        ⟨l, (rational cfg.precision 0 0).im⟩ := by
      exact ⟨he, by simpa only [Rat.cast_zero, zero_mul, add_zero,
        Complex.zero_im, Complex.ofReal_im] using hz0⟩
    have hh := mem_exp hp (mem_mul hL hz cfg.precision)
      (by simpa only [natPower, hl] using h)
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by exact_mod_cast hn.le)]
    exact hh

end RiemannGaussian.CertifiedComplexInterval
