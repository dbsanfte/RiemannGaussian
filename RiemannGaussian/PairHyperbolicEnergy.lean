import RiemannGaussian.FiniteKreinLanger

/-!
# One-pair hyperbolic energy

This file formalizes the separation-free scalar inequality from the uploaded
`Symmetric_Quartet_Gram_Weil_Defect_SeparationFree` note.  It is stated first
in real coordinates so every denominator and positivity hypothesis is
visible, and is then identified with the imaginary part of the corresponding
complex logarithmic-derivative pair.
-/

namespace RiemannGaussian

noncomputable section

/-- Squared numerator in the upper-half-plane pseudo-hyperbolic distance
between points whose horizontal displacement is `d` and heights are `v,a`. -/
def pairHyperbolicUpperSq (d v a : ℝ) : ℝ :=
  d ^ 2 + (v - a) ^ 2

/-- Squared denominator in that pseudo-hyperbolic distance. -/
def pairHyperbolicLowerSq (d v a : ℝ) : ℝ :=
  d ^ 2 + (v + a) ^ 2

/-- Pseudo-hyperbolic radius in real coordinates. -/
def pairHyperbolicRadius (d v a : ℝ) : ℝ :=
  Real.sqrt (pairHyperbolicUpperSq d v a /
    pairHyperbolicLowerSq d v a)

/-- Imaginary part of one conjugate-pair logarithmic-derivative contribution. -/
def pairImaginaryEnergy (m d v a : ℝ) : ℝ :=
  m * ((v - a) / pairHyperbolicUpperSq d v a +
    (v + a) / pairHyperbolicLowerSq d v a)

/-- Hyperbolic energy cost used in the quartet argument. -/
def pairHyperbolicCost (m a r : ℝ) : ℝ :=
  m / (2 * a) * (1 / r - r)

theorem pairHyperbolicLowerSq_pos
    {d v a : ℝ} (ha : 0 < a) (hv : 0 < v) :
    0 < pairHyperbolicLowerSq d v a := by
  unfold pairHyperbolicLowerSq
  nlinarith [sq_nonneg d, sq_pos_of_pos (add_pos hv ha)]

theorem pairHyperbolicUpperSq_nonneg (d v a : ℝ) :
    0 ≤ pairHyperbolicUpperSq d v a := by
  unfold pairHyperbolicUpperSq
  positivity

theorem pairHyperbolicUpperSq_lt_lowerSq
    {d v a : ℝ} (ha : 0 < a) (hv : 0 < v) :
    pairHyperbolicUpperSq d v a < pairHyperbolicLowerSq d v a := by
  unfold pairHyperbolicUpperSq pairHyperbolicLowerSq
  nlinarith

/-- Exact factorization exposing the sign of one conjugate-pair imaginary
energy.  Its only sign-changing factor is the signed squared distance
`d^2 + v^2 - a^2`. -/
theorem pairImaginaryEnergy_eq_signedDistance
    {m d v a : ℝ} (ha : 0 < a) (hv : 0 < v)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    pairImaginaryEnergy m d v a =
      2 * m * v * (d ^ 2 + v ^ 2 - a ^ 2) /
        (pairHyperbolicUpperSq d v a *
          pairHyperbolicLowerSq d v a) := by
  have hlower : 0 < pairHyperbolicLowerSq d v a :=
    pairHyperbolicLowerSq_pos ha hv
  unfold pairImaginaryEnergy
  field_simp [hupper.ne', hlower.ne']
  unfold pairHyperbolicUpperSq pairHyperbolicLowerSq
  ring

/-- A positive-height conjugate pair contributes nonnegative imaginary energy
at every upper-half-plane point outside (or on) its Euclidean influence disk.
-/
theorem pairImaginaryEnergy_nonneg_of_height_sq_le
    {m d v a : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (hv : 0 < v)
    (hupper : 0 < pairHyperbolicUpperSq d v a)
    (houtside : a ^ 2 ≤ d ^ 2 + v ^ 2) :
    0 ≤ pairImaginaryEnergy m d v a := by
  rw [pairImaginaryEnergy_eq_signedDistance ha hv hupper]
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hm) hv.le)
      (sub_nonneg.mpr houtside))
    (mul_nonneg hupper.le (pairHyperbolicLowerSq_pos ha hv).le)

/-- For positive weight, the influence-disk condition is not merely
sufficient: it exactly characterizes nonnegative pair energy. -/
theorem pairImaginaryEnergy_nonneg_iff_height_sq_le
    {m d v a : ℝ} (hm : 0 < m) (ha : 0 < a) (hv : 0 < v)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    0 ≤ pairImaginaryEnergy m d v a ↔ a ^ 2 ≤ d ^ 2 + v ^ 2 := by
  rw [pairImaginaryEnergy_eq_signedDistance ha hv hupper]
  have hcoeff : 0 < 2 * m * v := by positivity
  have hden : 0 < pairHyperbolicUpperSq d v a *
      pairHyperbolicLowerSq d v a :=
    mul_pos hupper (pairHyperbolicLowerSq_pos ha hv)
  constructor
  · intro h
    rcases div_nonneg_iff.mp h with hnum | hdenBad
    · exact sub_nonneg.mp
        ((mul_nonneg_iff_of_pos_left hcoeff).mp hnum.1)
    · exact False.elim (not_le_of_gt hden hdenBad.2)
  · intro houtside
    exact div_nonneg
      (mul_nonneg hcoeff.le (sub_nonneg.mpr houtside)) hden.le

/-- Equivalently, a positive-weight pair contributes strictly negatively
exactly when the evaluation point lies strictly inside its influence disk. -/
theorem pairImaginaryEnergy_neg_iff_height_sq_lt
    {m d v a : ℝ} (hm : 0 < m) (ha : 0 < a) (hv : 0 < v)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    pairImaginaryEnergy m d v a < 0 ↔ d ^ 2 + v ^ 2 < a ^ 2 := by
  rw [pairImaginaryEnergy_eq_signedDistance ha hv hupper]
  have hcoeff : 0 < 2 * m * v := by positivity
  have hden : 0 < pairHyperbolicUpperSq d v a *
      pairHyperbolicLowerSq d v a :=
    mul_pos hupper (pairHyperbolicLowerSq_pos ha hv)
  constructor
  · intro h
    rcases div_neg_iff.mp h with hdenBad | hnum
    · exact False.elim (not_lt_of_ge hden.le hdenBad.2)
    · apply sub_neg.mp
      apply lt_of_not_ge
      intro hdelta
      exact (not_lt_of_ge (mul_nonneg hcoeff.le hdelta)) hnum.1
  · intro hinside
    exact div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg hcoeff (sub_neg.mpr hinside)) hden

theorem pairHyperbolicRadius_sq
    {d v a : ℝ} (ha : 0 < a) (hv : 0 < v) :
    pairHyperbolicRadius d v a ^ 2 =
      pairHyperbolicUpperSq d v a / pairHyperbolicLowerSq d v a := by
  unfold pairHyperbolicRadius
  apply Real.sq_sqrt
  exact div_nonneg (pairHyperbolicUpperSq_nonneg d v a)
    (pairHyperbolicLowerSq_pos ha hv).le

theorem pairHyperbolicRadius_nonneg (d v a : ℝ) :
    0 ≤ pairHyperbolicRadius d v a :=
  Real.sqrt_nonneg _

theorem pairHyperbolicRadius_pos
    {d v a : ℝ} (ha : 0 < a) (hv : 0 < v)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    0 < pairHyperbolicRadius d v a := by
  unfold pairHyperbolicRadius
  exact Real.sqrt_pos.2 (div_pos hupper (pairHyperbolicLowerSq_pos ha hv))

theorem pairHyperbolicRadius_lt_one
    {d v a : ℝ} (ha : 0 < a) (hv : 0 < v) :
    pairHyperbolicRadius d v a < 1 := by
  let r := pairHyperbolicRadius d v a
  have hr0 : 0 ≤ r := pairHyperbolicRadius_nonneg d v a
  have hrsq : r ^ 2 = pairHyperbolicUpperSq d v a /
      pairHyperbolicLowerSq d v a := pairHyperbolicRadius_sq ha hv
  have hratio : pairHyperbolicUpperSq d v a /
      pairHyperbolicLowerSq d v a < 1 :=
    (div_lt_one (pairHyperbolicLowerSq_pos ha hv)).2
      (pairHyperbolicUpperSq_lt_lowerSq ha hv)
  nlinarith

@[simp] theorem pairHyperbolicRadius_neg (d v a : ℝ) :
    pairHyperbolicRadius (-d) v a = pairHyperbolicRadius d v a := by
  unfold pairHyperbolicRadius pairHyperbolicUpperSq pairHyperbolicLowerSq
  congr 2 <;> ring

theorem pairHyperbolicRadius_swap_heights (d v a : ℝ) :
    pairHyperbolicRadius d a v = pairHyperbolicRadius d v a := by
  unfold pairHyperbolicRadius pairHyperbolicUpperSq pairHyperbolicLowerSq
  congr 2 <;> ring

/-- The pseudo-hyperbolic circle height inequality, proved directly from the
real-coordinate distance formula rather than assumed from circle geometry. -/
theorem pair_height_lower_bound
    {d v a : ℝ} (ha : 0 < a) (hv : 0 < v) :
    a * (1 - pairHyperbolicRadius d v a) ≤
      v * (1 + pairHyperbolicRadius d v a) := by
  let r := pairHyperbolicRadius d v a
  have hr0 : 0 ≤ r := pairHyperbolicRadius_nonneg d v a
  by_cases hav : a ≤ v
  · nlinarith
  · have hva : v < a := lt_of_not_ge hav
    let A : ℝ := (a - v) ^ 2
    let B : ℝ := (a + v) ^ 2
    let U : ℝ := pairHyperbolicUpperSq d v a
    let L : ℝ := pairHyperbolicLowerSq d v a
    have hB : 0 < B := by
      dsimp only [B]
      positivity
    have hL : 0 < L := by
      exact pairHyperbolicLowerSq_pos ha hv
    have hBA : 0 ≤ B - A := by
      dsimp only [A, B]
      nlinarith
    have hcross : A * L ≤ U * B := by
      have hid : U * B - A * L = d ^ 2 * (B - A) := by
        dsimp only [A, B, U, L]
        unfold pairHyperbolicUpperSq pairHyperbolicLowerSq
        ring
      nlinarith [mul_nonneg (sq_nonneg d) hBA]
    have hratio : A / B ≤ U / L :=
      (div_le_div_iff₀ hB hL).2 hcross
    have hrsq : r ^ 2 = U / L := by
      exact pairHyperbolicRadius_sq ha hv
    have hquotpos : 0 ≤ (a - v) / (a + v) := by positivity
    have hquotSq : ((a - v) / (a + v)) ^ 2 = A / B := by
      dsimp only [A, B]
      field_simp [(add_pos ha hv).ne']
    have hquot_le_r : (a - v) / (a + v) ≤ r := by
      nlinarith [hratio, hquotSq]
    have hden := add_pos ha hv
    have hlinear : a - v ≤ r * (a + v) :=
      (div_le_iff₀ hden).1 hquot_le_r
    nlinarith

/-- The pseudo-hyperbolic circle height inequality is strict away from
vertical alignment of the two points. -/
theorem pair_height_lower_bound_strict_of_horizontal_ne
    {d v a : ℝ} (ha : 0 < a) (hv : 0 < v) (hd : d ≠ 0) :
    a * (1 - pairHyperbolicRadius d v a) <
      v * (1 + pairHyperbolicRadius d v a) := by
  let r := pairHyperbolicRadius d v a
  have hupper : 0 < pairHyperbolicUpperSq d v a := by
    unfold pairHyperbolicUpperSq
    nlinarith [sq_pos_of_ne_zero hd, sq_nonneg (v - a)]
  have hr : 0 < r := pairHyperbolicRadius_pos ha hv hupper
  by_cases hav : a ≤ v
  · nlinarith
  · have hva : v < a := lt_of_not_ge hav
    let A : ℝ := (a - v) ^ 2
    let B : ℝ := (a + v) ^ 2
    let U : ℝ := pairHyperbolicUpperSq d v a
    let L : ℝ := pairHyperbolicLowerSq d v a
    have hB : 0 < B := by
      dsimp only [B]
      positivity
    have hL : 0 < L := pairHyperbolicLowerSq_pos ha hv
    have hBA : 0 < B - A := by
      dsimp only [A, B]
      nlinarith
    have hcross : A * L < U * B := by
      have hid : U * B - A * L = d ^ 2 * (B - A) := by
        dsimp only [A, B, U, L]
        unfold pairHyperbolicUpperSq pairHyperbolicLowerSq
        ring
      nlinarith [mul_pos (sq_pos_of_ne_zero hd) hBA]
    have hratio : A / B < U / L :=
      (div_lt_div_iff₀ hB hL).2 hcross
    have hrsq : r ^ 2 = U / L := by
      exact pairHyperbolicRadius_sq ha hv
    have hquotpos : 0 ≤ (a - v) / (a + v) := by positivity
    have hquotSq : ((a - v) / (a + v)) ^ 2 = A / B := by
      dsimp only [A, B]
      field_simp [(add_pos ha hv).ne']
    have hquot_lt_r : (a - v) / (a + v) < r := by
      nlinarith [hratio, hquotSq]
    have hden := add_pos ha hv
    have hlinear : a - v < r * (a + v) :=
      (div_lt_iff₀ hden).1 hquot_lt_r
    nlinarith

/-- Algebraic normal form of the pair energy in terms of its
pseudo-hyperbolic radius. -/
theorem pairImaginaryEnergy_eq_hyperbolicNormalForm
    {m d v a : ℝ} (ha : 0 < a) (hv : 0 < v)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    pairImaginaryEnergy m d v a =
      m * (1 - pairHyperbolicRadius d v a ^ 2) /
          (4 * a * v * pairHyperbolicRadius d v a ^ 2) *
        (v * (1 + pairHyperbolicRadius d v a ^ 2) -
          a * (1 - pairHyperbolicRadius d v a ^ 2)) := by
  let U := pairHyperbolicUpperSq d v a
  let L := pairHyperbolicLowerSq d v a
  let r := pairHyperbolicRadius d v a
  have hU : 0 < U := hupper
  have hL : 0 < L := pairHyperbolicLowerSq_pos ha hv
  have hr : 0 < r := pairHyperbolicRadius_pos ha hv hupper
  have hrsq : r ^ 2 = U / L := pairHyperbolicRadius_sq ha hv
  have hdiff : L - U = 4 * a * v := by
    dsimp only [U, L]
    unfold pairHyperbolicUpperSq pairHyperbolicLowerSq
    ring
  unfold pairImaginaryEnergy
  change m * ((v - a) / U + (v + a) / L) = _
  change _ = m * (1 - r ^ 2) / (4 * a * v * r ^ 2) *
    (v * (1 + r ^ 2) - a * (1 - r ^ 2))
  have hUeq : U = r ^ 2 * L := by
    apply (eq_div_iff hL.ne').mp at hrsq
    nlinarith
  rw [hUeq] at hdiff ⊢
  have hcoeff : L * (1 - r ^ 2) = 4 * a * v := by
    nlinarith
  field_simp [hL.ne', ha.ne', hv.ne', hr.ne']
  change m * v * a * (v - a + r ^ 2 * (v + a)) * 4 =
    m * L * (1 - r ^ 2) *
      (v * (1 + r ^ 2) - a * (1 - r ^ 2))
  calc
    m * v * a * (v - a + r ^ 2 * (v + a)) * 4 =
        m * (4 * a * v) *
          (v * (1 + r ^ 2) - a * (1 - r ^ 2)) := by ring
    _ = m * (L * (1 - r ^ 2)) *
          (v * (1 + r ^ 2) - a * (1 - r ^ 2)) := by rw [hcoeff]
    _ = _ := by ring

/-- Universal one-pair hyperbolic-energy inequality.  No horizontal
separation condition appears. -/
theorem pairImaginaryEnergy_ge_neg_hyperbolicCost
    {m d v a : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (hv : 0 < v)
    (hupper : 0 < pairHyperbolicUpperSq d v a) :
    -pairHyperbolicCost m a (pairHyperbolicRadius d v a) ≤
      pairImaginaryEnergy m d v a := by
  let r := pairHyperbolicRadius d v a
  have hr : 0 < r := pairHyperbolicRadius_pos ha hv hupper
  have hr1 : r < 1 := pairHyperbolicRadius_lt_one ha hv
  have hheight : a * (1 - r) ≤ v * (1 + r) :=
    pair_height_lower_bound ha hv
  rw [pairImaginaryEnergy_eq_hyperbolicNormalForm ha hv hupper]
  unfold pairHyperbolicCost
  change -(m / (2 * a) * (1 / r - r)) ≤
    m * (1 - r ^ 2) / (4 * a * v * r ^ 2) *
      (v * (1 + r ^ 2) - a * (1 - r ^ 2))
  have hfactor : 0 ≤
      m * (1 - r ^ 2) * (1 + r) := by
    exact mul_nonneg (mul_nonneg hm (by nlinarith)) (by nlinarith)
  have hcore : 0 ≤ v * (1 + r) - a * (1 - r) := by linarith
  field_simp [ha.ne', hv.ne', hr.ne']
  nlinarith [mul_nonneg hfactor hcore]

/-- The universal one-pair energy inequality is strict when the evaluation
point and pair root are not vertically aligned. -/
theorem pairImaginaryEnergy_gt_neg_hyperbolicCost_of_horizontal_ne
    {m d v a : ℝ} (hm : 0 < m) (ha : 0 < a) (hv : 0 < v)
    (hd : d ≠ 0) :
    -pairHyperbolicCost m a (pairHyperbolicRadius d v a) <
      pairImaginaryEnergy m d v a := by
  let r := pairHyperbolicRadius d v a
  have hupper : 0 < pairHyperbolicUpperSq d v a := by
    unfold pairHyperbolicUpperSq
    nlinarith [sq_pos_of_ne_zero hd, sq_nonneg (v - a)]
  have hr : 0 < r := pairHyperbolicRadius_pos ha hv hupper
  have hr1 : r < 1 := pairHyperbolicRadius_lt_one ha hv
  have hheight : a * (1 - r) < v * (1 + r) :=
    pair_height_lower_bound_strict_of_horizontal_ne ha hv hd
  rw [pairImaginaryEnergy_eq_hyperbolicNormalForm ha hv hupper]
  unfold pairHyperbolicCost
  change -(m / (2 * a) * (1 / r - r)) <
    m * (1 - r ^ 2) / (4 * a * v * r ^ 2) *
      (v * (1 + r ^ 2) - a * (1 - r ^ 2))
  have hfactor : 0 < m * (1 - r ^ 2) * (1 + r) := by
    exact mul_pos (mul_pos hm (by nlinarith)) (by nlinarith)
  have hcore : 0 < v * (1 + r) - a * (1 - r) := by linarith
  field_simp [ha.ne', hv.ne', hr.ne']
  nlinarith [mul_pos hfactor hcore]

/-! ## Complex-coordinate identification -/

/-- Pseudo-hyperbolic distance in the open upper half-plane. -/
def upperHalfPlanePseudoHyperbolicDistance (z alpha : ℂ) : ℝ :=
  ‖(z - alpha) / (z - starRingEnd ℂ alpha)‖

private theorem norm_add_mul_I_sq (u w : ℝ) :
    ‖(u : ℂ) + Complex.I * (w : ℂ)‖ ^ 2 = u ^ 2 + w ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- Real-coordinate formula for the upper-half-plane pseudo-hyperbolic
distance. -/
theorem upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius
    (c a x v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    upperHalfPlanePseudoHyperbolicDistance
        ((x : ℂ) + Complex.I * (v : ℂ))
        ((c : ℂ) + Complex.I * (a : ℂ)) =
      pairHyperbolicRadius (x - c) v a := by
  let numerator : ℂ :=
    ((x : ℂ) + Complex.I * (v : ℂ)) -
      ((c : ℂ) + Complex.I * (a : ℂ))
  let denominator : ℂ :=
    ((x : ℂ) + Complex.I * (v : ℂ)) -
      starRingEnd ℂ ((c : ℂ) + Complex.I * (a : ℂ))
  have hnumerator : numerator =
      ((x - c : ℝ) : ℂ) + Complex.I * ((v - a : ℝ) : ℂ) := by
    dsimp only [numerator]
    apply Complex.ext <;> simp
  have hdenominator : denominator =
      ((x - c : ℝ) : ℂ) + Complex.I * ((v + a : ℝ) : ℂ) := by
    dsimp only [denominator]
    apply Complex.ext <;> simp
  have hnumSq : ‖numerator‖ ^ 2 =
      pairHyperbolicUpperSq (x - c) v a := by
    rw [hnumerator, norm_add_mul_I_sq]
    rfl
  have hdenSq : ‖denominator‖ ^ 2 =
      pairHyperbolicLowerSq (x - c) v a := by
    rw [hdenominator, norm_add_mul_I_sq]
    rfl
  have hdenNorm : 0 < ‖denominator‖ := by
    have hL := pairHyperbolicLowerSq_pos (d := x - c) ha hv
    have hnonneg := norm_nonneg denominator
    nlinarith [hdenSq]
  let R := upperHalfPlanePseudoHyperbolicDistance
    ((x : ℂ) + Complex.I * (v : ℂ))
    ((c : ℂ) + Complex.I * (a : ℂ))
  let r := pairHyperbolicRadius (x - c) v a
  have hR0 : 0 ≤ R := norm_nonneg _
  have hr0 : 0 ≤ r := pairHyperbolicRadius_nonneg (x - c) v a
  have hRsq : R ^ 2 = pairHyperbolicUpperSq (x - c) v a /
      pairHyperbolicLowerSq (x - c) v a := by
    dsimp only [R, upperHalfPlanePseudoHyperbolicDistance]
    change ‖numerator / denominator‖ ^ 2 = _
    rw [Complex.norm_div, div_pow, hnumSq, hdenSq]
  have hrsq : r ^ 2 = pairHyperbolicUpperSq (x - c) v a /
      pairHyperbolicLowerSq (x - c) v a :=
    pairHyperbolicRadius_sq ha hv
  nlinarith

/-- One conjugate-pair contribution to a logarithmic derivative. -/
def onePairLogDerivativeContribution (m : ℝ) (alpha z : ℂ) : ℂ :=
  (-(m : ℂ)) / (z - alpha) +
    (-(m : ℂ)) / (z - starRingEnd ℂ alpha)

private theorem neg_real_div_add_mul_I_im
    (m u w : ℝ) (hden : u ^ 2 + w ^ 2 ≠ 0) :
    ((-(m : ℂ)) / ((u : ℂ) + Complex.I * (w : ℂ))).im =
      m * w / (u ^ 2 + w ^ 2) := by
  rw [Complex.div_im]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, Complex.mul_re, Complex.mul_im, neg_zero, zero_mul,
    mul_zero, sub_zero, zero_add, one_mul, Complex.normSq_apply]
  field_simp [hden]
  ring

theorem onePairLogDerivativeContribution_im
    (m c a x v : ℝ)
    (ha : 0 < a) (hv : 0 < v)
    (hupper : 0 < pairHyperbolicUpperSq (x - c) v a) :
    (onePairLogDerivativeContribution m
      ((c : ℂ) + Complex.I * (a : ℂ))
      ((x : ℂ) + Complex.I * (v : ℂ))).im =
        pairImaginaryEnergy m (x - c) v a := by
  have hU : (x - c) ^ 2 + (v - a) ^ 2 ≠ 0 := by
    exact ne_of_gt hupper
  have hL : (x - c) ^ 2 + (v + a) ^ 2 ≠ 0 := by
    exact ne_of_gt (pairHyperbolicLowerSq_pos (d := x - c) ha hv)
  have hsubUpper :
      ((x : ℂ) + Complex.I * (v : ℂ)) -
          ((c : ℂ) + Complex.I * (a : ℂ)) =
        ((x - c : ℝ) : ℂ) + Complex.I * ((v - a : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hsubLower :
      ((x : ℂ) + Complex.I * (v : ℂ)) -
          starRingEnd ℂ ((c : ℂ) + Complex.I * (a : ℂ)) =
        ((x - c : ℝ) : ℂ) + Complex.I * ((v + a : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  unfold onePairLogDerivativeContribution
  rw [hsubUpper, hsubLower, Complex.add_im,
    neg_real_div_add_mul_I_im m (x - c) (v - a) hU,
    neg_real_div_add_mul_I_im m (x - c) (v + a) hL]
  unfold pairImaginaryEnergy pairHyperbolicUpperSq pairHyperbolicLowerSq
  ring

/-- Complex-coordinate form of the influence-disk sign criterion. -/
theorem onePairLogDerivativeContribution_im_nonneg_of_height_sq_le
    {m : ℝ} (hm : 0 ≤ m) {z alpha : ℂ}
    (hz : 0 < z.im) (halpha : 0 < alpha.im) (hne : z ≠ alpha)
    (houtside : alpha.im ^ 2 ≤
      (z.re - alpha.re) ^ 2 + z.im ^ 2) :
    0 ≤ (onePairLogDerivativeContribution m alpha z).im := by
  have hupper : 0 <
      pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im := by
    rw [show pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im =
        Complex.normSq (z - alpha) by
      unfold pairHyperbolicUpperSq Complex.normSq
      simp
      ring]
    exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have halphaForm :
      (alpha.re : ℂ) + Complex.I * (alpha.im : ℂ) = alpha := by
    rw [mul_comm]
    exact Complex.re_add_im alpha
  have hzForm : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  rw [← halphaForm, ← hzForm,
    onePairLogDerivativeContribution_im m alpha.re alpha.im z.re z.im
      halpha hz hupper]
  exact pairImaginaryEnergy_nonneg_of_height_sq_le
    hm halpha hz hupper houtside

/-- Exact complex-coordinate sign criterion for positive weight. -/
theorem onePairLogDerivativeContribution_im_nonneg_iff_height_sq_le
    {m : ℝ} (hm : 0 < m) {z alpha : ℂ}
    (hz : 0 < z.im) (halpha : 0 < alpha.im) (hne : z ≠ alpha) :
    0 ≤ (onePairLogDerivativeContribution m alpha z).im ↔
      alpha.im ^ 2 ≤ (z.re - alpha.re) ^ 2 + z.im ^ 2 := by
  have hupper : 0 <
      pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im := by
    rw [show pairHyperbolicUpperSq (z.re - alpha.re) z.im alpha.im =
        Complex.normSq (z - alpha) by
      unfold pairHyperbolicUpperSq Complex.normSq
      simp
      ring]
    exact Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
  have halphaForm :
      (alpha.re : ℂ) + Complex.I * (alpha.im : ℂ) = alpha := by
    rw [mul_comm]
    exact Complex.re_add_im alpha
  have hzForm : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  rw [← halphaForm, ← hzForm,
    onePairLogDerivativeContribution_im m alpha.re alpha.im z.re z.im
      halpha hz hupper]
  simpa using pairImaginaryEnergy_nonneg_iff_height_sq_le
    hm halpha hz hupper

/-- Strict negativity is exactly membership in the open influence disk. -/
theorem onePairLogDerivativeContribution_im_neg_iff_height_sq_lt
    {m : ℝ} (hm : 0 < m) {z alpha : ℂ}
    (hz : 0 < z.im) (halpha : 0 < alpha.im) (hne : z ≠ alpha) :
    (onePairLogDerivativeContribution m alpha z).im < 0 ↔
      (z.re - alpha.re) ^ 2 + z.im ^ 2 < alpha.im ^ 2 := by
  rw [← not_le,
    onePairLogDerivativeContribution_im_nonneg_iff_height_sq_le
      hm hz halpha hne, not_le]

/-- Complex form of the universal one-pair inequality from the research
note. -/
theorem onePairLogDerivativeContribution_im_ge_neg_hyperbolicCost
    {m c a x v : ℝ} (hm : 0 ≤ m) (ha : 0 < a) (hv : 0 < v)
    (hupper : 0 < pairHyperbolicUpperSq (x - c) v a) :
    -pairHyperbolicCost m a
        (upperHalfPlanePseudoHyperbolicDistance
          ((x : ℂ) + Complex.I * (v : ℂ))
          ((c : ℂ) + Complex.I * (a : ℂ))) ≤
      (onePairLogDerivativeContribution m
        ((c : ℂ) + Complex.I * (a : ℂ))
        ((x : ℂ) + Complex.I * (v : ℂ))).im := by
  rw [upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius c a x v ha hv,
    onePairLogDerivativeContribution_im m c a x v ha hv hupper]
  exact pairImaginaryEnergy_ge_neg_hyperbolicCost hm ha hv hupper

/-- Real-coordinate complex-value form of strict one-pair energy away from
vertical alignment. -/
theorem onePairLogDerivativeContribution_im_gt_neg_hyperbolicCost_of_horizontal_ne
    {m c a x v : ℝ} (hm : 0 < m) (ha : 0 < a) (hv : 0 < v)
    (hd : x - c ≠ 0) :
    -pairHyperbolicCost m a
        (upperHalfPlanePseudoHyperbolicDistance
          ((x : ℂ) + Complex.I * (v : ℂ))
          ((c : ℂ) + Complex.I * (a : ℂ))) <
      (onePairLogDerivativeContribution m
        ((c : ℂ) + Complex.I * (a : ℂ))
        ((x : ℂ) + Complex.I * (v : ℂ))).im := by
  have hupper : 0 < pairHyperbolicUpperSq (x - c) v a := by
    unfold pairHyperbolicUpperSq
    nlinarith [sq_pos_of_ne_zero hd, sq_nonneg (v - a)]
  rw [upperHalfPlanePseudoHyperbolicDistance_eq_pairRadius c a x v ha hv,
    onePairLogDerivativeContribution_im m c a x v ha hv hupper]
  exact pairImaginaryEnergy_gt_neg_hyperbolicCost_of_horizontal_ne
    hm ha hv hd

end

end RiemannGaussian
