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

@[simp] theorem pairHyperbolicRadius_swap_heights (d v a : ℝ) :
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

end

end RiemannGaussian
