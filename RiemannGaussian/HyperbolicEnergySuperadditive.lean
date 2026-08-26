import RiemannGaussian.PairHyperbolicEnergy

/-!
# Multiplicative superadditivity of pair hyperbolic energy

This file checks the collective scalar step in the symmetric-quartet note.
It also evaluates the exact radius threshold at which the one-pair cost is
one.  These are purely algebraic theorems and do not assume a Pick theorem or
an analytic factorization.
-/

namespace RiemannGaussian

noncomputable section

/-- Exact superadditivity defect under multiplication of radii. -/
theorem pairHyperbolicCost_mul_sub
    {m a r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0) :
    pairHyperbolicCost m a (r * s) -
        pairHyperbolicCost m a r - pairHyperbolicCost m a s =
      m / (2 * a) *
        ((1 - r) * (1 - s) * (1 - r * s) / (r * s)) := by
  unfold pairHyperbolicCost
  field_simp [hr, hs]
  ring

/-- The cost of a product dominates the sum of the individual costs for
radii in `(0,1]`. -/
theorem pairHyperbolicCost_superadditive
    {m a r s : ℝ} (hm : 0 ≤ m) (ha : 0 < a)
    (hr : 0 < r) (hr1 : r ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) :
    pairHyperbolicCost m a r + pairHyperbolicCost m a s ≤
      pairHyperbolicCost m a (r * s) := by
  rw [← sub_nonneg]
  rw [show pairHyperbolicCost m a (r * s) -
        (pairHyperbolicCost m a r + pairHyperbolicCost m a s) =
      pairHyperbolicCost m a (r * s) - pairHyperbolicCost m a r -
        pairHyperbolicCost m a s by ring]
  rw [pairHyperbolicCost_mul_sub hr.ne' hs.ne']
  exact mul_nonneg (div_nonneg hm (by positivity))
    (div_nonneg
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hr1) (sub_nonneg.mpr hs1))
        (sub_nonneg.mpr (mul_le_one₀ hr1 hs.le hs1)))
      (mul_nonneg hr.le hs.le))

/-- For a positive weight and two genuine interior radii, the collective
superadditivity gain is strict. -/
theorem pairHyperbolicCost_strictlySuperadditive
    {m a r s : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hr : 0 < r) (hr1 : r < 1) (hs : 0 < s) (hs1 : s < 1) :
    pairHyperbolicCost m a r + pairHyperbolicCost m a s <
      pairHyperbolicCost m a (r * s) := by
  rw [← sub_pos]
  rw [show pairHyperbolicCost m a (r * s) -
        (pairHyperbolicCost m a r + pairHyperbolicCost m a s) =
      pairHyperbolicCost m a (r * s) - pairHyperbolicCost m a r -
        pairHyperbolicCost m a s by ring]
  rw [pairHyperbolicCost_mul_sub hr.ne' hs.ne']
  apply mul_pos (div_pos hm (by positivity))
  apply div_pos
  · exact mul_pos (mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hs1))
      (sub_pos.mpr
        (mul_lt_one_of_nonneg_of_lt_one_left hr.le hr1 hs1.le))
  · exact mul_pos hr hs

/-! ## Arbitrary finite collections -/

/-- A finite product of positive radii at most one is at most one. -/
theorem positiveMultiset_prod_le_one
    {radii : Multiset ℝ}
    (hpos : ∀ r ∈ radii, 0 < r)
    (hone : ∀ r ∈ radii, r ≤ 1) :
    radii.prod ≤ 1 := by
  induction radii using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
      rw [Multiset.prod_cons]
      exact mul_le_one₀ (hone r (by simp))
        (Multiset.prod_pos fun u hu => hpos u (by simp [hu])).le
        (ih
          (fun u hu => hpos u (by simp [hu]))
          (fun u hu => hone u (by simp [hu])))

/-- A nonempty finite product of genuine interior radii is strictly below
one. -/
theorem positiveMultiset_prod_lt_one_of_nonempty
    {radii : Multiset ℝ} (hne : radii ≠ 0)
    (hpos : ∀ r ∈ radii, 0 < r)
    (hone : ∀ r ∈ radii, r < 1) :
    radii.prod < 1 := by
  induction radii using Multiset.induction_on with
  | empty => exact False.elim (hne rfl)
  | cons r s _ =>
      rw [Multiset.prod_cons]
      exact mul_lt_one_of_nonneg_of_lt_one_left
        (hpos r (by simp)).le (hone r (by simp))
        (positiveMultiset_prod_le_one
          (fun u hu => hpos u (by simp [hu]))
          (fun u hu => (hone u (by simp [hu])).le))

/-- N-ary multiplicative superadditivity: the cost of the product dominates
the sum of all equal-height, equal-weight pair costs. -/
theorem pairHyperbolicCost_multiset_sum_le_cost_prod
    {m a : ℝ} (hm : 0 ≤ m) (ha : 0 < a)
    (radii : Multiset ℝ)
    (hpos : ∀ r ∈ radii, 0 < r)
    (hone : ∀ r ∈ radii, r ≤ 1) :
    (radii.map fun r => pairHyperbolicCost m a r).sum ≤
      pairHyperbolicCost m a radii.prod := by
  induction radii using Multiset.induction_on with
  | empty => simp [pairHyperbolicCost]
  | cons r s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
      have hsPos : ∀ u ∈ s, 0 < u :=
        fun u hu => hpos u (by simp [hu])
      have hsOne : ∀ u ∈ s, u ≤ 1 :=
        fun u hu => hone u (by simp [hu])
      calc
        pairHyperbolicCost m a r +
            (s.map fun u => pairHyperbolicCost m a u).sum ≤
          pairHyperbolicCost m a r +
            pairHyperbolicCost m a s.prod :=
          add_le_add_right (ih hsPos hsOne) _
        _ ≤ pairHyperbolicCost m a (r * s.prod) :=
          pairHyperbolicCost_superadditive hm ha
            (hpos r (by simp)) (hone r (by simp))
            (Multiset.prod_pos hsPos)
            (positiveMultiset_prod_le_one hsPos hsOne)

/-- With at least two genuine interior radii and positive weight, the n-ary
superadditivity gain is strict. -/
theorem pairHyperbolicCost_multiset_sum_lt_cost_prod_of_two_le_card
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a)
    (radii : Multiset ℝ) (hcard : 2 ≤ radii.card)
    (hpos : ∀ r ∈ radii, 0 < r)
    (hone : ∀ r ∈ radii, r < 1) :
    (radii.map fun r => pairHyperbolicCost m a r).sum <
      pairHyperbolicCost m a radii.prod := by
  induction radii using Multiset.induction_on with
  | empty => simp at hcard
  | cons r s _ =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
      have hsPos : ∀ u ∈ s, 0 < u :=
        fun u hu => hpos u (by simp [hu])
      have hsOne : ∀ u ∈ s, u < 1 :=
        fun u hu => hone u (by simp [hu])
      have hsNonempty : s ≠ 0 := by
        intro hs
        subst s
        simp at hcard
      calc
        pairHyperbolicCost m a r +
            (s.map fun u => pairHyperbolicCost m a u).sum ≤
          pairHyperbolicCost m a r +
            pairHyperbolicCost m a s.prod :=
          add_le_add_right
            (pairHyperbolicCost_multiset_sum_le_cost_prod
              hm.le ha s hsPos fun u hu => (hsOne u hu).le) _
        _ < pairHyperbolicCost m a (r * s.prod) :=
          pairHyperbolicCost_strictlySuperadditive hm ha
            (hpos r (by simp)) (hone r (by simp))
            (Multiset.prod_pos hsPos)
            (positiveMultiset_prod_lt_one_of_nonempty hsNonempty hsPos hsOne)

/-- The one-pair radius at which the hyperbolic cost equals one. -/
def pairHyperbolicThreshold (m a : ℝ) : ℝ :=
  m / (Real.sqrt (m ^ 2 + a ^ 2) + a)

theorem pairHyperbolicThreshold_pos
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    0 < pairHyperbolicThreshold m a := by
  unfold pairHyperbolicThreshold
  positivity

theorem pairHyperbolicThreshold_lt_one
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    pairHyperbolicThreshold m a < 1 := by
  let beta := Real.sqrt (m ^ 2 + a ^ 2)
  have hbetaSq : beta ^ 2 = m ^ 2 + a ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  have hbeta0 : 0 ≤ beta := Real.sqrt_nonneg _
  have hmbeta : m < beta + a := by
    nlinarith [sq_nonneg (beta - m)]
  unfold pairHyperbolicThreshold
  exact (div_lt_one (by positivity)).2 hmbeta

/-- Rationalized form of the threshold. -/
theorem pairHyperbolicThreshold_eq_sqrt_sub_div
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    pairHyperbolicThreshold m a =
      (Real.sqrt (m ^ 2 + a ^ 2) - a) / m := by
  let beta := Real.sqrt (m ^ 2 + a ^ 2)
  have hbetaSq : beta ^ 2 = m ^ 2 + a ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  unfold pairHyperbolicThreshold
  change m / (beta + a) = (beta - a) / m
  field_simp [hm.ne', (by positivity : beta + a ≠ 0)]
  nlinarith

/-- Exact evaluation of the threshold cost. -/
@[simp] theorem pairHyperbolicCost_threshold
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    pairHyperbolicCost m a (pairHyperbolicThreshold m a) = 1 := by
  let beta := Real.sqrt (m ^ 2 + a ^ 2)
  have hbetaSq : beta ^ 2 = m ^ 2 + a ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  have hden : beta + a ≠ 0 := by positivity
  unfold pairHyperbolicCost pairHyperbolicThreshold
  change m / (2 * a) *
    (1 / (m / (beta + a)) - m / (beta + a)) = 1
  field_simp [hm.ne', ha.ne', hden]
  nlinarith

theorem pairHyperbolicCost_anti
    {m a r s : ℝ} (hm : 0 ≤ m) (ha : 0 < a)
    (hr : 0 < r) (hrs : r ≤ s) :
    pairHyperbolicCost m a s ≤ pairHyperbolicCost m a r := by
  have hs : 0 < s := hr.trans_le hrs
  have hinv : 1 / s ≤ 1 / r := by
    exact one_div_le_one_div_of_le hr hrs
  unfold pairHyperbolicCost
  exact mul_le_mul_of_nonneg_left (by linarith)
    (div_nonneg hm (by positivity))

theorem pairHyperbolicCost_strictAnti
    {m a r s : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hr : 0 < r) (hrs : r < s) :
    pairHyperbolicCost m a s < pairHyperbolicCost m a r := by
  have hs : 0 < s := hr.trans hrs
  have hinv : 1 / s < 1 / r := by
    exact one_div_lt_one_div_of_lt hr hrs
  unfold pairHyperbolicCost
  exact mul_lt_mul_of_pos_left (by linarith) (div_pos hm (by positivity))

/-- A cost of at least one forces the radius below the exact threshold. -/
theorem radius_le_pairHyperbolicThreshold_of_one_le_cost
    {m a r : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hcost : 1 ≤ pairHyperbolicCost m a r) :
    r ≤ pairHyperbolicThreshold m a := by
  apply le_of_not_gt
  intro hthreshold
  have hstrict := pairHyperbolicCost_strictAnti hm ha
    (pairHyperbolicThreshold_pos hm ha) hthreshold
  rw [pairHyperbolicCost_threshold hm ha] at hstrict
  linarith

/-- A cost strictly above one forces the radius strictly below the exact
threshold. -/
theorem radius_lt_pairHyperbolicThreshold_of_one_lt_cost
    {m a r : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hcost : 1 < pairHyperbolicCost m a r) :
    r < pairHyperbolicThreshold m a := by
  apply lt_of_not_ge
  intro hthreshold
  have hanti := pairHyperbolicCost_anti hm.le ha
    (pairHyperbolicThreshold_pos hm ha) hthreshold
  rw [pairHyperbolicCost_threshold hm ha] at hanti
  linarith

/-- Collective two-radius consequence used by the quartet pole equation. -/
theorem radius_mul_le_pairHyperbolicThreshold_of_cost_sum
    {m a r s : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hr : 0 < r) (hr1 : r < 1) (hs : 0 < s) (hs1 : s < 1)
    (hcost : 1 ≤ pairHyperbolicCost m a r +
      pairHyperbolicCost m a s) :
    r * s ≤ pairHyperbolicThreshold m a := by
  apply radius_le_pairHyperbolicThreshold_of_one_le_cost hm ha
  exact hcost.trans
    (pairHyperbolicCost_superadditive hm.le ha hr hr1.le hs hs1.le)

/-- For two genuine interior radii the product conclusion is strict, even
when the input cost sum is only weakly bounded below by one. -/
theorem radius_mul_lt_pairHyperbolicThreshold_of_cost_sum
    {m a r s : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hr : 0 < r) (hr1 : r < 1) (hs : 0 < s) (hs1 : s < 1)
    (hcost : 1 ≤ pairHyperbolicCost m a r +
      pairHyperbolicCost m a s) :
    r * s < pairHyperbolicThreshold m a := by
  apply radius_lt_pairHyperbolicThreshold_of_one_lt_cost hm ha
  exact hcost.trans_lt
    (pairHyperbolicCost_strictlySuperadditive hm ha hr hr1 hs hs1)

/-- N-ary strict threshold consequence.  A unit collective cost across at
least two genuine interior radii forces their complete product strictly below
the same exact threshold as in the quartet case. -/
theorem multiset_prod_lt_pairHyperbolicThreshold_of_cost_sum
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a)
    (radii : Multiset ℝ) (hcard : 2 ≤ radii.card)
    (hpos : ∀ r ∈ radii, 0 < r)
    (hone : ∀ r ∈ radii, r < 1)
    (hcost : 1 ≤
      (radii.map fun r => pairHyperbolicCost m a r).sum) :
    radii.prod < pairHyperbolicThreshold m a := by
  apply radius_lt_pairHyperbolicThreshold_of_one_lt_cost hm ha
  exact hcost.trans_lt
    (pairHyperbolicCost_multiset_sum_lt_cost_prod_of_two_le_card
      hm ha radii hcard hpos hone)

/-- Cayley transform of the threshold, used in the final defect estimate. -/
theorem two_mul_pairHyperbolicThreshold_div_one_add_sq
    {m a : ℝ} (hm : 0 < m) (ha : 0 < a) :
    2 * pairHyperbolicThreshold m a /
        (1 + pairHyperbolicThreshold m a ^ 2) =
      m / Real.sqrt (m ^ 2 + a ^ 2) := by
  let beta := Real.sqrt (m ^ 2 + a ^ 2)
  have hbetaSq : beta ^ 2 = m ^ 2 + a ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  have hbeta : 0 < beta := Real.sqrt_pos.2 (by positivity)
  have hden : beta + a ≠ 0 := by positivity
  unfold pairHyperbolicThreshold
  change 2 * (m / (beta + a)) /
      (1 + (m / (beta + a)) ^ 2) = m / beta
  field_simp [hm.ne', hbeta.ne', hden]
  nlinarith

end

end RiemannGaussian
