import Mathlib

/-! Scalar rational endpoint and large-`t` budgets for epsilon = 0.05. -/

namespace RiemannGaussian.Eps005Budgets

/-- Rational upper bound for the explicitly retained low prime channels. -/
def lowChannelUpper : ℚ :=
  2238670 / 10000000
    + 76630 / 10000000
    + 1174 / 10000000
    + 87 / 10000000

/-- Low-channel bound enlarged by the certified rounding allowance. -/
def primeRoundUpper : ℚ := lowChannelUpper + 6 / 10000000

theorem prime_round_upper_lt :
    primeRoundUpper < (231657 / 1000000 : ℚ) := by
  norm_num [primeRoundUpper, lowChannelUpper]

/-- The rounded endpoint inputs leave more than `0.00005`. -/
theorem endpoint_budget_positive :
    (1 / 20000 : ℚ) <
      40503 / 10000 - 288832 / 100000 - 93027 / 100000
        - 231657 / 1000000 := by
  norm_num

/-- Coarse rational lower bound for the large-parameter Archimedean term. -/
def archLargeLower : ℚ :=
  -6 / 100000 - 289 / 100
    + (132 / 100 : ℚ) * (7839 / 1000) * (7 / 22)
    - (423 / 100 : ℚ) * (81 / 1000) * (319 / 1000)

theorem arch_large_lower_gt : (293 / 1000 : ℚ) < archLargeLower := by
  norm_num [archLargeLower]

theorem large_t_margin_positive :
    (61 / 1000 : ℚ) < archLargeLower - 231657 / 1000000 := by
  norm_num [archLargeLower]

end RiemannGaussian.Eps005Budgets
