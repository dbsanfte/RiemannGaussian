import Mathlib

/-! Scalar rational endpoint and large-`t` budgets for epsilon = 0.06. -/

namespace RiemannGaussian.Eps006Budgets

/-- Rational upper bound for the explicitly retained low prime channels. -/
def lowChannelUpper : ℚ :=
  304986894290015 / 10^15
    + 19125653611519 / 10^15
    + 531544979074 / 10^15
    + 68121137322 / 10^15

/-- Low-channel bound enlarged by the certified rounding allowance. -/
def primeRoundUpper : ℚ := lowChannelUpper + 74 / 10^7

theorem prime_round_upper_lt :
    primeRoundUpper < (32472 / 100000 : ℚ) := by
  norm_num [primeRoundUpper, lowChannelUpper]

/-- The rounded endpoint inputs leave `0.000012`. -/
theorem endpoint_budget_positive :
    (1 / 100000 : ℚ) <
      1015113 / 250000 - 263665 / 100000 - 109907 / 100000
        - 32472 / 100000 := by
  norm_num

/-- Coarse rational lower bound for the large-parameter Archimedean term. -/
def archLargeLower : ℚ :=
  -1 / 100000 - 2637 / 1000
    + (132 / 100 : ℚ) * (71976 / 10000) * (7 / 22)
    - (423 / 100 : ℚ) * (384 / 10000) * (319 / 1000)

theorem arch_large_lower_gt : (334 / 1000 : ℚ) < archLargeLower := by
  norm_num [archLargeLower]

theorem large_t_margin_positive :
    (9 / 1000 : ℚ) < archLargeLower - 32472 / 100000 := by
  norm_num [archLargeLower]

end RiemannGaussian.Eps006Budgets
