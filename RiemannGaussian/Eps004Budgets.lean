import Mathlib

/-!
# Scalar rational budgets for epsilon = 0.04

These theorems kernel-check the final endpoint and large-`t` arithmetic after
the analytic and fixed-point bounds have been reduced to the displayed
rational inputs.  They do not assert those analytic inputs themselves.
-/

namespace RiemannGaussian.Eps004Budgets

def lowChannelUpper : ℚ :=
  (65960 / 1000000 : ℚ) /
      (693147180559 / 1000000000000 : ℚ) ^ 2
    + (2288 / 1000000 : ℚ) /
      (1098612288668 / 1000000000000 : ℚ) ^ 2
    + (2284 / 100000000 : ℚ) /
      (1386294361118 / 1000000000000 : ℚ) ^ 2

def primeRoundUpper : ℚ := lowChannelUpper + 1 / 1000000

/-- The first three channels plus the rounded `n ≥ 5` tail are below 0.14. -/
theorem prime_round_upper_lt : primeRoundUpper < (7 / 50 : ℚ) := by
  norm_num [primeRoundUpper, lowChannelUpper]

/-- The independently audited endpoint inputs leave more than 0.0006. -/
theorem endpoint_budget_positive :
    (3 / 5000 : ℚ) <
      40402 / 10000 - 32294 / 10000 - 671 / 1000 - primeRoundUpper := by
  norm_num [primeRoundUpper, lowChannelUpper]

def archLargeLower : ℚ :=
  -1 / 5000 - 81 / 25
    + (138 / 100 : ℚ) * (873 / 100) * (7 / 22)
    - (423 / 100 : ℚ) * (13 / 100) * (319 / 1000)

/-- The coarse direct Archimedean budget at `t = 16` exceeds 0.4. -/
theorem arch_large_lower_gt : (2 / 5 : ℚ) < archLargeLower := by
  norm_num [archLargeLower]

/-- The direct large-`t` budget retains more than 0.26 after all primes. -/
theorem large_t_margin_positive :
    (13 / 50 : ℚ) < archLargeLower - primeRoundUpper := by
  norm_num [archLargeLower, primeRoundUpper, lowChannelUpper]

end RiemannGaussian.Eps004Budgets
