import Mathlib

/-!
# Finite rational certificate for the epsilon = 0.06 derivative model

The certificate keeps four signed prime-power channels on all of `[0,15]`.
The lower derivative cells are positive up to `t = 14.645` and negative
afterward.  Instead of requiring pointwise monotonicity to the endpoint, the
last assertion checks the downward-rounded accumulated integral of `F'` and
proves that the total increase is greater than two.
-/

open scoped BigOperators

namespace RiemannGaussian.Eps006Finite

private def factQ (n : ℕ) : ℚ := (n.factorial : ℚ)

private def momentLower : ℕ → ℚ
  | 0 => 689713 / 500000
  | 1 => 984 / 100
  | 2 => 2405 / 10
  | 3 => 9980
  | 4 => 581000
  | 5 => 43500000
  | 6 => 3980000000
  | 7 => 430000000000
  | 8 => 53700000000000
  | 9 => 760 * 10^13
  | 10 => 120 * 10^16
  | 11 => 210 * 10^18
  | 12 => 402 * 10^20
  | 13 => 838 * 10^22
  | 14 => 188 * 10^25
  | 15 => 454 * 10^27
  | 16 => 117 * 10^30
  | 17 => 321 * 10^32
  | _ => 0

private def logLower : ℕ → ℚ
  | 0 => 693147180559 / 10^12
  | 1 => 1098612288668 / 10^12
  | 2 => 1386294361118 / 10^12
  | 3 => 1609437912434 / 10^12
  | _ => 0

private def logUpper : ℕ → ℚ
  | 0 => 693147180560 / 10^12
  | 1 => 1098612288669 / 10^12
  | 2 => 1386294361120 / 10^12
  | 3 => 1609437912435 / 10^12
  | _ => 0

private def qLower : ℕ → ℚ
  | 0 => 146531872567189 / 10^15
  | 1 => 23083687751283 / 10^15
  | 2 => 1021529548915 / 10^15
  | 3 => 176453527630 / 10^15
  | _ => 0

private def qUpper : ℕ → ℚ
  | 0 => 146531872567190 / 10^15
  | 1 => 23083687751284 / 10^15
  | 2 => 1021529548916 / 10^15
  | 3 => 176453527631 / 10^15
  | _ => 0

private def expNegativeTaylor (x : ℚ) (degree : ℕ) : ℚ :=
  (Finset.range (degree + 1)).sum (fun k =>
    (-1 : ℚ) ^ k * x ^ k / factQ k)

private def expPositiveLower (x : ℚ) (degree : ℕ) : ℚ :=
  (Finset.range (degree + 1)).sum (fun k => x ^ k / factQ k)

private def expPositiveUpper (x : ℚ) (degree : ℕ) : ℚ :=
  let partialSum := expPositiveLower x degree
  let omitted := x ^ (degree + 1) / factQ (degree + 1)
  let ratio := x / (degree + 2)
  partialSum + omitted / (1 - ratio)

private def expNegativeLower (x : ℚ) : ℚ :=
  1 / expPositiveUpper x 80

private def cosineUpper (x : ℚ) : ℚ :=
  (Finset.range 7).sum (fun k =>
    (-1 : ℚ) ^ k * x ^ (2 * k) / factQ (2 * k))

private def sincUpper (x : ℚ) : ℚ :=
  (Finset.range 7).sum (fun k =>
    (-1 : ℚ) ^ k * x ^ (2 * k) / factQ (2 * k + 1))

private def momentSum (t : ℚ) : ℚ :=
  (Finset.range 18).sum (fun j =>
    momentLower j * ((3 / 25 : ℚ) * t) ^ (2 * j) / factQ (2 * j + 1))

private def archBracketLower (t : ℚ) : ℚ :=
  let x := (3 / 50 : ℚ) * t
  momentSum t - (1015114 / 10^6 : ℚ) *
    (2 * cosineUpper x + (3 / 50 : ℚ) * sincUpper x)

private def sincPointLower (x : ℚ) (terms : ℕ) : ℚ :=
  (Finset.range terms).sum (fun k =>
    (-1 : ℚ) ^ k * x ^ (2 * k) / factQ (2 * k + 1))
    - x ^ (2 * terms) / factQ (2 * terms + 1)

private def sincCellLower (a b logLo logHi : ℚ) : ℚ :=
  if b ≤ 1 then
    sincPointLower (logHi * b) 10
  else
    let centre := (a + b) / 2
    let logMid := (logLo + logHi) / 2
    let xMid := logMid * centre
    let xLo := logLo * a
    let xHi := logHi * b
    let radius := max (xMid - xLo) (xHi - xMid)
    let variationSlope := min (1 / 2 : ℚ) (xHi / 3)
    sincPointLower xMid 45 - radius * variationSlope

private def cellEndpoints (i : ℕ) : ℚ × ℚ :=
  if i < 6000 then
    (i / 2000, (i + 1) / 2000)
  else
    (3 + (i - 6000) / 200, 3 + (i - 6000 + 1) / 200)

private def derivativeCellLower (i : ℕ) : ℚ :=
  let endpoints := cellEndpoints i
  let a := endpoints.1
  let b := endpoints.2
  let bracket := archBracketLower a
  let arch :=
    if bracket < 0 then
      (6 / 25 : ℚ) * expNegativeTaylor ((3 / 50 : ℚ) * a * a) 14 * bracket
    else
      (6 / 25 : ℚ) * expNegativeLower ((3 / 50 : ℚ) * b * b) * bracket
  let primes := (Finset.range 4).sum (fun channel =>
    let sincLo := sincCellLower a b (logLower channel) (logUpper channel)
    (if 0 ≤ sincLo then qLower channel else qUpper channel) * sincLo)
  arch + primes

private def roundedIncrement (i : ℕ) : ℚ :=
  let endpoints := cellEndpoints i
  let raw := derivativeCellLower i
    * (endpoints.2 ^ 2 - endpoints.1 ^ 2) / 2
  ((⌊raw * 10^18⌋ : ℤ) : ℚ) / 10^18

/-- Kernel-checked sign pattern and accumulated derivative certificate. -/
theorem signed_cells_and_cumulative_certificate :
    (∀ i : Fin 8329, 0 < derivativeCellLower i) ∧
    (∀ i : Fin 71, derivativeCellLower (8329 + i) < 0) ∧
    (2 : ℚ) < (Finset.range 8400).sum roundedIncrement := by
  native_decide

theorem initial_cells_positive :
    ∀ i : Fin 8329, 0 < derivativeCellLower i :=
  signed_cells_and_cumulative_certificate.1

theorem terminal_cells_negative :
    ∀ i : Fin 71, derivativeCellLower (8329 + i) < 0 :=
  signed_cells_and_cumulative_certificate.2.1

theorem cumulative_increase_gt_two :
    (2 : ℚ) < (Finset.range 8400).sum roundedIncrement :=
  signed_cells_and_cumulative_certificate.2.2

end RiemannGaussian.Eps006Finite
