import Mathlib

/-!
# Finite rational certificate for the epsilon = 0.04 derivative model

This file mirrors the two finite partitions checked by
`certificates/eps004_derivative_certificate.py`.  All definitions below are
over `ℚ`; the two final theorems are closed propositions discharged by the
Lean kernel through `native_decide`.

The analytic lemmas that reduce the Gaussian-Weil derivative to these
rational functions are intentionally not asserted here.
-/

open scoped BigOperators

namespace RiemannGaussian.Eps004Finite

private def factQ (n : ℕ) : ℚ := (n.factorial : ℚ)

private def momentLower : ℕ → ℚ
  | 0 => 16347 / 10000
  | 1 => 1757 / 100
  | 2 => 642
  | 3 => 39600
  | 4 => 3420000
  | 5 => 379000000
  | 6 => 51400000000
  | 7 => 8250000000000
  | 8 => 1530000000000000
  | 9 => 320000000000000000
  | 10 => 74500000000000000000
  | 11 => 19200000000000000000000
  | _ => 0

private def logLower : ℕ → ℚ
  | 0 => 693147180559 / 1000000000000
  | 1 => 1098612288668 / 1000000000000
  | 2 => 1386294361118 / 1000000000000
  | _ => 0

private def logUpper : ℕ → ℚ
  | 0 => 693147180560 / 1000000000000
  | 1 => 1098612288669 / 1000000000000
  | 2 => 1386294361120 / 1000000000000
  | _ => 0

private def qLower : ℕ → ℚ
  | 0 => 65958 / 1000000
  | 1 => 2287 / 1000000
  | 2 => 2282 / 100000000
  | _ => 0

private def qUpper : ℕ → ℚ
  | 0 => 65960 / 1000000
  | 1 => 2288 / 1000000
  | 2 => 2284 / 100000000
  | _ => 0

private def archBracket (t : ℚ) : ℚ :=
  (Finset.range 12).sum (fun j =>
    momentLower j * ((2 / 25 : ℚ) * t) ^ (2 * j) / factQ (2 * j + 1))
    - 10303 / 5000

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

private def sincPointLower (x : ℚ) : ℚ :=
  (Finset.range 17).sum (fun k =>
    (-1 : ℚ) ^ k * x ^ (2 * k) / factQ (2 * k + 1))
    - x ^ 34 / factQ 35

private def sincCellLower (a b logLo logHi : ℚ) : ℚ :=
  let centre := (a + b) / 2
  let logMid := (logLo + logHi) / 2
  let xMid := logMid * centre
  let xLo := logLo * a
  let xHi := logHi * b
  let radius := max (xMid - xLo) (xHi - xMid)
  sincPointLower xMid - radius / 2

private def compactCellLower (i : ℕ) : ℚ :=
  let a : ℚ := i / 200
  let b : ℚ := (i + 1) / 200
  let bracket := archBracket a
  let arch :=
    if bracket < 0 then
      (4 / 25 : ℚ) * expNegativeTaylor (a * a / 25) 12 * bracket
    else
      (4 / 25 : ℚ) * expNegativeTaylor (b * b / 25) 15 * bracket
  let primes := (Finset.range 3).sum (fun channel =>
    let sincLo := sincCellLower a b (logLower channel) (logUpper channel)
    (if 0 ≤ sincLo then qLower channel else qUpper channel) * sincLo)
  arch + primes

private def phaseCellLower (i : ℕ) : ℚ :=
  let a : ℚ := 11 / 2 + i / 5
  let b : ℚ := min (a + 1 / 5) 16
  let arch :=
    (4 / 25 : ℚ) / expPositiveUpper (b * b / 25) 60 * archBracket a
  let primes := -(Finset.range 3).sum (fun channel =>
    qUpper channel / (logLower channel * a))
  arch + primes

/-- All 1,100 width-1/200 cells covering `[0, 5.5]` clear `1/40000`. -/
theorem compact_cells_positive :
    ∀ i : Fin 1100, (1 / 40000 : ℚ) < compactCellLower i := by
  native_decide

/-- All 53 width-at-most-1/5 cells covering `[5.5, 16]` clear `1/2500`. -/
theorem phase_cells_positive :
    ∀ i : Fin 53, (1 / 2500 : ℚ) < phaseCellLower i := by
  native_decide

end RiemannGaussian.Eps004Finite
