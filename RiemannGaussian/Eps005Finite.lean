import Mathlib

/-!
# Finite rational certificate for the epsilon = 0.05 derivative model

The elementary boundary cosine and sinc are retained in this version.  The
analytic reduction is outside this file; the two finite rational partitions
are closed propositions checked by `native_decide`.
-/

open scoped BigOperators

namespace RiemannGaussian.Eps005Finite

private def factQ (n : ℕ) : ℚ := (n.factorial : ℚ)

private def momentLower : ℕ → ℚ
  | 0 => 14915 / 10000
  | 1 => 1287 / 100
  | 2 => 379
  | 3 => 18900
  | 4 => 1321000
  | 5 => 118800000
  | 6 => 13050000000
  | 7 => 1695000000000
  | 8 => 253900000000000
  | 9 => 43120000000000000
  | 10 => 8180000000000000000
  | 11 => 1716000000000000000000
  | 12 => 394100000000000000000000
  | 13 => 9839 * 10^22
  | 14 => 2652 * 10^25
  | 15 => 7678 * 10^27
  | 16 => 2374 * 10^30
  | 17 => 7814 * 10^32
  | _ => 0

private def logLower : ℕ → ℚ
  | 0 => 693147180559 / 1000000000000
  | 1 => 1098612288668 / 1000000000000
  | 2 => 1386294361118 / 1000000000000
  | 3 => 1609437912434 / 1000000000000
  | _ => 0

private def logUpper : ℕ → ℚ
  | 0 => 693147180560 / 1000000000000
  | 1 => 1098612288669 / 1000000000000
  | 2 => 1386294361120 / 1000000000000
  | 3 => 1609437912435 / 1000000000000
  | _ => 0

private def qLower : ℕ → ℚ
  | 0 => 1075575 / 10000000
  | 1 => 92488 / 10000000
  | 2 => 2255 / 10000000
  | 3 => 223 / 10000000
  | _ => 0

private def qUpper : ℕ → ℚ
  | 0 => 1075577 / 10000000
  | 1 => 92489 / 10000000
  | 2 => 2257 / 10000000
  | 3 => 224 / 10000000
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
  1 / expPositiveUpper x 70

private def cosineUpper (x : ℚ) : ℚ :=
  (Finset.range 7).sum (fun k =>
    (-1 : ℚ) ^ k * x ^ (2 * k) / factQ (2 * k))

private def sincUpper (x : ℚ) : ℚ :=
  (Finset.range 7).sum (fun k =>
    (-1 : ℚ) ^ k * x ^ (2 * k) / factQ (2 * k + 1))

private def momentSum (t : ℚ) : ℚ :=
  (Finset.range 18).sum (fun j =>
    momentLower j * (t / 10) ^ (2 * j) / factQ (2 * j + 1))

private def archBracketLower (t : ℚ) : ℚ :=
  let x := t / 20
  momentSum t - (1012579 / 1000000 : ℚ) *
    (2 * cosineUpper x + (1 / 20 : ℚ) * sincUpper x)

private def sincPointLower (x : ℚ) : ℚ :=
  (Finset.range 25).sum (fun k =>
    (-1 : ℚ) ^ k * x ^ (2 * k) / factQ (2 * k + 1))
    - x ^ 50 / factQ 51

private def sincCellLower (a b logLo logHi : ℚ) : ℚ :=
  let centre := (a + b) / 2
  let logMid := (logLo + logHi) / 2
  let xMid := logMid * centre
  let radius := max (xMid - logLo * a) (logHi * b - xMid)
  sincPointLower xMid - radius / 2

private def compactCellLower (i : ℕ) : ℚ :=
  let a : ℚ := i / 200
  let b : ℚ := (i + 1) / 200
  let bracket := archBracketLower a
  let arch :=
    if bracket < 0 then
      (1 / 5 : ℚ) * expNegativeTaylor (a * a / 20) 14 * bracket
    else
      (1 / 5 : ℚ) * expNegativeLower (b * b / 20) * bracket
  let primes := (Finset.range 4).sum (fun channel =>
    let sincLo := sincCellLower a b (logLower channel) (logUpper channel)
    (if 0 ≤ sincLo then qLower channel else qUpper channel) * sincLo)
  arch + primes

private def phaseCellLower (i : ℕ) : ℚ :=
  let a : ℚ := 6 + i / 40
  let b : ℚ := 6 + (i + 1) / 40
  let arch :=
    (1 / 5 : ℚ) * expNegativeLower (b * b / 20) * archBracketLower a
  let primes := -(Finset.range 4).sum (fun channel =>
    qUpper channel / (logLower channel * a))
  arch + primes

/-- All 1,200 cells covering `[0,6]` clear `8/100000`. -/
theorem compact_cells_positive :
    ∀ i : Fin 1200, (8 / 100000 : ℚ) < compactCellLower i := by
  native_decide

/-- All 360 cells covering `[6,15]` clear `1/10000`. -/
theorem phase_cells_positive :
    ∀ i : Fin 360, (1 / 10000 : ℚ) < phaseCellLower i := by
  native_decide

end RiemannGaussian.Eps005Finite
