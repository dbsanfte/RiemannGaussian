/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerMaclaurinEnclosure
/-!
# A kernel-checked Euler--Maclaurin sample near two

The exact n^(-2) amplitude is separated from the tiny phase. Every
normalized rising factorial and Bernoulli correction is verified by a
finite dyadic recurrence step. The complete Dirichlet prefix is checked
in blocks of eight, bounding the cost of individual kernel reductions.
Every stored intermediate value is checked against the actual recurrence.
The analytic tail is paid in `RosserSchoenfeldZetaTwoBudget`.
-/

open LeanCert.Core LeanCert.Engine
open RiemannGaussian.CertifiedComplexInterval RiemannGaussian.ZetaEulerMaclaurinEnclosure
namespace RiemannGaussian.RosserSchoenfeldZetaTwoSample
set_option maxRecDepth 20000

/-- Dyadic interval equality ignores only the proof of endpoint ordering. -/
private theorem interval_ext {A B : IntervalDyadic}
    (hl : A.lo=B.lo) (hu : A.hi=B.hi) : A=B := by
  cases A
  cases B
  simp_all

/-- Four exact endpoint equalities identify a complex rectangle. -/
private theorem box_ext {A B : Box}
    (h : A.re.lo=B.re.lo ∧ A.re.hi=B.re.hi ∧ A.im.lo=B.im.lo ∧ A.im.hi=B.im.hi) : A=B := by
  have hr := interval_ext h.1 h.2.1
  have hi := interval_ext h.2.2.1 h.2.2.2
  cases A
  cases B
  simp_all

/-- Outward dyadic precision and proved Taylor depth for the finite sample. -/
private def cfg : DyadicConfig := {precision := -110, taylorDepth := 20}
/-- Exact rational imaginary displacement. -/
private def h : ℚ := 1/10^12
/-- Outward rectangle containing the exact sample point. -/
private def input : Box := rational cfg.precision 2 h
/-- Preserve the exact rational amplitude before enclosing the complex phase. -/
private def power (n : ℕ) : EvalResult Box :=
  match natPower cfg n (rational cfg.precision 0 (-h)) with
  | .error err => .error err
  | .ok P => .ok (mul cfg.precision (rational cfg.precision (1/(n:ℚ)^2) 0) P)
/-- The literal finite Dirichlet prefix with all signed phases retained. -/
private def prefixTwo : ℕ → EvalResult Box
 | 0 => .ok (rational cfg.precision 0 0)
 | n+1 =>
   match prefixTwo n with
   | .error err => .error err
   | .ok P =>
     match power (n+1) with
     | .error err => .error err
     | .ok Q => .ok (add cfg.precision P Q)
/-- The whole finite Euler--Maclaurin expression at the fixed sample. -/
private def value : EvalResult Box :=
  match prefixTwo 64 with
  | .error err => .error err
  | .ok P =>
    match power 65 with
    | .error err => .error err
    | .ok Q =>
      match inv cfg (add cfg.precision input (rational cfg.precision (-1) 0)) with
      | .error err => .error err
      | .ok U => .ok (add cfg.precision P (mul cfg.precision Q
        (add cfg.precision
          (add cfg.precision (mul cfg.precision (rational cfg.precision 65 0) U)
            (rational cfg.precision (1/2) 0))
          (correctionBox cfg.precision 64 input 19))))
/-- The exact rational imaginary lower-bound test. -/
private def check : Bool := match value with
 | .error _ => false
 | .ok B => decide (-9375482548/10^22 < B.im.lo.toRat)


/-- Continue an exact interval prefix for a finite block of consecutive indices. -/
private def advance (n : ℕ) (B : Box) : ℕ → EvalResult Box
  | 0 => .ok B
  | k+1 =>
    match advance n B k with
    | .error err => .error err
    | .ok P =>
      match power (n+k+1) with
      | .error err => .error err
      | .ok Q => .ok (add cfg.precision P Q)

/-- Exact continuation of the original finite prefix through a block. -/
private lemma prefix_add (n k : ℕ) : prefixTwo (n+k) =
    match prefixTwo n with
    | .error err => .error err
    | .ok P => advance n P k := by
  induction k with
  | zero => cases he : prefixTwo n <;> simp [advance]
  | succ k ih =>
    rw [show n+(k+1)=(n+k)+1 by omega, prefixTwo, ih]
    cases he : prefixTwo n <;> simp [advance]

/-- Compare all four exact dyadic endpoints after successful evaluation. -/
private def sameResult (E : EvalResult Box) (B : Box) : Bool :=
  match E with
  | .error _ => false
  | .ok A => decide (A.re.lo=B.re.lo ∧ A.re.hi=B.re.hi ∧ A.im.lo=B.im.lo ∧ A.im.hi=B.im.hi)

/-- A successful endpoint comparison proves equality of the actual result. -/
private lemma eq_of_sameResult {E : EvalResult Box} {B : Box}
    (hh : sameResult E B = true) : E = .ok B := by
  cases E with
  | error err => simp [sameResult] at hh
  | ok A =>
    congr 1
    apply box_ext
    simpa [sameResult] using hh

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r0 : Box := { re := { lo := ⟨1298074214633706907132624082305024, -110⟩, hi := ⟨1298074214633706907132624082305024, -110⟩, le := by decide +kernel }, im := { lo := ⟨0, -110⟩, hi := ⟨0, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r0_check : scaledRisingBox cfg.precision 64 input 0 = r0 := by

  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c0 : Box := { re := { lo := ⟨0, -110⟩, hi := ⟨0, -110⟩, le := by decide +kernel }, im := { lo := ⟨0, -110⟩, hi := ⟨0, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c0_check : correctionBox cfg.precision 64 input 0 = c0 := by

  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r1 : Box := { re := { lo := ⟨39940745065652520219465356378616, -110⟩, hi := ⟨39940745065652520219465356378618, -110⟩, le := by decide +kernel }, im := { lo := ⟨19970372532826260109, -110⟩, hi := ⟨19970372532826260110, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r1_check : scaledRisingBox cfg.precision 64 input 1 = r1 := by

  rw [scaledRisingBox, r0_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c1 : Box := { re := { lo := ⟨3328395422137710018288779698217, -110⟩, hi := ⟨3328395422137710018288779698219, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664197711068855009, -110⟩, hi := ⟨1664197711068855010, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c1_check : correctionBox cfg.precision 64 input 1 = c1 := by

  rw [correctionBox, c0_check, r1_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r2 : Box := { re := { lo := ⟨1843419003030116317821477679468, -110⟩, hi := ⟨1843419003030116317821477679470, -110⟩, le := by decide +kernel }, im := { lo := ⟨1536182502525096930, -110⟩, hi := ⟨1536182502525096932, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r2_check : scaledRisingBox cfg.precision 64 input 2 = r2 := by

  rw [scaledRisingBox, r1_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c2 : Box := { re := { lo := ⟨3328395422137710018288779698217, -110⟩, hi := ⟨3328395422137710018288779698219, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664197711068855009, -110⟩, hi := ⟨1664197711068855010, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c2_check : correctionBox cfg.precision 64 input 2 = c2 := by

  rw [correctionBox, c1_check, r2_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r3 : Box := { re := { lo := ⟨113441169417237927250552448948, -110⟩, hi := ⟨113441169417237927250552448950, -110⟩, le := by decide +kernel }, im := { lo := ⟨122894600202007753, -110⟩, hi := ⟨122894600202007755, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r3_check : scaledRisingBox cfg.precision 64 input 3 = r3 := by

  rw [scaledRisingBox, r2_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c3 : Box := { re := { lo := ⟨3328237864957963854500931708704, -110⟩, hi := ⟨3328237864957963854500931708707, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027024124129998, -110⟩, hi := ⟨1664027024124130000, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c3_check : correctionBox cfg.precision 64 input 3 = c3 := by

  rw [correctionBox, c2_check, r3_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r4 : Box := { re := { lo := ⟨8726243801325994403888648028, -110⟩, hi := ⟨8726243801325994403888648030, -110⟩, le := by decide +kernel }, im := { lo := ⟨11198679545035025, -110⟩, hi := ⟨11198679545035027, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r4_check : scaledRisingBox cfg.precision 64 input 4 = r4 := by

  rw [scaledRisingBox, r3_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c4 : Box := { re := { lo := ⟨3328237864957963854500931708704, -110⟩, hi := ⟨3328237864957963854500931708707, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027024124129998, -110⟩, hi := ⟨1664027024124130000, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c4_check : correctionBox cfg.precision 64 input 4 = c4 := by

  rw [correctionBox, c3_check, r4_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r5 : Box := { re := { lo := ⟨805499427814707175743567337, -110⟩, hi := ⟨805499427814707175743567339, -110⟩, le := by decide +kernel }, im := { lo := ⟨1167974170331324, -110⟩, hi := ⟨1167974170331326, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r5_check : scaledRisingBox cfg.precision 64 input 5 = r5 := by

  rw [scaledRisingBox, r4_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c5 : Box := { re := { lo := ⟨3328237891594849694934370060012, -110⟩, hi := ⟨3328237891594849694934370060016, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062747614466, -110⟩, hi := ⟨1664027062747614469, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c5_check : correctionBox cfg.precision 64 input 5 = c5 := by

  rw [correctionBox, c4_check, r5_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r6 : Box := { re := { lo := ⟨86746092226199234310845695, -110⟩, hi := ⟨86746092226199234310845697, -110⟩, le := by decide +kernel }, im := { lo := ⟨138174132617445, -110⟩, hi := ⟨138174132617447, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r6_check : scaledRisingBox cfg.precision 64 input 6 = r6 := by

  rw [scaledRisingBox, r5_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c6 : Box := { re := { lo := ⟨3328237891594849694934370060012, -110⟩, hi := ⟨3328237891594849694934370060016, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062747614466, -110⟩, hi := ⟨1664027062747614469, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c6_check : correctionBox cfg.precision 64 input 6 = c6 := by

  rw [correctionBox, c5_check, r6_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r7 : Box := { re := { lo := ⟨10676442120147598069027159, -110⟩, hi := ⟨10676442120147598069027161, -110⟩, le := by decide +kernel }, im := { lo := ⟨18340602356395, -110⟩, hi := ⟨18340602356398, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r7_check : scaledRisingBox cfg.precision 64 input 7 = r7 := by

  rw [scaledRisingBox, r6_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c7 : Box := { re := { lo := ⟨3328237891586023271223930577481, -110⟩, hi := ⟨3328237891586023271223930577486, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732451930, -110⟩, hi := ⟨1664027062732451934, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c7_check : correctionBox cfg.precision 64 input 7 = c7 := by

  rw [correctionBox, c6_check, r7_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r8 : Box := { re := { lo := ⟨1478276601251205886480682, -110⟩, hi := ⟨1478276601251205886480684, -110⟩, le := by decide +kernel }, im := { lo := ⟨2703720974271, -110⟩, hi := ⟨2703720974274, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r8_check : scaledRisingBox cfg.precision 64 input 8 = r8 := by

  rw [scaledRisingBox, r7_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c8 : Box := { re := { lo := ⟨3328237891586023271223930577481, -110⟩, hi := ⟨3328237891586023271223930577486, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732451930, -110⟩, hi := ⟨1664027062732451934, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c8_check : correctionBox cfg.precision 64 input 8 = c8 := by

  rw [correctionBox, c7_check, r8_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r9 : Box := { re := { lo := ⟨227427169423262444073950, -110⟩, hi := ⟨227427169423262444073952, -110⟩, le := by decide +kernel }, im := { lo := ⟨438699789906, -110⟩, hi := ⟨438699789909, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r9_check : scaledRisingBox cfg.precision 64 input 9 = r9 := by

  rw [scaledRisingBox, r8_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c9 : Box := { re := { lo := ⟨3328237891586028019165679065637, -110⟩, hi := ⟨3328237891586028019165679065643, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461088, -110⟩, hi := ⟨1664027062732461093, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c9_check : correctionBox cfg.precision 64 input 9 = c9 := by

  rw [correctionBox, c8_check, r9_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r10 : Box := { re := { lo := ⟨38487674825475182843282, -110⟩, hi := ⟨38487674825475182843285, -110⟩, le := by decide +kernel }, im := { lo := ⟨77740382436, -110⟩, hi := ⟨77740382438, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r10_check : scaledRisingBox cfg.precision 64 input 10 = r10 := by

  rw [scaledRisingBox, r9_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c10 : Box := { re := { lo := ⟨3328237891586028019165679065637, -110⟩, hi := ⟨3328237891586028019165679065643, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461088, -110⟩, hi := ⟨1664027062732461093, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c10_check : correctionBox cfg.precision 64 input 10 = c10 := by

  rw [correctionBox, c9_check, r10_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r11 : Box := { re := { lo := ⟨7105416890856956832604, -110⟩, hi := ⟨7105416890856956832607, -110⟩, le := by decide +kernel }, im := { lo := ⟨14944188677, -110⟩, hi := ⟨14944188679, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r11_check : scaledRisingBox cfg.precision 64 input 11 = r11 := by

  rw [scaledRisingBox, r10_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c11 : Box := { re := { lo := ⟨3328237891586028015411041679044, -110⟩, hi := ⟨3328237891586028015411041679051, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461080, -110⟩, hi := ⟨1664027062732461086, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c11_check : correctionBox cfg.precision 64 input 11 = c11 := by

  rw [correctionBox, c10_check, r11_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r12 : Box := { re := { lo := ⟨1421083378171391366519, -110⟩, hi := ⟨1421083378171391366522, -110⟩, le := by decide +kernel }, im := { lo := ⟨3098151841, -110⟩, hi := ⟨3098151843, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r12_check : scaledRisingBox cfg.precision 64 input 12 = r12 := by

  rw [scaledRisingBox, r11_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c12 : Box := { re := { lo := ⟨3328237891586028015411041679044, -110⟩, hi := ⟨3328237891586028015411041679051, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461080, -110⟩, hi := ⟨1664027062732461086, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c12_check : correctionBox cfg.precision 64 input 12 = c12 := by

  rw [correctionBox, c11_check, r12_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r13 : Box := { re := { lo := ⟨306079496836915063556, -110⟩, hi := ⟨306079496836915063559, -110⟩, le := by decide +kernel }, im := { lo := ⟨689157063, -110⟩, hi := ⟨689157066, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r13_check : scaledRisingBox cfg.precision 64 input 13 = r13 := by

  rw [scaledRisingBox, r12_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c13 : Box := { re := { lo := ⟨3328237891586028015415137799091, -110⟩, hi := ⟨3328237891586028015415137799099, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461080, -110⟩, hi := ⟨1664027062732461087, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c13_check : correctionBox cfg.precision 64 input 13 = c13 := by

  rw [correctionBox, c12_check, r13_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r14 : Box := { re := { lo := ⟨70633730039288091588, -110⟩, hi := ⟨70633730039288091591, -110⟩, le := by decide +kernel }, im := { lo := ⟨163745160, -110⟩, hi := ⟨163745163, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r14_check : scaledRisingBox cfg.precision 64 input 14 = r14 := by

  rw [scaledRisingBox, r13_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c14 : Box := { re := { lo := ⟨3328237891586028015415137799091, -110⟩, hi := ⟨3328237891586028015415137799099, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461080, -110⟩, hi := ⟨1664027062732461087, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c14_check : correctionBox cfg.precision 64 input 14 = c14 := by

  rw [correctionBox, c13_check, r14_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r15 : Box := { re := { lo := ⟨17386764317363222543, -110⟩, hi := ⟨17386764317363222546, -110⟩, le := by decide +kernel }, im := { lo := ⟨41393172, -110⟩, hi := ⟨41393175, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r15_check : scaledRisingBox cfg.precision 64 input 15 = r15 := by

  rw [scaledRisingBox, r14_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c15 : Box := { re := { lo := ⟨3328237891586028015415131905533, -110⟩, hi := ⟨3328237891586028015415131905542, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461079, -110⟩, hi := ⟨1664027062732461087, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c15_check : correctionBox cfg.precision 64 input 15 = c15 := by

  rw [correctionBox, c14_check, r15_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r16 : Box := { re := { lo := ⟨4547307590694996664, -110⟩, hi := ⟨4547307590694996666, -110⟩, le := by decide +kernel }, im := { lo := ⟨11093394, -110⟩, hi := ⟨11093397, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r16_check : scaledRisingBox cfg.precision 64 input 16 = r16 := by

  rw [scaledRisingBox, r15_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c16 : Box := { re := { lo := ⟨3328237891586028015415131905533, -110⟩, hi := ⟨3328237891586028015415131905542, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461079, -110⟩, hi := ⟨1664027062732461087, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c16_check : correctionBox cfg.precision 64 input 16 = c16 := by

  rw [correctionBox, c15_check, r16_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r17 : Box := { re := { lo := ⟨1259254409730922152, -110⟩, hi := ⟨1259254409730922154, -110⟩, le := by decide +kernel }, im := { lo := ⟨3141974, -110⟩, hi := ⟨3141977, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r17_check : scaledRisingBox cfg.precision 64 input 17 = r17 := by

  rw [scaledRisingBox, r16_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c17 : Box := { re := { lo := ⟨3328237891586028015415131916345, -110⟩, hi := ⟨3328237891586028015415131916355, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461079, -110⟩, hi := ⟨1664027062732461088, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c17_check : correctionBox cfg.precision 64 input 17 = c17 := by

  rw [correctionBox, c16_check, r17_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r18 : Box := { re := { lo := ⟨368089750536731089, -110⟩, hi := ⟨368089750536731092, -110⟩, le := by decide +kernel }, im := { lo := ⟨937796, -110⟩, hi := ⟨937799, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r18_check : scaledRisingBox cfg.precision 64 input 18 = r18 := by

  rw [scaledRisingBox, r17_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c18 : Box := { re := { lo := ⟨3328237891586028015415131916345, -110⟩, hi := ⟨3328237891586028015415131916355, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461079, -110⟩, hi := ⟨1664027062732461088, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c18_check : correctionBox cfg.precision 64 input 18 = c18 := by

  rw [correctionBox, c17_check, r18_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def r19 : Box := { re := { lo := ⟨113258384780532641, -110⟩, hi := ⟨113258384780532644, -110⟩, le := by decide +kernel }, im := { lo := ⟨294214, -110⟩, hi := ⟨294217, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem r19_check : scaledRisingBox cfg.precision 64 input 19 = r19 := by

  rw [scaledRisingBox, r18_check]
  apply box_ext
  decide +kernel

/-- Exact finite interval witness, checked by the following recurrence. -/
private def c19 : Box := { re := { lo := ⟨3328237891586028015415131916320, -110⟩, hi := ⟨3328237891586028015415131916331, -110⟩, le := by decide +kernel }, im := { lo := ⟨1664027062732461078, -110⟩, hi := ⟨1664027062732461088, -110⟩, le := by decide +kernel } }

/-- Kernel verification of one exact recurrence step. -/
private theorem c19_check : correctionBox cfg.precision 64 input 19 = c19 := by

  rw [correctionBox, c18_check, r19_check]
  apply box_ext
  decide +kernel


/-- Exact outward rectangle after the first 0 Dirichlet terms. -/
private def p0 : Box := { re := { lo := ⟨0, -110⟩, hi := ⟨0, -110⟩, le := by decide +kernel }, im := { lo := ⟨0, -110⟩, hi := ⟨0, -110⟩, le := by decide +kernel } }
/-- The original prefix equals its exact checked block endpoint. -/
private theorem p0_check : prefixTwo 0 = .ok p0 := by
  apply eq_of_sameResult
  decide +kernel

/-- Exact outward rectangle after the first 8 Dirichlet terms. -/
private def p8 : Box := { re := { lo := ⟨1982707180764261600701924810132707, -110⟩, hi := ⟨1982707180764261600701924810132718, -110⟩, le := by decide +kernel }, im := { lo := ⟨-737761211943340445899, -110⟩, hi := ⟨-737761211414967271661, -110⟩, le := by decide +kernel } }
/-- The original prefix equals its exact checked block endpoint. -/
private theorem p8_check : prefixTwo 8 = .ok p8 := by
  rw [prefix_add 0 8, p0_check]
  apply eq_of_sameResult
  decide +kernel

/-- Exact outward rectangle after the first 16 Dirichlet terms. -/
private def p16 : Box := { re := { lo := ⟨2056599382109237650755012035758984, -110⟩, hi := ⟨2056599382109237650755012035759010, -110⟩, le := by decide +kernel }, im := { lo := ⟨-917847837016144669853, -110⟩, hi := ⟨-917847836357186276502, -110⟩, le := by decide +kernel } }
/-- The original prefix equals its exact checked block endpoint. -/
private theorem p16_check : prefixTwo 16 = .ok p16 := by
  rw [prefix_add 8 8, p8_check]
  apply eq_of_sameResult
  decide +kernel

/-- Exact outward rectangle after the first 24 Dirichlet terms. -/
private def p24 : Box := { re := { lo := ⟨2082271227291937296042332373256687, -110⟩, hi := ⟨2082271227291937296042332373256729, -110⟩, le := by decide +kernel }, im := { lo := ⟨-994570349120401328580, -110⟩, hi := ⟨-994570348402542002461, -110⟩, le := by decide +kernel } }
/-- The original prefix equals its exact checked block endpoint. -/
private theorem p24_check : prefixTwo 24 = .ok p24 := by
  rw [prefix_add 16 8, p16_check]
  apply eq_of_sameResult
  decide +kernel

/-- Exact outward rectangle after the first 32 Dirichlet terms. -/
private def p32 : Box := { re := { lo := ⟨2095308901982798256855748167330923, -110⟩, hi := ⟨2095308901982798256855748167330980, -110⟩, le := by decide +kernel }, im := { lo := ⟨-1038032538090746327483, -110⟩, hi := ⟨-1038032537341766288977, -110⟩, le := by decide +kernel } }
/-- The original prefix equals its exact checked block endpoint. -/
private theorem p32_check : prefixTwo 32 = .ok p32 := by
  rw [prefix_add 24 8, p24_check]
  apply eq_of_sameResult
  decide +kernel

/-- Exact outward rectangle after the first 40 Dirichlet terms. -/
private def p40 : Box := { re := { lo := ⟨2103196909795232547294456431207734, -110⟩, hi := ⟨2103196909795232547294456431207807, -110⟩, le := by decide +kernel }, im := { lo := ⟨-1066329985090311793815, -110⟩, hi := ⟨-1066329984318709169831, -110⟩, le := by decide +kernel } }
/-- The original prefix equals its exact checked block endpoint. -/
private theorem p40_check : prefixTwo 40 = .ok p40 := by
  rw [prefix_add 32 8, p32_check]
  apply eq_of_sameResult
  decide +kernel

/-- Exact outward rectangle after the first 48 Dirichlet terms. -/
private def p48 : Box := { re := { lo := ⟨2108483028195590782586423220314641, -110⟩, hi := ⟨2108483028195590782586423220314730, -110⟩, le := by decide +kernel }, im := { lo := ⟨-1086358212127767542670, -110⟩, hi := ⟨-1086358211341004470323, -110⟩, le := by decide +kernel } }
/-- The original prefix equals its exact checked block endpoint. -/
private theorem p48_check : prefixTwo 48 = .ok p48 := by
  rw [prefix_add 40 8, p40_check]
  apply eq_of_sameResult
  decide +kernel

/-- Exact outward rectangle after the first 56 Dirichlet terms. -/
private def p56 : Box := { re := { lo := ⟨2112272331775423194940042951549548, -110⟩, hi := ⟨2112272331775423194940042951549653, -110⟩, le := by decide +kernel }, im := { lo := ⟨-1101348838852752345603, -110⟩, hi := ⟨-1101348838055115052900, -110⟩, le := by decide +kernel } }
/-- The original prefix equals its exact checked block endpoint. -/
private theorem p56_check : prefixTwo 56 = .ok p56 := by
  rw [prefix_add 48 8, p48_check]
  apply eq_of_sameResult
  decide +kernel

/-- Exact outward rectangle after the first 64 Dirichlet terms. -/
private def p64 : Box := { re := { lo := ⟨2115121718416548905811818912180016, -110⟩, hi := ⟨2115121718416548905811818912180136, -110⟩, le := by decide +kernel }, im := { lo := ⟨-1113028616298712949290, -110⟩, hi := ⟨-1113028615492416245274, -110⟩, le := by decide +kernel } }
/-- The original prefix equals its exact checked block endpoint. -/
private theorem p64_check : prefixTwo 64 = .ok p64 := by
  rw [prefix_add 56 8, p56_check]
  apply eq_of_sameResult
  decide +kernel

/-- Exact outward rectangle for the shared endpoint power. -/
private def q65 : Box := { re := { lo := ⟨307236500505019386303576987573, -110⟩, hi := ⟨307236500505019386303576987575, -110⟩, le := by decide +kernel }, im := { lo := ⟨-1282524137065444364, -110⟩, hi := ⟨-1282524136008069549, -110⟩, le := by decide +kernel } }
/-- Kernel verification of the original shared endpoint power. -/
private theorem q65_check : power 65 = .ok q65 := by
  apply eq_of_sameResult
  decide +kernel

/-- Kernel-checked finite sample, using proved exact intermediate values. -/
private theorem checked : check = true := by
  unfold check value
  rw [p64_check, q65_check, c19_check]
  decide +kernel

noncomputable section
/-- Exact complex sample used by the analytic derivative estimate. -/
def point : ℂ := 2+(h : ℂ)*Complex.I
/-- The sample point agrees with the explicit complex rational displacement. -/
theorem point_eq : point = 2+(1/10^12 : ℂ)*Complex.I := by
  norm_num [point, h]

/-- The dyadic precision has the required sign. -/
private lemma hp : cfg.precision ≤ 0 := by decide
/-- Exact real rational values lie in their outward rectangles. -/
private lemma rat_mem (q : ℚ) : Mem (q : ℂ) (rational cfg.precision q 0) := by
  simpa only [Rat.cast_zero, zero_mul, add_zero] using mem_rational hp q 0
/-- The actual sample point is contained in the input rectangle. -/
private lemma input_mem : Mem point input := mem_rational hp 2 h

/-- A successful amplitude/phase evaluation encloses the literal power. -/
private lemma power_mem {n : ℕ} (hn : 0 < n) {B : Box} (hh : power n = .ok B) :
    Mem ((n : ℂ)^(-point)) B := by
  cases he : natPower cfg n (rational cfg.precision 0 (-h)) with
  | error err => simp [power, he] at hh
  | ok P =>
    simp only [power, he, Except.ok.injEq] at hh
    subst B
    have he' := mem_natPower hp hn (mem_rational hp 0 (-h)) he
    have hm := mem_mul (rat_mem (1/(n:ℚ)^2)) he' cfg.precision
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hc : (n : ℂ)^(-point) = (1/(n : ℂ)^2)*(n : ℂ)^(-(h : ℂ)*Complex.I) := by
      rw [show -point=-(2 : ℂ)+(-(h : ℂ)*Complex.I) by dsimp [point]; ring,
        Complex.cpow_add _ _ hn0]
      norm_num [Complex.cpow_neg, one_div]
    rw [hc]
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_zero, zero_mul, add_zero, Rat.cast_neg, zero_add] using hm

/-- Every successful prefix evaluation encloses the full finite sum. -/
private lemma prefix_mem (N : ℕ) {B : Box} (hh : prefixTwo N = .ok B) :
    Mem (ZetaEulerCell.partialSum N point) B := by
  induction N generalizing B with
  | zero =>
    simp only [prefixTwo, Except.ok.injEq] at hh
    subst B
    simpa only [ZetaEulerCell.partialSum, Finset.sum_range_zero, Rat.cast_zero] using rat_mem 0
  | succ N ih =>
    cases hP : prefixTwo N with
    | error err => simp [prefixTwo, hP] at hh
    | ok P =>
      cases hQ : power (N+1) with
      | error err => simp [prefixTwo, hP, hQ] at hh
      | ok Q =>
        simp only [prefixTwo, hP, hQ, Except.ok.injEq] at hh
        subst B
        have hq := power_mem (Nat.succ_pos N) hQ
        simpa only [ZetaEulerCell.partialSum, Finset.sum_range_succ, Nat.cast_succ,
          Nat.cast_add, Nat.cast_one] using mem_add (ih hP) hq cfg.precision

/-- The interval evaluation retains the entire finite approximation. -/
private lemma value_mem {B : Box} (hh : value = .ok B) :
    Mem (ZetaEulerMaclaurin.approximation 64 point 18) B := by
  cases hP : prefixTwo 64 with
  | error err => simp [value, hP] at hh
  | ok P =>
    cases hQ : power 65 with
    | error err => simp [value, hP, hQ] at hh
    | ok Q =>
      cases hU : inv cfg (add cfg.precision input (rational cfg.precision (-1) 0)) with
      | error err => simp [value, hP, hQ, hU] at hh
      | ok U =>
        simp only [value, hP, hQ, hU, Except.ok.injEq] at hh
        subst B
        have hu : Mem (point-1)⁻¹ U := mem_inv hp
          (by simpa [sub_eq_add_neg] using mem_add input_mem (rat_mem (-1)) cfg.precision) hU
        have hq := power_mem (by norm_num : 0 < (65 : ℕ)) hQ
        have ht := mem_add (prefix_mem 64 hP)
          (mem_mul hq
            (mem_add
              (mem_add (mem_mul (rat_mem 65) hu cfg.precision) (rat_mem (1/2)) cfg.precision)
              (mem_correctionBox hp input_mem 64 19) cfg.precision) cfg.precision) cfg.precision
        rw [approximation_factored]
        norm_num [div_eq_mul_inv] at *
        exact ht

/-- The actual finite approximation has this strict imaginary lower bound. -/
theorem approximation_im_lower :
    (-9375482548/10^22 : ℝ) < (ZetaEulerMaclaurin.approximation 64 point 18).im := by
  have hh := checked
  cases he : value with
  | error err => simp [check, he] at hh
  | ok B =>
    have hb : (-9375482548/10^22 : ℚ) < B.im.lo.toRat := by simpa [check, he] using hh
    have hr : (-9375482548/10^22 : ℝ) < B.im.lo.toRat := by exact_mod_cast hb
    exact hr.trans_le (value_mem he).2.1
end
end RiemannGaussian.RosserSchoenfeldZetaTwoSample
