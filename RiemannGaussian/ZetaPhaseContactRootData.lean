/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactSystem

/-!
# Exact rational data for isolating a phase contact solution

The numerical search supplies only rational inputs: a center and a
preconditioner. All error bounds in this module are independently checked
by Lean's kernel. The Chebyshev recurrence is connected to the actual
polynomials and their exact diagonal secants. Existence of a root is a
separate analytic step, not a numerical assumption.
-/

open scoped Classical

namespace RiemannGaussian

/-- Rational center of the four-contact system, ordered as four cosines,
four masses, and the efficiency parameter. -/
def phaseContactRootCenterQ (i : Fin 9) : ℚ :=
  match i.val with
  | 0 => -6714158615484004383702210961994113130849058552897 / 25000000000000000000000000000000000000000000000000
  | 1 => -7355018436672022124417068877817845348311249242321 / 10000000000000000000000000000000000000000000000000
  | 2 => -95037371013068638789595177140919624267475794222791 / 100000000000000000000000000000000000000000000000000
  | 3 => -99989401659883664305773784519217356813201589130767 / 100000000000000000000000000000000000000000000000000
  | 4 => 2795967407798632234391946622649189704149208461447 / 25000000000000000000000000000000000000000000000000
  | 5 => 8165267537528989980510064842584223285132067297821 / 100000000000000000000000000000000000000000000000000
  | 6 => 8453699559966854107580669965203208010711378234051 / 100000000000000000000000000000000000000000000000000
  | 7 => 4726476302353277541051349404657236548393777034837 / 100000000000000000000000000000000000000000000000000
  | 8 => 880041130906440667970319966905328715032412821633 / 50000000000000000000000000000000000000000000000000
  | _ => 0

/-- A rational approximation to the inverse central linearization.
Its residuals are checked below; it is not assumed to be an inverse. -/
def phaseContactRootPreconditionerQ : Matrix (Fin 9) (Fin 9) ℚ :=
  ![![-805223043349 / 125000000000, -263245994941 / 31250000000, 19322173161 / 1000000000000, 3966897410303 / 1000000000000, 215376689501 / 100000000000, 245209241119 / 1000000000000, 36983078481 / 500000000000, 8814331773 / 500000000000, 148187889 / 250000000000],
    ![167866978481 / 100000000000, 2195183564751 / 1000000000000, -140818887583 / 250000000000, -594092102353 / 250000000000, -1256931151479 / 1000000000000, 296309670423 / 1000000000000, 16970765663 / 40000000000, 35307363101 / 200000000000, 1786368073 / 200000000000],
    ![877115852269 / 1000000000000, 143374706621 / 125000000000, -357305023221 / 1000000000000, -502349583657 / 500000000000, -73053366047 / 200000000000, -5265553847 / 50000000000, 21778212043 / 1000000000000, 178326490011 / 1000000000000, 390070521 / 10000000000],
    ![-321403026729 / 1000000000000, -420296265723 / 1000000000000, -372092077 / 7812500000, 75030028139 / 1000000000000, 621693397 / 125000000000, 32615476821 / 500000000000, 7738659899 / 250000000000, -2421317833 / 100000000000, 15558598519 / 500000000000],
    ![881516773283 / 1000000000000, 1628067162849 / 1000000000000, 670379194319 / 1000000000000, -585422202969 / 1000000000000, -119912248049 / 200000000000, -6261611049 / 50000000000, -46457365647 / 1000000000000, -11956496201 / 1000000000000, -210614107 / 500000000000],
    ![-3096730020029 / 1000000000000, -3702546155847 / 1000000000000, -85258421549 / 1000000000000, 841696461187 / 500000000000, 359032887897 / 250000000000, 262500272463 / 1000000000000, -20904972047 / 250000000000, -39238981867 / 500000000000, -353484371 / 62500000000],
    ![1366087283753 / 1000000000000, 1072852031949 / 500000000000, -32393323479 / 1000000000000, -49625259297 / 100000000000, -141283265857 / 500000000000, -455250817741 / 1000000000000, 101532470107 / 500000000000, -15883869479 / 1000000000000, -37957866443 / 500000000000],
    ![33662904407 / 1000000000000, 122447981999 / 500000000000, -357800884453 / 1000000000000, -521417021537 / 1000000000000, -53658653777 / 100000000000, 63703746081 / 200000000000, -36446102049 / 500000000000, 53168509109 / 500000000000, 81993273533 / 1000000000000],
    ![184536941413 / 1000000000000, 158060517449 / 500000000000, 97463282419 / 500000000000, 40150552449 / 500000000000, 17417241859 / 1000000000000, 267982073 / 500000000000, 47741141 / 500000000000, 4672201 / 250000000000, 281249 / 500000000000]]

/-- Exact rational Chebyshev values and diagonal secants, each stored
with its successor so that evaluation uses the three-term recurrence. -/
def phaseContactJetQ (q : ℚ) : ℕ → (ℚ × ℚ) × (ℚ × ℚ)
  | 0 => ((1, q), (0, 1))
  | n + 1 => let p := phaseContactJetQ q n
    ((p.1.2, 2 * q * p.1.2 - p.1.1),
      (p.2.2, 2 * p.1.2 + 2 * q * p.2.2 - p.2.1))

/-- The rational jet evaluates the actual Chebyshev polynomials and the
same diagonal secants as the analytic contact system. -/
theorem phaseContactJetQ_cast (q : ℚ) (n : ℕ) :
    ((phaseContactJetQ q n).1.1 : ℝ) = phaseChebyshevValue n (q : ℝ) ∧
    ((phaseContactJetQ q n).1.2 : ℝ) = phaseChebyshevValue (n + 1) (q : ℝ) ∧
    ((phaseContactJetQ q n).2.1 : ℝ) = phaseChebyshevSecant (q : ℝ) (q : ℝ) n ∧
    ((phaseContactJetQ q n).2.2 : ℝ) = phaseChebyshevSecant (q : ℝ) (q : ℝ) (n + 1) := by
  induction n with
  | zero => simp [phaseContactJetQ, phaseChebyshevValue, phaseChebyshevSecant]
  | succ n ih =>
    have hv : phaseChebyshevValue (n + 2) (q : ℝ) =
        2 * (q : ℝ) * phaseChebyshevValue (n + 1) (q : ℝ) - phaseChebyshevValue n (q : ℝ) := by
      simp [phaseChebyshevValue, Polynomial.Chebyshev.T_add_two]
    simp only [phaseContactJetQ, Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat]
    refine ⟨ih.2.1, ?_, ih.2.2.2, ?_⟩
    · rw [ih.2.1, ih.1]
      exact hv.symm
    · rw [ih.2.1, ih.2.2.2, ih.2.2.1]
      rfl

/-- Rational evaluation of the residual at the proposed root center. -/
def phaseContactRootResidualQ (i : Fin 9) : ℚ :=
  let n := phaseContactFrequency i
  phaseContactRootCenterQ 8 * (if n = 0 then 1 else ((n : ℚ) + 1) / 2) -
    (if n = 0 then -4 / 13 else if n = 1 then 4 / 17 else 0) -
    ∑ j : Fin 4, phaseContactRootCenterQ (phaseContactMassCoordinate j) *
      (phaseContactJetQ (phaseContactRootCenterQ (phaseContactCosineCoordinate j)) n).1.1

/-- The exact rational matrix for the contact system's central linearization. -/
def phaseContactRootMatrixQ (i : Fin 9) : Fin 9 → ℚ :=
  let n := phaseContactFrequency i
  ![-phaseContactRootCenterQ 4 * (phaseContactJetQ (phaseContactRootCenterQ 0) n).2.1,
    -phaseContactRootCenterQ 5 * (phaseContactJetQ (phaseContactRootCenterQ 1) n).2.1,
    -phaseContactRootCenterQ 6 * (phaseContactJetQ (phaseContactRootCenterQ 2) n).2.1,
    -phaseContactRootCenterQ 7 * (phaseContactJetQ (phaseContactRootCenterQ 3) n).2.1,
    -(phaseContactJetQ (phaseContactRootCenterQ 0) n).1.1,
    -(phaseContactJetQ (phaseContactRootCenterQ 1) n).1.1,
    -(phaseContactJetQ (phaseContactRootCenterQ 2) n).1.1,
    -(phaseContactJetQ (phaseContactRootCenterQ 3) n).1.1,
    (if n = 0 then 1 else ((n : ℚ) + 1) / 2)]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- Exact evaluation proves that the proposed center solves each contact
equation with error at most `10⁻⁴⁰`. -/
theorem abs_phaseContactRootResidualQ_le (i : Fin 9) :
    |phaseContactRootResidualQ i| ≤ (1 / 10 ^ 40 : ℚ) := by
  fin_cases i <;>
    norm_num [phaseContactRootResidualQ, phaseContactJetQ, phaseContactRootCenterQ,
      phaseContactFrequency, phaseContactMassCoordinate, phaseContactCosineCoordinate,
      Fin.sum_univ_succ]

/-- The entire proposed center lies strictly inside the unit coordinate box. -/
theorem abs_phaseContactRootCenterQ_le (i : Fin 9) :
    |phaseContactRootCenterQ i| ≤ (999999 / 1000000 : ℚ) := by
  fin_cases i <;> norm_num [phaseContactRootCenterQ]

/-- The proposed contact masses are bounded away from zero. -/
theorem phaseContactRootCenterQ_mass_pos (j : Fin 4) :
    (1 / 100 : ℚ) ≤ phaseContactRootCenterQ (phaseContactMassCoordinate j) := by
  fin_cases j <;> norm_num [phaseContactRootCenterQ, phaseContactMassCoordinate]

/-- The preconditioner has a uniformly bounded absolute row sum. -/
theorem phaseContactRootPreconditionerQ_row_le (i : Fin 9) :
    ∑ j : Fin 9, |phaseContactRootPreconditionerQ i j| ≤ (22 : ℚ) := by
  fin_cases i <;>
    norm_num [phaseContactRootPreconditionerQ, Fin.sum_univ_succ]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Multiplication on the left by the proposed inverse leaves a strictly
contractive error in the central matrix. -/
theorem phaseContactRootMatrixQ_left_error (i : Fin 9) :
    ∑ j : Fin 9, |(if i.val = j.val then 1 else 0) -
      ∑ k : Fin 9, phaseContactRootPreconditionerQ i k * phaseContactRootMatrixQ k j| ≤ (1 / 10 ^ 9 : ℚ) := by
  fin_cases i <;>
    norm_num [phaseContactRootPreconditionerQ, phaseContactRootMatrixQ, phaseContactJetQ,
      phaseContactRootCenterQ, phaseContactFrequency, Fin.sum_univ_succ]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The right residual is contractive too. This will exclude a nonzero
system residual being annihilated by the preconditioner. -/
theorem phaseContactRootMatrixQ_right_error (i : Fin 9) :
    ∑ j : Fin 9, |(if i.val = j.val then 1 else 0) -
      ∑ k : Fin 9, phaseContactRootMatrixQ i k * phaseContactRootPreconditionerQ k j| ≤ (1 / 10 ^ 9 : ℚ) := by
  fin_cases i <;>
    norm_num [phaseContactRootPreconditionerQ, phaseContactRootMatrixQ, phaseContactJetQ,
      phaseContactRootCenterQ, phaseContactFrequency, Fin.sum_univ_succ]

/-- Every coefficient in the preconditioner's final row is separated
from zero by an exact rational margin. -/
theorem phaseContactRootPreconditionerQ_last_row_pos (i : Fin 9) :
    (1 / 2000000 : ℚ) ≤ phaseContactRootPreconditionerQ 8 i := by
  rw [show (8 : Fin 9) = ⟨8, by decide⟩ from rfl]
  fin_cases i <;> norm_num [phaseContactRootPreconditionerQ]

end RiemannGaussian
