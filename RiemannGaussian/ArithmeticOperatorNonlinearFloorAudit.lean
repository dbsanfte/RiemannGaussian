/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFloorApproximationAudit
import RiemannGaussian.ArithmeticOperatorPeriodicInverseAudit
import Mathlib.LinearAlgebra.Lagrange

/-!
# Fixed nonlinear integer floor profiles are exactly periodic codes

Every positive integer divisor row is the exact Euclidean remainder
- (N mod d)/d, including all cutoff endpoints. Arbitrary nonlinear functions
of any family of these rows, with fixed integer shifts and one fixed finite
common period, therefore introduce no new code alphabet. Conversely every
periodic code is a polynomial of ONE such row, of degree less than its period.

Complete actual Gamma evaluation of this whole class loses every actual
zero source. Coding before the actual Mobius inverse is a different word;
the existing source-bearing periodic inverse remains unpaid. No infinite
period limit, amplitude bound, arbitrary real dilation, or source-scale
signed estimate is claimed here.
-/

namespace RiemannGaussian.ArithmeticOperatorNonlinearFloorAudit
noncomputable section
open Complex Filter Topology
open scoped BigOperators Classical

/-- Literal density-balanced quotient row at every integer cutoff. -/
def quotientRow (d N : ℕ) : ℂ := ((N/d : ℕ) : ℂ)-(N : ℂ)/(d : ℂ)

/-- Integer division is retained exactly, not replaced by its density. -/
theorem quotientRow_eq_remainder {d : ℕ} (hd : 0<d) (N : ℕ) :
    quotientRow d N=-((N%d : ℕ) : ℂ)/(d : ℂ) := by
  have hdn : (d : ℂ)≠0 := by exact_mod_cast hd.ne'
  have he : (N : ℂ)=((N%d : ℕ) : ℂ)+(d : ℂ)*((N/d : ℕ) : ℂ) := by
    exact_mod_cast (Nat.mod_add_div N d).symm
  unfold quotientRow
  rw [he]
  field_simp
  ring

/-- Bridge to the existing literal floor row on EVERY real logarithmic
cutoff, including discontinuity endpoints and the entire negative-time head. -/
theorem physical_row_eq {d : ℕ} (hd : 0<d) (t : ℝ) :
    ArithmeticOperatorFloorApproximationAudit.row (-Real.log d) t=
      quotientRow d ⌊Real.exp t⌋₊ := by
  rw [ArithmeticOperatorFloorApproximationAudit.row_integer d hd t]
  have hf := Int.natCast_floor_eq_floor (Real.exp_pos t).le
  have hg : ⌊Real.exp t/(d : ℝ)⌋=((⌊Real.exp t⌋₊/d : ℕ) : ℤ) := by
    rw [Int.floor_div_natCast,←hf,Int.natCast_ediv]
  rw [hg,←hf]
  simp only [Int.cast_natCast]
  unfold quotientRow
  ring

/-- Reducing through a common period preserves every shifted endpoint. -/
theorem quotientRow_common_period {q d : ℕ} (hd : 0<d) (hdq : d∣q) (N h : ℕ) :
    quotientRow d (N%q+h)=quotientRow d (N+h) := by
  rw [quotientRow_eq_remainder hd,quotientRow_eq_remainder hd,
    Nat.add_mod,Nat.mod_mod_of_dvd N hdq,←Nat.add_mod]

/-- The exact residue code of the whole nonlinear profile, before any
norm or prime/cofactor completion. F need not be a polynomial or factor. -/
def profileCode {ι : Type*} (q : ℕ) (d shift : ι → ℕ)
    (F : (ι → ℂ) → ℂ) (a : ZMod q) : ℂ :=
  F (fun i => quotientRow (d i) (a.val+shift i))

/-- ANY fixed nonlinear functional of the native rows is one periodic
code. Correlated products, max/min selectors and all integer shifts survive. -/
theorem profile_eq_code {ι : Type*} {q : ℕ}
    (d shift : ι → ℕ) (hd : ∀ i,0<d i) (hq : ∀ i,d i∣q)
    (F : (ι → ℂ) → ℂ) (N : ℕ) :
    F (fun i => quotientRow (d i) (N+shift i))=
      profileCode q d shift F (N : ZMod q) := by
  unfold profileCode
  rw [ZMod.val_natCast]
  congr 1
  funext i
  exact (quotientRow_common_period (hd i) (hq i) N (shift i)).symm

/-- Every finite family of positive integer scales has a native finite
common period. No coprimality or prime-power deletion is required. -/
theorem exists_common_period {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (hd : ∀ i,0<d i) : ∃ q : ℕ,0<q ∧ ∀ i,d i∣q := by
  refine ⟨∏ i,d i,Finset.prod_pos (fun i _ => hd i),?_⟩
  intro i
  exact Finset.dvd_prod_of_mem d (Finset.mem_univ i)

/-- Actual divisor/cofactor Gamma rows are evaluated with the entire
nonlinear whole-label code and both original height phases retained. -/
theorem nonlinear_whole_row {ι : Type*} {q : ℕ}
    (d shift : ι → ℕ) (hd : ∀ i,0<d i) (hq : ∀ i,d i∣q)
    (F : (ι → ℂ) → ℂ) (y : ℝ) (N : ℕ) :
    ArithmeticOperatorPeriodicGammaAudit.wholeRow (profileCode q d shift F) y N=
      F (fun i => quotientRow (d i) (N+shift i))*
        SuzukiCarryCorrelation.primePhase y N*(Real.log N : ℂ) := by
  rw [ArithmeticOperatorPeriodicGammaAudit.wholeRow_eq_log,
    ←profile_eq_code d shift hd hq F N]

/-- The EXACT source gate fails for the entire nonlinear fixed-profile
class after complete Gamma evaluation, at every actual zero multiplicity. -/
theorem nonlinear_gamma_zero_source {ι : Type*} {q : ℕ} [NeZero q]
    (d shift : ι → ℕ) (F : (ι → ℂ) → ℂ) (y : ℝ) (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-(rho.1-I*y))*
      ArithmeticOperatorPeriodicGammaAudit.response (profileCode q d shift F) y s)
      (𝓝[≠] (rho.1-I*y)) (𝓝 0) :=
  ArithmeticOperatorPeriodicGammaAudit.actual_zero_source_vanishes _ y rho

/-- Density centering of the full code also kills density, and DOES NOT
restore the already lost actual-zero source. -/
theorem nonlinear_gamma_density_source {ι : Type*} {q : ℕ} [NeZero q]
    (d shift : ι → ℕ) (F : (ι → ℂ) → ℂ)
    (hmean : ∑ a : ZMod q,profileCode q d shift F a=0) :
    Tendsto (fun s : ℂ => (s-1)*ArithmeticOperatorPeriodicGammaAudit.response
      (profileCode q d shift F) 0 s) (𝓝[≠] (1 : ℂ)) (𝓝 0) :=
  ArithmeticOperatorPeriodicGammaAudit.density_source_vanishes _ hmean

/-- The distinct nodes of one native quotient row, with no continuous
residue or floor approximation. -/
def node (q : ℕ) (a : Fin q) : ℂ := -(a.val : ℂ)/(q : ℂ)

theorem node_injective {q : ℕ} [NeZero q] : Function.Injective (node q) := by
  intro a b hh
  have hqn : (q : ℂ)≠0 := by exact_mod_cast NeZero.ne q
  have hab : (a.val : ℂ)=(b.val : ℂ) := by
    exact neg_injective ((div_left_inj' hqn).mp hh)
  exact Fin.ext (Nat.cast_injective hab)

/-- Exact polynomial encoding of EVERY periodic code in a single row.
Its coefficients are unrestricted; no bounded-amplitude estimate is implied. -/
def interpolant {q : ℕ} (Phi : ZMod q → ℂ) : Polynomial ℂ :=
  Lagrange.interpolate Finset.univ (node q) (fun a : Fin q => Phi (a.val : ZMod q))

theorem interpolant_degree_lt {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ) :
    (interpolant Phi).degree<(q : WithBot ℕ) := by
  simpa only [interpolant,Finset.card_univ,Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := Finset.univ)
      (fun a : Fin q => Phi (a.val : ZMod q))
      node_injective.injOn

/-- Every integer value, including the unit and all proper powers, is
interpolated exactly. Increasing nonlinear degree adds no residue data. -/
theorem interpolant_eval {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ) (N : ℕ) :
    (interpolant Phi).eval (quotientRow q N)=Phi (N : ZMod q) := by
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  let a : Fin q := ⟨N%q,Nat.mod_lt N hq⟩
  have hr : quotientRow q N=node q a := quotientRow_eq_remainder hq N
  rw [hr]
  change Polynomial.eval (node q a) (Lagrange.interpolate Finset.univ (node q)
    (fun a : Fin q => Phi (a.val : ZMod q)))=_
  rw [Lagrange.eval_interpolate_at_node _ node_injective.injOn (Finset.mem_univ a)]
  simp [a]

/-- Residue code of the literal polynomial, used by the existing Gamma
and inverse APIs without inventing a new carrier. -/
def polynomialCode (q : ℕ) (P : Polynomial ℂ) (a : ZMod q) : ℂ :=
  P.eval (-(a.val : ℂ)/(q : ℂ))

theorem polynomialCode_nat {q : ℕ} [NeZero q] (P : Polynomial ℂ) (N : ℕ) :
    polynomialCode q P (N : ZMod q)=P.eval (quotientRow q N) := by
  rw [polynomialCode,ZMod.val_natCast,
    quotientRow_eq_remainder (Nat.pos_of_ne_zero (NeZero.ne q))]

/-- The nonlinear single-row polynomial alphabet is EXACTLY the old
periodic-code alphabet, not a new arithmetic restriction on those codes. -/
theorem polynomialCode_interpolant {q : ℕ} [NeZero q] (Phi : ZMod q → ℂ) :
    polynomialCode q (interpolant Phi)=Phi := by
  funext a
  rw [←ZMod.natCast_zmod_val a,polynomialCode_nat,interpolant_eval,
    ZMod.natCast_zmod_val]

end
end RiemannGaussian.ArithmeticOperatorNonlinearFloorAudit
