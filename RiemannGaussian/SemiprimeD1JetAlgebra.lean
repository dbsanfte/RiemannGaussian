/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-! # Explicit rectangular multijet quotient algebra
The commutative ring is constructed from formal power series and an actual
coefficient-vanishing ideal. No caller-provided algebra or faithfulness oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1JetAlgebra
noncomputable section
open scoped BigOperators
variable {σ R : Type*} [CommRing R]

/-- Exact componentwise nilpotent exponent box. A zero axis makes it empty. -/
def InBox (dims : σ→ℕ) (e : σ→₀ℕ) : Prop := ∀i,e i<dims i

/-- The original rectangular coefficient-vanishing condition is an actual ideal. -/
def vanishing (dims : σ→ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {f | ∀e,InBox dims e→MvPowerSeries.coeff e f=0}
  zero_mem' := by intro e _;simp
  add_mem' := by intro f g hf hg e he;simp only [map_add,hf e he,hg e he,zero_add]
  smul_mem' := by
    classical
    intro a f hf e he
    change MvPowerSeries.coeff e (a*f)=0
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨u,v⟩ huv
    have heq : u+v=e := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
    have hv : InBox dims v := by
      intro i
      have hi:=he i
      have hei:=congrArg (fun z : σ→₀ℕ => z i) heq
      simp only [Finsupp.add_apply] at hei
      omega
    simp only [hf v hv,mul_zero]

/-- Concrete truncated multijet ring, inheriting the ideal quotient CommRing. -/
abbrev Algebra (dims : σ→ℕ) (R : Type*) [CommRing R] :=
  MvPowerSeries σ R ⧸ vanishing (R:=R) dims

/-- Concrete coefficient ring used by the acquired word backend. -/
abbrev Modular (m p : ℕ) (dims : Fin m→ℕ) := Algebra dims (ZMod (2^p))

/-- Actual quotient projection of a formal series. -/
def project (dims : σ→ℕ) : MvPowerSeries σ R→+*Algebra dims R := Ideal.Quotient.mk _

/-- Quotient membership is exactly coefficient vanishing, not a desired identity. -/
theorem mem_vanishing (dims : σ→ℕ) (f : MvPowerSeries σ R) :
    f∈vanishing dims ↔∀e,InBox dims e→MvPowerSeries.coeff e f=0 := Iff.rfl

/-- Two representatives define the same jet iff ALL below-box coefficients agree. -/
theorem project_eq_iff (dims : σ→ℕ) (f g : MvPowerSeries σ R) :
    project dims f=project dims g ↔
      ∀e,InBox dims e→MvPowerSeries.coeff e f=MvPowerSeries.coeff e g := by
  rw [project,Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  change (∀e,InBox dims e→MvPowerSeries.coeff e (f-g)=0)↔_
  simp only [map_sub,sub_eq_zero]

/-- Canonical bounded coefficient extraction from the actual quotient. -/
noncomputable def coefficient (dims : σ→ℕ) (e : σ→₀ℕ) (he : InBox dims e) :
    Algebra dims R→R :=
  Quotient.lift (fun f : MvPowerSeries σ R => MvPowerSeries.coeff e f) (by
    intro f g h
    have hm : f-g∈vanishing (R:=R) dims := (Submodule.quotientRel_def _).mp h
    have hz:=hm e he
    simpa only [map_sub,sub_eq_zero] using hz)

/-- Extraction of a supplied representative has its literal original coefficient. -/
theorem coefficient_project (dims : σ→ℕ) (e : σ→₀ℕ) (he : InBox dims e)
    (f : MvPowerSeries σ R) : coefficient dims e he (project dims f)=MvPowerSeries.coeff e f := rfl

/-- No two different coefficient vectors are collapsed by the quotient. -/
theorem ext (dims : σ→ℕ) (f g : Algebra dims R)
    (h : ∀e,(he : InBox dims e)→coefficient dims e he f=coefficient dims e he g) : f=g := by
  induction f using Quotient.inductionOn with
  | h f =>
    induction g using Quotient.inductionOn with
    | h g => exact (project_eq_iff dims f g).mpr h

/-- Explicit quotient generator for an original nilpotent axis. -/
def generator (dims : σ→ℕ) (i : σ) : Algebra dims R := project dims (MvPowerSeries.X i)

/-- The acquired axis dimension is its actual nilpotence exponent, includingzero. -/
theorem generator_pow (dims : σ→ℕ) (i : σ) : (generator (R:=R) dims i)^dims i=0 := by
  classical
  rw [generator,←map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  intro e he
  have hn : e≠Finsupp.single i (dims i) := by
    intro hz
    have hi:=he i
    rw [hz,Finsupp.single_eq_same] at hi
    omega
  simp only [MvPowerSeries.coeff_X_pow,hn,ite_false]

/-- A zero-dimensional axis gives the actual zero ring, not a malformed basis. -/
theorem project_zero_of_zero_axis (dims : σ→ℕ) (i : σ) (hi : dims i=0)
    (f : MvPowerSeries σ R) : project dims f=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  intro e he
  have h:=he i
  omega

/-- The coefficient-ring constant map is an actual unital ring homomorphism. -/
def constants (dims : σ→ℕ) : R→+*Algebra dims R := (project dims).comp MvPowerSeries.C

/-- Finite rectangular upper exponent, with zero axes filtered separately. -/
def bound [Fintype σ] (dims : σ→ℕ) : σ→₀ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => dims i-1)

/-- Literal finite monomial box; zero axes produce an empty set. -/
def box [Fintype σ] (dims : σ→ℕ) : Finset (σ→₀ℕ) := by
  classical
  exact (Finset.Iic (bound dims)).filter (InBox dims)

/-- Finite catalogue membership is exactly the rectangular exponent predicate. -/
theorem mem_box [Fintype σ] (dims : σ→ℕ) (e : σ→₀ℕ) :
    e∈box dims ↔InBox dims e := by
  classical
  unfold box
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Iic.mpr ?_,h⟩
    intro i
    change e i≤dims i-1
    have hi:=h i
    omega

/-- Original finite canonical representative, using actual bounded coefficients. -/
def normalForm [Fintype σ] (dims : σ→ℕ) (f : MvPowerSeries σ R) : MvPolynomial σ R :=
  MvPowerSeries.truncFinset R (box dims) f

/-- The finite canonical representative has all the original below-box coefficients. -/
theorem normalForm_coeff [Fintype σ] (dims : σ→ℕ) (f : MvPowerSeries σ R)
    (e : σ→₀ℕ) (he : InBox dims e) :
    (normalForm dims f).coeff e=MvPowerSeries.coeff e f :=
  MvPowerSeries.coeff_truncFinset_of_mem f ((mem_box dims e).mpr he)

/-- Every quotient element has the actual finite canonical polynomial representative. -/
theorem normalForm_project [Fintype σ] (dims : σ→ℕ) (f : MvPowerSeries σ R) :
    project dims ((normalForm dims f : MvPolynomial σ R) : MvPowerSeries σ R)=project dims f := by
  apply (project_eq_iff dims _ _).mpr
  intro e he
  simpa only [MvPolynomial.coeff_coe] using normalForm_coeff dims f e he

/-- Explicit fresh outer axis at0; every existing axis is shifted bysucc. -/
def outerDims {m : ℕ} (q : ℕ) (dims : Fin m→ℕ) : Fin (m+1)→ℕ := Fin.cases q dims

/-- The actual fresh quotient generator occupies the new indexzero. -/
def fresh {m : ℕ} (q : ℕ) (dims : Fin m→ℕ) : Algebra (outerDims q dims) R :=
  generator (outerDims q dims) 0

/-- Fresh generator nilpotence is proved from the concrete quotient, not advice. -/
theorem fresh_pow {m : ℕ} (q : ℕ) (dims : Fin m→ℕ) : (fresh (R:=R) q dims)^q=0 := by
  simpa only [fresh,outerDims,Fin.cases_zero] using
    generator_pow (R:=R) (outerDims q dims) 0

/-- The explicit embedding of all old exponent coordinates into the shifted axes. -/
def axisShift (m : ℕ) : Fin m↪Fin (m+1) := ⟨Fin.succ,Fin.succ_injective m⟩

/-- Old bounded exponent vectors stay bounded after adding a fresh outer axis. -/
theorem shifted_inBox {m : ℕ} (q : ℕ) (dims : Fin m→ℕ) (hq : 0<q)
    (e : Fin m→₀ℕ) (he : InBox dims e) :
    InBox (outerDims q dims) (Finsupp.embDomain (axisShift m) e) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hz : (Finsupp.embDomain (axisShift m) e) 0=0 := by
      apply Finsupp.embDomain_of_notMem_range
      intro h
      rcases h with ⟨j,hj⟩
      exact Fin.succ_ne_zero j hj
    simpa only [hz,outerDims,Fin.cases_zero] using hq
  · have hj := he j
    change (Finsupp.embDomain (axisShift m) e) ((axisShift m) j)<dims j
    rw [Finsupp.embDomain_apply_self]
    exact hj

/-- Same-precision variable renaming carries the actual old vanishing ideal into
the actual new ideal, so quotient extension is a genuine ring map. -/
theorem rename_mem_vanishing {m : ℕ} (q : ℕ) (dims : Fin m→ℕ)
    (f : MvPowerSeries (Fin m) R) (hf : f∈vanishing dims) :
    MvPowerSeries.rename (axisShift m) f∈vanishing (outerDims q dims) := by
  classical
  intro e he
  by_cases hx : e∈Set.range (Finsupp.mapDomain (axisShift m))
  · rcases hx with ⟨d,rfl⟩
    rw [← Finsupp.embDomain_eq_mapDomain,MvPowerSeries.coeff_embDomain_rename]
    apply hf
    intro j
    have hj:=he j.succ
    change (Finsupp.mapDomain (axisShift m) d) ((axisShift m) j)<dims j at hj
    rw [Finsupp.mapDomain_apply_of_injective (axisShift m).injective] at hj
    exact hj
  · exact MvPowerSeries.coeff_rename_eq_zero (axisShift m) f hx

/-- Explicit same-precision constant-in-new-axis embedding of the quotient rings. -/
def outerEmbedding {m : ℕ} (q : ℕ) (dims : Fin m→ℕ) :
    Algebra dims R→+*Algebra (outerDims q dims) R :=
  Ideal.Quotient.lift (vanishing (R:=R) dims)
    ((project (R:=R) (outerDims q dims)).comp (MvPowerSeries.rename (R:=R) (axisShift m)).toRingHom)
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr (rename_mem_vanishing q dims f hf))

/-- Existing series are extended by the actual variable renaming, not reevaluated. -/
theorem outerEmbedding_project {m : ℕ} (q : ℕ) (dims : Fin m→ℕ)
    (f : MvPowerSeries (Fin m) R) :
    outerEmbedding q dims (project dims f)=
      project (outerDims q dims) (MvPowerSeries.rename (axisShift m) f) := rfl

/-- All old coefficients are preserved by constant embedding in the fresh axis. -/
theorem outerEmbedding_coefficient {m : ℕ} (q : ℕ) (dims : Fin m→ℕ) (hq : 0<q)
    (e : Fin m→₀ℕ) (he : InBox dims e) (f : Algebra dims R) :
    coefficient (outerDims q dims) (Finsupp.embDomain (axisShift m) e)
      (shifted_inBox q dims hq e he) (outerEmbedding q dims f)=coefficient dims e he f := by
  induction f using Quotient.inductionOn with
  | h f =>
    change coefficient (outerDims q dims) (Finsupp.embDomain (axisShift m) e)
      (shifted_inBox q dims hq e he) (outerEmbedding q dims (project dims f))=
        coefficient dims e he (project dims f)
    rw [outerEmbedding_project,coefficient_project,coefficient_project,
      MvPowerSeries.coeff_embDomain_rename]

/-- A positive fresh axis preserves the entire old algebra, not just constants. -/
theorem outerEmbedding_injective {m : ℕ} (q : ℕ) (dims : Fin m→ℕ) (hq : 0<q) :
    Function.Injective (outerEmbedding (R:=R) q dims) := by
  intro f g hfg
  apply ext dims f g
  intro e he
  have hc:=congrArg (coefficient (outerDims q dims) (Finsupp.embDomain (axisShift m) e)
    (shifted_inBox q dims hq e he)) hfg
  rw [outerEmbedding_coefficient q dims hq e he,outerEmbedding_coefficient q dims hq e he] at hc
  exact hc

end
end RiemannGaussian.SemiprimeD1JetAlgebra
