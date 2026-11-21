import CheckAlpogeFixedPrimeBandCorner
import RiemannGaussian.ZetaVaughanIdentity

/-! # The fourth-power sample from Möbius values through its fourth root -/

noncomputable section
namespace RiemannGaussian.AlpogeMined
open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- One Newton step for the inverse of the constant-one arithmetic function.
Products here are Dirichlet convolutions. -/
def fixedBandInverseStep (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f+f-f*f*ζ

/-- An inverse correct through U becomes correct through U². -/
theorem fixedBandInverseStep_exact {f : ArithmeticFunction ℝ} {U : ℕ}
    (hf : ∀ j ≤ U, f j = (μ j : ℝ)) {j : ℕ} (hj : j ≤ U^2) :
    fixedBandInverseStep f j = (μ j : ℝ) := by
  let m : ArithmeticFunction ℝ := μ
  have he : m-fixedBandInverseStep f=(m-f)*(m-f)*(ζ : ArithmeticFunction ℝ) := by
    have hm : m*(ζ : ArithmeticFunction ℝ)=1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
    calc
      _ = m*(m*ζ)-f*(m*ζ)-f*(m*ζ)+f*f*ζ := by rw [hm]; dsimp only [fixedBandInverseStep]; ring
      _ = _ := by ring
  have hs {q : ℕ} (hq : q ≤ U^2) : ((m-f)*(m-f)) q = 0 := by
    rw [ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro p hp
    obtain ⟨hab,_⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    by_cases ha : p.1 ≤ U
    · change (m p.1-f p.1)*(m p.2-f p.2)=0
      rw [hf _ ha]; simp [m]
    · have hb : p.2 ≤ U := by
        by_contra! h
        have hh := Nat.mul_lt_mul_of_lt_of_lt (lt_of_not_ge ha) h
        rw [hab,← pow_two] at hh
        omega
      change (m p.1-f p.1)*(m p.2-f p.2)=0
      rw [hf _ hb]; simp [m]
  have hz : (m-fixedBandInverseStep f) j=0 := by
    rw [he,ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro p hp
    obtain ⟨hab,hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hdiv : p.1 ∣ j := ⟨p.2,hab.symm⟩
    rw [hs ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv).trans hj),zero_mul]
  exact (sub_eq_zero.mp (show m j-fixedBandInverseStep f j=0 from hz)).symm

/-- A quartic expression for a quadratic form truncated at any square s². -/
def fixedBandQuarticAt (N s : ℕ) : ℝ :=
  let f := fixedBandInverseStep (ZetaVaughanReduction.head s μ)
  ∑ a ∈ Ioc 0 (s^2), ∑ b ∈ Ioc 0 (s^2), f a*f b*fixedBandProductEntry N a b

theorem fixedBandQuarticAt_eq (N s : ℕ) :
    fixedBandQuarticAt N s = fixedBandQuadratic N (s^2) := by
  have hf {j : ℕ} (hj : j ≤ s^2) :
      fixedBandInverseStep (ZetaVaughanReduction.head s μ) j = (μ j : ℝ) :=
    fixedBandInverseStep_exact (U := s) (fun d hd => by simp [ZetaVaughanReduction.head,hd]) hj
  exact sum_congr rfl fun a ha => sum_congr rfl fun b hb => by rw [hf (mem_Ioc.mp ha).2,hf (mem_Ioc.mp hb).2]

/-- Both factors are evaluated from the same finite list through n. -/
def fixedBandShortQuadratic (n : ℕ) : ℝ := fixedBandQuarticAt (n^4) n

theorem fixedBandShortQuadratic_eq (n : ℕ) :
    fixedBandShortQuadratic n = fixedBandQuadratic (n^4) (n^2) := fixedBandQuarticAt_eq _ _

/-- Only the inputs through the shorter root occur in the trimmed window. -/
theorem fixedBandQuarticAt_trimmed_mass (m b : ℕ) :
    (∑ n ∈ Icc m b, max (-fixedBandQuarticAt (n^4) (fixedBandShortRoot n)) 0/(n:ℝ)^3) =
      fixedBandTrimmedMass m b := by
  simp only [fixedBandQuarticAt_eq,fixedBandTrimmedMass]

/-- The negative-part mass is unchanged even on individual finite windows. -/
theorem fixedBandShortQuadratic_mass (m b : ℕ) :
    (∑ n ∈ Icc m b, max (-fixedBandShortQuadratic n) 0/(n:ℝ)^3) = fixedBandQuadraticMass m b := by
  simp only [fixedBandShortQuadratic_eq,fixedBandQuadraticMass]

/-- The quartic calculation supplies the window criterion with no error. -/
theorem rh_of_fixedBandShortQuadratic_powerWindows
    (h : ∀ α : ℝ, 0 < α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ A : ℕ, ∃ m ≥ A,
      (∑ n ∈ Icc m ⌈(m:ℝ)^(1+δ)⌉₊, max (-fixedBandShortQuadratic n) 0/(n:ℝ)^3) ≤ (m:ℝ)^α) :
    RiemannHypothesis := by
  apply rh_of_fixedBandQuadraticMass_powerWindows
  simpa only [fixedBandShortQuadratic_mass] using h

end RiemannGaussian.AlpogeMined
end

open Lean Elab Command in
run_cmd do
  for decl in [``RiemannGaussian.AlpogeMined.fixedBandInverseStep_exact,
      ``RiemannGaussian.AlpogeMined.fixedBandShortQuadratic_eq,
      ``RiemannGaussian.AlpogeMined.fixedBandQuarticAt_trimmed_mass,
      ``RiemannGaussian.AlpogeMined.rh_of_fixedBandShortQuadratic_powerWindows] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
