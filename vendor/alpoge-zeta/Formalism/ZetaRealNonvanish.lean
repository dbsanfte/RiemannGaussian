import Formalism.Statement

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def Pfun {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  if s = 1 then DirichletCharacter.LFunction χ 1
  else (s - 1) * riemannZeta s * DirichletCharacter.LFunction χ s

def MellinDeriv : Prop :=
  ∀ (H : ℝ → ℂ) (σs : ℝ), AEStronglyMeasurable H (volume.restrict (Ioi 1)) →
    (∀ σ : ℝ, σs < σ → IntegrableOn (fun x : ℝ => ‖H x‖ * x ^ (-σ - 1)) (Ioi 1)) →
    ∀ s : ℂ, σs < s.re →
      HasDerivAt (fun z : ℂ => ∫ x in Ioi (1:ℝ), H x * (x : ℂ) ^ (-z - 1))
        (∫ x in Ioi (1:ℝ), -(Real.log x : ℂ) * H x * (x : ℂ) ^ (-s - 1)) s

def LandauLemma : Prop :=
  ∀ (H : ℝ → ℝ) (a b : ℝ), a < b → AEStronglyMeasurable H (volume.restrict (Ioi 1)) →
    (∀ x : ℝ, 1 < x → 0 ≤ H x) →
    (∀ σ : ℝ, b < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)) →
    ∀ Φ : ℂ → ℂ, (∀ s : ℂ, b < s.re → AnalyticAt ℂ Φ s) →
    (∀ σ : ℝ, a < σ → σ ≤ b → AnalyticAt ℂ Φ σ) →
    (∀ s : ℂ, b < s.re → Φ s = ∫ x in Ioi (1:ℝ), (H x : ℂ) * (x : ℂ) ^ (-s - 1)) →
    ∀ σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1)

def MellinS : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N),
    Measurable (S χ) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |S χ x| * x ^ (-σ - 1)) (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (S χ x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => (LamF χ n : ℂ)) s / (s * (s - 1))

def LSeriesLamF : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), (∀ n : ℕ, (χ n).im = 0) →
    ∀ s : ℂ, 1 < s.re →
      LSeries (fun n => (LamF χ n : ℂ)) s =
        -deriv riemannZeta s / riemannZeta s -
          deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

def MellinElem : Prop :=
  (∀ a σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => x ^ a * x ^ (-σ - 1)) (Ioi 1)) ∧
  (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |x * Real.log x| * x ^ (-σ - 1)) (Ioi 1)) ∧
  (∀ (a : ℝ) (s : ℂ), a < s.re →
      ∫ x in Ioi (1:ℝ), ((x ^ a : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - a)) ∧
  (∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - 1) ^ 2)

def PFacts : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    Differentiable ℂ (Pfun χ) ∧
    deriv (Pfun χ) 1 = (Real.eulerMascheroniConstant : ℂ) * DirichletCharacter.LFunction χ 1 +
      deriv (DirichletCharacter.LFunction χ) 1

def LRealAxis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
    ∀ σ : ℝ, (DirichletCharacter.LFunction χ σ).im = 0 ∧
      (deriv (DirichletCharacter.LFunction χ) σ).im = 0

def ZetaRealNonvanish : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta σ ≠ 0

def CharFacts : Prop :=
  quadraticCharFour ≠ 1 ∧ quadraticCharThree ≠ 1 ∧ quadraticCharacterMod7 ≠ 1 ∧ (∀ n : ℕ, (quadraticCharFour n).im = 0) ∧
    (∀ n : ℕ, (quadraticCharThree n).im = 0) ∧ (∀ n : ℕ, (quadraticCharacterMod7 n).im = 0)

def LRealNonvanish : Prop :=
  (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction quadraticCharFour σ ≠ 0) ∧
  (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction quadraticCharThree σ ≠ 0) ∧
  (∀ σ : ℝ, 0 < σ → σ < 1 → DirichletCharacter.LFunction quadraticCharacterMod7 σ ≠ 0)

def RHofHalfPlane : Prop := (∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0) → RiemannHypothesis

def LogDerivZeroFree : Prop :=
  ∀ (P q : ℂ → ℂ) (U : Set ℂ), IsOpen U → Differentiable ℂ P → (∃ z, P z ≠ 0) →
    DifferentiableOn ℂ q U → (∀ s ∈ U, deriv P s = q s * P s) → ∀ s ∈ U, P s ≠ 0

end Formalism
