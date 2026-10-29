import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.PackingAlgorithm

namespace OAI.Algorithms

/-! End-to-end correlated incidence packing with balanced original heads. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
noncomputable section

variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

/-- The searched words meet both quantitative energy budgets. -/
theorem computedWords_energies (a₀ : Word r Q) (tail : List (Word r Q))
    (haN : (a₀::tail).Nodup) (haC : ∀ w, w ∈ a₀::tail)
    (terms : List (ScoreTerm I V Q)) (htN : terms.Nodup) (htC : ∀ z, z ∈ terms)
    (indices : List (V ⊕ E)) (hiN : indices.Nodup) (hiC : ∀ i, i ∈ indices)
    (ε : ℚ) (hε : 0 < ε) (B a : ℕ)
    (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
    (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a)
    (hM : 0 < Fintype.card I) (hn : 0 < Fintype.card V)
    (hlarge : 4*((B+a : ℕ) : ℚ)*(Fintype.card (UniversalType r Q 1) : ℚ)^2 ≤
      ε^2*(Fintype.card I : ℚ))
    (hhead : 16*(Q : ℚ)*(r : ℚ)^2 ≤ (Fintype.card V : ℚ)) :
    let x := ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ)
    let y := (Fintype.card V : ℚ)/(2*(r : ℚ))
    let ω := computedWords ivar factor a₀ tail terms indices x y
    energy (incidenceType ivar factor ω) ≤ x^2 ∧ headEnergy ω ≤ y^2 := by
  dsimp only
  have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast hM
  have hV : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn
  have hN : (0 : ℚ) < Fintype.card (UniversalType r Q 1) := by
    exact_mod_cast Fintype.card_pos
  have hr : (0 : ℚ) < r := by exact_mod_cast Nat.pos_of_neZero r
  apply jointScore_controls _ _ (by positivity) (by positivity)
    (fun ω => energy_nonneg (incidenceType ivar factor ω)) headEnergy_nonneg
  exact (computedWords_score_le_mean ivar factor a₀ tail haN haC terms htN htC
    indices hiN hiC _ _).trans
      (incidence_mean_jointScore_le ivar factor ε hε B a hB ha hM hn hlarge hhead)

/-- Main packing interface: the exact searched assignment, full blocks, coverage,
and balanced original-variable head supports. No truth table is an input. -/
theorem correlated_packing (a₀ : Word r Q) (tail : List (Word r Q))
    (haN : (a₀::tail).Nodup) (haC : ∀ w, w ∈ a₀::tail)
    (terms : List (ScoreTerm I V Q)) (htN : terms.Nodup) (htC : ∀ z, z ∈ terms)
    (indices : List (V ⊕ E)) (hiN : indices.Nodup) (hiC : ∀ i, i ∈ indices)
    (ε : ℚ) (hε : 0 < ε) (B a : ℕ)
    (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
    (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a)
    (hM : 0 < Fintype.card I) (hn : 0 < Fintype.card V)
    (hlarge : 4*((B+a : ℕ) : ℚ)*(Fintype.card (UniversalType r Q 1) : ℚ)^2 ≤
      ε^2*(Fintype.card I : ℚ))
    (hhead : 16*(Q : ℚ)*(r : ℚ)^2 ≤ (Fintype.card V : ℚ)) :
    let x := ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ)
    let y := (Fintype.card V : ℚ)/(2*(r : ℚ))
    let ω := computedWords ivar factor a₀ tail terms indices x y
    ∃ b, ∃ _P : SubexponentialSAT.BlockPacking.CompleteBlocks (incidenceType ivar factor ω) b,
      (1-ε)*(Fintype.card I : ℚ) ≤ (b : ℚ)*Fintype.card (UniversalType r Q 1) ∧
      ∀ (t : Fin Q) (g : Fin r), ((headSupport ω t g).card : ℚ) ≤
        3*(Fintype.card V : ℚ)/(2*(r : ℚ)) := by
  dsimp only
  have hgood := computedWords_energies ivar factor a₀ tail haN haC terms htN htC
    indices hiN hiC ε hε B a hB ha hM hn hlarge hhead
  dsimp only at hgood
  obtain ⟨b, P, hc⟩ := completeBlocks_of_energy _ ε (le_of_lt hε) hgood.1
  refine ⟨b, P, hc, ?_⟩
  intro t g
  have hr : (0 : ℚ) < r := by exact_mod_cast Nat.pos_of_neZero r
  have hu := head_count_upper _ (by positivity) hgood.2 t g
  change ((Finset.univ.filter fun v : V => _).card : ℚ) ≤ _
  calc
    _ ≤ (Fintype.card V : ℚ)/(r : ℚ) + (Fintype.card V : ℚ)/(2*(r : ℚ)) := hu
    _ = _ := by field_simp; ring

end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
