import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.PackingTheorem
import OpenAISemiprime.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

namespace OAI.Algorithms

/-! Concrete bucket scans and embeddings for the searched incidence labels. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

section General
variable {I U : Type*} [Fintype I] [Fintype U] [DecidableEq I] [DecidableEq U]
  [Nonempty U]

theorem concrete_coverage_of_energy (P : PackingData I U) (ε : ℚ) (hε : 0 ≤ ε)
    (h : energy P.label ≤ (ε*(Fintype.card I : ℚ)/(Fintype.card U : ℚ))^2) :
    (1-ε)*(Fintype.card I : ℚ) ≤ (P.blockCount : ℚ)*Fintype.card U := by
  apply P.coverage_of_count_lower ε Fintype.card_pos hε
  intro u
  have hx : 0 ≤ ε*(Fintype.card I : ℚ)/(Fintype.card U : ℚ) := by positivity
  have hh := (abs_le.mp (count_deviation_le P.label hx h u)).1
  rw [SubexponentialSAT.BlockPacking.count_eq_filter_card]
  have hN : (0 : ℚ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hl : (1-ε)*(Fintype.card I : ℚ)/(Fintype.card U : ℚ) ≤
      ((Finset.univ.filter fun i => P.label i = u).card : ℚ) := by
    calc
      _ = (Fintype.card I : ℚ)/(Fintype.card U : ℚ) -
          ε*(Fintype.card I : ℚ)/(Fintype.card U : ℚ) := by ring
      _ ≤ _ := by linarith
  simpa only [mul_comm] using (div_le_iff₀ hN).mp hl
end General

section Computed
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

/-- All lists used by bucket scans are explicit supplied enumerations. -/
def computedPacking (incidences : FiniteEnumeration I)
    (types : FiniteEnumeration (UniversalType r Q 1))
    (a₀ : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) :
    PackingData I (UniversalType r Q 1) where
  vertices := incidences
  types := types
  label := incidenceType ivar factor (computedWords ivar factor a₀ tail terms indices x y)

omit [Fintype E] [DecidableEq I] [NeZero r] in
@[simp] theorem computedPacking_head (incidences : FiniteEnumeration I)
    (types : FiniteEnumeration (UniversalType r Q 1))
    (a₀ : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) (i : I) :
    ((computedPacking ivar factor incidences types a₀ tail terms indices x y).label i).head =
      computedWords ivar factor a₀ tail terms indices x y (.inl (ivar i)) := rfl

omit [Fintype E] [DecidableEq I] [NeZero r] in
@[simp] theorem computedPacking_slot (incidences : FiniteEnumeration I)
    (types : FiniteEnumeration (UniversalType r Q 1))
    (a₀ : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) (i : I) (s : Fin 1) :
    ((computedPacking ivar factor incidences types a₀ tail terms indices x y).label i).slot s =
      computedWords ivar factor a₀ tail terms indices x y (.inr (factor i)) := rfl

theorem computedPacking_coverage (incidences : FiniteEnumeration I)
    (types : FiniteEnumeration (UniversalType r Q 1))
    (a₀ : Word r Q) (tail : List (Word r Q))
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
    (1-ε)*(Fintype.card I : ℚ) ≤
      ((computedPacking ivar factor incidences types a₀ tail terms indices x y).blockCount : ℚ)*
        Fintype.card (UniversalType r Q 1) := by
  apply concrete_coverage_of_energy _ ε (le_of_lt hε)
  exact (computedWords_energies ivar factor a₀ tail haN haC terms htN htC indices hiN hiC
    ε hε B a hB ha hM hn hlarge hhead).1

end Computed
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
