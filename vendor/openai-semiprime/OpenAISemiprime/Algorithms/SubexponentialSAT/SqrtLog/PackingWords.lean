import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.PackingVariance
import OpenAISemiprime.Algorithms.SubexponentialSAT.MulticolorTypes

namespace OAI.Algorithms

/-! Actual shared-head/shared-factor words on an arbitrary finite incidence set. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes

noncomputable section

section Evaluation
variable {J W : Type*} [Fintype J] [DecidableEq J] [Fintype W] [Nonempty W]

def singletonRead (j : J) : Unit ↪ J := ⟨fun _ => j, fun _ _ _ => Subsingleton.elim _ _⟩

theorem mean_eval (j : J) (F : W → ℚ) :
    mean uniformWeight (fun ω : J → W => F (ω j)) = mean uniformWeight F := by
  calc
    _ = mean uniformWeight (fun ξ : Unit → W => F (ξ ())) :=
      SubexponentialSAT.TypeDistribution.mean_restrict (singletonRead j) _
    _ = _ := SubexponentialSAT.TypeDistribution.mean_equiv (Equiv.funUnique Unit W) F

theorem mean_eval_mul {j k : J} (h : j ≠ k) (F G : W → ℚ) :
    mean uniformWeight (fun ω : J → W => F (ω j) * G (ω k)) =
      mean uniformWeight F * mean uniformWeight G := by
  calc
    _ = mean uniformWeight (fun ξ : Unit → W => F (ξ ())) *
        mean uniformWeight (fun ξ : Unit → W => G (ξ ())) :=
      SubexponentialSAT.TypeDistribution.mean_restrict_mul (singletonRead j) (singletonRead k)
        (fun _ _ => h) _ _
    _ = _ := congrArg₂ (· * ·)
      (SubexponentialSAT.TypeDistribution.mean_equiv (Equiv.funUnique Unit W) F)
      (SubexponentialSAT.TypeDistribution.mean_equiv (Equiv.funUnique Unit W) G)
end Evaluation

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

abbrev WordAssignment (V E : Type*) (r Q : ℕ) := (V ⊕ E) → Word r Q

def incidenceReads (i : I) : Bool ↪ (V ⊕ E) where
  toFun b := if b then .inr (factor i) else .inl (ivar i)
  inj' := by intro b c h; cases b <;> cases c <;> simp_all

def twoWordEquiv (r Q : ℕ) : (Bool → Word r Q) ≃ UniversalType r Q 1 where
  toFun f := ⟨f false, fun _ => f true⟩
  invFun u b := if b then u.slot 0 else u.head
  left_inv f := by funext b; cases b <;> rfl
  right_inv u := by
    apply UniversalType.ext
    · rfl
    · funext i
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl

def incidenceType (ω : WordAssignment V E r Q) (i : I) : UniversalType r Q 1 :=
  ⟨ω (.inl (ivar i)), fun _ => ω (.inr (factor i))⟩

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
@[simp] theorem incidenceType_head (ω : WordAssignment V E r Q) (i : I) :
    (incidenceType ivar factor ω i).head = ω (.inl (ivar i)) := rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
@[simp] theorem incidenceType_slot (ω : WordAssignment V E r Q) (i : I) (j : Fin 1) :
    (incidenceType ivar factor ω i).slot j = ω (.inr (factor i)) := rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] [DecidableEq V] [DecidableEq E] in
theorem incidenceType_eq (ω : WordAssignment V E r Q) (i : I) :
    incidenceType ivar factor ω i =
      twoWordEquiv r Q (fun b => ω (incidenceReads ivar factor i b)) := by
  rfl

def dependencySet (i : I) : Finset I :=
  Finset.univ.filter fun j => ivar j = ivar i ∨ factor j = factor i

omit [Fintype V] [Fintype E] [DecidableEq I] in
@[simp] theorem mem_dependencySet (i j : I) :
    j ∈ dependencySet ivar factor i ↔
      ivar j = ivar i ∨ factor j = factor i := by simp [dependencySet]

omit [Fintype V] [Fintype E] in
theorem dependencySet_card_le (B a : ℕ)
    (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
    (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a) (i : I) :
    (dependencySet ivar factor i).card ≤ B + a - 1 := by
  let X := Finset.univ.filter fun j => ivar j = ivar i
  let Y := Finset.univ.filter fun j => factor j = factor i
  have heq : dependencySet ivar factor i = X ∪ Y := by
    ext j
    simp [dependencySet, X, Y]
  have hi : i ∈ X ∩ Y := by simp [X, Y]
  have hpos : 1 ≤ (X ∩ Y).card := Finset.card_pos.mpr ⟨i, hi⟩
  have hc := Finset.card_union_add_card_inter X Y
  have hx : X.card ≤ B := hB (ivar i)
  have hy : Y.card ≤ a := ha (factor i)
  rw [heq]
  omega

variable [NeZero r]

omit [Fintype I] [DecidableEq I] in
theorem mean_incidenceType (i : I) (F : UniversalType r Q 1 → ℚ) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      F (incidenceType ivar factor ω i)) = mean uniformWeight F := by
  simp_rw [incidenceType_eq]
  exact (SubexponentialSAT.TypeDistribution.mean_restrict (incidenceReads ivar factor i) _).trans
    (SubexponentialSAT.TypeDistribution.mean_equiv (twoWordEquiv r Q) F)

omit [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceReads_disjoint {i j : I} (h : j ∉ dependencySet ivar factor i) :
    ∀ b c, incidenceReads ivar factor i b ≠ incidenceReads ivar factor j c := by
  have hh : ivar j ≠ ivar i ∧ factor j ≠ factor i := by
    simpa only [mem_dependencySet, not_or] using h
  intro b c
  cases b <;> cases c
  · change Sum.inl (ivar i) ≠ Sum.inl (ivar j)
    exact fun hij => (Ne.symm hh.1) (Sum.inl.inj hij)
  · change Sum.inl (ivar i) ≠ Sum.inr (factor j)
    exact Sum.inl_ne_inr
  · change Sum.inr (factor i) ≠ Sum.inl (ivar j)
    exact Sum.inr_ne_inl
  · change Sum.inr (factor i) ≠ Sum.inr (factor j)
    exact fun hij => (Ne.symm hh.2) (Sum.inr.inj hij)

omit [DecidableEq I] in
theorem mean_incidenceType_mul {i j : I} (h : j ∉ dependencySet ivar factor i)
    (F G : UniversalType r Q 1 → ℚ) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      F (incidenceType ivar factor ω i) * G (incidenceType ivar factor ω j)) =
      mean uniformWeight F * mean uniformWeight G := by
  simp_rw [incidenceType_eq]
  calc
    _ = mean uniformWeight (fun ξ => F (twoWordEquiv r Q ξ)) *
        mean uniformWeight (fun ξ => G (twoWordEquiv r Q ξ)) :=
      SubexponentialSAT.TypeDistribution.mean_restrict_mul
        (incidenceReads ivar factor i) (incidenceReads ivar factor j)
        (incidenceReads_disjoint ivar factor h) _ _
    _ = _ := congrArg₂ (· * ·)
      (SubexponentialSAT.TypeDistribution.mean_equiv (twoWordEquiv r Q) F)
      (SubexponentialSAT.TypeDistribution.mean_equiv (twoWordEquiv r Q) G)

instance nonemptyUniversal : Nonempty (UniversalType r Q 1) :=
  ⟨⟨fun _ => 0, fun _ _ => 0⟩⟩

omit [DecidableEq I] in
theorem mean_incidence_collision {i j : I} (h : j ∉ dependencySet ivar factor i) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      if incidenceType ivar factor ω i = incidenceType ivar factor ω j then (1 : ℚ) else 0) =
        1 / (Fintype.card (UniversalType r Q 1) : ℚ) := by
  apply mean_collision_of_indicators
  intro u
  exact (mean_incidenceType_mul ivar factor h
    (fun x => if x = u then (1 : ℚ) else 0)
    (fun x => if x = u then (1 : ℚ) else 0)).trans
      (by rw [SubexponentialSAT.TypeDistribution.mean_indicator])

theorem mean_incidence_energy_le (B a : ℕ)
    (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
    (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      energy (incidenceType ivar factor ω)) ≤
        ((B + a - 1 : ℕ) : ℚ) * (Fintype.card I : ℚ) := by
  exact mean_energy_le _ (dependencySet ivar factor) (B + a - 1)
    (dependencySet_card_le ivar factor B a hB ha)
    (fun _ _ h => mean_incidence_collision ivar factor h)

/-- Original-variable heads remain independent even though incidence heads repeat. -/
theorem mean_head_collision (t : Fin Q) {v w : V} (h : v ≠ w) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      if ω (.inl v) t = ω (.inl w) t then (1 : ℚ) else 0) = 1 / (r : ℚ) := by
  have h' : mean uniformWeight (fun ω : WordAssignment V E r Q =>
      if ω (.inl v) t = ω (.inl w) t then (1 : ℚ) else 0) =
        1 / (Fintype.card (Fin r) : ℚ) := by
    apply mean_collision_of_indicators
    intro g
    have hi : mean uniformWeight (fun a : Word r Q => if a t = g then (1 : ℚ) else 0) =
        1 / (Fintype.card (Fin r) : ℚ) :=
      (mean_eval t (fun x => if x = g then (1 : ℚ) else 0)).trans
        (SubexponentialSAT.TypeDistribution.mean_indicator g)
    exact (mean_eval_mul (J := V ⊕ E) (W := Word r Q)
      (j := Sum.inl v) (k := Sum.inl w) (by simpa using h)
      (fun a => if a t = g then (1 : ℚ) else 0)
      (fun a => if a t = g then (1 : ℚ) else 0)).trans (by rw [hi])
  simpa using h'

theorem mean_head_energy_le (t : Fin Q) :
    mean uniformWeight (fun ω : WordAssignment V E r Q =>
      energy (fun v => ω (.inl v) t)) ≤ (Fintype.card V : ℚ) := by
  have h := mean_energy_le
    (fun (ω : WordAssignment V E r Q) v => ω (.inl v) t)
    (fun v => {v}) 1 (by intro v; simp)
    (by
      intro v w hw
      simpa using mean_head_collision (E := E) (r := r) t (by simpa [eq_comm] using hw))
  simpa using h

/-- Joint head energy at all interpolation nodes. -/
def headEnergy (ω : WordAssignment V E r Q) : ℚ :=
  ∑ t : Fin Q, energy (fun v : V => ω (.inl v) t)

omit [Fintype E] [DecidableEq E] in
omit [DecidableEq V] [NeZero r] in
theorem headEnergy_nonneg (ω : WordAssignment V E r Q) : 0 ≤ headEnergy ω :=
  Finset.sum_nonneg fun _ _ => energy_nonneg _

theorem mean_headEnergy_le :
    mean uniformWeight (fun ω : WordAssignment V E r Q => headEnergy ω) ≤
      (Q : ℚ) * (Fintype.card V : ℚ) := by
  unfold headEnergy
  rw [mean_sum]
  calc
    _ ≤ ∑ _t : Fin Q, (Fintype.card V : ℚ) :=
      Finset.sum_le_sum fun t _ => mean_head_energy_le t
    _ = _ := by simp

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
