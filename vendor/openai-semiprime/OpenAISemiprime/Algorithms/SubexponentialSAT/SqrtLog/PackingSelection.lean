import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.PackingWords

namespace OAI.Algorithms

/-! Simultaneous type packing and original-variable head balance. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes
noncomputable section

section Joint
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- A denominator-free joint score; only rational arithmetic is needed. -/
def jointScore (X Y : Ω → ℚ) (x y : ℚ) (ω : Ω) : ℚ :=
  y^2 * X ω + x^2 * Y ω

omit [Nonempty Ω] in
theorem mean_jointScore (X Y : Ω → ℚ) (x y : ℚ) :
    mean uniformWeight (jointScore X Y x y) =
      y^2 * mean uniformWeight X + x^2 * mean uniformWeight Y := by
  unfold jointScore
  simp only [mul_comm (y^2), mul_comm (x^2), mean_add, mean_mul_const]

omit [Nonempty Ω] in
theorem mean_jointScore_le (X Y : Ω → ℚ) (x y A B : ℚ)
    (hX : mean uniformWeight X ≤ A) (hY : mean uniformWeight Y ≤ B)
    (hA : 4*A ≤ x^2) (hB : 4*B ≤ y^2) :
    mean uniformWeight (jointScore X Y x y) ≤ x^2*y^2 := by
  rw [mean_jointScore]
  have hx := mul_le_mul_of_nonneg_left hX (sq_nonneg y)
  have hy := mul_le_mul_of_nonneg_left hY (sq_nonneg x)
  have ha := mul_le_mul_of_nonneg_left hA (sq_nonneg y)
  have hb := mul_le_mul_of_nonneg_left hB (sq_nonneg x)
  nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg y)]

omit [Fintype Ω] [Nonempty Ω] in
theorem jointScore_controls (X Y : Ω → ℚ) {x y : ℚ} (hx : 0 < x) (hy : 0 < y)
    (hX : ∀ ω, 0 ≤ X ω) (hY : ∀ ω, 0 ≤ Y ω) (ω : Ω)
    (h : jointScore X Y x y ω ≤ x^2*y^2) : X ω ≤ x^2 ∧ Y ω ≤ y^2 := by
  have hx2 : 0 < x^2 := sq_pos_of_pos hx
  have hy2 : 0 < y^2 := sq_pos_of_pos hy
  have h0X := mul_nonneg (le_of_lt hy2) (hX ω)
  have h0Y := mul_nonneg (le_of_lt hx2) (hY ω)
  dsimp [jointScore] at h
  constructor
  · exact le_of_mul_le_mul_left (by nlinarith) hy2
  · exact le_of_mul_le_mul_left (by nlinarith) hx2

theorem exists_joint_controls (X Y : Ω → ℚ) {x y : ℚ} (hx : 0 < x) (hy : 0 < y)
    (hX : ∀ ω, 0 ≤ X ω) (hY : ∀ ω, 0 ≤ Y ω)
    (hmean : mean uniformWeight (jointScore X Y x y) ≤ x^2*y^2) :
    ∃ ω, X ω ≤ x^2 ∧ Y ω ≤ y^2 := by
  obtain ⟨ω, hω⟩ := SubexponentialSAT.ConditionalExpectation.exists_le_of_uniform_mean_le
    (jointScore X Y x y) (x^2*y^2) (by rwa [← mean_uniformWeight])
  exact ⟨ω, jointScore_controls X Y hx hy hX hY ω hω⟩
end Joint

section Counts
variable {I U : Type*} [Fintype I] [Fintype U] [DecidableEq I] [DecidableEq U]
  [Nonempty U]

omit [DecidableEq I] [Nonempty U] in
theorem count_deviation_le (label : I → U) {x : ℚ} (hx : 0 ≤ x)
    (h : energy label ≤ x^2) (u : U) :
    |((Finset.univ.filter fun i => label i = u).card : ℚ) -
      (Fintype.card I : ℚ) / (Fintype.card U : ℚ)| ≤ x := by
  have hone : (((Finset.univ.filter fun i => label i = u).card : ℚ) -
      (Fintype.card I : ℚ) / (Fintype.card U : ℚ))^2 ≤ energy label :=
    show _ ≤ ∑ v : U, (((Finset.univ.filter fun i => label i = v).card : ℚ) -
      (Fintype.card I : ℚ) / (Fintype.card U : ℚ))^2 from
      Finset.single_le_sum
        (fun v _ => sq_nonneg (((Finset.univ.filter fun i => label i = v).card : ℚ) -
          (Fintype.card I : ℚ) / (Fintype.card U : ℚ))) (Finset.mem_univ u)
  simpa only [abs_of_nonneg hx] using sq_le_sq.mp (hone.trans h)

omit [DecidableEq I] in
theorem completeBlocks_of_energy (label : I → U) (ε : ℚ) (hε : 0 ≤ ε)
    (h : energy label ≤ (ε*(Fintype.card I : ℚ)/(Fintype.card U : ℚ))^2) :
    ∃ b, ∃ _P : SubexponentialSAT.BlockPacking.CompleteBlocks label b,
      (1-ε)*(Fintype.card I : ℚ) ≤ (b : ℚ)*Fintype.card U := by
  apply SubexponentialSAT.SubexpBlockPacking.exists_completeBlocks_of_count_lower label ε
  intro u
  have hx : 0 ≤ ε*(Fintype.card I : ℚ)/(Fintype.card U : ℚ) := by positivity
  have hh := (abs_le.mp (count_deviation_le label hx h u)).1
  rw [SubexponentialSAT.BlockPacking.count_eq_filter_card]
  have hN : (0 : ℚ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hl : (1-ε)*(Fintype.card I : ℚ)/(Fintype.card U : ℚ) ≤
      ((Finset.univ.filter fun i => label i = u).card : ℚ) := by
    calc
      _ = (Fintype.card I : ℚ)/(Fintype.card U : ℚ) -
          ε*(Fintype.card I : ℚ)/(Fintype.card U : ℚ) := by ring
      _ ≤ _ := by linarith
  simpa only [mul_comm] using (div_le_iff₀ hN).mp hl
end Counts

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

def headSupport (ω : WordAssignment V E r Q) (t : Fin Q) (g : Fin r) : Finset V :=
  Finset.univ.filter fun v => ω (.inl v) t = g

omit [Fintype E] [DecidableEq V] [DecidableEq E] [NeZero r] in
@[simp] theorem mem_headSupport (ω : WordAssignment V E r Q) (t : Fin Q)
    (g : Fin r) (v : V) :
    v ∈ headSupport ω t g ↔ ω (.inl v) t = g := by simp [headSupport]

omit [Fintype E] [DecidableEq V] [DecidableEq E] [NeZero r] in
theorem headSupport_disjoint (ω : WordAssignment V E r Q) (t : Fin Q)
    {g h : Fin r} (hgh : g ≠ h) : Disjoint (headSupport ω t g) (headSupport ω t h) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact hgh ((mem_headSupport ω t g v).mp hv |>.symm.trans ((mem_headSupport ω t h v).mp hw))

omit [Fintype E] [DecidableEq V] [DecidableEq E] [NeZero r] in
theorem headSupport_cover (ω : WordAssignment V E r Q) (t : Fin Q) (v : V) :
    ∃ g, v ∈ headSupport ω t g := ⟨ω (.inl v) t, by simp⟩

omit [Fintype E] [DecidableEq E] in
omit [DecidableEq V] [NeZero r] in
theorem head_count_upper (ω : WordAssignment V E r Q) {y : ℚ}
    (hy : 0 ≤ y) (h : headEnergy ω ≤ y^2) (t : Fin Q) (g : Fin r) :
    ((Finset.univ.filter fun v : V => ω (.inl v) t = g).card : ℚ) ≤
      (Fintype.card V : ℚ)/(r : ℚ) + y := by
  have hterm : energy (fun v : V => ω (.inl v) t) ≤ headEnergy ω :=
    Finset.single_le_sum (fun _ _ => energy_nonneg _) (Finset.mem_univ t)
  have hh := (abs_le.mp (count_deviation_le (fun v : V => ω (.inl v) t)
    hy (hterm.trans h) g)).2
  simpa only [Fintype.card_fin] using (show _ ≤ _ from (by linarith :
    ((Finset.univ.filter fun v : V => ω (.inl v) t = g).card : ℚ) ≤
      (Fintype.card V : ℚ)/(Fintype.card (Fin r) : ℚ) + y))

/-- Explicit sufficient size conditions for the two simultaneous energy budgets. -/
theorem incidence_mean_jointScore_le (ε : ℚ) (_hε : 0 < ε) (B a : ℕ)
    (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
    (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a)
    (hM : 0 < Fintype.card I) (hn : 0 < Fintype.card V)
    (hlarge : 4*((B+a : ℕ) : ℚ)*(Fintype.card (UniversalType r Q 1) : ℚ)^2 ≤
      ε^2*(Fintype.card I : ℚ))
    (hhead : 16*(Q : ℚ)*(r : ℚ)^2 ≤ (Fintype.card V : ℚ)) :
    mean uniformWeight (jointScore
      (fun ω : WordAssignment V E r Q => energy (incidenceType ivar factor ω))
      headEnergy (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))
      ((Fintype.card V : ℚ)/(2*(r : ℚ)))) ≤
      (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))^2 *
      ((Fintype.card V : ℚ)/(2*(r : ℚ)))^2 := by
  apply mean_jointScore_le _ _ _ _
    (((B+a-1 : ℕ) : ℚ)*(Fintype.card I : ℚ)) ((Q : ℚ)*Fintype.card V)
    (mean_incidence_energy_le ivar factor B a hB ha) mean_headEnergy_le
  · have hN : (0 : ℚ) < Fintype.card (UniversalType r Q 1) := by
      exact_mod_cast Fintype.card_pos
    have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast hM
    have hd : ((B+a-1 : ℕ) : ℚ) ≤ ((B+a : ℕ) : ℚ) := by
      exact_mod_cast Nat.sub_le (B+a) 1
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
    have hm := mul_le_mul_of_nonneg_right hlarge (le_of_lt hI)
    have hd' := mul_le_mul_of_nonneg_right hd (by positivity :
      0 ≤ 4*(Fintype.card I : ℚ)*(Fintype.card (UniversalType r Q 1) : ℚ)^2)
    nlinarith
  · have hr : (0 : ℚ) < r := by exact_mod_cast Nat.pos_of_neZero r
    have hv : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos (by positivity : (0 : ℚ) < 2*r))).mpr
    have hm := mul_le_mul_of_nonneg_right hhead (le_of_lt hv)
    nlinarith

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
