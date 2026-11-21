import CheckAlpogeAdelicClassProjection
import CheckAlpogePrincipalLevelCharacters
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.EqOneOfCoprimeTorsionTwoPrimes
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.PSplitT
import Formalism.LocalToGlobal.GlobalTheory.GL6.ValuationClassTranslateMem

/-! # Positive ramified rank and frame loss from level-zero adelic forms -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0
open scoped TensorProduct

/-- The finite stabilizer embeds in the rational group. Its conjugate at each
of the two auxiliary primes kills prime-to-residue-characteristic torsion. -/
theorem stabilizers_trivial_of_two_level_primes {D : D7} {u : D.what₂.Word}
    (Tf : Forms0 D u) : product_first_zeroth_parts.admS D u := by
  intro c
  let K := Tf.cls0
  let y := (K.y c).val
  let incl := bc (inclE (E := D.host.E) (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (n := Fin (D.R.N 0))
  have htriv (s : (D.mem u).C.stab 0 c) : s = 1 := by
    let γ := (K.stabI c s).val
    obtain ⟨κ, hκ, he⟩ := (K.stabI_range c _).1 ⟨s, rfl⟩
    have hconj : incl γ = (MulAut.conj y) κ := he.symm
    have hpow (j : ℕ) : κ ^ j = y⁻¹ * incl (γ ^ j) * y := by
      rw [map_pow, hconj, ← map_pow, MulAut.conj_apply]
      group
    have hcop (i : Fin 2) (j N : ℕ) (hc : Nat.Coprime N (D.host.g i))
        (hj : (γ ^ j) ^ N = 1) : γ ^ j = 1 := by
      obtain ⟨w, hw⟩ := Formalism.L2.G.Triv.exists_place (F := D.host.F) (D.host.g i) (D.host.g_prime i)
      let pr := bc (prV (E := D.host.E) w) (n := Fin (D.R.N 0))
      have hloc : pr (κ ^ j) ∈ K.lev.Uloc w := ((K.lev.U_eq _).1 (K.lev.U.pow_mem hκ j)).2 w
      have h1 := torsion_reduction_trivial K.lev Tf.gl Tf.glev0 rank_zero_le_weight
        i (D.host.g_prime i) w hw _ hloc N hc (pow_image_eq_one pr incl κ y γ hpow j N hj)
      exact pow_eq_one_of_comp_eq_one incl pr (bc (Tf.gl.phi i w hw))
        (base_change_GL_comp_injective (m := D.R.N 0) _ _ _ (RingHom.injective _)) κ y γ hpow j h1
    have horder : γ ^ orderOf s = 1 := by
      change ((K.stabI c s).val) ^ orderOf s = 1
      rw [← Subgroup.coe_pow, ← map_pow, pow_orderOf_eq_one, map_one, Subgroup.coe_one]
    have hγ := eq_one_of_coprime_torsion_two_primes γ _ _ _ (D.host.g_prime 0) (D.host.g_prime 1)
      D.host.g_ne (orderOf_pos s) horder (hcop 0) (hcop 1)
    apply K.stabI_inj c
    rw [map_one]
    exact Subtype.ext hγ
  exact ⟨fun a b => (htriv a).trans (htriv b).symm⟩

/-- For genuine level-zero forms the local class tests follow from the adelic data. -/
theorem freeLevelClasses_of_forms {D : D7} {u : D.what₂.Word} (Tf : Forms0 D u) :
    FreeLevelClasses D u := by
  refine ⟨single_mem_unramified_forms Tf.val0, ?_⟩
  intro v g hg c hc
  obtain ⟨k, hk, δ, hδ⟩ := diamond_elements_exist_all Tf 0 (Nat.zero_le _) rfl v g
  exact hg (dilation_free_on_classes Tf (stabilizers_trivial_of_two_level_primes Tf) v g k hk δ hδ c hc)

/-- A highest-weight polynomial defines a nonzero unramified form. Trivial
rational stabilizers allow its values on the class representatives to extend. -/
theorem unramified_dimension_pos_of_forms {D : D7} {u : D.what₂.Word} (Tf : Forms0 D u) :
    0 < D.duS u := by
  classical
  let K := Tf.cls0
  let W := Tf.val0
  let F : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) → ℂ :=
    Formalism.L2.Col.evV (embT D) (gramN D 0 (Nat.zero_le _)) ((D.fm u).lam 0)
    (RingHom.id ℂ) (Formalism.L2.Col.extV ℂ ((D.fm u).lam 0))
  have hF : F ≠ 0 := Formalism.L2.Col.evV_extV_ne_zero _ _ _ _ ⟨fun _ => 1, fun _ => by simp⟩
  let φ := fun (_ : (D.mem u).C.cls 0) (z : (D.mem u).C.Y 0) => F (W.eY z)
  have hφ : φ ∈ (D.mem u).A.Mu0 := by
    apply (Mu0_iff W _).2
    apply Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.adelic_function_ext K.lev (embT D)
      (embedding_conj_compat D) ((D.fm u).lam 0) K.y K.y_bij
    · intro c γ hγ hm
      obtain ⟨s, hs⟩ := ((K.stabI_range c ⟨γ, hγ⟩).2 hm)
      have := stabilizers_trivial_of_two_level_primes Tf c
      rw [Subsingleton.elim s 1, map_one] at hs
      exact (congrArg Subtype.val hs).symm
    · intro c
      change (fun z => F (W.eY (W.eY.symm z))) ∈ _
      simp only [Equiv.apply_symm_apply]
      exact Formalism.L2.Col.evV_mem_ValC (embT D) (gramN D 0 (Nat.zero_le _)) ((D.fm u).lam 0) (RingHom.id ℂ) _
  obtain ⟨c, _⟩ := K.y_bij.2 (Quotient.mk'' 1)
  have hn : (⟨φ, hφ⟩ : (D.mem u).A.Mu0) ≠ 0 := by
    intro hz
    apply hF
    funext z
    have hv := congrFun (congrFun (congrArg Subtype.val hz) c) (W.eY.symm z)
    change F (W.eY (W.eY.symm z)) = 0 at hv
    rw [W.eY.apply_symm_apply] at hv
    exact hv
  have : Nontrivial (D.mem u).A.Mu0 := ⟨⟨_, _, hn⟩⟩
  have := (D.mem u).A.Mu0_fd
  exact Module.finrank_pos

/-- Every sufficiently late record has the level-zero adelic forms on every word. -/
def HasLevelZeroForms {ε : ℝ} (Fm : FamP ε) : Prop :=
  ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, Nonempty (Forms0 (Fm.D x i) u)

/-- Level-zero forms on each word suffice for the positive division rank and
the ramified dimension bound used by the global frame estimate. -/
theorem principal_family_rank_and_share_of_forms {ε : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hTu : TuSize Fm)
    (hforms : HasLevelZeroForms Fm) :
    J.MuRank Fm ∧ ∃ b : ℝ, ∀ x ≥ b, ∀ i : Fm.Ix x, ∃ de : ℝ,
      0 ≤ de ∧ Real.sqrt de ≤ Real.exp (-(x ^ (ε/8))) ∧ ∀ u,
        ((Fm.D x i).duS u : ℝ) - (((Fm.D x i).mem u).A.du : ℝ) ≤ de * ((Fm.D x i).duS u : ℝ) := by
  obtain ⟨a, ha⟩ := hforms
  have hN : ∀ x ≥ a, ∀ (i : Fm.Ix x) u, LocalNormRankBound (Fm.D x i) u :=
    fun x hx i u => localNormRankBound_of_free_classes _ u
      ((ha x hx i u).elim freeLevelClasses_of_forms)
  obtain ⟨b, hb⟩ := principal_ramified_share_of_local_norms Fm hε hTu ⟨a, hN⟩
  refine ⟨principal_family_muRank_of_positive_dimension Fm hε hTu
    ⟨a, fun x hx i u => (ha x hx i u).elim unramified_dimension_pos_of_forms⟩ ⟨a, hN⟩,
    b, fun x hx i => ⟨_, sq_nonneg _, ?_, hb x hx i⟩⟩
  exact (Real.sqrt_sq (Real.exp_pos _).le).le

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.principal_family_rank_and_share_of_forms
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
