import CheckAlpogePrincipalLattice

/-! # Positive division rank from the individual level-place actions -/

namespace RiemannGaussian.AlpogeWindow
open Formalism.BasicNotions Formalism.MainNotions Classical

/-- The action of the units at one level place on the unramified space. -/
noncomputable def levelUnitAction (D : D7) (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    Representation ℂ ((D.mem u).A.Fv v)ˣ (D.mem u).A.Mu0 :=
  let A := (D.mem u).A
  Representation.subrepresentation (A.rhoT v) A.Mu0 fun g =>
    Submodule.map_le_iff_le_comap.mp (A.Mu0_stable v g)

/-- The norm image at one place has dimension at most the multiplicity of the
trivial representation for that place. The finite-group character formula computes it. -/
theorem level_norm_rank_of_character (D : D7) (u : D.what₂.Word) (v : (D.mem u).A.vT)
    (h : ∀ g : ((D.mem u).A.Fv v)ˣ, g ≠ 1 → (levelUnitAction D u v).character g = 0) :
    let A := (D.mem u).A
    (A.T - 1) * Module.finrank ℂ (LinearMap.range ((A.Nm v).domRestrict A.Mu0)) ≤ D.duS u := by
  classical
  let A := (D.mem u).A
  let G := (A.Fv v)ˣ
  let ρ := levelUnitAction D u v
  have := A.Mu0_fd
  have hnorm : (A.Nm v).domRestrict A.Mu0 = A.Mu0.subtype.comp ρ.norm := by
    ext x : 1
    change (∑ g : G, A.rhoT v g) x.val = A.Mu0.subtype ((∑ g : G, ρ g) x)
    simp only [LinearMap.sum_apply, map_sum]
    rfl
  have hrange : LinearMap.range ρ.norm ≤ ρ.invariants := by
    rintro _ ⟨x, rfl⟩ g
    exact ρ.self_norm_apply g x
  have hr : Module.finrank ℂ (LinearMap.range ((A.Nm v).domRestrict A.Mu0)) ≤
      Module.finrank ℂ ρ.invariants := by
    rw [hnorm, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective A.Mu0.subtype A.Mu0.injective_subtype _).finrank_eq.symm.le.trans
      (Submodule.finrank_mono hrange)
  have hcard : Nat.card G = A.T - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, A.card_Fv]
  have hn : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  let := invertibleOfNonzero hn
  have hav := ρ.card_inv_mul_sum_char_eq_finrank
  have he : ∑ g : G, ρ.character g = ρ.character 1 :=
    Finset.sum_eq_single 1 (fun g _ hg => h g hg) (by simp)
  rw [he, Representation.char_one, ← div_eq_inv_mul] at hav
  have heq : (A.T - 1) * Module.finrank ℂ ρ.invariants = D.duS u := by
    rw [← hcard, Nat.mul_comm]
    exact_mod_cast ((div_eq_iff hn).mp hav).symm
  exact (Nat.mul_le_mul_left _ hr).trans_eq heq

theorem principal_family_muRank_of_level_characters {ε C0 : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hC0 : 0 < C0) (hP : ChosenProviso Fm C0) (hTu : TuSize Fm)
    (h : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u v g, g ≠ 1 →
      (levelUnitAction (Fm.D x i) u v).character g = 0) : J.MuRank Fm := by
  obtain ⟨a, ha⟩ := h
  exact principal_family_muRank_of_local_norms Fm hε hC0 hP hTu
    ⟨a, fun x hx i u v => level_norm_rank_of_character _ u v (ha x hx i u v)⟩

/-- A unit moving every class has trace zero as soon as restriction of an unramified
form to one class stays in the unramified space. Fibres may have different dimensions. -/
theorem level_character_eq_zero_of_free_classes (D : D7) (u : D.what₂.Word)
    (v : (D.mem u).A.vT) (g : ((D.mem u).A.Fv v)ˣ)
    (hcut : ∀ c (φ : (D.mem u).A.Mu0), Pi.single c (φ.val c) ∈ (D.mem u).A.Mu0)
    (hfree : ∀ c, (D.fm u).dil 0 v g c ≠ c) : (levelUnitAction D u v).character g = 0 := by
  classical
  let A := (D.mem u).A
  let C := (D.mem u).C
  let U := levelUnitAction D u v g
  let P (c : C.cls 0) : Module.End ℂ A.Mu0 :=
    (((LinearMap.single ℂ (fun _ : C.cls 0 => C.Y 0 → ℂ) c).comp (LinearMap.proj c)).comp
      A.Mu0.subtype).codRestrict A.Mu0 (hcut c)
  have hPc (c : C.cls 0) (φ : A.Mu0) : (P c φ).val = Pi.single c (φ.val c) := rfl
  have htotal : ∑ c, P c = 1 := by
    ext φ : 1
    apply Subtype.ext
    rw [LinearMap.sum_apply]
    change A.Mu0.subtype (∑ c, P c φ) = φ.val
    simp only [map_sum, Submodule.subtype_apply, hPc, Finset.univ_sum_single]
  have hproj (c : C.cls 0) : P c * P c = P c := by
    ext φ : 1
    apply Subtype.ext
    change (P c (P c φ)).val = _
    simp only [hPc, Pi.single_eq_same]
  have hoff (c : C.cls 0) : P c * U * P c = 0 := by
    ext φ : 1
    apply Subtype.ext
    change (P c (U (P c φ))).val = 0
    rw [hPc]
    change (Pi.single c (A.rhoT v g (P c φ).val c) : C.cls 0 → C.Y 0 → ℂ) = 0
    rw [(D.fm u).rhoT_dil, hPc, Pi.single_eq_of_ne (hfree c), map_zero, Pi.single_zero]
  change LinearMap.trace ℂ A.Mu0 U = 0
  calc LinearMap.trace ℂ A.Mu0 U = LinearMap.trace ℂ A.Mu0 (U * ∑ c, P c) := by rw [htotal, mul_one]
       _ = ∑ c, LinearMap.trace ℂ A.Mu0 (U * P c) := by rw [Finset.mul_sum, map_sum]
       _ = 0 := Finset.sum_eq_zero fun c _ => by
         calc LinearMap.trace ℂ A.Mu0 (U * P c)
             = LinearMap.trace ℂ A.Mu0 (P c * U * P c) := by
               rw [LinearMap.trace_mul_cycle, hproj, LinearMap.trace_mul_comm]
           _ = 0 := by rw [hoff, map_zero]

/-- Two conditions on one level word. Projection to one class preserves the space,
and each nonidentity unit moves every class at its own place. -/
def FreeLevelClasses (D : D7) (u : D.what₂.Word) : Prop :=
  (∀ c (φ : (D.mem u).A.Mu0), Pi.single c (φ.val c) ∈ (D.mem u).A.Mu0) ∧
    ∀ v (g : ((D.mem u).A.Fv v)ˣ), g ≠ 1 → ∀ c, (D.fm u).dil 0 v g c ≠ c

theorem localNormRankBound_of_free_classes (D : D7) (u : D.what₂.Word) (h : FreeLevelClasses D u) :
    LocalNormRankBound D u := fun v => level_norm_rank_of_character D u v fun g hg =>
      level_character_eq_zero_of_free_classes D u v g h.1 (h.2 v g hg)

/-- The same local hypotheses give positive rank and the exponentially small dimension
loss that enters the real frame comparison. The share is uniform over the level words. -/
theorem principal_family_rank_and_share_of_free_classes {ε C0 : ℝ} (Fm : FamP ε) (hε : 0 < ε)
    (hC0 : 0 < C0) (hP : ChosenProviso Fm C0) (hTu : TuSize Fm)
    (h : ∃ a : ℝ, ∀ x ≥ a, ∀ (i : Fm.Ix x) u, FreeLevelClasses (Fm.D x i) u) :
    J.MuRank Fm ∧ ∃ b : ℝ, ∀ x ≥ b, ∀ i : Fm.Ix x, ∃ de : ℝ,
      0 ≤ de ∧ Real.sqrt de ≤ Real.exp (-(x ^ (ε/8))) ∧ ∀ u,
        ((Fm.D x i).duS u : ℝ) - (((Fm.D x i).mem u).A.du : ℝ) ≤ de * ((Fm.D x i).duS u : ℝ) := by
  obtain ⟨a, ha⟩ := h
  have hN := fun x hx i u => localNormRankBound_of_free_classes _ u (ha x hx i u)
  obtain ⟨b, hb⟩ := principal_ramified_share_of_local_norms Fm hε hTu ⟨a, hN⟩
  refine ⟨principal_family_muRank_of_local_norms Fm hε hC0 hP hTu ⟨a, hN⟩,
    b, fun x hx i => ⟨_, sq_nonneg _, ?_, hb x hx i⟩⟩
  exact (Real.sqrt_sq (Real.exp_pos _).le).le

end RiemannGaussian.AlpogeWindow

open Lean Elab Command in
run_cmd do
  let decl := ``RiemannGaussian.AlpogeWindow.principal_family_rank_and_share_of_free_classes
  let axs ← collectAxioms decl
  for ax in axs do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {decl}"
  logInfo m!"{decl} depends on {axs}"
