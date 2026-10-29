import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# The finite free ring used for prime-power counting

This file constructs the quotient by a monic polynomial, proves that a
positive-degree quotient retains the base ring, and constructs coefficient
reduction maps between these polynomial quotient rings.
-/

namespace SubexponentialSAT.LiftRing

noncomputable section

open Polynomial

section General

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Quotient by the principal ideal of the defining polynomial. -/
abbrev Extension (F : R[X]) := R[X] ⧸ Ideal.span {F}

/-- The polynomial quotient map. -/
def mk (F : R[X]) : R[X] →+* Extension F := Ideal.Quotient.mk _

/-- The constant-polynomial map into the extension ring. -/
def of (F : R[X]) : R →+* Extension F := (mk F).comp C

@[simp]
theorem mk_eq_zero {F q : R[X]} : mk F q = 0 ↔ F ∣ q :=
  Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton

@[simp]
theorem mk_eq_mk {F q r : R[X]} : mk F q = mk F r ↔ F ∣ q - r :=
  Ideal.Quotient.eq.trans Ideal.mem_span_singleton

/-- Constants embed for every monic defining polynomial of positive degree. -/
theorem base_injective {F : R[X]} (hF : F.Monic) (hdeg : 0 < F.natDegree) :
    Function.Injective (of F) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have hC : C a ≠ (0 : R[X]) := by simpa only [ne_eq, C_eq_zero] using h
  exact hF.not_dvd_of_natDegree_lt hC
    (by simpa only [natDegree_C] using hdeg) ((mk_eq_zero).mp ha)

/-- The unique remainder is a linear function on the quotient. -/
def remainder {F : R[X]} (hF : F.Monic) : Extension F →ₗ[R] R[X] :=
  (Submodule.liftQ _ (Polynomial.modByMonicHom F)
      fun _ hq => (mem_ker_modByMonic hF).mpr (Ideal.mem_span_singleton.mp hq)).comp
    (Submodule.Quotient.restrictScalarsEquiv R
      (Ideal.span {F} : Ideal R[X])).symm.toLinearMap

@[simp]
theorem remainder_mk {F : R[X]} (hF : F.Monic) (q : R[X]) :
    remainder hF (mk F q) = q %ₘ F := rfl

theorem mk_remainder {F : R[X]} (hF : F.Monic) (x : Extension F) :
    mk F (remainder hF x) = x := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change mk F (remainder hF (mk F q)) = mk F q
  rw [remainder_mk, mk_eq_mk, modByMonic_eq_sub_mul_div,
    sub_sub_cancel_left, dvd_neg]
  exact dvd_mul_right _ _

theorem remainder_of {F : R[X]} (hF : F.Monic) (hdeg : 0 < F.natDegree)
    (a : R) : remainder hF (of F a) = C a := by
  nontriviality R
  change C a %ₘ F = C a
  apply (modByMonic_eq_self_iff hF).mpr
  exact degree_C_le.trans_lt (natDegree_pos_iff_degree_pos.mp hdeg)

/-- Every residue class has one and only one vector of coefficients below
the degree of the monic defining polynomial. -/
noncomputable def coordinates {F : R[X]} (hF : F.Monic) :
    Extension F ≃ₗ[R] (Fin F.natDegree → R) := by
  classical
  exact
    { toFun := fun x i => (remainder hF x).coeff i
      invFun := fun c => mk F (∑ i : Fin F.natDegree, monomial i (c i))
      map_add' := fun x y => by
        funext i
        simp only [map_add, coeff_add, Pi.add_apply]
      map_smul' := fun a x => by
        funext i
        simp only [map_smul, coeff_smul, Pi.smul_apply, RingHom.id_apply]
      left_inv := fun x => by
        obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
        change mk F (∑ i : Fin F.natDegree,
          monomial i ((remainder hF (mk F q)).coeff i)) = mk F q
        simp only [remainder_mk, sum_modByMonic_coeff hF degree_le_natDegree]
        rw [mk_eq_mk, modByMonic_eq_sub_mul_div, sub_sub_cancel_left, dvd_neg]
        exact dvd_mul_right _ _
      right_inv := fun c => by
        funext i
        nontriviality R
        simp only [remainder_mk]
        rw [(modByMonic_eq_self_iff hF).mpr, finsetSum_coeff]
        · simp_rw [coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq',
            ite_eq_left (Finset.mem_univ _)]
        · simp_rw [← C_mul_X_pow_eq_monomial]
          exact (degree_eq_natDegree hF.ne_zero).symm ▸ degree_sum_fin_lt _ }

theorem extension_free {F : R[X]} (hF : F.Monic) :
    Module.Free R (Extension F) :=
  Module.Free.of_basis (Module.Basis.ofEquivFun (coordinates hF))

theorem extension_finite {F : R[X]} (hF : F.Monic) :
    Module.Finite R (Extension F) :=
  Module.Finite.of_basis (Module.Basis.ofEquivFun (coordinates hF))

/-- A finite coefficient ring yields a genuinely finite quotient ring. -/
theorem extension_finite_type [Finite R] {F : R[X]} (hF : F.Monic) :
    Finite (Extension F) :=
  Finite.of_injective (coordinates hF) (coordinates hF).injective

theorem natCard_extension {F : R[X]} (hF : F.Monic) :
    Nat.card (Extension F) = Nat.card R ^ F.natDegree := by
  calc
    Nat.card (Extension F) = Nat.card (Fin F.natDegree → R) :=
      Nat.card_congr (coordinates hF).toEquiv
    _ = Nat.card R ^ F.natDegree := by rw [Nat.card_fun]; simp

/-- Change the coefficient ring in the quotient. -/
def reduction (φ : R →+* S) (F : R[X]) :
    Extension F →+* Extension (F.map φ) :=
  Ideal.Quotient.lift _ ((mk (F.map φ)).comp (Polynomial.mapRingHom φ))
    (by
      intro q hq
      apply mk_eq_zero.mpr
      exact map_dvd φ (Ideal.mem_span_singleton.mp hq))

@[simp]
theorem reduction_mk (φ : R →+* S) (F q : R[X]) :
    reduction φ F (mk F q) = mk (F.map φ) (q.map φ) := rfl

@[simp]
theorem reduction_of (φ : R →+* S) (F : R[X]) (a : R) :
    reduction φ F (of F a) = of (F.map φ) (φ a) := by
  change mk (F.map φ) ((C a).map φ) = _
  simp only [map_C]
  rfl

theorem reduction_surjective (φ : R →+* S) (hφ : Function.Surjective φ) (F : R[X]) :
    Function.Surjective (reduction φ F) := by
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r, rfl⟩ := Polynomial.map_surjective φ hφ q
  exact ⟨mk F r, rfl⟩

theorem remainder_reduction (φ : R →+* S) {F : R[X]} (hF : F.Monic)
    (x : Extension F) :
    remainder (hF.map φ) (reduction φ F x) = (remainder hF x).map φ := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  change remainder (hF.map φ) (reduction φ F (mk F q)) =
    (remainder hF (mk F q)).map φ
  rw [reduction_mk, remainder_mk, remainder_mk, map_modByMonic φ hF]

/-- A principal kernel in the coefficient ring stays the same principal
kernel after adjoining a root of a monic polynomial. -/
theorem reduction_eq_zero_iff (φ : R →+* S) {F : R[X]} (hF : F.Monic)
    {c : R} (hker : ∀ a : R, φ a = 0 ↔ c ∣ a) (x : Extension F) :
    reduction φ F x = 0 ↔ of F c ∣ x := by
  constructor
  · intro hx
    have hm : (remainder hF x).map φ = 0 := by
      rw [← remainder_reduction φ hF x, hx, map_zero]
    have hd : C c ∣ remainder hF x := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      apply (hker _).mp
      have hi := congrArg (fun q : S[X] => q.coeff i) hm
      simpa only [coeff_map, coeff_zero] using hi
    obtain ⟨q, hq⟩ := hd
    refine ⟨mk F q, ?_⟩
    rw [← mk_remainder hF x, hq, map_mul]
    rfl
  · rintro ⟨y, rfl⟩
    rw [map_mul, reduction_of, (hker c).mpr (dvd_refl c), map_zero, zero_mul]

end General

/-- Over a field, an irreducible defining polynomial makes the concrete
polynomial quotient a field. -/
@[instance_reducible]
noncomputable def extensionField {K : Type*} [Field K] {g : K[X]}
    (hg : Irreducible g) : Field (Extension g) := by
  letI : (Ideal.span {g} : Ideal K[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hg
  exact Ideal.Quotient.field _

/-- The prime-power coefficient ring. -/
abbrev Base (p μ : ℕ) := ZMod (p ^ μ)

/-- The ring Lambda in Section 4.1. -/
abbrev Lambda (p μ : ℕ) (F : (Base p μ)[X]) := Extension F

theorem natCard_lambda (p μ : ℕ) {F : (Base p μ)[X]} (hF : F.Monic) :
    Nat.card (Lambda p μ F) = (p ^ μ) ^ F.natDegree := by
  simpa only [Base, Nat.card_zmod] using natCard_extension hF

/-- Reduction of prime-power coefficients modulo p.  Primality is not
needed for this ring homomorphism. -/
def baseReduction (p μ : ℕ) (hμ : 0 < μ) : Base p μ →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt hμ)) (ZMod p)

theorem baseReduction_surjective (p μ : ℕ) [NeZero p] (hμ : 0 < μ) :
    Function.Surjective (baseReduction p μ hμ) := by
  intro a
  refine ⟨(a.val : Base p μ), ?_⟩
  simp only [map_natCast, ZMod.natCast_zmod_val]

/-- A monic residue-field polynomial always has a monic lift of the same
degree; this discharges existence of the defining polynomial. -/
theorem exists_monic_lift (p μ : ℕ) [NeZero p] (hμ : 0 < μ)
    (g : (ZMod p)[X]) (hg : g.Monic) :
    ∃ F : (Base p μ)[X],
      F.map (baseReduction p μ hμ) = g ∧ F.natDegree = g.natDegree ∧ F.Monic := by
  apply Polynomial.lifts_and_natDegree_eq_and_monic _ hg
  rw [Polynomial.mem_lifts]
  exact Polynomial.map_surjective _ (baseReduction_surjective p μ hμ) g

theorem baseReduction_eq_zero_iff (p μ : ℕ) [NeZero p] (hμ : 0 < μ)
    (a : Base p μ) :
    baseReduction p μ hμ a = 0 ↔ (p : Base p μ) ∣ a := by
  constructor
  · intro ha
    have hv : (a.val : ZMod p) = 0 := by
      rw [← ZMod.natCast_zmod_val a] at ha
      simpa only [map_natCast] using ha
    obtain ⟨b, hb⟩ := (ZMod.natCast_eq_zero_iff a.val p).mp hv
    refine ⟨(b : Base p μ), ?_⟩
    rw [← Nat.cast_mul, ← hb, ZMod.natCast_zmod_val]
  · rintro ⟨b, rfl⟩
    simp only [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- The residue-ring map induced by coefficientwise reduction. -/
def residue (p μ : ℕ) (hμ : 0 < μ) (F : (Base p μ)[X]) :
    Lambda p μ F →+* Extension (F.map (baseReduction p μ hμ)) :=
  reduction (baseReduction p μ hμ) F

theorem residue_surjective (p μ : ℕ) [NeZero p] (hμ : 0 < μ)
    (F : (Base p μ)[X]) :
    Function.Surjective (residue p μ hμ F) :=
  reduction_surjective _ (baseReduction_surjective p μ hμ) F

theorem residue_eq_zero_iff (p μ : ℕ) [NeZero p] (hμ : 0 < μ)
    {F : (Base p μ)[X]} (hF : F.Monic) (x : Lambda p μ F) :
    residue p μ hμ F x = 0 ↔ (p : Lambda p μ F) ∣ x := by
  unfold residue
  simpa only [map_natCast] using
    reduction_eq_zero_iff (baseReduction p μ hμ) hF
      (baseReduction_eq_zero_iff p μ hμ) x

theorem residue_ker (p μ : ℕ) [NeZero p] (hμ : 0 < μ)
    {F : (Base p μ)[X]} (hF : F.Monic) :
    RingHom.ker (residue p μ hμ F) =
      Ideal.span {(p : Lambda p μ F)} := by
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_span_singleton, residue_eq_zero_iff p μ hμ hF]

/-- Reducing Lambda modulo its ideal (p) is exactly the quotient by the
reduced defining polynomial, not merely a homomorphic image of it. -/
noncomputable def residueQuotientEquiv (p μ : ℕ) [NeZero p] (hμ : 0 < μ)
    {F : (Base p μ)[X]} (hF : F.Monic) :
    (Lambda p μ F ⧸ Ideal.span {(p : Lambda p μ F)}) ≃+*
      Extension (F.map (baseReduction p μ hμ)) :=
  (Ideal.quotEquivOfEq (residue_ker p μ hμ hF).symm).trans
    (RingHom.quotientKerEquivOfSurjective (residue_surjective p μ hμ F))

/-- Integer representatives of the prime-field labels. -/
def label (p μ : ℕ) (F : (Base p μ)[X]) (i : Fin p) : Lambda p μ F :=
  (i.val : Lambda p μ F)

@[simp]
theorem residue_label (p μ : ℕ) (hμ : 0 < μ)
    (F : (Base p μ)[X]) (i : Fin p) :
    residue p μ hμ F (label p μ F i) =
      (i.val : Extension (F.map (baseReduction p μ hμ))) :=
  map_natCast _ _

theorem prime_power_zero (p μ : ℕ) (F : (Base p μ)[X]) :
    (p : Lambda p μ F) ^ μ = 0 := by
  rw [← Nat.cast_pow]
  have h : ((p ^ μ : ℕ) : Base p μ) = 0 := ZMod.natCast_self _
  have hm := congrArg (of F) h
  simpa only [map_natCast, map_zero] using hm

/-- Exact preservation of divisibility for constant natural-number counts. -/
theorem natCast_eq_zero_iff (p μ : ℕ) {F : (Base p μ)[X]}
    (hF : F.Monic) (hdeg : 0 < F.natDegree) (n : ℕ) :
    (n : Lambda p μ F) = 0 ↔ p ^ μ ∣ n := by
  calc
    (n : Lambda p μ F) = 0 ↔ of F (n : Base p μ) = of F 0 := by
      simp only [map_natCast, map_zero]
    _ ↔ (n : Base p μ) = 0 := (base_injective hF hdeg).eq_iff
    _ ↔ p ^ μ ∣ n := ZMod.natCast_eq_zero_iff _ _

/-- A count strictly below the chosen modulus vanishes in Lambda exactly
when the ordinary integer count is zero. -/
theorem count_eq_zero_iff (p μ : ℕ) {F : (Base p μ)[X]}
    (hF : F.Monic) (hdeg : 0 < F.natDegree) (n : ℕ) (hn : n < p ^ μ) :
    (n : Lambda p μ F) = 0 ↔ n = 0 := by
  rw [natCast_eq_zero_iff p μ hF hdeg]
  constructor
  · intro hd
    exact Nat.eq_zero_of_dvd_of_lt hd hn
  · rintro rfl
    exact dvd_zero _

/-- Read the constant coefficient as its standard nonnegative residue. -/
def decodeCount (p μ : ℕ) {F : (Base p μ)[X]} (hF : F.Monic)
    (x : Lambda p μ F) : ℕ :=
  ((remainder hF x).coeff 0).val

theorem decodeCount_natCast (p μ : ℕ) {F : (Base p μ)[X]}
    (hF : F.Monic) (hdeg : 0 < F.natDegree) (n : ℕ) (hn : n < p ^ μ) :
    decodeCount p μ hF (n : Lambda p μ F) = n := by
  have hcast : (n : Lambda p μ F) = of F (n : Base p μ) := by
    simp only [map_natCast]
  simp only [decodeCount, hcast, remainder_of hF hdeg, coeff_C_zero]
  exact ZMod.val_natCast_of_lt hn

end

end SubexponentialSAT.LiftRing

end OAI.Algorithms
