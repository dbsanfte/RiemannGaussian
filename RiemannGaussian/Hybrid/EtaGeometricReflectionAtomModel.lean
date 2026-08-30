import RiemannGaussian.Hybrid.EtaGeometricReflectionParity
import RiemannGaussian.Hybrid.EtaSpectralHeatPowerSeries

/-!
# Normalized eigenvalue atoms for reflection-even eta compression

The positive reflection-even eta compression from the parity layer has the
right zero-eigenspace semantics for a zeta-zero certificate.  This module
turns that matrix into a literal finite nonnegative atom model without losing
its zero channel.

For a nonzero positive-semidefinite matrix `A` of dimension `N`, give every
eigenvalue weight `1/N` and normalize its node by

`xᵢ = (N / rtrace A) * λᵢ`.

Lean proves that these weights and nodes are nonnegative, have total mass and
first moment one, and retain every matrix-power trace and every heat-moment
trace exactly.  Most importantly, the mass at the zero node is precisely
`nullity(A) / N`.

Applied to `A₊ = E₊ K E₊`, positive definiteness of the eta Gram `K` makes
that zero mass exactly the upper off-line-pair fraction.  Hence the atom
certificate `1 - 2 * zeroMass` is definitionally aligned with the direct
reflection-count certificate and equals the represented critical-zero
fraction.  This establishes correct certificate semantics; it does not yet
prove a lower bound for that fraction.
-/

open Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

variable {K : Type*} [RCLike K]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A finite probability model on nonnegative nodes, normalized to have
first moment one. -/
structure NormalizedNonnegativeAtomModel (d : Type*) [Fintype d] where
  /-- The mass carried by each atom. -/
  weight : d → ℝ
  /-- The location of each atom. -/
  node : d → ℝ
  /-- Every atom weight is nonnegative. -/
  weight_nonneg : ∀ i, 0 ≤ weight i
  /-- Every atom location is nonnegative. -/
  node_nonneg : ∀ i, 0 ≤ node i
  /-- The atom weights have total mass one. -/
  total_weight : ∑ i, weight i = 1
  /-- The weighted first moment is one. -/
  first_moment : ∑ i, weight i * node i = 1

/-- The ordinary moment sequence of a normalized nonnegative atom model. -/
def NormalizedNonnegativeAtomModel.moment
    (M : NormalizedNonnegativeAtomModel d) (order : ℕ) : ℝ :=
  ∑ i, M.weight i * M.node i ^ order

/-- The complete heat-moment hierarchy of a normalized nonnegative atom
model. -/
def NormalizedNonnegativeAtomModel.heatMoment
    (M : NormalizedNonnegativeAtomModel d) (order : ℕ) (u : ℝ) : ℝ :=
  ∑ i, M.weight i * M.node i ^ order *
    Real.exp (-u * M.node i ^ 2)

/-- The total mass at the distinguished zero node. -/
def NormalizedNonnegativeAtomModel.zeroMass
    (M : NormalizedNonnegativeAtomModel d) : ℝ :=
  ∑ i, if M.node i = 0 then M.weight i else 0

/-- The good-direction certificate attached to the zero atom. -/
def NormalizedNonnegativeAtomModel.certificate
    (M : NormalizedNonnegativeAtomModel d) : ℝ :=
  1 - 2 * M.zeroMass

/-- A nonzero positive-semidefinite matrix has strictly positive real trace. -/
theorem rtrace_pos_of_posSemidef_of_ne_zero {A : Matrix d d K}
    (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    0 < rtrace A := by
  rw [rtrace_eq_sum_eigenvalues hA.isHermitian]
  have hnonneg : 0 ≤ ∑ i, hA.isHermitian.eigenvalues i :=
    Finset.sum_nonneg fun i _hi ↦ hA.eigenvalues_nonneg i
  have hne : (∑ i, hA.isHermitian.eigenvalues i) ≠ 0 := by
    intro hsum
    apply hA0
    apply hA.trace_eq_zero_iff.mp
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    exact_mod_cast hsum
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Uniform weights on the eigenvalues of a nonzero PSD matrix, rescaled by
their mean, form a normalized nonnegative atom model. -/
def normalizedEigenvalueAtomModel [Nonempty d]
    {A : Matrix d d K} (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    NormalizedNonnegativeAtomModel d where
  weight := fun _ ↦ 1 / (Fintype.card d : ℝ)
  node := fun i ↦
    ((Fintype.card d : ℝ) / rtrace A) * hA.isHermitian.eigenvalues i
  weight_nonneg := fun _ ↦ by positivity
  node_nonneg := fun i ↦ mul_nonneg
    (div_nonneg (Nat.cast_nonneg _)
      (rtrace_pos_of_posSemidef_of_ne_zero hA hA0).le)
    (hA.eigenvalues_nonneg i)
  total_weight := by
    simp [Fintype.card_ne_zero]
  first_moment := by
    have hcard : (Fintype.card d : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have htrace : rtrace A ≠ 0 :=
      (rtrace_pos_of_posSemidef_of_ne_zero hA hA0).ne'
    calc
      ∑ i, (1 / (Fintype.card d : ℝ)) *
          (((Fintype.card d : ℝ) / rtrace A) *
            hA.isHermitian.eigenvalues i) =
        (1 / (Fintype.card d : ℝ)) *
          ((Fintype.card d : ℝ) / rtrace A) *
            (∑ i, hA.isHermitian.eigenvalues i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ =
        (1 / (Fintype.card d : ℝ)) *
          ((Fintype.card d : ℝ) / rtrace A) * rtrace A := by
            rw [← rtrace_eq_sum_eigenvalues hA.isHermitian]
      _ = 1 := by field_simp

/-- Exact ordinary moments of the uniform normalized eigenvalue model. -/
theorem normalizedEigenvalueAtomModel_moment_eq [Nonempty d]
    {A : Matrix d d K} (hA : A.PosSemidef) (hA0 : A ≠ 0)
    (order : ℕ) :
    (normalizedEigenvalueAtomModel hA hA0).moment order =
      (1 / (Fintype.card d : ℝ)) *
        ((Fintype.card d : ℝ) / rtrace A) ^ order *
          rtrace (A ^ order) := by
  unfold NormalizedNonnegativeAtomModel.moment
    normalizedEigenvalueAtomModel
  rw [rtrace_pow_eq_sum_eigenvalues hA.isHermitian]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [mul_pow]
  ring_nf

/-- Exact heat moments of the uniform normalized eigenvalue model. -/
theorem normalizedEigenvalueAtomModel_heatMoment_eq [Nonempty d]
    {A : Matrix d d K} (hA : A.PosSemidef) (hA0 : A ≠ 0)
    (order : ℕ) (u : ℝ) :
    (normalizedEigenvalueAtomModel hA hA0).heatMoment order u =
      (1 / (Fintype.card d : ℝ)) *
        ((Fintype.card d : ℝ) / rtrace A) ^ order *
          hermitianHeatMomentTrace hA.isHermitian order
            (u * ((Fintype.card d : ℝ) / rtrace A) ^ 2) := by
  unfold NormalizedNonnegativeAtomModel.heatMoment
    normalizedEigenvalueAtomModel
  rw [hermitianHeatMomentTrace_eq_sum_eigenvalues]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  change
    (1 / (Fintype.card d : ℝ)) *
        ((((Fintype.card d : ℝ) / rtrace A) *
          hA.isHermitian.eigenvalues i) ^ order) *
        Real.exp (-u *
          (((Fintype.card d : ℝ) / rtrace A) *
            hA.isHermitian.eigenvalues i) ^ 2) =
      ((1 / (Fintype.card d : ℝ)) *
        ((Fintype.card d : ℝ) / rtrace A) ^ order) *
        (hA.isHermitian.eigenvalues i ^ order *
          Real.exp (-(u * ((Fintype.card d : ℝ) / rtrace A) ^ 2) *
            hA.isHermitian.eigenvalues i ^ 2))
  rw [mul_pow, show
    -u * (((Fintype.card d : ℝ) / rtrace A) *
      hA.isHermitian.eigenvalues i) ^ 2 =
      -(u * ((Fintype.card d : ℝ) / rtrace A) ^ 2) *
        hA.isHermitian.eigenvalues i ^ 2 by ring]
  ring

/-- The number of zero eigenvalues of a Hermitian matrix is its ambient
dimension minus its rank. -/
theorem card_eigenvalues_eq_zero {A : Matrix d d K}
    (hA : A.IsHermitian) :
    (Finset.univ.filter fun i ↦ hA.eigenvalues i = 0).card =
      Fintype.card d - A.rank := by
  have hrank := hA.rank_eq_card_non_zero_eigs
  rw [Fintype.card_subtype] at hrank
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset d)) (fun i ↦ hA.eigenvalues i = 0)
  simp only [Finset.card_univ] at hpartition
  rw [← hrank] at hpartition
  omega

/-- The zero mass of the uniform normalized PSD eigenvalue model is exactly
ambient nullity divided by ambient dimension. -/
theorem normalizedEigenvalueAtomModel_zeroMass_eq_nullity [Nonempty d]
    {A : Matrix d d K} (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    (normalizedEigenvalueAtomModel hA hA0).zeroMass =
      ((Fintype.card d - A.rank : ℕ) : ℝ) /
        (Fintype.card d : ℝ) := by
  have hscale :
      ((Fintype.card d : ℝ) / rtrace A) ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
      (rtrace_pos_of_posSemidef_of_ne_zero hA hA0).ne'
  unfold NormalizedNonnegativeAtomModel.zeroMass
    normalizedEigenvalueAtomModel
  simp only [mul_eq_zero, hscale, false_or]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_eigenvalues_eq_zero hA.isHermitian]
  ring

/-! ## An exact ordinary-heat separator -/

/-- The ordinary heat mass carried by nonzero atoms. -/
def NormalizedNonnegativeAtomModel.independentHeatExcess
    (M : NormalizedNonnegativeAtomModel d) (u : ℝ) : ℝ :=
  ∑ i, if M.node i = 0 then 0
    else M.weight i * Real.exp (-u * M.node i ^ 2)

omit [DecidableEq d] in
/-- First-moment normalization forces a positive-weight nonzero atom. -/
theorem NormalizedNonnegativeAtomModel.exists_weight_pos_and_node_ne_zero
    (M : NormalizedNonnegativeAtomModel d) :
    ∃ i, 0 < M.weight i ∧ M.node i ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hweightZero : ∀ i, M.node i ≠ 0 → M.weight i = 0 := by
    intro i hi
    apply le_antisymm
    · exact not_lt.mp fun hpos ↦ hi (h i hpos)
    · exact M.weight_nonneg i
  have hmoment : ∑ i, M.weight i * M.node i = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    by_cases hi : M.node i = 0
    · simp [hi]
    · rw [hweightZero i hi]
      simp
  rw [M.first_moment] at hmoment
  norm_num at hmoment

omit [DecidableEq d] in
/-- Ordinary heat splits into zero mass and its nonzero-atom excess. -/
theorem NormalizedNonnegativeAtomModel.zeroMass_add_independentHeatExcess
    (M : NormalizedNonnegativeAtomModel d) (u : ℝ) :
    M.zeroMass + M.independentHeatExcess u = M.heatMoment 0 u := by
  unfold NormalizedNonnegativeAtomModel.zeroMass
    NormalizedNonnegativeAtomModel.independentHeatExcess
    NormalizedNonnegativeAtomModel.heatMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : M.node i = 0 <;> simp [hi]

omit [DecidableEq d] in
/-- The nonzero-atom heat excess is positive at every finite scale. -/
theorem NormalizedNonnegativeAtomModel.independentHeatExcess_pos
    (M : NormalizedNonnegativeAtomModel d) (u : ℝ) :
    0 < M.independentHeatExcess u := by
  unfold NormalizedNonnegativeAtomModel.independentHeatExcess
  apply Finset.sum_pos'
  · intro i _hi
    by_cases hi : M.node i = 0
    · simp [hi]
    · simp only [hi, ↓reduceIte]
      exact mul_nonneg (M.weight_nonneg i) (Real.exp_pos _).le
  · obtain ⟨i, hweight, hnode⟩ := M.exists_weight_pos_and_node_ne_zero
    refine ⟨i, Finset.mem_univ i, ?_⟩
    simp only [hnode, ↓reduceIte]
    exact mul_pos hweight (Real.exp_pos _)

omit [DecidableEq d] in
/-- At every finite scale, ordinary heat remains strictly above zero mass. -/
theorem NormalizedNonnegativeAtomModel.zeroMass_lt_heatMoment_zero
    (M : NormalizedNonnegativeAtomModel d) (u : ℝ) :
    M.zeroMass < M.heatMoment 0 u := by
  rw [← M.zeroMass_add_independentHeatExcess u]
  linarith [M.independentHeatExcess_pos u]

omit [DecidableEq d] in
/-- Ordinary heat converges to zero mass at large heat time. -/
theorem NormalizedNonnegativeAtomModel.tendsto_heatMoment_zero_atTop_zeroMass
    (M : NormalizedNonnegativeAtomModel d) :
    Tendsto (M.heatMoment 0) atTop (nhds M.zeroMass) := by
  have hsum : Tendsto
      (fun u : ℝ ↦ ∑ i,
        M.weight i * Real.exp (-u * M.node i ^ 2)) atTop
      (nhds (∑ i, M.weight i *
        (if M.node i = 0 then 1 else 0))) := by
    exact tendsto_finsetSum Finset.univ fun i _hi ↦
      (tendsto_scalarHeat_atTop (M.node i)).const_mul (M.weight i)
  have hlimit :
      (∑ i, M.weight i * (if M.node i = 0 then 1 else 0)) =
        M.zeroMass := by
    unfold NormalizedNonnegativeAtomModel.zeroMass
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : M.node i = 0 <;> simp [hi]
  rw [hlimit] at hsum
  change Tendsto
    (fun u : ℝ ↦ ∑ i, M.weight i * M.node i ^ 0 *
      Real.exp (-u * M.node i ^ 2)) atTop (nhds M.zeroMass)
  simpa using hsum

omit [DecidableEq d] in
/-- Beating `13/18` is exactly an ordinary-heat crossing below `5/36` for
every normalized nonnegative atom model. -/
theorem NormalizedNonnegativeAtomModel.thirteen_eighteen_lt_certificate_iff_exists_heat
    (M : NormalizedNonnegativeAtomModel d) :
    (13 : ℝ) / 18 < M.certificate ↔
      ∃ u : ℝ, 0 ≤ u ∧ M.heatMoment 0 u < (5 : ℝ) / 36 := by
  constructor
  · intro hcertificate
    have hzeroMass : M.zeroMass < (5 : ℝ) / 36 := by
      unfold NormalizedNonnegativeAtomModel.certificate at hcertificate
      linarith
    have heventually : ∀ᶠ u : ℝ in atTop,
        M.heatMoment 0 u < (5 : ℝ) / 36 :=
      M.tendsto_heatMoment_zero_atTop_zeroMass.eventually_lt_const hzeroMass
    obtain ⟨u, huHeat, hu⟩ :=
      (heventually.and (eventually_ge_atTop (0 : ℝ))).exists
    exact ⟨u, hu, huHeat⟩
  · rintro ⟨u, _hu, hheat⟩
    unfold NormalizedNonnegativeAtomModel.certificate
    linarith [M.zeroMass_lt_heatMoment_zero u]

end

end RiemannGaussian.HermitianRankTrace

namespace RiemannGaussian

noncomputable section

open HermitianRankTrace

/-! ## The literal reflection-even eta atom model -/

/-- A nonempty separated eta window makes its positive reflection-even
compression nonzero. -/
theorem pairedEtaGeometricReflectionEvenCompressedZeroGram_ne_zero
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n ≠ 0 := by
  have hwindowCard : 0 < (spectralZetaZeroWindow T).card :=
    Finset.card_pos.mpr hwindow
  have hdecomp :=
    spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper hT
  have hrank :=
    pairedEtaGeometricReflectionEvenCompressedZeroGram_rank q hT n hK
  intro hzero
  rw [hzero] at hrank
  simp only [Matrix.rank_zero] at hrank
  omega

/-- The real trace used to normalize the even-compressed eta spectrum is
strictly positive on every nonempty separated window. -/
theorem pairedEtaGeometricReflectionEvenCompressedZeroGram_rtrace_pos
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    0 < rtrace
      (pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n) :=
  rtrace_pos_of_posSemidef_of_ne_zero
    (pairedEtaGeometricReflectionEvenCompressedZeroGram_posSemidef q T hT n)
    (pairedEtaGeometricReflectionEvenCompressedZeroGram_ne_zero
      q hT n hwindow hK)

/-- The literal uniform atom model of the positive reflection-even eta
compression. Its nodes are the nonnegative eigenvalues of `A₊`, divided by
their mean. -/
def pairedEtaGeometricReflectionEvenAtomModel
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    NormalizedNonnegativeAtomModel
      (Fin (spectralZetaZeroWindow T).card) := by
  let _ : Nonempty (Fin (spectralZetaZeroWindow T).card) :=
    Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hwindow)
  exact normalizedEigenvalueAtomModel
    (pairedEtaGeometricReflectionEvenCompressedZeroGram_posSemidef q T hT n)
    (pairedEtaGeometricReflectionEvenCompressedZeroGram_ne_zero
      q hT n hwindow hK)

/-- Every eta atom node is nonnegative. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_node_nonneg
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (i : Fin (spectralZetaZeroWindow T).card) :
    0 ≤ (pairedEtaGeometricReflectionEvenAtomModel
      q hT n hwindow hK).node i :=
  (pairedEtaGeometricReflectionEvenAtomModel
    q hT n hwindow hK).node_nonneg i

/-- The eta atom model has total mass one. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_moment_zero
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenAtomModel
      q hT n hwindow hK).moment 0 = 1 := by
  simpa [NormalizedNonnegativeAtomModel.moment] using
    (pairedEtaGeometricReflectionEvenAtomModel
      q hT n hwindow hK).total_weight

/-- Mean normalization makes the first eta atom moment exactly one. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_moment_one
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenAtomModel
      q hT n hwindow hK).moment 1 = 1 := by
  simpa [NormalizedNonnegativeAtomModel.moment] using
    (pairedEtaGeometricReflectionEvenAtomModel
      q hT n hwindow hK).first_moment

/-- Every ordinary eta atom moment is exactly a normalized matrix-power
trace of the positive reflection-even compression. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_moment_eq_rtrace_pow
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n order : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenAtomModel
        q hT n hwindow hK).moment order =
      (1 / ((spectralZetaZeroWindow T).card : ℝ)) *
        (((spectralZetaZeroWindow T).card : ℝ) /
          rtrace (pairedEtaGeometricReflectionEvenCompressedZeroGram
            q T hT n)) ^ order *
        rtrace ((pairedEtaGeometricReflectionEvenCompressedZeroGram
          q T hT n) ^ order) := by
  let _ : Nonempty (Fin (spectralZetaZeroWindow T).card) :=
    Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hwindow)
  unfold pairedEtaGeometricReflectionEvenAtomModel
  simpa only [Fintype.card_fin] using
    normalizedEigenvalueAtomModel_moment_eq
      (pairedEtaGeometricReflectionEvenCompressedZeroGram_posSemidef q T hT n)
      (pairedEtaGeometricReflectionEvenCompressedZeroGram_ne_zero
        q hT n hwindow hK) order

/-- The full eta atom heat hierarchy is exactly the normalized Hermitian
heat-moment trace of the positive reflection-even compression. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_heatMoment_eq
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n order : ℕ) (u : ℝ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenAtomModel
        q hT n hwindow hK).heatMoment order u =
      (1 / ((spectralZetaZeroWindow T).card : ℝ)) *
        (((spectralZetaZeroWindow T).card : ℝ) /
          rtrace (pairedEtaGeometricReflectionEvenCompressedZeroGram
            q T hT n)) ^ order *
        hermitianHeatMomentTrace
          (pairedEtaGeometricReflectionEvenCompressedZeroGram_posSemidef
            q T hT n).isHermitian order
          (u * (((spectralZetaZeroWindow T).card : ℝ) /
            rtrace (pairedEtaGeometricReflectionEvenCompressedZeroGram
              q T hT n)) ^ 2) := by
  let _ : Nonempty (Fin (spectralZetaZeroWindow T).card) :=
    Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hwindow)
  unfold pairedEtaGeometricReflectionEvenAtomModel
  simpa only [Fintype.card_fin] using
    normalizedEigenvalueAtomModel_heatMoment_eq
      (pairedEtaGeometricReflectionEvenCompressedZeroGram_posSemidef q T hT n)
      (pairedEtaGeometricReflectionEvenCompressedZeroGram_ne_zero
        q hT n hwindow hK) order u

/-- The eta atom mass at zero is exactly the upper off-line-pair fraction. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_zeroMass_eq_upperFraction
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenAtomModel
        q hT n hwindow hK).zeroMass =
      (spectralUpperZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card := by
  let _ : Nonempty (Fin (spectralZetaZeroWindow T).card) :=
    Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hwindow)
  unfold pairedEtaGeometricReflectionEvenAtomModel
  rw [normalizedEigenvalueAtomModel_zeroMass_eq_nullity]
  simp only [Fintype.card_fin]
  rw [pairedEtaGeometricReflectionEvenCompressedZeroGram_nullity_eq_upper
    q hT n hK]

/-- The spectral zero-mass certificate and the direct reflection-count
certificate are definitionally aligned. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_certificate_eq_countCertificate
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenAtomModel
        q hT n hwindow hK).certificate =
      pairedEtaZeroWindowReflectionCountCertificate T hT := by
  unfold NormalizedNonnegativeAtomModel.certificate
    pairedEtaZeroWindowReflectionCountCertificate
  rw [pairedEtaGeometricReflectionEvenAtomModel_zeroMass_eq_upperFraction
    q hT n hwindow hK]
  unfold HermitianInertia.rtrace
  rw [pairedEtaZeroWindowReflectionOddProjection_trace]
  simp
  ring

/-- The eta atom certificate is exactly the represented critical-zero
fraction. This is an identity, not yet a lower bound for that fraction. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_certificate_eq_criticalFraction
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenAtomModel
        q hT n hwindow hK).certificate =
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card := by
  rw [pairedEtaGeometricReflectionEvenAtomModel_certificate_eq_countCertificate
    q hT n hwindow hK]
  exact pairedEtaZeroWindowReflectionCountCertificate_eq_criticalFraction
    hT hwindow

/-- The literal eta atom certificate beats `13/18` exactly when its ordinary
heat trace crosses below `5/36` at a nonnegative scale. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_thirteen_eighteen_lt_criticalFraction_iff_exists_heat
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (13 : ℝ) / 18 <
        (spectralCriticalZetaZeroWindow T).card /
          (spectralZetaZeroWindow T).card ↔
      ∃ u : ℝ, 0 ≤ u ∧
        (pairedEtaGeometricReflectionEvenAtomModel
          q hT n hwindow hK).heatMoment 0 u < (5 : ℝ) / 36 := by
  rw [← pairedEtaGeometricReflectionEvenAtomModel_certificate_eq_criticalFraction
    q hT n hwindow hK]
  exact
    (pairedEtaGeometricReflectionEvenAtomModel
      q hT n hwindow hK).thirteen_eighteen_lt_certificate_iff_exists_heat

/-- Matrix form of the exact `13/18` crossing criterion: the remaining
arithmetic target is an upper bound for the ordinary Hermitian heat trace of
the literal positive reflection-even eta compression. -/
theorem pairedEtaGeometricReflectionEvenAtomModel_thirteen_eighteen_lt_criticalFraction_iff_exists_rtrace_heat
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (13 : ℝ) / 18 <
        (spectralCriticalZetaZeroWindow T).card /
          (spectralZetaZeroWindow T).card ↔
      ∃ u : ℝ, 0 ≤ u ∧
        (1 / ((spectralZetaZeroWindow T).card : ℝ)) *
          hermitianHeatMomentTrace
            (pairedEtaGeometricReflectionEvenCompressedZeroGram_posSemidef
              q T hT n).isHermitian 0
            (u * (((spectralZetaZeroWindow T).card : ℝ) /
              rtrace (pairedEtaGeometricReflectionEvenCompressedZeroGram
                q T hT n)) ^ 2) < (5 : ℝ) / 36 := by
  rw [pairedEtaGeometricReflectionEvenAtomModel_thirteen_eighteen_lt_criticalFraction_iff_exists_heat
    q hT n hwindow hK]
  apply exists_congr
  intro u
  apply and_congr_right
  intro _hu
  rw [pairedEtaGeometricReflectionEvenAtomModel_heatMoment_eq
    q hT n 0 u hwindow hK]
  norm_num

end

end RiemannGaussian
