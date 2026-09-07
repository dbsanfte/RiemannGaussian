import RiemannGaussian.EtaMoebiusQuotientShells

/-!
# Abel transforms of the actual complete quotient shells

Summation by parts moves the discrete derivative from the Möbius prefix
onto the literal eta prefix. The resulting bulk alternates in the quotient
index. Both complex boundary terms remain in each capped shell; their
telescoping leaves the original moving cap in the complete carrier.
No estimate for the full signed quadratic form is inferred from the identity.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The alternating Möbius-prefix bulk at an independently specified quotient cap. -/
def pairedEtaMoebiusQuotientAbelBulk (rho : NontrivialZetaZero) (M Q : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 Q, (pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-rho.1) *
    complexMoebiusFinitePrefix rho.1 (M / q)

/-- The exact upper Abel boundary, including the eta prefix and the reciprocal arithmetic endpoint. -/
def pairedEtaMoebiusQuotientAbelBoundary (rho : NontrivialZetaZero) (M Q : ℕ) : ℂ :=
  pairedEtaUnpairedDirichletPrefix Q rho.1 * complexMoebiusFinitePrefix rho.1 (M / (Q + 1))

/-- Abel summation for every complete quotient prefix retains its exact alternating bulk and upper boundary, including the empty prefix. -/
theorem sum_pairedEtaCompletedMoebiusQuotientBlock_eq_abel
    (rho : NontrivialZetaZero) (M Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, pairedEtaCompletedMoebiusQuotientBlock rho M q) =
      pairedEtaXiCompletionFactor rho.1 *
        (pairedEtaMoebiusQuotientAbelBulk rho M Q - pairedEtaMoebiusQuotientAbelBoundary rho M Q) := by
  induction Q with
  | zero =>
    simp [pairedEtaMoebiusQuotientAbelBulk, pairedEtaMoebiusQuotientAbelBoundary,
      pairedEtaUnpairedDirichletPrefix]
  | succ Q ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    rw [pairedEtaCompletedMoebiusQuotientBlock,
      complexMoebiusDividedCutoffBlock_eq_prefix_sub rho.1 M (by omega : 0 < Q + 1)]
    simp only [pairedEtaMoebiusQuotientAbelBulk, pairedEtaMoebiusQuotientAbelBoundary,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ Q + 1), pairedEtaUnpairedDirichletPrefix_succ]
    ring

private theorem sum_Ioc_eq_prefix_sub (f : ℕ → ℂ) {L U : ℕ} (hLU : L ≤ U) :
    (∑ q ∈ Finset.Ioc L U, f q) = (∑ q ∈ Finset.Icc 1 U, f q) - ∑ q ∈ Finset.Icc 1 L, f q := by
  have hs : Finset.Icc 1 L ⊆ Finset.Icc 1 U := Finset.Icc_subset_Icc le_rfl hLU
  have he : Finset.Icc 1 U \ Finset.Icc 1 L = Finset.Ioc L U := by
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [← he]
  exact Finset.sum_sdiff_eq_sub hs

/-- Every quotient band has its full Abel identity, with the two distinct arithmetic endpoints retained before shell summation. -/
theorem sum_pairedEtaCompletedMoebiusQuotientBlock_Ioc_eq_abel
    (rho : NontrivialZetaZero) (M : ℕ) {L U : ℕ} (hLU : L ≤ U) :
    (∑ q ∈ Finset.Ioc L U, pairedEtaCompletedMoebiusQuotientBlock rho M q) =
      pairedEtaXiCompletionFactor rho.1 *
        ((∑ q ∈ Finset.Ioc L U, (pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-rho.1) *
          complexMoebiusFinitePrefix rho.1 (M / q)) +
          pairedEtaMoebiusQuotientAbelBoundary rho M L - pairedEtaMoebiusQuotientAbelBoundary rho M U) := by
  rw [sum_Ioc_eq_prefix_sub _ hLU, sum_pairedEtaCompletedMoebiusQuotientBlock_eq_abel,
    sum_pairedEtaCompletedMoebiusQuotientBlock_eq_abel, sum_Ioc_eq_prefix_sub _ hLU]
  unfold pairedEtaMoebiusQuotientAbelBulk
  ring

/-- The original zero-extended dyadic shell is exactly a complete band with both endpoints clipped by the same original quotient cap. -/
theorem pairedEtaCompletedMoebiusQuotientShell_eq_capped_band
    (rho : NontrivialZetaZero) (D M j : ℕ) :
    let Q := M / (D + 1)
    pairedEtaCompletedMoebiusQuotientShell rho D M j =
      ∑ q ∈ Finset.Ioc (min Q (2 ^ j - 1)) (min Q (2 ^ (j + 1) - 1)),
        pairedEtaCompletedMoebiusQuotientBlock rho M q := by
  dsimp only
  have hp : 0 < (2 : ℕ) ^ j := pow_pos (by norm_num) j
  have hs : 2 ^ j ≤ (2 : ℕ) ^ (j + 1) := by rw [pow_succ]; omega
  have he : (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (fun q ↦ q ≤ M / (D + 1)) =
      Finset.Ioc (min (M / (D + 1)) (2 ^ j - 1)) (min (M / (D + 1)) (2 ^ (j + 1) - 1)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
    omega
  unfold pairedEtaCompletedMoebiusQuotientShell pairedEtaCompletedMoebiusLargeQuotientFamily
  rw [← Finset.sum_filter, he]

/-- Abel summation of each actual capped dyadic shell exposes its alternating bilinear bulk without dropping either complex boundary. -/
theorem pairedEtaCompletedMoebiusQuotientShell_eq_abel
    (rho : NontrivialZetaZero) (D M j : ℕ) :
    let Q := M / (D + 1)
    let L := min Q (2 ^ j - 1)
    let U := min Q (2 ^ (j + 1) - 1)
    pairedEtaCompletedMoebiusQuotientShell rho D M j =
      pairedEtaXiCompletionFactor rho.1 *
        ((∑ q ∈ Finset.Ioc L U, (pairedEtaDirichletSign q : ℂ) * (q : ℂ) ^ (-rho.1) *
          complexMoebiusFinitePrefix rho.1 (M / q)) +
          pairedEtaMoebiusQuotientAbelBoundary rho M L - pairedEtaMoebiusQuotientAbelBoundary rho M U) := by
  dsimp only
  rw [pairedEtaCompletedMoebiusQuotientShell_eq_capped_band]
  apply sum_pairedEtaCompletedMoebiusQuotientBlock_Ioc_eq_abel
  apply min_le_min_left
  have hs : 2 ^ j ≤ (2 : ℕ) ^ (j + 1) := by rw [pow_succ]; omega
  omega

/-- The whole surviving carrier is the alternating Abel bulk minus its original moving boundary; all internal shell endpoints cancel exactly. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_abel
    (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M D =
      pairedEtaXiCompletionFactor rho.1 *
        (pairedEtaMoebiusQuotientAbelBulk rho M (M / (D + 1)) -
          pairedEtaMoebiusQuotientAbelBoundary rho M (M / (D + 1))) :=
  sum_pairedEtaCompletedMoebiusQuotientBlock_eq_abel rho M (M / (D + 1))

end

end RiemannGaussian
