import RiemannGaussian.EtaMoebiusQuotientAbel
import RiemannGaussian.EtaInverseHyperbolicCoefficients

/-!
# The alternating bilinear hyperbola behind complete quotient shells

The upper Abel boundary is absorbed exactly into a lower cutoff on the
Möbius divisor. The full surviving carrier is therefore an alternating
bilinear sum on a literal subregion of the existing hyperbolic product
region. This keeps the cutoff and every complex phase, rather than
estimating the Abel bulk and its boundary separately.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The actual Abel region: quotient at most `Q`, product at most `M`, and Möbius divisor above the same reciprocal cap boundary. -/
def pairedEtaMoebiusQuotientBilinearRegion (M Q : ℕ) : Finset (ℕ × ℕ) :=
  (pairedEtaInverseHyperbolicRegion M).filter (fun p ↦ p.1 ≤ Q ∧ M / (Q + 1) < p.2)

/-- Both positive indices, the quotient cap, the reciprocal boundary, and the product cutoff characterize the bilinear region exactly. -/
theorem mem_pairedEtaMoebiusQuotientBilinearRegion {M Q : ℕ} {p : ℕ × ℕ} :
    p ∈ pairedEtaMoebiusQuotientBilinearRegion M Q ↔
      1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 * p.2 ≤ M ∧ p.1 ≤ Q ∧ M / (Q + 1) < p.2 := by
  simp only [pairedEtaMoebiusQuotientBilinearRegion, Finset.mem_filter,
    mem_pairedEtaInverseHyperbolicRegion, and_assoc]

/-- The whole Abel region is a literal portion of the existing hyperbolic inverse region, so its product-fibre machinery applies without a new region hypothesis. -/
theorem pairedEtaMoebiusQuotientBilinearRegion_subset (M Q : ℕ) :
    pairedEtaMoebiusQuotientBilinearRegion M Q ⊆ pairedEtaInverseHyperbolicRegion M :=
  Finset.filter_subset _ _

/-- Once the Abel boundary is absorbed into the Möbius divisor cutoff, the quotient cap follows from the product constraint and is redundant. -/
theorem pairedEtaMoebiusQuotientBilinearRegion_eq_divisor_cut (M Q : ℕ) :
    pairedEtaMoebiusQuotientBilinearRegion M Q =
      (pairedEtaInverseHyperbolicRegion M).filter (fun p ↦ M / (Q + 1) < p.2) := by
  ext p
  simp only [pairedEtaMoebiusQuotientBilinearRegion, Finset.mem_filter]
  constructor
  · rintro ⟨hp, _, hR⟩
    exact ⟨hp, hR⟩
  · rintro ⟨hp, hR⟩
    refine ⟨hp, ?_, hR⟩
    by_contra hq
    have hprod := (mem_pairedEtaInverseHyperbolicRegion.mp hp).2.2
    have hd : p.2 ≤ M / (Q + 1) := by
      apply (Nat.le_div_iff_mul_le (Nat.succ_pos Q)).mpr
      calc
        p.2 * (Q + 1) ≤ p.2 * p.1 := Nat.mul_le_mul_left _ (by omega)
        _ = p.1 * p.2 := Nat.mul_comm _ _
        _ ≤ M := hprod
    omega

/-- Quotient fibres in the actual bilinear region have the exact divided upper endpoint and the common lower Abel boundary. -/
theorem sum_pairedEtaMoebiusQuotientBilinearRegion_eq_divided
    (M Q : ℕ) (f : ℕ × ℕ → ℂ) :
    (∑ p ∈ pairedEtaMoebiusQuotientBilinearRegion M Q, f p) =
      ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Ioc (M / (Q + 1)) (M / q), f (q, d) := by
  have hs := Finset.sum_fiberwise_of_maps_to
    (s := pairedEtaMoebiusQuotientBilinearRegion M Q) (t := Finset.Icc 1 Q)
    (g := fun p : ℕ × ℕ ↦ p.1) (fun p hp ↦ by
      obtain ⟨hq, _, _, hQ, _⟩ := mem_pairedEtaMoebiusQuotientBilinearRegion.mp hp
      exact Finset.mem_Icc.mpr ⟨hq, hQ⟩) f
  rw [← hs]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqp, hqQ⟩ := Finset.mem_Icc.mp hq
  apply Finset.sum_bij (fun p _ ↦ p.2)
  · intro p hp
    obtain ⟨hpS, hpq⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, _, hprod, _, hR⟩ := mem_pairedEtaMoebiusQuotientBilinearRegion.mp hpS
    refine Finset.mem_Ioc.mpr ⟨hR, ?_⟩
    apply (Nat.le_div_iff_mul_le hqp).mpr
    simpa only [hpq, Nat.mul_comm] using hprod
  · intro a ha b hb hab
    apply Prod.ext _ hab
    exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
  · intro d hd
    obtain ⟨hdR, hdM⟩ := Finset.mem_Ioc.mp hd
    refine ⟨(q, d), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
    apply mem_pairedEtaMoebiusQuotientBilinearRegion.mpr
    refine ⟨hqp, lt_of_le_of_lt (Nat.zero_le _) hdR, ?_, hqQ, hdR⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hqp).mp hdM
  · intro p hp
    congr 1
    exact Prod.ext (Finset.mem_filter.mp hp).2 rfl

/-- The actual alternating bilinear Möbius sum, with the two arithmetic factors combined into their exact complex product phase. -/
def pairedEtaMoebiusQuotientBilinearSum (rho : NontrivialZetaZero) (M Q : ℕ) : ℂ :=
  ∑ p ∈ pairedEtaMoebiusQuotientBilinearRegion M Q,
    (pairedEtaDirichletSign p.1 : ℂ) * (μ p.2 : ℂ) * ((p.1 * p.2 : ℕ) : ℂ) ^ (-rho.1)

/-- The Möbius prefix difference at each Abel quotient is exactly the original truncated divisor sum; its common lower endpoint lies below the divided upper endpoint. -/
theorem complexMoebiusFinitePrefix_sub_quotient_boundary
    (s : ℂ) (M Q : ℕ) {q : ℕ} (hq : q ∈ Finset.Icc 1 Q) :
    complexMoebiusFinitePrefix s (M / q) - complexMoebiusFinitePrefix s (M / (Q + 1)) =
      ∑ d ∈ Finset.Ioc (M / (Q + 1)) (M / q), (μ d : ℂ) * (d : ℂ) ^ (-s) := by
  have hR : M / (Q + 1) ≤ M / q :=
    Nat.div_le_div_left ((Finset.mem_Icc.mp hq).2.trans (Nat.le_succ Q)) (Finset.mem_Icc.mp hq).1
  have hs : Finset.Icc 1 (M / (Q + 1)) ⊆ Finset.Icc 1 (M / q) :=
    Finset.Icc_subset_Icc le_rfl hR
  have he : Finset.Icc 1 (M / q) \ Finset.Icc 1 (M / (Q + 1)) =
      Finset.Ioc (M / (Q + 1)) (M / q) := by
    ext d
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    have hR0 := Nat.zero_le (M / (Q + 1))
    omega
  rw [complexMoebiusFinitePrefix_eq_sum_Icc, complexMoebiusFinitePrefix_eq_sum_Icc,
    ← he, Finset.sum_sdiff_eq_sub hs]

/-- The complete Abel boundary is absorbed into the bilinear region exactly; neither the bulk nor its boundary is bounded separately. -/
theorem pairedEtaMoebiusQuotientAbel_sub_boundary_eq_bilinear
    (rho : NontrivialZetaZero) (M Q : ℕ) :
    pairedEtaMoebiusQuotientAbelBulk rho M Q - pairedEtaMoebiusQuotientAbelBoundary rho M Q =
      pairedEtaMoebiusQuotientBilinearSum rho M Q := by
  unfold pairedEtaMoebiusQuotientAbelBulk pairedEtaMoebiusQuotientAbelBoundary
    pairedEtaUnpairedDirichletPrefix pairedEtaMoebiusQuotientBilinearSum
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib, sum_pairedEtaMoebiusQuotientBilinearRegion_eq_divided]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_sub, complexMoebiusFinitePrefix_sub_quotient_boundary rho.1 M Q hq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

/-- The entire original complete quotient carrier is one alternating bilinear sum on the actual hyperbola, with its completion and moving cap unchanged. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_bilinear
    (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M D =
      pairedEtaXiCompletionFactor rho.1 * pairedEtaMoebiusQuotientBilinearSum rho M (M / (D + 1)) := by
  rw [pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_abel,
    pairedEtaMoebiusQuotientAbel_sub_boundary_eq_bilinear]

end

end RiemannGaussian
