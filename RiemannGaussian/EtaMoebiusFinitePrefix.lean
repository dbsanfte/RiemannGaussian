import RiemannGaussian.EtaMoebiusDivisor

/-!
# Möbius-weighted finite eta prefixes with exact endpoint corrections

Finite divisor fibers are regrouped by their first factor. The resulting
identity uses the actual eta Dirichlet prefixes at divided cutoffs. Each
prefix is exactly the existing paired polynomial plus its possible odd
last term; neither that term nor its complex phase is discarded.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The eta Dirichlet prefix ending at an arbitrary integer, retaining
an unpaired last term when that endpoint is odd. -/
def pairedEtaUnpairedDirichletPrefix (M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, (pairedEtaDirichletSign n : ℂ) * (n : ℂ) ^ (-s)

/-- One successor adds exactly the original signed Dirichlet term. -/
theorem pairedEtaUnpairedDirichletPrefix_succ (M : ℕ) (s : ℂ) :
    pairedEtaUnpairedDirichletPrefix (M + 1) s = pairedEtaUnpairedDirichletPrefix M s +
      (pairedEtaDirichletSign (M + 1) : ℂ) * ((M + 1 : ℕ) : ℂ) ^ (-s) := by
  unfold pairedEtaUnpairedDirichletPrefix
  exact Finset.sum_Icc_succ_top (by omega) _

/-- At an even endpoint the unpaired definition is exactly the
repository's original paired eta polynomial. -/
theorem pairedEtaUnpairedDirichletPrefix_even (K : ℕ) (s : ℂ) :
    pairedEtaUnpairedDirichletPrefix (2 * K) s = pairedEtaCorePartialSum K s := by
  induction K with
  | zero => simp [pairedEtaUnpairedDirichletPrefix, pairedEtaCorePartialSum]
  | succ K ih =>
    rw [show 2 * (K + 1) = (2 * K + 1) + 1 by omega, pairedEtaUnpairedDirichletPrefix_succ,
      pairedEtaUnpairedDirichletPrefix_succ, ih]
    simp only [pairedEtaCorePartialSum, Finset.sum_range_succ, pairedEtaCoreSummand]
    norm_num [pairedEtaDirichletSign, Nat.even_iff, Nat.add_mod, Nat.mul_mod]
    ring_nf

/-- At an odd endpoint the original paired eta polynomial has exactly
one additional positive Dirichlet term. -/
theorem pairedEtaUnpairedDirichletPrefix_odd (K : ℕ) (s : ℂ) :
    pairedEtaUnpairedDirichletPrefix (2 * K + 1) s = pairedEtaCorePartialSum K s + (2 * K + 1 : ℂ) ^ (-s) := by
  rw [pairedEtaUnpairedDirichletPrefix_succ, pairedEtaUnpairedDirichletPrefix_even]
  norm_num [pairedEtaDirichletSign, Nat.even_iff, Nat.add_mod, Nat.mul_mod]

/-- The exact odd endpoint correction at every divided arithmetic cutoff. -/
theorem pairedEtaUnpairedDirichletPrefix_eq_paired_add_endpoint (M : ℕ) (s : ℂ) :
    pairedEtaUnpairedDirichletPrefix M s = pairedEtaCorePartialSum (M / 2) s +
      if Odd M then (M : ℂ) ^ (-s) else 0 := by
  rcases Nat.mod_two_eq_zero_or_one M with hM | hM
  · have he : M = 2 * (M / 2) := by omega
    rw [he, pairedEtaUnpairedDirichletPrefix_even]
    simp [Nat.odd_iff]
  · have he : M = 2 * (M / 2) + 1 := by omega
    conv_lhs => rw [he]
    rw [pairedEtaUnpairedDirichletPrefix_odd]
    have ho : Odd M := Nat.odd_iff.mpr hM
    rw [if_pos ho]
    congr 2
    exact_mod_cast he.symm

/-- Regrouping finite divisor fibers by their first factor gives exact
divided prefix cutoffs, with no infinite rearrangement. -/
theorem sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix (M : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 M, ∑ p ∈ n.divisorsAntidiagonal, f p.1 p.2) =
      ∑ d ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 (M / d), f d k := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun a _ ↦ (⟨a.2.1, a.2.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨han, hap⟩ := Finset.mem_sigma.mp ha
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hap).1
    obtain ⟨hd, hk⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hap
    have hdp : 0 < a.2.1 := Nat.pos_of_ne_zero hd
    have hkp : 0 < a.2.2 := Nat.pos_of_ne_zero hk
    have hprodle : a.2.1 * a.2.2 ≤ M := by rw [hprod]; exact (Finset.mem_Icc.mp han).2
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨hdp, by nlinarith⟩
    · exact Finset.mem_Icc.mpr ⟨hkp, (Nat.le_div_iff_mul_le hdp).2 (by simpa [mul_comm] using hprodle)⟩
  · intro a ha b hb hab
    have hp : a.2 = b.2 := Prod.ext
      (congrArg (fun x : Σ _ : ℕ, ℕ ↦ x.1) hab) (congrArg (fun x : Σ _ : ℕ, ℕ ↦ x.2) hab)
    have han := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp ha).2).1
    have hbn := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hb).2).1
    have hn : a.1 = b.1 := by rw [← han, ← hbn, hp]
    exact Sigma.ext hn (heq_of_eq hp)
  · intro b hb
    obtain ⟨hbd, hbk⟩ := Finset.mem_sigma.mp hb
    have hd := (Finset.mem_Icc.mp hbd).1
    have hk := (Finset.mem_Icc.mp hbk).1
    have hprodle : b.1 * b.2 ≤ M := by
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hd).1 (Finset.mem_Icc.mp hbk).2
    have hprod : 0 < b.1 * b.2 := Nat.mul_pos hd hk
    refine ⟨⟨b.1 * b.2, (b.1, b.2)⟩, ?_, rfl⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hprod, hprodle⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hprod.ne'⟩⟩
  · intro a ha
    rfl

/-- Möbius-weighted actual finite eta prefixes collapse exactly to the
nonvanishing dyadic factor, with all divided cutoffs and phases retained. -/
theorem sum_moebius_mul_pairedEtaUnpairedDirichletPrefix (s : ℂ) {M : ℕ} (hM : 2 ≤ M) :
    (∑ d ∈ Finset.Icc 1 M, (μ d : ℂ) * (d : ℂ) ^ (-s) * pairedEtaUnpairedDirichletPrefix (M / d) s) =
      1 - 2 * (2 : ℂ) ^ (-s) := by
  simp only [pairedEtaUnpairedDirichletPrefix, Finset.mul_sum]
  rw [← sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix]
  exact sum_Icc_moebius_mul_pairedEtaDirichletTerm s hM

/-- The same finite multiplicative identity uses the repository's
original paired eta polynomials and explicit odd endpoint corrections. -/
theorem sum_moebius_mul_pairedEtaCorePartialSum_add_endpoint (s : ℂ) {M : ℕ} (hM : 2 ≤ M) :
    (∑ d ∈ Finset.Icc 1 M, (μ d : ℂ) * (d : ℂ) ^ (-s) *
      (pairedEtaCorePartialSum ((M / d) / 2) s + if Odd (M / d) then ((M / d : ℕ) : ℂ) ^ (-s) else 0)) =
        1 - 2 * (2 : ℂ) ^ (-s) := by
  simpa only [pairedEtaUnpairedDirichletPrefix_eq_paired_add_endpoint] using
    sum_moebius_mul_pairedEtaUnpairedDirichletPrefix s hM

end

end RiemannGaussian
