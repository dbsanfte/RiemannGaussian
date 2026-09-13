/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ConsecutiveBlockPacking
import RiemannGaussian.External.Zeta23BlockSpectrum
import RiemannGaussian.External.Zeta23InverseSamplingEndgame

/-!
# Arbitrary consecutive blocks in the literal zeta counting argument

These theorems place complete blocks of every fixed size inside the actual
simple-zero sampling Gram. They retain the full within-block energy and
charge the exact padding and span costs before taking asymptotic limits.
-/

namespace RiemannGaussian.Zeta23InverseSampling
noncomputable section
open RHLinalg
open scoped BigOperators

/-- The actual simple-zero Gram reindexed into arbitrary finite blocks
after adjoining explicitly zero columns. -/
def zetaSimpleBlockGram {Z : Zeta23.ZeroConfig} {T : ℝ} {P : Zeta23.Params}
    {γ β κ : Type*} (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (e : γ × β ≃ Sum (Zeta23.ZeroSide.blockData Z T P hconj).S₁ κ) :
    Matrix (γ × β) (γ × β) ℂ :=
  ZeroBlockData.columnGram (ZeroBlockData.paddedBlockFamily e
    (ZeroBlockData.simpleVhat (Zeta23.ZeroSide.blockData Z T P hconj)
      (P.a T * P.L T ^ 2)))

/-- Selected actual-zero columns are unchanged by reindexing and zero
padding, including their complex entries. -/
theorem zetaSimpleBlockGram_apply_of_inl
    {Z : Zeta23.ZeroConfig} {T : ℝ} {P : Zeta23.Params} {γ β κ : Type*}
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (e : γ × β ≃ Sum (Zeta23.ZeroSide.blockData Z T P hconj).S₁ κ)
    (p p' : γ × β) (z z' : (Zeta23.ZeroSide.blockData Z T P hconj).S₁)
    (hp : e p = Sum.inl z) (hp' : e p' = Sum.inl z') :
    zetaSimpleBlockGram hconj e p p' = zetaSimpleGram Z T P hconj z z' := by
  classical
  unfold zetaSimpleBlockGram zetaSimpleGram
  unfold ZeroBlockData.columnGram ZeroBlockData.simpleGram
  rw [Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.conjTranspose_apply,
    Zeta23.ZeroSide.RankTraceMult.Wmat, RCLike.star_def,
    ZeroBlockData.paddedBlockFamily, hp, hp', Sum.elim_inl]

/-- The literal finite zero side pays unit-capped energies for blocks of
any finite size, with exactly one unit per zero padding column. -/
theorem hatAz_mult2_blockCertificate
    {Z : Zeta23.ZeroConfig} {T : ℝ} {P : Zeta23.Params}
    {γ β κ : Type*} [Fintype γ] [DecidableEq γ]
    [Fintype β] [DecidableEq β] [Fintype κ]
    (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hreal : Zeta23.ZeroSide.PhiHatReal T P)
    (hPois : Zeta23.ZeroSide.PoissonSq T P)
    (hc : 0 < P.a T * P.L T ^ 2)
    (e : γ × β ≃ Sum (Zeta23.ZeroSide.blockData Z T P hconj).S₁ κ) :
    4 * rtrace (P.hat T (Z.Az P T)) -
        frobSq (P.hat T (Z.Az P T)) - 2 * (Z.NIprime T : ℝ) +
        (∑ b, min (ZeroBlockData.offDiagEnergy
          ((zetaSimpleBlockGram hconj e).submatrix
            (fun j : γ => (j, b)) (fun j : γ => (j, b)))) 1) ≤
      (Z.s1 T : ℝ) + Fintype.card κ := by
  classical
  have hzero := hatAz_mult2_retained Z T P hconj hreal hPois hc
  have hpack := ZeroBlockData.packedBlockEnergy_le_originalDefect_add_padding
    (ZeroBlockData.simpleVhat (Zeta23.ZeroSide.blockData Z T P hconj)
      (P.a T * P.L T ^ 2)) e
  change (∑ b, min (ZeroBlockData.offDiagEnergy
    ((zetaSimpleBlockGram hconj e).submatrix
      (fun j : γ => (j, b)) (fun j : γ => (j, b)))) 1) ≤
      (∑ z, ZeroBlockData.simpleDefect
        ((zetaSimpleGram_posSemidef Z T P hconj).1.eigenvalues z)) +
          Fintype.card κ at hpack
  linarith

/-- The matrix perturbation and endpoint collars preserve the arbitrary
block improvement through the finite prime-side counting inequality. -/
theorem seamA_mult2_blockCertificate
    {Z : Zeta23.ZeroConfig} {T : ℝ} {P : Zeta23.Params}
    {γ β κ : Type*} [Fintype γ] [DecidableEq γ]
    [Fintype β] [DecidableEq β] [Fintype κ]
    (hT : 0 ≤ T) (hconj : Zeta23.ZeroSide.PhiHatConj T P)
    (hreal : Zeta23.ZeroSide.PhiHatReal T P)
    (hPois : Zeta23.ZeroSide.PoissonSq T P)
    {θ₀ : ℝ} (hTl : Zeta23.Assembly.TailInputs Z P T θ₀)
    (ha : 0 < P.a T) (hL : 0 < P.L T)
    (e : γ × β ≃ Sum (Zeta23.ZeroSide.blockData Z T P hconj).S₁ κ) :
    4 * rtrace (P.hat T (Z.Gz P T)) -
        frobSq (P.hat T (Z.Gz P T)) -
        2 * (Z.N T (2 * T) : ℝ) - 3 * (Zeta23.Assembly.NII Z T : ℝ) -
        θ₀ / (P.a T * P.L T) *
          (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) +
            θ₀ / (P.a T * P.L T)) +
        (∑ b, min (ZeroBlockData.offDiagEnergy
          ((zetaSimpleBlockGram hconj e).submatrix
            (fun j : γ => (j, b)) (fun j : γ => (j, b)))) 1) ≤
      (Z.N0s T (2 * T) : ℝ) + Fintype.card κ := by
  obtain ⟨Bc, hBc0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) =
      P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← Zeta23.Assembly.hat_add]
    congr 1
    simp [Zeta23.ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) :=
    div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := hatAz_mult2_blockCertificate hconj hreal hPois (by positivity) e
  have hpert := Zeta23.Assembly.ctr_sub_frobSq_perturb
    4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
      (hfrE.trans (pow_le_pow_left₀ hBc0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤
      (Z.N0s T (2 * T) : ℝ) + (Zeta23.Assembly.NII Z T : ℝ) := by
    exact_mod_cast Zeta23.Assembly.s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) =
      (Z.N T (2 * T) : ℝ) + (Zeta23.Assembly.NII Z T : ℝ) := by
    exact_mod_cast Zeta23.Assembly.NIprime_eq Z hT
  rw [hNI] at hcore
  linarith

/-- Actual interior simple zeros have consecutive blocks of every size.
The span cost is averaged over every shift, and all omitted and padding
columns are counted explicitly. -/
theorem exists_literalInteriorBlockPacking
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} {T : ℝ}
    (hT : 4 ≤ T) (hconj : Zeta23.ZeroSide.PhiHatConj T P) (k : ℕ) :
    let α := (Zeta23.ZeroSide.blockData Z T P hconj).S₁
    let s := interiorSimpleZeros Z P T hconj
    let Q := (Fintype.card α + k) / (k + 1)
    let pad := (k + 1) * Q - Fintype.card α
    ∃ q : ℕ, ∃ f : Fin (k + 1) × Fin q ↪ α,
      ∃ e : Fin (k + 1) × Fin Q ≃ Sum α (Fin pad), ∃ hqQ : q ≤ Q,
        (∀ p, f p ∈ s) ∧
        (∀ b : Fin q, Monotone (fun j => simpleZeroOrdinate (f (j, b)))) ∧
        (k + 1 : ℕ) * (∑ b : Fin q,
          (simpleZeroOrdinate (f (Fin.last k, b)) -
            simpleZeroOrdinate (f (0, b)))) ≤ (k : ℝ) * T ∧
        s.card ≤ (k + 1) * q + 2 * k ∧ pad ≤ k ∧
        ∀ j b, e (j, Fin.castLE hqQ b) = Sum.inl (f (j, b)) := by
  classical
  let α := (Zeta23.ZeroSide.blockData Z T P hconj).S₁
  let ord : α → ℝ := simpleZeroOrdinate
  let s := interiorSimpleZeros Z P T hconj
  have hord : Monotone ord := fun _ _ hab => hab
  have hlohi : T + Real.sqrt T ≤ 2 * T - Real.sqrt T := by
    nlinarith [Real.sq_sqrt (show 0 ≤ T by linarith),
      sq_nonneg (Real.sqrt T - 2)]
  have hbounds : ∀ z ∈ s,
      T + Real.sqrt T ≤ ord z ∧ ord z ≤ 2 * T - Real.sqrt T :=
    fun _ hz => mem_interiorSimpleZeros_iff.mp hz
  obtain ⟨r, hspan⟩ := ConsecutiveBlockPacking.exists_orderEmbedding_span_le
    s ord hord k hlohi hbounds
  let q := ConsecutiveBlockPacking.count s.card k r
  let f : Fin (k + 1) × Fin q ↪ α := ConsecutiveBlockPacking.orderEmbedding s k r
  have hqQ : q ≤ (Fintype.card α + k) / (k + 1) :=
    ConsecutiveBlockPacking.count_le_ceiling interiorCard_le_fullCard
  obtain ⟨e, he⟩ := ConsecutiveBlockPacking.exists_paddedEquiv_extending k q hqQ f
  refine ⟨q, f, e, hqQ, ?_, ?_, ?_, ?_, (ConsecutiveBlockPacking.ceiling_bounds _ _).2, he⟩
  · intro p
    exact ConsecutiveBlockPacking.orderEmbedding_mem s k r p
  · intro b i j hij
    exact ConsecutiveBlockPacking.orderEmbedding_monotone s k r b hij
  · exact hspan.trans (mul_le_mul_of_nonneg_left
      (by linarith [Real.sqrt_nonneg T]) (Nat.cast_nonneg k))
  · exact ConsecutiveBlockPacking.count_coverage s.card k r

/-- Entrywise endpoint approximation controls the complete correlation
energy of any fixed-size block. The explicit quadratic dimension factor
vanishes with the sampler error once the block size is fixed. -/
theorem lagEnergy_le_offDiagEnergy_add_error
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) (x : ℕ → ℝ) {e : ℝ}
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hclose : ∀ i j : Fin n,
      ‖K i j - (montgomeryTaylorKernel (x j - x i) : ℂ)‖ ≤ e) :
    MontgomeryTaylorWindowEnergy.lagEnergy (fun t => montgomeryTaylorKernel t ^ 2) x n ≤
      ZeroBlockData.offDiagEnergy K + 6 * e * (n : ℝ) ^ 2 := by
  classical
  have hpairs :
      MontgomeryTaylorWindowEnergy.lagEnergy (fun t => montgomeryTaylorKernel t ^ 2) x n =
        ∑ i : Fin n, ∑ j : Fin n,
          if i = j then 0 else montgomeryTaylorKernel (x j - x i) ^ 2 := by
    rw [MontgomeryTaylorWindowEnergy.lagEnergy_eq_orderedPairs _
      (fun t => by rw [montgomeryTaylorKernel_neg])]
    simp only [← Fin.val_inj]
    symm
    calc
      _ = ∑ i : Fin n, ∑ j ∈ Finset.range n,
          if (i : ℕ) = j then 0 else montgomeryTaylorKernel (x j - x i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact Fin.sum_univ_eq_sum_range
          (fun j => if (i : ℕ) = j then 0 else montgomeryTaylorKernel (x j - x i) ^ 2) n
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun i => ∑ j ∈ Finset.range n,
          if i = j then 0 else montgomeryTaylorKernel (x j - x i) ^ 2) n
  rw [hpairs, ZeroBlockData.offDiagEnergy_eq_sum_ite]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      (fun j _ => show
        (if i = j then 0 else montgomeryTaylorKernel (x j - x i) ^ 2) ≤
          (if i = j then 0 else ‖K i j‖ ^ 2) + 6 * e from by
        by_cases hij : i = j
        · simp only [hij, ite_true, zero_add]
          positivity
        · simp only [hij, ite_false]
          linarith [sq_norm_ge_sq_sub_six_mul he0 he1
            (abs_montgomeryTaylorKernel_le_twelve_elevenths (x j - x i)) (hclose i j)]))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith

/-- A uniform affine floor for the complete endpoint-kernel energy passes
to consecutive blocks of literal simple zeros. Every coefficient of the
finite approximation, span and padding error is displayed. -/
theorem exists_literalBlockEnergy_affine_lower
    {Z : Zeta23.ZeroConfig} {P : Zeta23.Params} (hP : P.Valid)
    (hlam : P.lam = 1) {T : ℝ} (hT : 4 ≤ T)
    (h8 : 8 * P.w ≤ P.L T) (h4pi : 4 * Real.pi * P.w ≤ P.L T)
    (hgrid : 2 * Real.pi / P.L T ≤ Real.sqrt T / 2)
    (hconj : Zeta23.ZeroSide.PhiHatConj T (P.atD T)) (k : ℕ)
    {A B : ℝ} (hB0 : 0 < B) (hA1 : A ≤ 1)
    (hcert : ∀ x : ℕ → ℝ, Monotone x →
      A ≤ MontgomeryTaylorWindowEnergy.lagEnergy
        (fun t => montgomeryTaylorKernel t ^ 2) x (k + 1) + B * (x k - x 0))
    (herr1 : endpointSamplerError P T ≤ 1) :
    let α := (Zeta23.ZeroSide.blockData Z T (P.atD T) hconj).S₁
    let Q := (Fintype.card α + k) / (k + 1)
    let pad := (k + 1) * Q - Fintype.card α
    ∃ q : ℕ, ∃ e : Fin (k + 1) × Fin Q ≃ Sum α (Fin pad),
      q ≤ Q ∧
      (interiorSimpleZeros Z (P.atD T) T hconj).card ≤ (k + 1) * q + 2 * k ∧
      pad ≤ k ∧
      A * (q : ℝ) ≤
        (∑ b : Fin Q, min (ZeroBlockData.offDiagEnergy
          ((zetaSimpleBlockGram hconj e).submatrix
            (fun j : Fin (k + 1) => (j, b))
            (fun j : Fin (k + 1) => (j, b)))) 1) +
          ((k : ℝ) * B * P.L T * T) / (k + 1 : ℕ) +
          6 * (k + 1 : ℕ) ^ 2 * endpointSamplerError P T * (q : ℝ) := by
  classical
  have hTpos : 0 < T := by linarith
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have herr0 := endpointSamplerError_nonneg hP h8 h4pi hTpos
  obtain ⟨q, f, e, hqQ, hmem, hord, hspan, hcard, hpad, he⟩ :=
    exists_literalInteriorBlockPacking (Z := Z) (P := P.atD T) hT hconj k
  let Q := (Fintype.card (Zeta23.ZeroSide.blockData Z T (P.atD T) hconj).S₁ + k) /
    (k + 1)
  let packed := zetaSimpleBlockGram hconj e
  let E : Fin Q → ℝ := fun b => min (ZeroBlockData.offDiagEnergy
    (packed.submatrix (fun j : Fin (k + 1) => (j, b))
      (fun j : Fin (k + 1) => (j, b)))) 1
  let cap : ℕ → Fin (k + 1) := fun n => ⟨min n k, by omega⟩
  have hcap : ∀ j : Fin (k + 1), cap j = j := by
    intro j
    apply Fin.ext
    exact Nat.min_eq_left (Nat.le_of_lt_succ j.isLt)
  have hper : ∀ b : Fin q,
      A ≤ E (Fin.castLE hqQ b) +
        B * (P.L T * (simpleZeroOrdinate (f (Fin.last k, b)) -
          simpleZeroOrdinate (f (0, b)))) +
        6 * (k + 1 : ℕ) ^ 2 * endpointSamplerError P T := by
    intro b
    let x : ℕ → ℝ := fun j => P.L T * simpleZeroOrdinate (f (cap j, b))
    let K : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
      packed.submatrix (fun j => (j, Fin.castLE hqQ b))
        (fun j => (j, Fin.castLE hqQ b))
    have hx : Monotone x := by
      intro i j hij
      apply mul_le_mul_of_nonneg_left _ hL.le
      apply hord b
      exact Fin.mk_le_mk.mpr (min_le_min hij le_rfl)
    have hxj : ∀ j : Fin (k + 1), x j = P.L T * simpleZeroOrdinate (f (j, b)) := by
      intro j
      simp only [x, hcap]
    have hclose : ∀ i j : Fin (k + 1),
        ‖K i j - (montgomeryTaylorKernel (x j - x i) : ℂ)‖ ≤
          endpointSamplerError P T := by
      intro i j
      have hi := mem_interiorSimpleZeros_iff.mp (hmem (i, b))
      have hj := mem_interiorSimpleZeros_iff.mp (hmem (j, b))
      have hraw := atD_zetaSimpleGram_apply_close_montgomeryTaylorKernel
        hP hlam h8 h4pi hTpos hgrid (f (i, b)) (f (j, b)) hi.1 hi.2 hj.1 hj.2
      change ‖packed (i, Fin.castLE hqQ b) (j, Fin.castLE hqQ b) - _‖ ≤ _
      dsimp only [packed]
      rw [zetaSimpleBlockGram_apply_of_inl hconj e _ _ _ _ (he i b) (he j b)]
      have hsign : P.L T *
          (simpleZeroOrdinate (f (i, b)) - simpleZeroOrdinate (f (j, b))) =
            -(x j - x i) := by rw [hxj, hxj]; ring
      change ‖zetaSimpleGram Z T (P.atD T) hconj (f (i, b)) (f (j, b)) -
        (montgomeryTaylorKernel (P.L T *
          (simpleZeroOrdinate (f (i, b)) - simpleZeroOrdinate (f (j, b)))) : ℂ)‖ ≤
          endpointSamplerError P T at hraw
      rw [hsign, montgomeryTaylorKernel_neg] at hraw
      exact hraw
    have hstable := lagEnergy_le_offDiagEnergy_add_error K x herr0 herr1 hclose
    have hcost0 : 0 ≤ B * (x k - x 0) :=
      mul_nonneg hB0.le (sub_nonneg.mpr (hx (Nat.zero_le k)))
    have hcapEnergy := affine_le_min_energy_add_cost
      (energy := ZeroBlockData.offDiagEnergy K) hA1 hcost0
      (show 0 ≤ 6 * endpointSamplerError P T * (k + 1 : ℕ) ^ 2 by positivity)
      (hcert x hx) (by linarith [hstable])
    have hxlast := hxj (Fin.last k)
    have hxzero := hxj 0
    simp only [Fin.val_last, Fin.val_zero] at hxlast hxzero
    change A ≤ min (ZeroBlockData.offDiagEnergy K) 1 + _ + _
    rw [hxlast, hxzero] at hcapEnergy
    convert hcapEnergy using 1
    ring
  have hselected := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q)))
    (fun b _ => hper b)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hselected
  have hE0 : ∀ b : Fin Q, 0 ≤ E b := by
    intro b
    apply le_min _ zero_le_one
    unfold ZeroBlockData.offDiagEnergy
    positivity
  have hselectedFull : (∑ b : Fin q, E (Fin.castLE hqQ b)) ≤ ∑ b : Fin Q, E b := by
    let emb : Fin q ↪ Fin Q := Fin.castLEEmb hqQ
    calc
      _ = ∑ b ∈ Finset.univ.map emb, E b := by rw [Finset.sum_map]; rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun b _ _ => hE0 b)
  have hspanCost :
      (∑ b : Fin q, B * (P.L T * (simpleZeroOrdinate (f (Fin.last k, b)) -
        simpleZeroOrdinate (f (0, b))))) ≤
          ((k : ℝ) * B * P.L T * T) / (k + 1 : ℕ) := by
    simp_rw [← mul_assoc]
    rw [← Finset.mul_sum, le_div_iff₀ (by positivity : (0 : ℝ) < (k + 1 : ℕ))]
    nlinarith [mul_le_mul_of_nonneg_left hspan (mul_nonneg hB0.le hL.le)]
  refine ⟨q, e, hqQ, hcard, hpad, ?_⟩
  change A * (q : ℝ) ≤ (∑ b : Fin Q, E b) + _ + _
  nlinarith

end
end RiemannGaussian.Zeta23InverseSampling
