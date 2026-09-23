/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovLiteratureStep
import RiemannGaussian.VinogradovResidueMonotone
import RiemannGaussian.VinogradovDiagonalMoment
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Backward mixed-system estimates with the conditioning cost retained

These are the count-level steps of the backward iteration in Ford,
arXiv:1910.08209v1, proof of Lemma 3.4 and the subsequent shrinking-tuple
variant. The quotient endpoint is compared by a proved injection, and
conditioning retains the exponent from the modular count instead of
weakening it to the larger displayed one-step coefficient. Prime packets,
endpoint sizes and any subsequent bound are explicit premises.
-/

namespace RiemannGaussian.VinogradovLiteratureIteration
noncomputable section
open scoped BigOperators Classical
open Polynomial VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovPolynomialNonsingular VinogradovTypeMaximum VinogradovMixedMoments
open VinogradovMixedDifferencing VinogradovNonsingularDescent VinogradovMeanValue
open VinogradovLiteratureStep VinogradovResidueMonotone

/-- The prime exponent actually paid by the low-degree tail and modular fibre count. -/
def conditioningExponent (d r s : ℕ) : ℕ :=
  2 * s - d + (r - d) * (r - d - 1) / 2

/-- The exact conditioning exponent in ordinary real arithmetic. The
triangular depth term remains visible when auditing the scale recurrence. -/
theorem conditioningExponent_cast {d r s : ℕ} (hds : d ≤ 2 * s) (hdr : d ≤ r) :
    (conditioningExponent d r s : ℝ) =
      2 * (s : ℝ) + ((r : ℝ) ^ 2 - r - 2 * r * d + (d : ℝ) ^ 2 - d) / 2 := by
  have ht (a : ℕ) : 2 * (a.choose 2 : ℝ) = (a : ℝ) * ((a : ℝ) - 1) := by
    cases a with
    | zero => norm_num
    | succ a =>
      have h := VinogradovDiagonalExponent.twice_choose_two (a + 1)
      simp only [Nat.add_sub_cancel] at h
      have hh : (2 : ℝ) * ((a + 1).choose 2 : ℝ) = ((a : ℝ) + 1) * a := by exact_mod_cast h
      push_cast
      nlinarith only [hh]
  have he := ht (r - d)
  rw [Nat.cast_sub hdr] at he
  simp only [conditioningExponent, ← Nat.choose_two_right, Nat.cast_add,
    Nat.cast_sub hds, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [he]

/-- Exact real endpoints pass to the integer quotient with no inflation.
This supplies the cutoff premise for the paper's real prime scales. -/
theorem quotient_floor_le {X M : ℝ} {p : ℕ} (hX : 0 ≤ X) (hM : 0 < M)
    (hp : M ≤ (p : ℝ)) : ⌊X⌋₊ / p ≤ ⌊X / M⌋₊ := by
  rw [← Nat.floor_div_natCast]
  exact Nat.floor_mono (div_le_div_of_nonneg_left hX hM hp)

/-- Substituting the displayed Bellotti 2.3 scale into the exponent
obtained from our current sharp conditioning cost leaves this exact
triangular residual. This audits this particular backward normalization;
it neither assumes nor disproves the published final moment bound. -/
theorem published_scale_balance {k d r s : ℕ} (hds : d ≤ 2 * s) (hdr : d ≤ r)
    (hdk : d < k) (hr : 0 < r) (delta psi : ℝ) :
    let lambda := 2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + delta
    let phi := 1 / (2 * (r : ℝ)) +
      ((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r - 2 * delta - 2 * r * d) /
        (4 * r * ((k : ℝ) - d)) * psi
    1 / 2 - r * phi + ((conditioningExponent d r s : ℝ) - lambda) /
      (2 * ((k : ℝ) - d)) * psi =
      (d : ℝ) * ((d : ℝ) - 1) * psi / (4 * ((k : ℝ) - d)) := by
  dsimp only
  rw [conditioningExponent_cast hds hdr]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hkd : (k : ℝ) - d ≠ 0 := by
    have h : (d : ℝ) < k := by exact_mod_cast hdk
    linarith
  field_simp [hr0, hkd]
  ring

/-- Beyond the first depth, the residual in this normalization is
strictly positive; it cannot silently be replaced by zero. -/
theorem published_scale_residual_pos {k d : ℕ} (hd : 2 ≤ d) (hdk : d < k)
    {psi : ℝ} (hpsi : 0 < psi) :
    0 < (d : ℝ) * ((d : ℝ) - 1) * psi / (4 * ((k : ℝ) - d)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdkR : (d : ℝ) < k := by exact_mod_cast hdk
  apply div_pos
  · exact mul_pos (mul_pos (by linarith) (by linarith)) hpsi
  · linarith

/-- No numerical factor is lost when the literal dilated tail is enlarged. -/
theorem monomial_residue_mono {m d P p q r Q Q' s : ℕ} (hp : 0 < p)
    (F : Fin m → ℤ[X]) (hQ : Q ≤ Q') :
    residueMixedMoment m s P (p ^ r) (pow_pos hp r)
      (fullFrequency d F) (monomialTail m d p q Q) ≤
    residueMixedMoment m s P (p ^ r) (pow_pos hp r)
      (fullFrequency d F) (monomialTail m d p q Q') := by
  let u : ℕ → (Fin d ⊕ Fin m) → ℤ := fun n =>
    Sum.elim (fun i => (((p * q : ℕ) : ℤ) * (n : ℤ)) ^ (i.val + 1))
      (fun i => (((p * q : ℕ) : ℤ) * (n : ℤ)) ^ (d + i.val + 1))
  have he (A : ℕ) : (fun x : Fin A => u (x.val + 1)) = monomialTail m d p q A := by
    funext x i
    cases i <;> simp [u, monomialTail]
  have h := residueMixedMoment_mono m s P (p ^ r) (pow_pos hp r) (fullFrequency d F) u hQ
  rw [he Q, he Q'] at h
  exact h

/-- Conditioning reaches the prescribed next endpoint with the exact
factorial cost and the original prime exponent. The integer quotient
comparison is explicit and costs one. -/
theorem exists_conditioning_at_endpoint {m d T e P s M U r Q Q' q : ℕ}
    {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P) (hMdeg : d + m ≤ M)
    (hT0 : 0 < T) (hT : T ≤ P ^ d) (π : Finset ℕ)
    (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ U)
    (hbudget : P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p)
    (hr1 : 1 ≤ r) (hr : r ≤ d + m) (hds : d ≤ s) (hs : 1 ≤ s)
    (hq : 0 < q) (hQ : 16 * s ^ 2 * U ≤ Q)
    (hnext : ∀ p : ℕ, M < p → p ≤ U → Q / p ≤ Q') :
    ∃ (e' p : ℕ) (hp : p.Prime) (G : Fin m → ℤ[X]),
      HasType G d T e' ∧ M < p ∧ p ≤ U ∧ ¬p ∣ T ∧
      (typeCount d P s F (monomialTail m d 1 q Q) : ℝ) ≤
        ((4 * π.card * d.factorial * m.factorial : ℕ) : ℝ) *
          (p : ℝ) ^ conditioningExponent d r s *
          residueMixedMoment m s P (p ^ r) (pow_pos hp.pos r)
            (fullFrequency d G) (monomialTail m d p q Q') := by
  obtain ⟨e', p, xi, hp, G, hG, hpM, hpU, hpT, _hxi, hb⟩ :=
    VinogradovUnrestrictedConditioning.exists_conditioning_of_packet hF hm hP hMdeg
      hT0 hT π hπ hbudget hr1 hr hds hs hq hQ
  refine ⟨e', p, hp, G, hG, hpM, hpU, hpT, ?_⟩
  have hc : (((4 * π.card * d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) *
      ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ)) =
      ((4 * π.card * d.factorial * m.factorial : ℕ) : ℝ) *
        (p : ℝ) ^ conditioningExponent d r s := by
    simp only [conditioningExponent, Nat.cast_mul, Nat.cast_pow, pow_add]
    ring
  rw [hc] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (monomial_residue_mono hp.pos G (hnext p hpM hpU)) (by positivity))

/-- A uniform next residue bound yields a numerical bound on the actual
current count. There is no assumed estimate on an intervening `K`. -/
theorem typeCount_le_of_residue_bound {m d T e P s M U r Q Q' q : ℕ} {B : ℝ}
    {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P) (hMdeg : d + m ≤ M)
    (hT0 : 0 < T) (hT : T ≤ P ^ d) (π : Finset ℕ)
    (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ U)
    (hbudget : P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p)
    (hr1 : 1 ≤ r) (hr : r ≤ d + m) (hds : d ≤ s) (hs : 1 ≤ s)
    (hq : 0 < q) (hQ : 16 * s ^ 2 * U ≤ Q)
    (hnext : ∀ p : ℕ, M < p → p ≤ U → Q / p ≤ Q')
    (hbound : ∀ (e' p : ℕ) (hp : p.Prime) (G : Fin m → ℤ[X]),
      HasType G d T e' → M < p → p ≤ U →
      residueMixedMoment m s P (p ^ r) (pow_pos hp.pos r)
        (fullFrequency d G) (monomialTail m d p q Q') ≤ B) :
    (typeCount d P s F (monomialTail m d 1 q Q) : ℝ) ≤
      ((4 * π.card * d.factorial * m.factorial : ℕ) : ℝ) *
        (U : ℝ) ^ conditioningExponent d r s * B := by
  obtain ⟨e', p, hp, G, hG, hpM, hpU, _hpT, hb⟩ :=
    exists_conditioning_at_endpoint hF hm hP hMdeg hT0 hT π hπ hbudget
      hr1 hr hds hs hq hQ hnext
  apply hb.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hpU) _) (by positivity)
  · exact hbound e' p hp G hG hpM hpU
  · apply MeasureTheory.integral_nonneg
    intro theta
    exact mul_nonneg (pow_nonneg (VinogradovDifferenceEnergy.residueEnergy_nonneg _ _ _ _ _) _)
      (pow_nonneg (norm_nonneg _) _)
  · positivity

/-- The literal backward `L -> K -> L` step, with its complete numerical
cost. The premise is only on the next residue moment; the intermediate
type, prime choice, quotient cutoff and both branches are proved here. -/
theorem backward_step_of_packet {m d T e P s M U r Q Q' p q : ℕ} {B : ℝ}
    {F : Fin (m + 1) → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P) (hMdeg : d + 1 + m ≤ M)
    (hT0 : 0 < T) (hT : T ≤ P ^ d) (π : Finset ℕ)
    (hπ : ∀ p' ∈ π, p'.Prime ∧ M < p' ∧ p' ≤ U)
    (hbudget : P ^ (d + 1 + 2 * m.choose 2) < ∏ p' ∈ π, p')
    (hr1 : 1 ≤ r) (hr : r ≤ d + 1 + m) (hds : d + 1 ≤ s) (hs : 1 ≤ s)
    (hp : 0 < p) (hq : 0 < q) (hQ : 16 * s ^ 2 * U ≤ Q)
    (hnext : ∀ p' : ℕ, M < p' → p' ≤ U → Q / p' ≤ Q')
    (hbound : ∀ (T' e' p' q' : ℕ) (hp' : p'.Prime) (G : Fin m → ℤ[X]),
      0 < T' → T' ≤ P ^ (d + 1) → HasType G (d + 1) T' e' →
      M < p' → p' ≤ U → 0 < q' →
      residueMixedMoment m s P (p' ^ r) (pow_pos hp'.pos r)
        (fullFrequency (d + 1) G) (monomialTail m (d + 1) p' q' Q') ≤ B) :
    residueMixedMoment (m + 1) s P (p ^ r) (pow_pos hp r)
      (fullFrequency d F) (monomialTail (m + 1) d p q Q) ≤
      (2 * (P : ℝ)) ^ (m + 1) *
        max (((d + (m + 1) : ℕ) : ℝ) ^ (m + 1) * meanValue s (d + (m + 1)) Q)
          ((2 / (p : ℝ) ^ (r * (m + 1))) *
            meanValue s (d + (m + 1)) Q ^ (((m : ℝ) - 1) / (2 * (m : ℝ))) *
            (((4 * π.card * (d + 1).factorial * m.factorial : ℕ) : ℝ) *
              (U : ℝ) ^ conditioningExponent (d + 1) r s * B) ^
                (((m : ℝ) + 1) / (2 * (m : ℝ)))) := by
  have hPpos : 1 ≤ P := by
    have hmpos : 0 < 4 * m ^ 4 := by positivity
    omega
  obtain ⟨T', G, hlo, hhi, hG, hb⟩ :=
    exists_difference_step (by omega) hF s P Q p q r hp hq hPpos
  have hT' : T' ≤ P ^ (d + 1) := by
    rw [pow_succ, mul_comm]
    exact hhi.trans (Nat.mul_le_mul_left P hT)
  have hT'0 : 0 < T' := lt_of_lt_of_le hT0 hlo
  have hcount := typeCount_le_of_residue_bound hG hm hP hMdeg hT'0 hT' π hπ hbudget
    hr1 hr hds hs (Nat.mul_pos hp hq) hQ hnext
    (fun e' p' hp' H hH hpM hpU =>
      hbound T' e' p' (p * q) hp' H hT'0 hT' hH hpM hpU (Nat.mul_pos hp hq))
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply max_le_max le_rfl
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow (Nat.cast_nonneg _) hcount (by positivity)
  · exact mul_nonneg (by positivity)
      (Real.rpow_nonneg (MeasureTheory.integral_nonneg (fun _ => by positivity)) _)

/-- The finite backward allowance. The terminal stage is the exact
diagonal cost; every earlier stage retains both branches and all prime
packet costs. It contains no unknown mixed count. -/
def backwardAllowance (k b P s r : ℕ) (M U : ℕ → ℕ) (π : ℕ → Finset ℕ)
    (J : ℕ → ℝ) : ℕ → ℕ → ℝ
  | d, 0 => (P : ℝ) ^ b * J d
  | d, n + 1 =>
      (2 * (P : ℝ)) ^ (b + n + 1) *
        max ((k : ℝ) ^ (b + n + 1) * J d)
          ((2 / ((M d + 1 : ℕ) : ℝ) ^ (r * (b + n + 1))) *
              J d ^ ((((b + n : ℕ) : ℝ) - 1) / (2 * ((b + n : ℕ) : ℝ))) *
              (((4 * (π (d + 1)).card * (d + 1).factorial * (b + n).factorial : ℕ) : ℝ) *
                (U (d + 1) : ℝ) ^ conditioningExponent (d + 1) r s *
                backwardAllowance k b P s r M U π J (d + 1) n) ^
                  ((((b + n : ℕ) : ℝ) + 1) / (2 * ((b + n : ℕ) : ℝ))))

/-- Every finite allowance is nonnegative when its source moments are. -/
theorem backwardAllowance_nonneg (k b P s r : ℕ) (M U : ℕ → ℕ)
    (π : ℕ → Finset ℕ) (J : ℕ → ℝ) (hJ : ∀ d, 0 ≤ J d) (d n : ℕ) :
    0 ≤ backwardAllowance k b P s r M U π J d n := by
  induction n generalizing d with
  | zero => exact mul_nonneg (by positivity) (hJ d)
  | succ n _ih =>
    rw [backwardAllowance]
    apply mul_nonneg (by positivity)
    exact le_max_of_le_left (mul_nonneg (by positivity) (hJ d))

/-- A finite backward induction bounds every actual residue mixed moment
from ordinary source-moment bounds and finite prime packets. The base is
proved diagonal, so no unproved mixed estimate is supplied to the induction.
The remaining literature task is to instantiate the scales and simplify
this explicit allowance to the published coefficient and exponent. -/
theorem iterated_residue_bound (k b P s r : ℕ) (M U Q : ℕ → ℕ)
    (π : ℕ → Finset ℕ) (J : ℕ → ℝ)
    (hb : 2 ≤ b) (hP : 4 * k ^ 4 ≤ P) (hs : k ≤ s)
    (hr1 : 1 ≤ r) (hr : r ≤ k)
    (hMdeg : ∀ d ≤ k, k ≤ M d)
    (hπ : ∀ d ≤ k, ∀ p ∈ π d, p.Prime ∧ M d < p ∧ p ≤ U d)
    (hbudget : ∀ d ≤ k, P ^ (d + 2 * (k - d).choose 2) < ∏ p ∈ π d, p)
    (hQ : ∀ d < k, 16 * s ^ 2 * U (d + 1) ≤ Q d)
    (hnext : ∀ d < k, ∀ p : ℕ, M (d + 1) < p → p ≤ U (d + 1) →
      Q d / p ≤ Q (d + 1))
    (hdiag : ∀ d, d + b = k → P < (M d + 1) ^ r)
    (hJ : ∀ d, 0 ≤ J d) (hsource : ∀ d ≤ k, meanValue s k (Q d) ≤ J d)
    (n d : ℕ) (hk : d + (b + n) = k)
    (T e p q : ℕ) (hp : p.Prime) (hpM : M d < p) (hq : 0 < q)
    (F : Fin (b + n) → ℤ[X]) (hF : HasType F d T e)
    (hT0 : 0 < T) (hT : T ≤ P ^ d) :
    residueMixedMoment (b + n) s P (p ^ r) (pow_pos hp.pos r)
      (fullFrequency d F) (monomialTail (b + n) d p q (Q d)) ≤
        backwardAllowance k b P s r M U π J d n := by
  induction n generalizing d T e p q with
  | zero =>
    have hdiag' : P < p ^ r :=
      (hdiag d (by simpa using hk)).trans_le (Nat.pow_le_pow_left hpM r)
    rw [residueMixedMoment_eq_diagonal _ _ _ _ _ hdiag',
      monomialTail_moment _ _ _ _ _ _ hp.pos hq, hk]
    exact mul_le_mul_of_nonneg_left (hsource d (by omega)) (by positivity)
  | succ n ih =>
    have hm : 2 ≤ b + n := by omega
    have hd : d < k := by omega
    have hdk : d + 1 ≤ k := by omega
    have hmn : b + n ≤ k := by omega
    have hPm : 4 * (b + n) ^ 4 ≤ P :=
      (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hmn 4)).trans hP
    have hM : d + 1 + (b + n) ≤ M (d + 1) := by
      have h := hMdeg (d + 1) hdk
      omega
    have hbgt : P ^ (d + 1 + 2 * (b + n).choose 2) < ∏ p ∈ π (d + 1), p := by
      have he : k - (d + 1) = b + n := by omega
      simpa only [he] using hbudget (d + 1) hdk
    have hstep := backward_step_of_packet (m := b + n) (d := d) hF hm hPm hM
      hT0 hT (π (d + 1)) (hπ (d + 1) hdk) hbgt hr1 (by omega) (by omega)
      (by omega) hp.pos hq (hQ d hd) (hnext d hd)
      (fun T' e' p' q' hp' G hT'0 hT' hG hp'M _hp'U hq' =>
        ih (d + 1) (by omega) T' e' p' q' hp' hp'M hq' G hG hT'0 hT')
    have hdeg : d + (b + n + 1) = k := by omega
    rw [hdeg] at hstep
    change _ ≤ (2 * (P : ℝ)) ^ (b + n + 1) * _ at hstep
    apply hstep.trans
    rw [backwardAllowance]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply max_le_max
    · exact mul_le_mul_of_nonneg_left (hsource d hd.le) (by positivity)
    · have hJ0 : 0 ≤ meanValue s k (Q d) :=
        MeasureTheory.integral_nonneg (fun _ => by positivity)
      have hp' : ((M d + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hpM
      have hbeta : 0 ≤ ((((b + n : ℕ) : ℝ) - 1) / (2 * ((b + n : ℕ) : ℝ))) := by
        apply div_nonneg _ (by positivity)
        have hm' : (2 : ℝ) ≤ b + n := by exact_mod_cast hm
        push_cast
        linarith
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg
        (mul_nonneg (by positivity) (backwardAllowance_nonneg k b P s r M U π J hJ _ _)) _)
      apply mul_le_mul
      · apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ (by positivity) hp' _
      · exact Real.rpow_le_rpow hJ0 (hsource d hd.le) hbeta
      · exact Real.rpow_nonneg hJ0 _
      · positivity

/-- The entire finite mixed iteration starts at the literal homogeneous
moment. Its conclusion is a numerical recurrence in the source moments,
with no intermediate type count or residue bound left as a premise. -/
theorem iterated_moment_bound (k b P s r : ℕ) (M U Q : ℕ → ℕ)
    (π : ℕ → Finset ℕ) (J : ℕ → ℝ)
    (hb : 2 ≤ b) (hP : 4 * k ^ 4 ≤ P) (hs : k ≤ s)
    (hr1 : 1 ≤ r) (hr : r ≤ k)
    (hMdeg : ∀ d ≤ k, k ≤ M d)
    (hπ : ∀ d ≤ k, ∀ p ∈ π d, p.Prime ∧ M d < p ∧ p ≤ U d)
    (hbudget : ∀ d ≤ k, P ^ (d + 2 * (k - d).choose 2) < ∏ p ∈ π d, p)
    (hQ : ∀ d < k, 16 * s ^ 2 * U (d + 1) ≤ Q d)
    (hnext : ∀ d < k, ∀ p : ℕ, M (d + 1) < p → p ≤ U (d + 1) →
      Q d / p ≤ Q (d + 1))
    (hdiag : ∀ d, d + b = k → P < (M d + 1) ^ r)
    (hJ : ∀ d, 0 ≤ J d) (hsource : ∀ d ≤ k, meanValue s k (Q d) ≤ J d)
    (n : ℕ) (hk : b + n = k)
    (hfirst : 16 * s ^ 2 * U 0 ≤ P)
    (hfirstNext : ∀ p : ℕ, M 0 < p → p ≤ U 0 → P / p ≤ Q 0) :
    meanValue (s + k) k P ≤
      ((4 * (π 0).card * k.factorial : ℕ) : ℝ) *
        (U 0 : ℝ) ^ conditioningExponent 0 r s *
        backwardAllowance k b P s r M U π J 0 n := by
  subst k
  have h := typeCount_le_of_residue_bound
    (VinogradovDiagonalMoment.monomialSystem_hasType (b + n))
    (by omega) hP (by simpa only [Nat.zero_add] using hMdeg 0 (by omega))
    (by norm_num) (by simp) (π 0) (hπ 0 (by omega))
    (by simpa only [Nat.zero_add, Nat.sub_zero] using hbudget 0 (by omega))
    hr1 (by omega) (by omega) (by omega) (by norm_num : 0 < 1) hfirst hfirstNext
    (fun e p hp G hG hpM _hpU =>
      iterated_residue_bound (b + n) b P s r M U Q π J hb hP hs hr1 hr
        hMdeg hπ hbudget hQ hnext hdiag hJ hsource n 0 (by omega)
        1 e p 1 hp hpM (by norm_num) G hG (by norm_num) (by simp))
  simpa only [VinogradovDiagonalMoment.initial_count_eq, Nat.factorial_zero, mul_one] using h

end
end RiemannGaussian.VinogradovLiteratureIteration
