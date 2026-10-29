import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# A finite dependency-graph variance bound

All expectations below are finite rational sums. The main theorem expands the
square of a centered count into a double sum of covariances. Nonneighbors have
zero covariance; at most `d + 1` entries in each row remain, each at most one.
-/

namespace SubexponentialSAT.Variance

open scoped BigOperators

variable {Ω V U : Type*}

/-- Finite weighted expectation. Normalization is an explicit theorem hypothesis. -/
def mean [Fintype Ω] (weight : Ω → ℚ) (f : Ω → ℚ) : ℚ :=
  ∑ ω, weight ω * f ω

section Mean

variable [Fintype Ω] (weight : Ω → ℚ)

theorem mean_add (f g : Ω → ℚ) :
    mean weight (fun ω => f ω + g ω) = mean weight f + mean weight g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_sub (f g : Ω → ℚ) :
    mean weight (fun ω => f ω - g ω) = mean weight f - mean weight g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

theorem mean_mul_const (f : Ω → ℚ) (a : ℚ) :
    mean weight (fun ω => f ω * a) = mean weight f * a := by
  simp [mean, Finset.sum_mul, mul_assoc]

theorem mean_const (hweight : ∑ ω, weight ω = 1) (a : ℚ) :
    mean weight (fun _ => a) = a := by
  rw [mean, ← Finset.sum_mul, hweight, one_mul]

theorem mean_sum {I : Type*} [Fintype I] (f : I → Ω → ℚ) :
    mean weight (fun ω => ∑ i, f i ω) = ∑ i, mean weight (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_mono (hweight : ∀ ω, 0 ≤ weight ω) {f g : Ω → ℚ}
    (hfg : ∀ ω, f ω ≤ g ω) : mean weight f ≤ mean weight g := by
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (hweight ω)

/-- Expanding a centered product gives the covariance formula. -/
theorem mean_centered_mul (hweight : ∑ ω, weight ω = 1)
    (f g : Ω → ℚ) (a : ℚ) (hf : mean weight f = a) (hg : mean weight g = a) :
    mean weight (fun ω => (f ω - a) * (g ω - a)) =
      mean weight (fun ω => f ω * g ω) - a ^ 2 := by
  have hfun : (fun ω => (f ω - a) * (g ω - a)) =
      (fun ω => ((f ω * g ω - f ω * a) - g ω * a) + a * a) := by
    funext ω
    ring
  rw [hfun, mean_add, mean_sub, mean_sub, mean_mul_const,
    mean_mul_const, mean_const weight hweight, hf, hg]
  ring

/-- Equal weights on a finite outcome space. -/
def uniformWeight (_ω : Ω) : ℚ := 1 / (Fintype.card Ω : ℚ)

theorem uniformWeight_nonneg (ω : Ω) : 0 ≤ uniformWeight ω := by
  exact div_nonneg (by norm_num) (Nat.cast_nonneg _)

theorem uniformWeight_sum [Nonempty Ω] : ∑ ω : Ω, uniformWeight ω = 1 := by
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [uniformWeight, div_eq_mul_inv, hcard]

/-- Bridge to the ordinary sum-divided-by-cardinality finite average. -/
theorem mean_uniformWeight (f : Ω → ℚ) :
    mean uniformWeight f = (∑ ω, f ω) / (Fintype.card Ω : ℚ) := by
  simp only [mean, uniformWeight, ← Finset.mul_sum]
  ring

end Mean

section Matrix

variable [Fintype V] [DecidableEq V]

/-- A sparse matrix with at most `d` off-diagonal nonzero entries per row,
all entries at most one, has total sum at most `(1+d) * card V`. -/
theorem sparse_sum_le (c : V → V → ℚ) (neighbors : V → Finset V) (d : ℕ)
    (hdegree : ∀ v, (neighbors v).card ≤ d)
    (hbound : ∀ v w, c v w ≤ 1)
    (hzero : ∀ v w, v ≠ w → w ∉ neighbors v → c v w = 0) :
    (∑ v, ∑ w, c v w) ≤ (1 + (d : ℚ)) * (Fintype.card V : ℚ) := by
  have hrow (v : V) : (∑ w, c v w) ≤ (d : ℚ) + 1 := by
    calc
      (∑ w, c v w) ≤
          ∑ w, if w ∈ insert v (neighbors v) then (1 : ℚ) else 0 := by
        apply Finset.sum_le_sum
        intro w _
        by_cases hw : w ∈ insert v (neighbors v)
        · simpa only [ite_eq_left hw] using hbound v w
        · simp only [Finset.mem_insert, not_or] at hw
          simp only [Finset.mem_insert, hw.1, hw.2, or_self, ite_false]
          rw [hzero v w (Ne.symm hw.1) hw.2]
      _ = ((insert v (neighbors v)).card : ℚ) := by
        have hs : Finset.univ.filter (fun w => w ∈ insert v (neighbors v)) =
            insert v (neighbors v) := by
          ext w
          simp
        rw [Finset.sum_boole, hs]
      _ ≤ (d : ℚ) + 1 := by
        exact_mod_cast (Finset.card_insert_le v (neighbors v)).trans
          (Nat.add_le_add_right (hdegree v) 1)
  calc
    (∑ v, ∑ w, c v w) ≤ ∑ _v : V, ((d : ℚ) + 1) :=
      Finset.sum_le_sum fun v _ => hrow v
    _ = (1 + (d : ℚ)) * (Fintype.card V : ℚ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Matrix

section Variance

variable [Fintype Ω] [Fintype V] [DecidableEq V]

omit [Fintype Ω] [DecidableEq V] in
/-- The square of a centered sum is the sum of all centered products. -/
theorem centered_sum_square (X : Ω → V → ℚ) (a : ℚ) (ω : Ω) :
    ((∑ v, X ω v) - (Fintype.card V : ℚ) * a) ^ 2 =
      ∑ v, ∑ w, (X ω v - a) * (X ω w - a) := by
  have hs : (∑ v, (X ω v - a)) =
      (∑ v, X ω v) - (Fintype.card V : ℚ) * a := by
    simp [Finset.sum_sub_distrib]
  rw [← hs, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]

omit [DecidableEq V] in
/-- Algebraic expansion of the variance of the total count. -/
theorem mean_centered_sum_square (weight : Ω → ℚ) (X : Ω → V → ℚ) (a : ℚ) :
    mean weight (fun ω => ((∑ v, X ω v) - (Fintype.card V : ℚ) * a) ^ 2) =
      ∑ v, ∑ w, mean weight (fun ω => (X ω v - a) * (X ω w - a)) := by
  simp_rw [centered_sum_square, mean_sum]

/-- Dependency-graph variance bound for identically distributed variables in
`[0,1]`. The independence hypothesis is exactly factorization of pair moments
for distinct nonneighbors; no independence of adjacent variables is assumed. -/
theorem variance_sum_le (weight : Ω → ℚ)
    (hweight_nonneg : ∀ ω, 0 ≤ weight ω) (hweight_sum : ∑ ω, weight ω = 1)
    (X : Ω → V → ℚ) (a : ℚ)
    (hX : ∀ ω v, 0 ≤ X ω v ∧ X ω v ≤ 1)
    (hmarginal : ∀ v, mean weight (fun ω => X ω v) = a)
    (neighbors : V → Finset V) (d : ℕ)
    (hdegree : ∀ v, (neighbors v).card ≤ d)
    (hindependent : ∀ v w, v ≠ w → w ∉ neighbors v →
      mean weight (fun ω => X ω v * X ω w) = a * a) :
    mean weight (fun ω => ((∑ v, X ω v) - (Fintype.card V : ℚ) * a) ^ 2) ≤
      (1 + (d : ℚ)) * (Fintype.card V : ℚ) := by
  rw [mean_centered_sum_square]
  apply sparse_sum_le _ neighbors d hdegree
  · intro v w
    rw [mean_centered_mul weight hweight_sum _ _ a (hmarginal v) (hmarginal w)]
    have hprod : mean weight (fun ω => X ω v * X ω w) ≤ 1 := by
      calc
        mean weight (fun ω => X ω v * X ω w) ≤ mean weight (fun _ => 1) :=
          mean_mono weight hweight_nonneg fun ω =>
            (mul_le_mul_of_nonneg_right (hX ω v).2 (hX ω w).1).trans
              (by simpa using (hX ω w).2)
        _ = 1 := mean_const weight hweight_sum 1
    nlinarith [sq_nonneg a]
  · intro v w hvw hn
    rw [mean_centered_mul weight hweight_sum _ _ a (hmarginal v) (hmarginal w),
      hindependent v w hvw hn]
    ring

end Variance

section Types

variable [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

/-- The indicator that chunk `v` has type `u` in outcome `ω`. -/
def typeIndicator (T : Ω → V → U) (u : U) (ω : Ω) (v : V) : ℚ :=
  if T ω v = u then 1 else 0

/-- Number of chunks having a prescribed type. -/
def typeCount (T : Ω → V → U) (u : U) (ω : Ω) : ℕ :=
  (Finset.univ.filter fun v => T ω v = u).card

omit [Fintype Ω] [DecidableEq V] [Fintype U] in
theorem typeCount_cast (T : Ω → V → U) (u : U) (ω : Ω) :
    (typeCount T u ω : ℚ) = ∑ v, typeIndicator T u ω v := by
  simp [typeCount, typeIndicator]

omit [DecidableEq V] in
/-- The center `D/N` is the actual mean of a uniformly distributed type count. -/
theorem mean_typeCount (weight : Ω → ℚ) (T : Ω → V → U) (u : U)
    (hmarginal : ∀ v, mean weight (fun ω => typeIndicator T u ω v) =
      1 / (Fintype.card U : ℚ)) :
    mean weight (fun ω => (typeCount T u ω : ℚ)) =
      (Fintype.card V : ℚ) / (Fintype.card U : ℚ) := by
  simp_rw [typeCount_cast, mean_sum, hmarginal]
  simp [div_eq_mul_inv]

/-- The single-type estimate in Section 5.4. -/
theorem typeCount_variance_le (weight : Ω → ℚ)
    (hweight_nonneg : ∀ ω, 0 ≤ weight ω) (hweight_sum : ∑ ω, weight ω = 1)
    (T : Ω → V → U) (u : U)
    (hmarginal : ∀ v, mean weight (fun ω => typeIndicator T u ω v) =
      1 / (Fintype.card U : ℚ))
    (neighbors : V → Finset V) (d : ℕ)
    (hdegree : ∀ v, (neighbors v).card ≤ d)
    (hindependent : ∀ v w, v ≠ w → w ∉ neighbors v →
      mean weight (fun ω => typeIndicator T u ω v * typeIndicator T u ω w) =
        (1 / (Fintype.card U : ℚ)) * (1 / (Fintype.card U : ℚ))) :
    mean weight (fun ω =>
      ((typeCount T u ω : ℚ) - (Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) ≤
        (1 + (d : ℚ)) * (Fintype.card V : ℚ) := by
  have hX : ∀ ω v, 0 ≤ typeIndicator T u ω v ∧ typeIndicator T u ω v ≤ 1 := by
    intro ω v
    unfold typeIndicator
    split_ifs <;> norm_num
  simpa only [typeCount_cast, div_eq_mul_inv, one_mul] using
    variance_sum_le weight hweight_nonneg hweight_sum (typeIndicator T u)
      (1 / (Fintype.card U : ℚ)) hX hmarginal neighbors d hdegree hindependent

/-- Expected sum of squared type-count deviations, the bound preceding (5.8). -/
theorem sum_typeCount_variances_le (weight : Ω → ℚ)
    (hweight_nonneg : ∀ ω, 0 ≤ weight ω) (hweight_sum : ∑ ω, weight ω = 1)
    (T : Ω → V → U)
    (hmarginal : ∀ u v, mean weight (fun ω => typeIndicator T u ω v) =
      1 / (Fintype.card U : ℚ))
    (neighbors : V → Finset V) (d : ℕ)
    (hdegree : ∀ v, (neighbors v).card ≤ d)
    (hindependent : ∀ u v w, v ≠ w → w ∉ neighbors v →
      mean weight (fun ω => typeIndicator T u ω v * typeIndicator T u ω w) =
        (1 / (Fintype.card U : ℚ)) * (1 / (Fintype.card U : ℚ))) :
    mean weight (fun ω => ∑ u,
      ((typeCount T u ω : ℚ) - (Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) ≤
        (Fintype.card U : ℚ) * (1 + (d : ℚ)) * (Fintype.card V : ℚ) := by
  rw [mean_sum]
  calc
    (∑ u, mean weight (fun ω =>
      ((typeCount T u ω : ℚ) - (Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2)) ≤
        ∑ _u : U, (1 + (d : ℚ)) * (Fintype.card V : ℚ) := by
      apply Finset.sum_le_sum
      intro u _
      exact typeCount_variance_le weight hweight_nonneg hweight_sum T u
        (hmarginal u) neighbors d hdegree (hindependent u)
    _ = (Fintype.card U : ℚ) * (1 + (d : ℚ)) * (Fintype.card V : ℚ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Types

end SubexponentialSAT.Variance

end OAI.Algorithms
