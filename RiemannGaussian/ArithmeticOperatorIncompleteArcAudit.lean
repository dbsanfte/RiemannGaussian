/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFareyFourierAudit

/-!
# Hard one-point primitive arcs retain the inverse-weight obstruction

The point mask is imposed BEFORE primitive projection and may depend on
the literal denominator, cutoff, height or factorial order. Exact Mobius
inversion still joins it to one signed inverse-weight kernel. No arc is
completed, approximated or norm-paid. Arbitrary free inverse arrays obey
the same algebra, but are not claimed to count actual reduced fractions.

The reflection-paired upper half-circle has precisely the original
Mobius source with explicit real-axis endpoints. This closes linear
one-point projection as an additional identity-only arithmetic constraint;
ordered adjacent gaps and nonlinear multi-point masks remain separate.
-/

namespace RiemannGaussian.ArithmeticOperatorIncompleteArcAudit
noncomputable section
open Complex Filter Polynomial
open ArithmeticOperatorFareyFourierAudit
open ArithmeticOperatorCompositeRamanujanFreedom
open scoped BigOperators Classical Topology ComplexConjugate

/-- Arbitrary literal point mask, including hard arcs. No continuity
or symmetry is assumed, and every primitive order is retained. -/
def primitiveRow (q : ℕ) (f : ℂ → ℂ) : ℂ :=
  ∑ z∈primitiveRoots q ℂ,f z

/-- The complete grid is used only inside exact Mobius inversion;
the original point mask remains imposed at each grid point. -/
def gridRow (q : ℕ) (f : ℂ → ℂ) : ℂ :=
  ∑ z∈nthRootsFinset q (1 : ℂ),f z

/-- The point mask is applied to literal reduced ordinary fractions,
including the unit denominator and without any arc completion. -/
theorem primitiveRow_eq_reduced {q : ℕ} (hq : 0<q) (f : ℂ → ℂ) :
    primitiveRow q f=∑ a∈(Finset.range q).filter (fun a => a.Coprime q),
      f (Complex.exp (2*Real.pi*I*((a : ℂ)/(q : ℂ)))) := by
  let z := Complex.exp (2*Real.pi*I/(q : ℂ))
  have hz : IsPrimitiveRoot z q := Complex.isPrimitiveRoot_exp q hq.ne'
  let : NeZero q := ⟨hq.ne'⟩
  symm
  refine Finset.sum_bij (fun a _ => z^a) ?_ ?_ ?_ ?_
  · intro a ha
    exact (mem_primitiveRoots hq).mpr (hz.pow_of_coprime a (Finset.mem_filter.mp ha).2)
  · intro a ha b hb he
    exact hz.pow_inj (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1) he
  · intro v hv
    obtain ⟨a,ha,hac,he⟩ := hz.isPrimitiveRoot_iff.mp ((mem_primitiveRoots hq).mp hv)
    exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha,hac⟩,he⟩
  · intro a _
    change _=f (Complex.exp _^a)
    apply congrArg f
    rw [←Complex.exp_nat_mul]
    congr 1
    ring

/-- Exact primitive-order partition with the hard mask already present. -/
theorem sum_divisors_primitiveRow (q : ℕ) (f : ℂ → ℂ) :
    (∑ d∈q.divisors,primitiveRow d f)=gridRow q f := by
  rw [gridRow,IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
    Finset.sum_biUnion (fun a _ b _ hab => IsPrimitiveRoot.disjoint hab)]
  rfl

/-- The literal row equals an inverse-divisor sum even for a
discontinuous or denominator-dependent point mask. -/
theorem primitiveRow_eq_inverse {q : ℕ} (hq : 0<q) (f : ℂ → ℂ) :
    primitiveRow q f=∑ da∈q.divisorsAntidiagonal,
      (ArithmeticFunction.moebius da.1 : ℂ)*gridRow da.2 f := by
  exact ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => primitiveRow d f) (g := fun d => gridRow d f)).mp
      (fun d _ => sum_divisors_primitiveRow d f) q hq).symm

/-- Actual ordinary-integer cutoff with correlated denominator weight
and point mask. The phase belongs to w or f and is retained unchanged. -/
def nativePacket (X : ℕ) (w : ℕ → ℂ) (f : ℕ → ℂ → ℂ) : ℂ :=
  ∑ q∈Finset.Icc 1 X,w q*primitiveRow q (f q)

/-- Free inverse-array version, solely for the collapse audit. These
coefficients are NOT asserted to be actual primitive-point counts. -/
def freePacket (X : ℕ) (v w : ℕ → ℂ) (f : ℕ → ℂ → ℂ) : ℂ :=
  ∑ q∈Finset.Icc 1 X,w q*∑ da∈q.divisorsAntidiagonal,v da.1*gridRow da.2 (f q)

/-- Exact arithmetic bridge with every physical mask present. -/
theorem nativePacket_eq_free (X : ℕ) (w : ℕ → ℂ) (f : ℕ → ℂ → ℂ) :
    nativePacket X w f=freePacket X (fun d => (ArithmeticFunction.moebius d : ℂ)) w f := by
  apply Finset.sum_congr rfl
  intro q hq
  rw [primitiveRow_eq_inverse (Finset.mem_Icc.mp hq).1]

/-- Joining the complete finite cutoff produces one signed scalar
kernel. Neither the arc nor the denominator dependence is removed. -/
theorem freePacket_eq_scalar (X : ℕ) (v w : ℕ → ℂ) (f : ℕ → ℂ → ℂ) :
    freePacket X v w f=∑ a∈Finset.Icc 1 X,v a*
      (∑ d∈Finset.Icc 1 (X/a),w (a*d)*gridRow d (f (a*d))) := by
  have he (q : ℕ) : w q*(∑ da∈q.divisorsAntidiagonal,v da.1*gridRow da.2 (f q))=
      ∑ da∈q.divisorsAntidiagonal,v da.1*(w (da.1*da.2)*gridRow da.2 (f (da.1*da.2))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro da hda
    rw [(Nat.mem_divisorsAntidiagonal.mp hda).1]
    ring
  simp_rw [freePacket,he]
  rw [sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix X
    (fun a d => v a*(w (a*d)*gridRow d (f (a*d))))]
  simp only [←Finset.mul_sum]

/-- No extra literal-prime constraint follows from the one-point join. -/
theorem nativePacket_eq_scalar (X : ℕ) (w : ℕ → ℂ) (f : ℕ → ℂ → ℂ) :
    nativePacket X w f=∑ a∈Finset.Icc 1 X,(ArithmeticFunction.moebius a : ℂ)*
      (∑ d∈Finset.Icc 1 (X/a),w (a*d)*gridRow d (f (a*d))) := by
  rw [nativePacket_eq_free,freePacket_eq_scalar]

/-- An identity-only norm allowance for all free inverse arrays is
possible exactly when the ENTIRE joined kernel is zero. -/
theorem free_bound_iff (X : ℕ) (w : ℕ → ℂ) (f : ℕ → ℂ → ℂ) (B : ℝ) :
    (∀ v,‖freePacket X v w f‖≤B) ↔
      0≤B ∧ ∀ a∈Finset.Icc 1 X,
        (∑ d∈Finset.Icc 1 (X/a),w (a*d)*gridRow d (f (a*d)))=0 := by
  simp_rw [freePacket_eq_scalar]
  simpa only [mul_comm] using ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff
    (Finset.Icc 1 X) (fun a => ∑ d∈Finset.Icc 1 (X/a),w (a*d)*gridRow d (f (a*d))) B

private theorem primitive_conj {q : ℕ} {z : ℂ} (hz : z∈primitiveRoots q ℂ) :
    conj z∈primitiveRoots q ℂ := by
  by_cases hq : q=0
  · simp [hq] at hz
  · have hp := (mem_primitiveRoots (Nat.pos_of_ne_zero hq)).mp hz
    exact (mem_primitiveRoots (Nat.pos_of_ne_zero hq)).mpr
      (hp.map_of_injective (f := starRingEnd ℂ) star_injective)

/-- Reflection retains the actual primitive order and each hard mask. -/
theorem primitiveRow_conj_input (q : ℕ) (f : ℂ → ℂ) :
    primitiveRow q (fun z => f (conj z))=primitiveRow q f := by
  unfold primitiveRow
  refine Finset.sum_bij (fun z _ => conj z) ?_ ?_ ?_ ?_
  · intro z hz
    exact primitive_conj hz
  · intro z _ v _ he
    exact star_injective he
  · intro z hz
    exact ⟨conj z,primitive_conj hz,by simp⟩
  · intro z _
    rfl

/-- The open upper half-circle is a genuine hard point cutoff.
The real-axis endpoints are separate, not silently dropped. -/
def upperRow (q : ℕ) : ℂ :=
  primitiveRow q (fun z => if 0<z.im then z else 0)

/-- Literal lower half-circle, paired by conjugating each point,
without conjugating any exterior height or denominator weight. -/
def lowerRow (q : ℕ) : ℂ :=
  primitiveRow q (fun z => if z.im<0 then z else 0)

/-- Exact zero and half-turn arc endpoints. -/
def axisRow (q : ℕ) : ℂ :=
  primitiveRow q (fun z => if z.im=0 then z else 0)

theorem upperRow_conj (q : ℕ) : conj (upperRow q)=lowerRow q := by
  have he := primitiveRow_conj_input q (fun z => if z.im<0 then z else 0)
  rw [upperRow,primitiveRow,map_sum]
  simp_rw [apply_ite, map_zero]
  simpa only [primitiveRow,lowerRow,Complex.conj_im,neg_lt_zero] using he

/-- Exact reflection join of the hard arc BEFORE any norm or sign.
All nonsquarefree primitive rows and real-axis endpoints remain. -/
theorem half_arc_join (q : ℕ) :
    upperRow q+lowerRow q+axisRow q=(ArithmeticFunction.moebius q : ℂ) := by
  rw [upperRow,lowerRow,axisRow,primitiveRow,primitiveRow,primitiveRow,
    ←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  have he : (∑ z∈primitiveRoots q ℂ,
      ((if 0<z.im then z else 0)+(if z.im<0 then z else 0)+
        (if z.im=0 then z else 0)))=fourierRow q 1 := by
    apply Finset.sum_congr rfl
    intro z _
    rcases lt_trichotomy z.im 0 with h|h|h
    · simp [h,h.not_gt,h.ne]
    · simp [h]
    · simp [h,h.not_gt,h.ne']
  rw [he,fourierRow_one]

/-- Only denominators one and two can meet an arc's real-axis
boundary. These native endpoints are evaluated exactly. -/
theorem axisRow_eq (q : ℕ) :
    axisRow q=if q=1 then (1 : ℂ) else if q=2 then -1 else 0 := by
  by_cases h1 : q=1
  · simp [h1,axisRow,primitiveRow,IsPrimitiveRoot.primitiveRoots_one]
  by_cases h2 : q=2
  · have he : primitiveRoots 2 ℂ={(-1 : ℂ)} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨(mem_primitiveRoots (by norm_num)).mpr
        (IsPrimitiveRoot.neg_one 0 (by norm_num)),fun z hz =>
          ((mem_primitiveRoots (by norm_num)).mp hz).eq_neg_one_of_two_right⟩
    simp [h2,axisRow,primitiveRow,he]
  rw [ite_eq_right h1,ite_eq_right h2,axisRow,primitiveRow]
  apply Finset.sum_eq_zero
  intro z hz
  by_cases hz0 : z.im=0
  · by_cases hq : q=0
    · simp [hq] at hz
    have hp := (mem_primitiveRoots (Nat.pos_of_ne_zero hq)).mp hz
    have hn := hp.norm'_eq_one hq
    have hs : z.re^2=1 := by
      have he := normSq_eq_norm_sq z
      rw [hn,normSq_apply,hz0] at he
      nlinarith
    rcases (sq_eq_one_iff.mp hs) with hr|hr
    · have he : z=1 := Complex.ext (by simpa using hr) (by simpa using hz0)
      rw [he] at hp
      exact False.elim (h1 (hp.unique (IsPrimitiveRoot.one_right_iff.mpr rfl)))
    · have he : z=-1 := Complex.ext (by simpa using hr) (by simpa using hz0)
      rw [he] at hp
      exact False.elim (h2 (hp.unique (IsPrimitiveRoot.neg_one 0 (by norm_num))))
  · simp [hz0]

/-- The reflected half arcs, with exactly their two boundary points,
are source-equivalent to the original arithmetic coefficient atomwise. -/
theorem corrected_half_eq_moebius (q : ℕ) :
    upperRow q+conj (upperRow q)+(if q=1 then (1 : ℂ) else if q=2 then -1 else 0)=
      (ArithmeticFunction.moebius q : ℂ) := by
  rw [upperRow_conj,←axisRow_eq]
  exact half_arc_join q

/-- The height, radial/factorial and all correlated exterior weights
are untouched when the reflected arc is joined. -/
theorem corrected_half_packet_eq (X : ℕ) (w : ℕ → ℂ) :
    (∑ q∈Finset.Icc 1 X,w q*(upperRow q+conj (upperRow q)+axisRow q))=
      ∑ q∈Finset.Icc 1 X,w q*(ArithmeticFunction.moebius q : ℂ) := by
  simp_rw [upperRow_conj,half_arc_join]

/-- The literal reflection-paired arc has the genuine original Euler
response, with every boundary coefficient retained. -/
theorem corrected_half_euler {s : ℂ} (hs : 1<s.re) :
    LSeries (fun q => upperRow q+conj (upperRow q)+axisRow q) s=response s := by
  have he (q : ℕ) : upperRow q+conj (upperRow q)+axisRow q=fourierRow q 1 := by
    rw [upperRow_conj,half_arc_join,fourierRow_one]
  simp_rw [he]
  exact first_frequency_euler hs

/-- Original fixed-height phase, with neither arc estimated separately. -/
theorem corrected_half_twisted_euler (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun q => (upperRow q+conj (upperRow q)+axisRow q)*
      SuzukiCarryCorrelation.primePhase y q) s=response (s+I*y) := by
  have he (q : ℕ) : upperRow q+conj (upperRow q)+axisRow q=fourierRow q 1 := by
    rw [upperRow_conj,half_arc_join,fourierRow_one]
  simp_rw [he]
  exact first_frequency_twisted_euler y hs

/-- Every actual zero retains a nonzero source of its exact analytic
multiplicity in this corrected hard-arc response. No cutoff asymptotic
or source gate for an arbitrary asymmetric arc is inferred. -/
theorem corrected_half_actual_zero_source (rho : NontrivialZetaZero) :
    ∃ v : ℂ,v≠0 ∧ Tendsto
      (fun s : ℂ => (s-rho.1)^(analyticZetaZeroMultiplicity rho)*response s)
      (𝓝[≠] rho.1) (𝓝 v) := actual_zero_source rho

/-- Exact density removal without removing that zero source. -/
theorem corrected_half_density_zero : Tendsto response (𝓝[≠] (1 : ℂ)) (𝓝 0) :=
  response_density_zero

/-- An independent arithmetic regularization of the corrected hard arc
would still have precisely the strength of original strip nonvanishing. -/
theorem corrected_half_removable_iff {s : ℂ} (hs0 : 0<s.re) (hs1 : s.re<1) :
    RemovableAt s ↔ riemannZeta s≠0 := response_removable_iff hs0 hs1

/-- A hard reflection-paired arc bound is exactly the original signed
Mobius bound, not an additional cancellation consequence of ordering. -/
theorem corrected_half_bound_iff (X : ℕ) (w : ℕ → ℂ) (B : ℝ) :
    ‖∑ q∈Finset.Icc 1 X,w q*(upperRow q+conj (upperRow q)+axisRow q)‖≤B ↔
      ‖∑ q∈Finset.Icc 1 X,w q*(ArithmeticFunction.moebius q : ℂ)‖≤B := by
  rw [corrected_half_packet_eq]

end
end RiemannGaussian.ArithmeticOperatorIncompleteArcAudit
