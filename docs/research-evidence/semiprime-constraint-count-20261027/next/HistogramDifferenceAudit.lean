import Mathlib

/-! Scratch-only exact histogram updates. No canonical source is changed.
These lemmas check the ring identities and order transport; the note states
separately the still-needed original finite-sum/compiler refinement.
-/
set_option autoImplicit false
namespace SourceHistogramShortcut
open scoped BigOperators

/-- L times the weighted equality kernel quadratic form. -/
def B (L H P U S : ℚ) : ℚ := L*H+2*P*U+U^2+(L-1)*S

/-- Move one formerly free key of weight z into one fixed label bin of mass h. -/
def after (L H P U S z h : ℚ) : ℚ :=
  B L (H+2*h*z+z^2) (P+z) (U-z) (S-z^2)

 theorem after_update (L H P U S z h : ℚ) :
    after L H P U S z h=B L H P U S+2*z*(L*h-P) := by
  unfold after B
  ring

 theorem after_difference (L H P U S z hc hd : ℚ) :
    after L H P U S z hc-after L H P U S z hd=2*z*L*(hc-hd) := by
  rw [after_update,after_update]
  ring

/-- Vertex-prefix incidence count after the next candidate has been fixed. -/
def vertexI {E : Type*} [Fintype E] (L H P U S z hc : ℚ)
    (He Pe Ue Se ze he : E → ℚ) : ℚ :=
  L^2*(after L H P U S z hc+(L-1)*∑e,after L (He e) (Pe e) (Ue e) (Se e) (ze e) (he e))

 theorem vertexI_difference {E : Type*} [Fintype E] (L H P U S z hc hd : ℚ)
    (He Pe Ue Se ze he hd' : E → ℚ) :
    vertexI L H P U S z hc He Pe Ue Se ze he-
      vertexI L H P U S z hd He Pe Ue Se ze hd'=
    2*L^3*(z*(hc-hd)+(L-1)*∑e,ze e*(he e-hd' e)) := by
  have hs : (∑e,after L (He e) (Pe e) (Ue e) (Se e) (ze e) (he e))-
      (∑e,after L (He e) (Pe e) (Ue e) (Se e) (ze e) (hd' e))=
      2*L*∑e,ze e*(he e-hd' e) := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [after_difference]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  unfold vertexI
  have ha := after_difference L H P U S z hc hd
  linear_combination L^2*ha+L^2*(L-1)*hs

/-- Original padded head sum after one vertex is fixed; F is the candidate's
sum of old coordinate-bin frequencies. -/
def vertexH (L G Q p f S F : ℚ) : ℚ :=
  L^4*(S+2*F+Q+Q*(f-1))+G*Q*(2*(p+1)*(f-1)+(f-1)*(f-2))

 theorem vertexH_difference (L G Q p f S Fc Fd : ℚ) :
    vertexH L G Q p f S Fc-vertexH L G Q p f S Fd=2*L^4*(Fc-Fd) := by
  unfold vertexH
  ring

/-- Full original integer-weighted score, expressed in the rational embedding
so its signed candidate differences remain exact. -/
def vertexReduced {E : Type*} [Fintype E] (A B L z hc Fc : ℚ)
    (ze he : E → ℚ) : ℚ := A*(z*hc+(L-1)*∑e,ze e*he e)+B*L*Fc

 theorem vertex_weighted_difference {E : Type*} [Fintype E]
    (A B L G Q p f S0 H P U S z hc hd Fc Fd : ℚ)
    (He Pe Ue Se ze he hd' : E → ℚ) :
    (A*vertexI L H P U S z hc He Pe Ue Se ze he+B*vertexH L G Q p f S0 Fc)-
    (A*vertexI L H P U S z hd He Pe Ue Se ze hd'+B*vertexH L G Q p f S0 Fd)=
    2*L^3*(vertexReduced A B L z hc Fc ze he-vertexReduced A B L z hd Fd ze hd') := by
  have hi := vertexI_difference L H P U S z hc hd He Pe Ue Se ze he hd'
  have hh := vertexH_difference L G Q p f S0 Fc Fd
  have hs : (∑e,ze e*he e)-(∑e,ze e*hd' e)=∑e,ze e*(he e-hd' e) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  unfold vertexReduced
  linear_combination A*hi+B*hh-2*A*L^3*(L-1)*hs

/-- Factor-prefix incidence count after the next factor label is fixed. -/
def factorI {C : Type*} [Fintype C] (L : ℚ) (H P U S z h : C → ℚ) : ℚ :=
  L^3*∑c,after L (H c) (P c) (U c) (S c) (z c) (h c)

 theorem factor_weighted_difference {C : Type*} [Fintype C]
    (A B L head : ℚ) (H P U S z hc hd : C → ℚ) :
    (A*factorI L H P U S z hc+B*head)-(A*factorI L H P U S z hd+B*head)=
      2*L^4*(A*(∑c,z c*hc c)-A*(∑c,z c*hd c)) := by
  have hs : (∑c,after L (H c) (P c) (U c) (S c) (z c) (hc c))-
      (∑c,after L (H c) (P c) (U c) (S c) (z c) (hd c))=
      2*L*((∑c,z c*hc c)-(∑c,z c*hd c)) := by
    rw [← Finset.sum_sub_distrib,mul_sub,Finset.mul_sum,Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [after_difference]
    ring
  unfold factorI
  linear_combination A*L^3*hs

/-- A positive common difference factor preserves weak order, even when either
original nonnegative score coefficient is zero. -/
theorem order_of_difference (s t u v k : ℚ) (hk : 0<k) (h : s-t=k*(u-v)) :
    s ≤ t ↔ u ≤ v := by
  constructor
  · intro hst
    by_contra huv
    have hp : 0<k*(u-v) := mul_pos hk (sub_pos.mpr (lt_of_not_ge huv))
    linarith
  · intro huv
    have hm : k*(u-v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr huv)
    linarith

/-- Equality and the original deterministic first-candidate ties are preserved. -/
theorem tie_of_difference (s t u v k : ℚ) (hk : 0<k) (h : s-t=k*(u-v)) :
    s=t ↔ u=v := by
  constructor
  · intro he
    have hz : k*(u-v)=0 := by linarith
    have hv := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hk)
    linarith
  · intro he
    rw [he,sub_self,mul_zero] at h
    linarith

end SourceHistogramShortcut

#print axioms SourceHistogramShortcut.after_update

#print axioms SourceHistogramShortcut.after_difference

#print axioms SourceHistogramShortcut.vertexI_difference

#print axioms SourceHistogramShortcut.vertexH_difference

#print axioms SourceHistogramShortcut.vertex_weighted_difference

#print axioms SourceHistogramShortcut.factor_weighted_difference

#print axioms SourceHistogramShortcut.order_of_difference

#print axioms SourceHistogramShortcut.tie_of_difference
