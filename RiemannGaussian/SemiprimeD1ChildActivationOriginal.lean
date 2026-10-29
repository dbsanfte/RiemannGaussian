/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildActivation

/-! # Original selected-vertex interpretation of every physical activation bit
The proof covers all original vertices, with no incidence/non-isolation premise.
No activation mask, word getter or tensor truth answer is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace RiemannGaussian.SemiprimeD1ChildActivationOriginal
open SemiprimeD1ChildActivation

/-- The physically read selected ID yields exactly its original finite colour test. -/
theorem readOne_original (r a : ℕ) [NeZero r] (id : List Bool)
    (hi : id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) (q : Fin a) (g : Fin r) :
    (readOne (SemiprimeSourceHistogramRows.acquire r a) a q.val
      (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits id).value=true ↔
      (SemiprimeSourceWordBankSemantics.decode r a id) q=g := by
  have hh := SemiprimeD1PacketRows.original_fields r a id hi
  simp only [readOne,hh.1,hh.2,ite_true]
  exact SemiprimeD1ChildGraphSemantics.test_fields _ q g

/-- The actual physical mask has exactly one bit per old vertex, including isolated ones. -/
theorem mask_length (n F r a : ℕ) (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (acquire n F r a inputArity inputOwner q g).bits.length=n+F := by
  change (fromReplay _ q g).bits.length=_
  rw [fromReplay_bits,List.length_map,List.length_reverse]
  exact SemiprimeD1IncidenceSearch.run_length n F r a inputArity inputOwner

/-- Every actual activation bit, including zero-port old vertices, is the original
selected vertex's colour predicate. No selected-colour answer is an input. -/
theorem mask_value (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r)
    (v : Fin (n+F)) :
    (((acquire n F r a inputArity inputOwner q g).bits[v.val]?).getD false=true) ↔
      SemiprimeMaterializedScoreEnvironment.denote
        (SemiprimeSourceHistogramHeadOriginal.originalEnv r a
          (SemiprimeD1IncidenceSearch.run n F r a inputArity inputOwner).value) v.val q=g := by
  let fixed := (SemiprimeD1IncidenceSearch.run n F r a inputArity inputOwner).value
  have hlen : fixed.length=n+F := SemiprimeD1IncidenceSearch.run_length n F r a inputArity inputOwner
  have hv : v.val<fixed.reverse.length := by simpa only [List.length_reverse,hlen] using v.isLt
  let id := fixed.reverse[v.val]
  have hid : id∈(SemiprimeSourceCompactWordBank.acquire r a).ids := by
    have hm : id∈fixed := List.mem_reverse.mp (List.getElem_mem hv)
    exact SemiprimeD1IncidenceSearch.run_valid n F r a inputArity inputOwner id hm
  have ht := readOne_original r a id hid q g
  have hdecode : SemiprimeSourceHistogramDictRefinement.labels r a fixed v.val=
      SemiprimeSourceWordBankSemantics.decode r a id := by
    unfold SemiprimeSourceHistogramDictRefinement.labels
    rw [SemiprimeSourceHistogramDictRefinement.decoder_map,
      SemiprimeSourceHistogramDictRefinement.decoder_reverse]
    simp only [List.getElem?_eq_getElem hv,Option.getD_some]
    rfl
  change (((fromReplay _ q g).bits[v.val]?).getD false=true) ↔ _
  rw [fromReplay_bits]
  change (((fixed.reverse.map (fun id => (readOne (SemiprimeSourceHistogramRows.acquire r a)
    a q.val (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits id).value))[v.val]?).getD false=true) ↔ _
  rw [List.getElem?_map,List.getElem?_eq_getElem hv,Option.map_some,Option.getD_some]
  rw [ht]
  have he : SemiprimeMaterializedScoreEnvironment.denote
      (SemiprimeSourceHistogramHeadOriginal.originalEnv r a fixed)=
      SemiprimeSourceHistogramDictRefinement.labels r a fixed :=
    SemiprimeSourceHistogramDictRefinement.labels_original r a fixed
  change _ ↔ SemiprimeMaterializedScoreEnvironment.denote
    (SemiprimeSourceHistogramHeadOriginal.originalEnv r a fixed) v.val q=g
  rw [he,hdecode]

/-- Exact complete physical activation vector, not merely final or incident bits. -/
theorem mask_vector (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (g : Fin r) :
    (acquire n F r a inputArity inputOwner q g).bits=
      List.ofFn (fun v : Fin (n+F) => decide
        (SemiprimeMaterializedScoreEnvironment.denote
          (SemiprimeSourceHistogramHeadOriginal.originalEnv r a
            (SemiprimeD1IncidenceSearch.run n F r a inputArity inputOwner).value) v.val q=g)) := by
  apply List.ext_getElem
  · simp only [mask_length,List.length_ofFn]
  · intro i hi hj
    have hiv : i<n+F := by simpa only [List.length_ofFn] using hj
    have hh := mask_value n F r a inputArity inputOwner q g ⟨i,hiv⟩
    simp only [List.getElem?_eq_getElem hi,Option.getD_some] at hh
    simp only [List.getElem_ofFn]
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hh)

/-- Exactly one actual colour child activates every old vertex, even if isolated. -/
theorem unique_group (n F r a : ℕ) [NeZero r] (inputArity : Fin F→ℕ)
    (inputOwner : ((e : Fin F)×Fin (inputArity e))→Fin n) (q : Fin a) (v : Fin (n+F)) :
    ∃! g : Fin r,((acquire n F r a inputArity inputOwner q g).bits[v.val]?).getD false=true := by
  let colour := SemiprimeMaterializedScoreEnvironment.denote
    (SemiprimeSourceHistogramHeadOriginal.originalEnv r a
      (SemiprimeD1IncidenceSearch.run n F r a inputArity inputOwner).value) v.val q
  refine ⟨colour,(mask_value n F r a inputArity inputOwner q colour v).mpr rfl,?_⟩
  intro g hg
  exact ((mask_value n F r a inputArity inputOwner q g v).mp hg).symm

end RiemannGaussian.SemiprimeD1ChildActivationOriginal
