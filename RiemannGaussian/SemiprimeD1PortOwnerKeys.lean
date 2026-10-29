/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1VertexDescriptorDecode
import RiemannGaussian.SemiprimeSourceCompactWordIds
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueEmit
import RiemannGaussian.SemiprimeD1StackUnaryDivmod
/-! # Exact physical-key licence for original E-wire endpoint lookup
The endpoint equivalence and descriptor inverse below are proof-only. The
physical implementation must build both forward endpoint keys from actual
wire records and scan that acquired catalogue; no inverse/permutation is an
input. A final true sentinel makes numeric WordEqual literal-key equality.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PortOwnerKeys
open SemiprimeMacroGraph
open SemiprimeD1EdgeCatalogueEncoding (Record record vertex)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeSourceHistogramKeyBits (frame frame_injective)
open SemiprimeSourceCompactBits (Compact)
open SemiprimeBitArithmetic (bitValue)
/-- Original factor-major typed port; this is a semantic type, not a dynamic control label. -/
abbrev Port (r t digits:ℕ) := (v:SubdividedVertex r t digits)×Fin (subdividedArity v)
/-- Exact six-field port matching key, with a PHYSICALLY acquired final true sentinel. -/
def key {r t digits:ℕ} (p:Port r t digits) : List Bool :=
  frame (unary p.2.val) (record (vertex p.1) [true])
/-- Framing five actual descriptor fields is injective in all words and suffix bits. -/
theorem record_injective (w z:Record) (tail rest:List Bool) (h:record w tail=record z rest) :
    w=z ∧ tail=rest := by
  unfold record at h
  have h0:=frame_injective _ _ _ _ h
  have h1:=frame_injective _ _ _ _ h0.2
  have h2:=frame_injective _ _ _ _ h1.2
  have h3:=frame_injective _ _ _ _ h2.2
  have h4:=frame_injective _ _ _ _ h3.2
  constructor
  · funext j
    fin_cases j
    · exact h0.1
    · exact h1.1
    · exact h2.1
    · exact h3.1
    · exact h4.1
  · exact h4.2
/-- Exact original vertices and local slots cannot alias in the actual framed key format. -/
theorem key_injective (r t digits:ℕ) : Function.Injective (key (r:=r) (t:=t) (digits:=digits)) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ h
  have hf:=frame_injective _ _ _ _ h
  have hd:vertex v=vertex w:=(record_injective _ _ _ _ hf.2).1
  have hv:=SemiprimeD1VertexDescriptorDecode.vertex_injective r t digits hd
  subst w
  have hi:=congrArg List.length hf.1
  simp only [unary,List.length_replicate] at hi
  have he:i=j:=Fin.ext hi
  subst j
  rfl
/-- Appending a real true cell produces a canonical compact nonzero word. -/
theorem compact_sentinel (xs:List Bool) : Compact (xs++[true]) := by
  induction xs with
  | nil => simp [Compact]
  | cons b xs ih => simp [Compact,ih]
/-- The literal key ends in its own sentinel, not an assumed canonicalization answer. -/
theorem key_sentinel {r t digits:ℕ} (p:Port r t digits) :
    key p=frame (unary p.2.val) (record (vertex p.1) [])++[true] := by
  unfold key
  rw [SemiprimeD1StackEdgeCatalogueEmit.record_append,SemiprimeD1StackEdgeCatalogueEmit.frame_tail]
/-- Actual physical key width is compact by construction. -/
theorem key_compact {r t digits:ℕ} (p:Port r t digits) : Compact (key p) := by
  rw [key_sentinel]
  exact compact_sentinel _
/-- A physical numeric WordEqual test is exact literal port-key equality. -/
theorem key_value_iff {r t digits:ℕ} (p q:Port r t digits) : bitValue (key p)=bitValue (key q) ↔ p=q := by
  constructor
  · intro h
    exact key_injective r t digits (SemiprimeSourceCompactWordIds.compact_value_injective _ _
      (key_compact p) (key_compact q) h)
  · rintro rfl;rfl
/-- Original forward endpoint catalogue, computed from a wire and its subdivision-host side. -/
def endpoint {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t) (e:Edge r t digits) (host:Bool) : Port r t digits :=
  subdividedOrderedEndpointEquiv r t digits hd hc (e,host)
/-- Both actual endpoints are distinct, as are endpoints of different original wire keys. -/
theorem endpoint_injective {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t) :
    Function.Injective (fun p:Edge r t digits×Bool=>key (endpoint hd hc p.1 p.2)) := by
  intro p q h
  apply (subdividedOrderedEndpointEquiv r t digits hd hc).injective
  exact key_injective r t digits h
/-- Every actual port has exactly one original wire/host-side entry in the complete forward catalogue. -/
theorem endpoint_exists_unique {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t) (p:Port r t digits) :
    ∃! eh:Edge r t digits×Bool,key (endpoint hd hc eh.1 eh.2)=key p := by
  refine ⟨(subdividedOrderedEndpointEquiv r t digits hd hc).symm p,?_,?_⟩
  · change key ((subdividedOrderedEndpointEquiv r t digits hd hc)
      ((subdividedOrderedEndpointEquiv r t digits hd hc).symm p))=key p
    rw [Equiv.apply_symm_apply]
  · intro eh h
    apply (subdividedOrderedEndpointEquiv r t digits hd hc).injective
    have he:=key_injective r t digits h
    simpa only [endpoint,Prod.mk.eta,Equiv.apply_symm_apply] using he
end RiemannGaussian.SemiprimeD1PortOwnerKeys
