/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PortOwnerKeys
/-! # Original endpoint records for the physical owner router
These are proof-side identities about the acquired six-field records. No
endpoint function is supplied to the physical caller as an evaluator.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1PortOwnerEndpointEncoding
open SemiprimeMacroGraph SemiprimeD1PortOwnerKeys
open SemiprimeD1EdgeCatalogueEncoding
/-- The equality endpoint needs precisely the original edge record, terminated
by the compact-key sentinel. No coordinate arithmetic or edge permutation. -/
theorem equality_key {r t digits:ℕ} (hd:0<digits) (hc:digits≤r*t)
    (e:Edge r t digits) :
    key (endpoint hd hc e true)=edge e [true] := by
  rcases e with ⟨s,b⟩
  cases b <;> rfl
/-- The original six-field equality endpoint keys have no aliases, including
all signal constructors and both original half-edge endpoints. -/
theorem equality_key_injective (r t digits:ℕ) :
    Function.Injective (fun e:Edge r t digits=>edge e [true]) := by
  intro e f he
  rcases e with ⟨e,b⟩;rcases f with ⟨f,c⟩
  have h:=SemiprimeSourceHistogramKeyBits.frame_injective _ _ _ _ he
  have hb:b=c:=by cases b <;> cases c <;> simp_all [edge,half,sideWord]
  subst c
  have hv:vertex (.inr e:SubdividedVertex r t digits)=vertex (.inr f):=by
    exact (record_injective _ _ _ _ h.2).1
  have hv':(Sum.inr e:SubdividedVertex r t digits)=Sum.inr f:=
    SemiprimeD1VertexDescriptorDecode.vertex_injective r t digits hv
  exact Prod.ext (Sum.inr.inj hv') rfl
end RiemannGaussian.SemiprimeD1PortOwnerEndpointEncoding
