/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeTags
/-! # Raw edge/side bytes and native resolved tags agree at every actual child position
Every equality below follows the actual original ID bank and same-position
resolution. No chosen bijection, caller permutation or decoded tag is advised.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeTagResolution
namespace Raw
export SemiprimeD1StackChildGroupFactoryNativeTags (edgeFor rawTag edgeFor_pair)
end Raw
namespace Native
export SemiprimeD1ChildAssignmentEquiv (Tag acquired tags scope childEquiv childEquiv_value tags_length)
export SemiprimeD1ChildAssignmentEndpoint (endpoint_pair childEquiv_resolve childEquiv_endpoint)
export SemiprimeD1ChildPortBijection (linkVertex)
export SemiprimeD1ChildPortPullbackCorrectness (resolve ids_value ids_nodup findPort_member)
end Native
/-- The actually resolved original typed port keeps its actual original edge word. -/
theorem resolved_edge (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (q:Fin a) (g:Fin 64) (endpoint:SemiprimeD1ChildGraph.Endpoint (n+F))
    (he:endpoint∈(Native.acquired n F 64 a arity owner q g).graph.factors.flatten)
    (tag:Native.Tag arity) (hr:Native.resolve (Native.acquired n F 64 a arity owner q g).ids endpoint=some tag):
    Raw.edgeFor n F a arity owner tag.1=endpoint.edge:=by
  obtain ⟨pair,hp,horigin⟩:=Native.endpoint_pair n F 64 a arity owner q g endpoint he
  have hfind:(SemiprimeD1ChildPortPullback.findPort pair.2.edge
      (Native.acquired n F 64 a arity owner q g).ids).value=some pair.1:=by
    apply Native.findPort_member _ (Native.ids_nodup n F 64 a arity owner q g)
    rw [Native.ids_value]
    exact List.mem_map.mpr ⟨pair,hp,rfl⟩
  rcases horigin with hleft|hright
  · subst endpoint
    change (SemiprimeD1ChildPortPullback.findPort pair.2.edge _).value.map (fun port=>(port,true))=some tag at hr
    rw [hfind] at hr
    have ht:(pair.1,true)=tag:=Option.some.inj hr
    subst tag
    exact Raw.edgeFor_pair n F a arity owner pair hp
  · subst endpoint
    change (SemiprimeD1ChildPortPullback.findPort pair.2.edge _).value.map (fun port=>(port,false))=some tag at hr
    rw [hfind] at hr
    have ht:(pair.1,false)=tag:=Option.some.inj hr
    subst tag
    exact Raw.edgeFor_pair n F a arity owner pair hp
/-- Complete vertex/raw-tag stream at the SAME actual native child positions. -/
theorem tags_with_vertices (n F a:Nat) (arity:Fin F→Nat) (owner:((e:Fin F)×Fin (arity e))→Fin n)
    (q:Fin a) (g:Fin 64):
    (Native.tags n F 64 a arity owner q g).map (fun t=>(Native.linkVertex owner t,Raw.rawTag n F a arity owner t))=
      (Native.acquired n F 64 a arity owner q g).graph.factors.flatten.map
        (fun e=>(e.vertex,SemiprimeSourceHistogramKeyBits.frame e.edge [e.side])):=by
  apply List.ext_getElem
  · simp only [List.length_map]
    exact Native.tags_length n F 64 a arity owner q g
  · intro j hj he
    have hscope:j<Native.scope n F 64 a arity owner q g:=by
      simpa only [List.length_map,Native.scope] using he
    let index:Fin (Native.scope n F 64 a arity owner q g):=⟨j,hscope⟩
    have hres:=Native.childEquiv_resolve n F 64 a arity owner q g index
    have hv:=Native.childEquiv_endpoint n F 64 a arity owner q g index
    have htag:=Native.childEquiv_value n F 64 a arity owner q g index
    have hedge:=resolved_edge n F a arity owner q g _ (List.getElem_mem hscope) _ hres
    rw [htag] at hv hedge
    simp only [List.getElem_map]
    apply Prod.ext
    · exact hv.1
    · dsimp only [Raw.rawTag]
      rw [hedge,hv.2]
      rfl
/-- Exact first index is unchanged by an injective original tag codec, even when a query is absent. -/
theorem idxOf_map {A B:Type} [BEq A] [LawfulBEq A] [BEq B] [LawfulBEq B]
    (code:A→B) (hi:Function.Injective code) (xs:List A) (target:A):
    (xs.map code).idxOf (code target)=xs.idxOf target:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    by_cases h:x=target
    · subst target;simp only [List.map_cons,List.idxOf_cons_self]
    · have hn:code x≠code target:=fun he=>h (hi he)
      simp only [List.map_cons,List.idxOf_cons_ne _ hn,List.idxOf_cons_ne _ h,ih]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryNativeTagResolution
