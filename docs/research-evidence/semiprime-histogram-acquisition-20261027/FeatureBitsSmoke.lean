import RiemannGaussian.SemiprimeSourceHistogramFeatureBitsBounds
import RiemannGaussian.SemiprimeSourceHistogramPrefix
set_option autoImplicit false
open RiemannGaussian
open SemiprimeBitArithmetic

def featureArity (_ : Fin 2) : ℕ := 2

def featureOwner (i : (e : Fin 2)×Fin (featureArity e)) : Fin 3 :=
  ⟨(i.1.val+i.2.val)%3,Nat.mod_lt _ (by decide)⟩

def matrix (dict : SemiprimeSourceHistogramTrie.Trie) (k s : ℕ)
    (rows : List SemiprimeSourceHistogramPortKeys.PortRecord) : List (List ℕ) :=
  (List.finRange 4).map (fun f => (List.finRange 4).map (fun g =>
    bitValue (SemiprimeSourceHistogramFeatureBits.acquire dict k s f g rows).bits))

#eval let rows := (SemiprimeSourceHistogramPortKeys.acquireOriginal 3 2 1 featureArity featureOwner).records
      matrix .empty 0 5 rows

#eval let ids := (SemiprimeSourceCompactWordIds.acquire 3).value
      let fixed := [ids[2]!,ids[0]!,ids[1]!]
      let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
      let rows := (SemiprimeSourceHistogramPortKeys.acquireOriginal 3 2 1 featureArity featureOwner).records
      matrix dict 3 2 rows

#eval let ids := (SemiprimeSourceCompactWordIds.acquire 3).value
      let fixed := [ids[0]!,ids[1]!,ids[2]!,ids[0]!,ids[1]!]
      let dict := (SemiprimeSourceHistogramPrefix.acquire fixed).trie
      let rows := (SemiprimeSourceHistogramPortKeys.acquireOriginal 3 2 0 featureArity featureOwner).records
      matrix dict 5 0 rows

#eval let rows := (SemiprimeSourceHistogramPortKeys.acquireOriginal 3 2 1 featureArity featureOwner).records
      (List.finRange 4).all (fun f => (List.finRange 4).all (fun g =>
        (SemiprimeSourceHistogramFeatureBits.acquire .empty 0 5 f g rows).clock ≤
          SemiprimeSourceHistogramFeatureBitsBounds.budget 5 3 rows.length))
