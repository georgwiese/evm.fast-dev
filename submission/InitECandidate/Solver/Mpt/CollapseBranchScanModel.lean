import InitECandidate.Solver.Mpt.CollapseBranchScanStep
import InitECandidate.Solver.Mpt.TrieWalkMemory

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual scan counters and selected nonnull child, with no assumed
completion or later successful merge. -/
structure ScanModel (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) where
  index : BitVec 64
  count : BitVec 64
  selectedIndex : BitVec 64
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))
  counterCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  countCell : source.locals.lookup (ofString "count")=some (.val (.word count))
  indexCell : source.locals.lookup (ofString "idx")=some (.val (.word selectedIndex))
  bounded : index.toNat≤16
  countBound : count.toNat≤index.toNat
  indexBound : selectedIndex.toNat<16
  selectedBefore : count≠0#64 → selectedIndex.toNat<index.toNat
  selectedNonzero : count≠0#64 → wordAt source.memory (node+32#64+selectedIndex*8#64)≠0#64

/-- The two actual branches of the original scan retain the model. -/
def ScanModel.step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node child : BitVec 64)
    (model : ScanModel source node) (active : model.index.toNat<16)
    (stored : source.memory (node+32#64+model.index*8#64)=.word child) :
    ScanModel (scanned source model.index model.count child) node := by
  have indexNumber : (model.index+1#64).toNat=model.index.toNat+1:=BitVec.toNat_add_of_lt (by change model.index.toNat+1<2^64; omega)
  have countNumber : (model.count+1#64).toNat=model.count.toNat+1:=BitVec.toNat_add_of_lt (by change model.count.toNat+1<2^64; have bound:=model.countBound; omega)
  have rawChild : wordAt source.memory (node+32#64+model.index*8#64)=child:=by simp [wordAt,stored,MemoryBytes.wordBits]
  by_cases zero : child=0#64
  · refine ⟨model.index+1#64,model.count,model.selectedIndex,?_,?_,?_,?_,?_,?_,model.indexBound,?_,?_⟩
    · simpa [scanned,zero,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using model.nodeCell
    · simp [scanned,zero,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    · simpa [scanned,zero,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using model.countCell
    · simpa [scanned,zero,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using model.indexCell
    · rw [indexNumber]; omega
    · rw [indexNumber]; have bound:=model.countBound; omega
    · intro nonzero; rw [indexNumber]; exact Nat.lt_trans (model.selectedBefore nonzero) (by omega)
    · simpa only [scanned,if_pos zero,QueryBranch.bind,setVarHOLFinite] using model.selectedNonzero
  · refine ⟨model.index+1#64,model.count+1#64,model.index,?_,?_,?_,?_,?_,?_,active,?_,?_⟩
    · simpa [scanned,zero,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using model.nodeCell
    · simp [scanned,zero,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    · simp [scanned,zero,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
    · simp [scanned,zero,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]
    · rw [indexNumber]; omega
    · rw [countNumber,indexNumber]; exact Nat.add_le_add_right model.countBound 1
    · intro nonzero; rw [indexNumber]; omega
    · intro nonzero
      simp only [scanned,if_neg zero,QueryBranch.bind,setVarHOLFinite]
      rwa [rawChild]

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.ScanModel.step
