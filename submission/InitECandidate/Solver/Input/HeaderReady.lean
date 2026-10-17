import InitECandidate.Solver.Input.HeaderGuard

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Derive the actual guard arguments and two-word array from its concrete
local/global/header cells, independently of how those cells were installed. -/
theorem guard_ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array total : BitVec 64)
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total)))
    (firstMapped : source.memaddrs array) (secondMapped : source.memaddrs (array+8#64))
    (firstCell : source.memory array=.word (firstWord input)) (secondCell : source.memory (array+8#64)=.word (secondWord input)) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) guardArguments=
      some (Offsets.arguments array 16#64 total 2) ∧
    (∀ position<2,source.memaddrs (array+BitVec.ofNat 64 (8*position))) ∧
    (∀ position<2,source.memory (array+BitVec.ofNat 64 (8*position))=.word (offsetWords input position)) := by
  classical
  refine ⟨?_,?_,?_⟩
  · simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,guardArguments,Offsets.arguments,
      offsets,WitnessRadix.QueryBranch.localVar,arrayGlobal,totalLocal]
  · intro position small
    have alternatives : position=0 ∨ position=1 := by omega
    rcases alternatives with rfl|rfl
    · simpa using firstMapped
    · simpa using secondMapped
  · intro position small
    have alternatives : position=0 ∨ position=1 := by omega
    rcases alternatives with rfl|rfl
    · simpa [offsetWords] using firstCell
    · simpa [offsetWords] using secondCell

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.guard_ready
