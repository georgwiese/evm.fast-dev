import InitECandidate.Solver.Rlp.ValidationArena
import InitECandidate.Solver.Rlp.ValidationDepth
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Only current physical records, cursors and control words are modeled.
There is no premise about a future header, allocation, or loop execution. -/
structure View (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending go : BitVec 64) (frames : List Frame) : Prop where
  arena : Arena source cursor limit
  positionCell : source.locals.lookup (ofString "pos")=some (.val (.word position))
  endCell : source.locals.lookup (ofString "end")=some (.val (.word ending))
  topCell : source.locals.lookup (ofString "top")=some (.val (.word (topOf frames)))
  goCell : source.locals.lookup (ofString "go")=some (.val (.word go))
  ordered : position.toNat≤ending.toNat
  binary : go=0#64 ∨ go=1#64
  pending : Pending source.memory source.memaddrs cursor.toNat rootEnd frames ending

theorem View.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending go : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending go frames)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (globals : target.globals=source.globals)
    (positionCell : target.locals.lookup (ofString "pos")=some (.val (.word position)))
    (endCell : target.locals.lookup (ofString "end")=some (.val (.word ending)))
    (topCell : target.locals.lookup (ofString "top")=some (.val (.word (topOf frames))))
    (goCell : target.locals.lookup (ofString "go")=some (.val (.word go))) :
    View target rootEnd cursor limit position ending go frames :=
  ⟨Arena.of_fields source target cursor limit view.arena domain globals,positionCell,endCell,topCell,goCell,
    view.ordered,view.binary,by rw [memory,domain]; exact view.pending⟩

theorem View.clock (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending go : BitVec 64) (frames : List Frame) (clock : Nat)
    (view : View source rootEnd cursor limit position ending go frames) :
    View {source with clock:=clock} rootEnd cursor limit position ending go frames :=
  View.of_fields source _ _ _ _ _ _ _ _ view rfl rfl rfl view.positionCell view.endCell view.topCell view.goCell

theorem View.bound_word (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending go word : BitVec 64) (frames : List Frame) (name : String)
    (view : View source rootEnd cursor limit position ending go frames)
    (posOther : ofString name≠ofString "pos") (endOther : ofString name≠ofString "end")
    (topOther : ofString name≠ofString "top") (goOther : ofString name≠ofString "go") :
    View (bind source name word) rootEnd cursor limit position ending go frames :=
  View.of_fields source _ _ _ _ _ _ _ _ view rfl rfl rfl
    ((bind_lookup_other source name "pos" word posOther).trans view.positionCell)
    ((bind_lookup_other source name "end" word endOther).trans view.endCell)
    ((bind_lookup_other source name "top" word topOther).trans view.topCell)
    ((bind_lookup_other source name "go" word goOther).trans view.goCell)

theorem View.restored (source saved : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending go : BitVec 64) (frames : List Frame) (name : String)
    (view : View source rootEnd cursor limit position ending go frames)
    (posOther : ofString "pos"≠ofString name) (endOther : ofString "end"≠ofString name)
    (topOther : ofString "top"≠ofString name) (goOther : ofString "go"≠ofString name) :
    View (restore saved name source) rootEnd cursor limit position ending go frames :=
  View.of_fields source _ _ _ _ _ _ _ _ view rfl rfl rfl
    ((restore_lookup_other saved source name "pos" posOther).trans view.positionCell)
    ((restore_lookup_other saved source name "end" endOther).trans view.endCell)
    ((restore_lookup_other saved source name "top" topOther).trans view.topCell)
    ((restore_lookup_other saved source name "go" goOther).trans view.goCell)

theorem View.rank_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending go : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending go frames) :
    currentRank rootEnd source=rank rootEnd position frames.length (decide (go≠0#64)) :=
  current_rank_eq source rootEnd cursor position ending go frames view.arena.cursorGlobal view.positionCell view.endCell view.topCell view.goCell view.pending

def Invariant (rootEnd limit : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ cursor position ending go frames,View source rootEnd cursor limit position ending go frames

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.View.of_fields
#print axioms InitECandidate.Solver.Rlp.Validation.View.clock
#print axioms InitECandidate.Solver.Rlp.Validation.View.bound_word
#print axioms InitECandidate.Solver.Rlp.Validation.View.restored
#print axioms InitECandidate.Solver.Rlp.Validation.View.rank_eq
