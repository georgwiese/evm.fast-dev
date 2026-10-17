import InitECandidate.Solver.WitnessRadix.AllocationCode

namespace InitECandidate.Solver.WitnessRadix.SplitProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem branchPost_frame {F : Type} (source : PanSemStateFiniteExact 64 F)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64) :
    emptyLocalsHOLFinite (branchPost source node depth start count zeros bit dest pendingStart pendingCount pendingNode) =
      emptyLocalsHOLFinite { source with
        memory := branchMemory source.memory node depth start count zeros bit dest pendingStart pendingCount pendingNode } := rfl

theorem branchPost_other {F : Type} (source : PanSemStateFiniteExact 64 F)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64) (name : MlS)
    (notNext : ofString "node_next" ≠ name) (notDepth : ofString "depth" ≠ name)
    (notCount : ofString "count" ≠ name) (notDest : ofString "dest" ≠ name) (notBit : ofString "bit" ≠ name) :
    (branchPost source node depth start count zeros bit dest pendingStart pendingCount pendingNode).locals.lookup name =
      source.locals.lookup name := by
  simp [branchPost, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
    notNext, notDepth, notCount, notDest, notBit]

theorem restore_branch {F : Type} (saved state : PanSemStateFiniteExact 64 F) (name : String)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64)
    (notNext : ofString name ≠ ofString "node_next") (notDepth : ofString name ≠ ofString "depth")
    (notCount : ofString name ≠ ofString "count") (notDest : ofString name ≠ ofString "dest")
    (notBit : ofString name ≠ ofString "bit") :
    restore saved name (branchPost state node depth start count zeros bit dest pendingStart pendingCount pendingNode) =
      branchPost (restore saved name state) node depth start count zeros bit dest pendingStart pendingCount pendingNode := by
  unfold branchPost
  rw [restore_bind_other saved _ name "bit" _ notBit, restore_bind_other saved _ name "dest" _ notDest,
    restore_bind_other saved _ name "count" _ notCount, restore_bind_other saved _ name "depth" _ notDepth,
    restore_bind_other saved _ name "node_next" _ notNext]
  rfl

theorem mapped_of_field {F : Type} {source target : PanSemStateFiniteExact 64 F}
    (domain : source.memaddrs = target.memaddrs)
    {node depth dest pendingStart pendingCount pendingNode : BitVec 64}
    (mapped : Mapped source node depth dest pendingStart pendingCount pendingNode) :
    Mapped target node depth dest pendingStart pendingCount pendingNode := by
  rcases mapped with ⟨a,b,c,d,e,f,g⟩
  rw [domain] at a b c d e f g
  exact ⟨a,b,c,d,e,f,g⟩

end InitECandidate.Solver.WitnessRadix.SplitProgram

#print axioms InitECandidate.Solver.WitnessRadix.SplitProgram.branchPost_frame
#print axioms InitECandidate.Solver.WitnessRadix.SplitProgram.restore_branch
