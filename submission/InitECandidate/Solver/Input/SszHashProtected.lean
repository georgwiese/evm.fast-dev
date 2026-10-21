import InitECandidate.Solver.Input.SszHashWorkspace
import InitECandidate.Solver.Input.CopyAwaySubrange

namespace InitECandidate.Solver.Input.SszHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Current initialized workspace and one word outside its actual mutable
crypto regions. This is geometric separation only: it makes no assertion
about that word's contents or any future execution. -/
structure Protected (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel chunk zeros query : BitVec 64) : Prop where
  workspace : Workspace source stp accel chunk zeros
  stateAway : CopyGeneral.Away stp query 64
  accelAway : CopyGeneral.Away accel query 96
  chunkAway : CopyGeneral.Away chunk query 32

theorem Protected.with_workspace (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel chunk zeros query : BitVec 64)
    (actual : Protected source stp accel chunk zeros query) (workspace : Workspace target stp accel chunk zeros) : Protected target stp accel chunk zeros query :=
  ⟨workspace,actual.stateAway,actual.accelAway,actual.chunkAway⟩

theorem Protected.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel chunk zeros query : BitVec 64)
    (actual : Protected source stp accel chunk zeros query) (code : target.code=source.code) (domain : target.memaddrs=source.memaddrs)
    (globals : ∀ key,key≠ofString "heap_ptr" → target.globals.lookup key=source.globals.lookup key) : Protected target stp accel chunk zeros query :=
  actual.with_workspace source target stp accel chunk zeros query (Workspace.of_fields source target stp accel chunk zeros actual.workspace code domain globals)

theorem Protected.after (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel chunk zeros query : BitVec 64)
    (actual : Protected source stp accel chunk zeros query) (program : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source program=(result,target))
    (effects : ∀ key,key≠ofString "heap_ptr" → GlobalEffects.Preserves key source.code program) : Protected target stp accel chunk zeros query :=
  actual.with_workspace source target stp accel chunk zeros query (Workspace.after source target stp accel chunk zeros actual.workspace program result run effects)

theorem Protected.at_callee (source : PanSemStateFiniteExact 64 Guest.HostMemory) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (stp accel chunk zeros query : BitVec 64)
    (actual : Protected source stp accel chunk zeros query) : Protected (callEntryStateHOLFinite source callee) stp accel chunk zeros query :=
  actual.with_workspace source _ stp accel chunk zeros query (Workspace.at_callee source callee stp accel chunk zeros actual.workspace)

end InitECandidate.Solver.Input.SszHash

#print axioms InitECandidate.Solver.Input.SszHash.Protected.with_workspace
#print axioms InitECandidate.Solver.Input.SszHash.Protected.of_fields
#print axioms InitECandidate.Solver.Input.SszHash.Protected.after
#print axioms InitECandidate.Solver.Input.SszHash.Protected.at_callee
