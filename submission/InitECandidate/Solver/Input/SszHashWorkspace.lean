import InitECandidate.Solver.Input.ShaWorkspace

namespace InitECandidate.Solver.Input.SszHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Current initialized hashing pointers and physical arenas. No memory
contents, crypto properties, future run or caller cost is assumed. -/
structure Workspace (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel chunk zeros : BitVec 64) : Prop where
  sha : ShaPair.Workspace source stp accel
  stateArena : AllocatedBytes.Arena stp 64
  chunkLocal : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk))
  chunkArena : AllocatedBytes.Arena chunk 32
  chunkAligned : chunk.toNat%8=0
  zerosLocal : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros))
  zeroArena : AllocatedBytes.Arena zeros 2048

theorem Workspace.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel chunk zeros : BitVec 64)
    (actual : Workspace source stp accel chunk zeros) (code : target.code=source.code) (domain : target.memaddrs=source.memaddrs)
    (globals : ∀ key,key≠ofString "heap_ptr" → target.globals.lookup key=source.globals.lookup key) : Workspace target stp accel chunk zeros :=
  ⟨ShaPair.Workspace.of_fields source target stp accel actual.sha code domain (globals _ (by decide)) (globals _ (by decide)),actual.stateArena,
    (globals _ (by decide)).trans actual.chunkLocal,actual.chunkArena,actual.chunkAligned,(globals _ (by decide)).trans actual.zerosLocal,actual.zeroArena⟩

/-- Current workspace transport follows checked effects of the actual
execution, on errors and terminal FFI outcomes as well as normal returns. -/
theorem Workspace.after (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp accel chunk zeros : BitVec 64)
    (actual : Workspace source stp accel chunk zeros) (program : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source program=(result,target))
    (effects : ∀ key,key≠ofString "heap_ptr" → GlobalEffects.Preserves key source.code program) : Workspace target stp accel chunk zeros := by
  have fields := evaluation_fields source target program result run
  apply Workspace.of_fields source target stp accel chunk zeros actual fields.2.2.2 fields.1
  intro key different
  have frame := effects key different source rfl
  rw [run] at frame
  exact congrArg Prod.snd frame

theorem Workspace.at_callee (source : PanSemStateFiniteExact 64 Guest.HostMemory) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (stp accel chunk zeros : BitVec 64) (actual : Workspace source stp accel chunk zeros) : Workspace (callEntryStateHOLFinite source callee) stp accel chunk zeros :=
  Workspace.of_fields source _ stp accel chunk zeros actual rfl rfl (by intro key different; rfl)

end InitECandidate.Solver.Input.SszHash

#print axioms InitECandidate.Solver.Input.SszHash.Workspace.of_fields
#print axioms InitECandidate.Solver.Input.SszHash.Workspace.after
#print axioms InitECandidate.Solver.Input.SszHash.Workspace.at_callee
