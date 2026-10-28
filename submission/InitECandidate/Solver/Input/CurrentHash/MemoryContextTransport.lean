import InitECandidate.Solver.Input.CurrentHash.MerkleMemory
import InitECandidate.Solver.Input.CurrentHash.Effects

namespace InitECandidate.Solver.Input.CurrentHash.MerkleMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Transport the actual immutable/workspace facts through a current helper.
Heap restoration is supplied by that same call's normal-return frame. -/
theorem Context.after_call {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {cursor zeros query : BitVec 64}
    (data : Context source cursor zeros query) (routine : Code.Routine) (arguments : List (ExpHOL 64))
    (heap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (Code.name routine) arguments)=(none,post)) : Context post cursor zeros query := by
  have fields := evaluation_fields source post _ none actual
  have installed : OriginalCode.Installed post.code := by rw [fields.2.2.2]; exact data.installed
  have frame := Effects.call_preserves .zeroHashes source.code data.installed routine (some none) arguments source rfl
  change GlobalEffects.erase (key .zeroHashes) (evaluateHOLFiniteState source (.call (some (none,none)) (Code.name routine) arguments)).2 = _ at frame
  rw [actual] at frame
  exact ⟨installed,fields.1.trans data.domain,(congrArg Prod.snd frame).trans data.zeroCell,data.zeroArena,heap,
    data.heapLower,data.heapBound,data.aligned,data.below⟩

end InitECandidate.Solver.Input.CurrentHash.MerkleMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleMemory.Context.after_call
