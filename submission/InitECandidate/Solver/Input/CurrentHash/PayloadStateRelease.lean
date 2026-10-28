import InitECandidate.Solver.Input.CurrentHash.PayloadStateTransport
import InitECandidate.Solver.Input.SavedHeapReturn
import InitECandidate.Solver.Input.HeapScopeMemory

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual saved-mark release reconstitutes the earlier parent frontier;
its geometry was established when that mark was taken, not assumed as room
for a later allocation. Memory and caller bindings are retained by this call. -/
theorem State.released {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (saved : String) (mark : BitVec 64)
    (binding : source.locals.lookup (ofString saved)=some (.val (.word mark)))
    (lower : 2701131776≤mark.toNat) (upper : mark.toNat≤2952790016) (aligned : mark.toNat%8=0) (afterChunks : ch.toNat+608≤mark.toNat)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "heap_release") [localVar saved])=(none,post)) :
    State input post blob record array ch mark chunk out zeros length start size := by
  have heap := SavedHeapReturn.release_call source post saved mark data.context.installed binding actual
  have fields := evaluation_fields source post _ none actual
  have installed : OriginalCode.Installed post.code := by rw [fields.2.2.2]; exact data.context.installed
  have global (cursorKey : Cursor) := Effects.call_preserves cursorKey source.code data.context.installed .heap_release (some none) [localVar saved] source rfl
  have zero := global .zeroHashes
  change GlobalEffects.erase (key .zeroHashes) (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "heap_release") [localVar saved])).2=_ at zero
  rw [actual] at zero
  have context : MerkleMemory.Context post mark zeros record := ⟨installed,fields.1.trans data.context.domain,(congrArg Prod.snd zero).trans data.context.zeroCell,
    data.context.zeroArena,heap,lower,upper,aligned,by have h:=data.afterRecord; omega⟩
  have chunkCell := global .lengthChunk
  change GlobalEffects.erase (key .lengthChunk) (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "heap_release") [localVar saved])).2=_ at chunkCell
  rw [actual] at chunkCell
  have memory := HeapScope.ignored_release_memory source post [localVar saved] data.context.installed actual
  have kept (name : String) := CallNormal.ignored_lookup source post (ofString name) (ofString "heap_release") [localVar saved] actual
  exact data.with_context mark context afterChunks (by intro query lower upper; exact congrFun memory query)
    ((kept "pl").trans data.payload) ((kept "raw").trans data.raw) ((kept "ch").trans data.chunks) ((kept "out").trans data.output)
    ((congrArg Prod.snd chunkCell).trans data.chunkCell)

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.released
