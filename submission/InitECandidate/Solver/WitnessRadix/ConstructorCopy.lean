import InitECandidate.Solver.WitnessRadix.ConstructorStores
import InitECandidate.Solver.WitnessRadix.Copy32Alignment

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

theorem copy_arguments {F : Type} (source : PanSemStateFiniteExact 64 F)
    (keys vals order records index hashScratch : BitVec 64)
    (locals : Locals source keys vals order records index)
    (global : source.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word hashScratch))) :
    evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      copyArguments = some (Copy32.values (keys + index * 32#64) hashScratch) := by
  simp [copyArguments, scaled, scratch, localVar, Copy32.values, evalListHOLFinite,
    evalListHOLExact, evalHOLExact, toExact, locals.keysLocal, locals.indexLocal, global,
    panOpHOL, valueIsWord, valueWord, wordOpHOL, wordOp]

def copyPost {F : Type} (source : PanSemStateFiniteExact 64 F)
    (keys index : BitVec 64) (words : Fin 4 → BitVec 64) : PanSemStateFiniteExact 64 F :=
  { source with
    memory := Copy32.memory source.memory (keys + index * 32#64) words
    clock := source.clock - 2 }

/-- The real constructor suffix after hashing: copy all four digest words,
store the record pointer and ordinal, then advance the ordinal. -/
theorem after_hash_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (keys vals order records index hashScratch : BitVec 64) (words : Fin 4 → BitVec 64)
    (locals : Locals source keys vals order records index)
    (global : source.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word hashScratch)))
    (code : source.code.lookup (ofString "memcpy") = some (Copy32.formals, Copy32.body, .one))
    (srcAligned : hashScratch.toNat % 8 = 0) (dstAligned : (keys + index * 32#64).toNat % 8 = 0)
    (view : MemoryBytes.WordView source hashScratch words)
    (mapped : ∀ limb : Fin 4, source.memaddrs (keys + index * 32#64 + BitVec.ofNat 64 (8 * limb.val)))
    (separate : ∀ read write : Fin 4,
      hashScratch + BitVec.ofNat 64 (8 * read.val) ≠ keys + index * 32#64 + BitVec.ofNat 64 (8 * write.val))
    (valsMapped : source.memaddrs (vals + index * 8#64))
    (orderMapped : source.memaddrs (order + index * 8#64)) (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source afterHash =
      (none, storesPost (copyPost source keys index words) vals order records index) := by
  classical
  obtain ⟨callee, lookup, dstLocal, srcLocal, lengthLocal, _⟩ :=
    Copy32.environment source.code.lookup (keys + index * 32#64) hashScratch code
  have args := copy_arguments source keys vals order records index hashScratch locals global
  have copied := Copy32.call_execute source callee copyArguments hashScratch (keys + index * 32#64)
    words args lookup srcLocal dstLocal lengthLocal
    (Copy32.alignment_mask _ _ srcAligned dstAligned) view mapped separate enough
  have locals' : Locals (copyPost source keys index words) keys vals order records index :=
    ⟨locals.keysLocal, locals.valsLocal, locals.orderLocal, locals.recordsLocal, locals.indexLocal⟩
  have finished := stores_execute (copyPost source keys index words) keys vals order records index
    locals' valsMapped orderMapped
  rw [afterHash, StateSteps.next_sequence source (copyPost source keys index words) _ _ copied (by
    change source.clock - 2 ≤ source.clock; omega)]
  exact finished

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.copy_arguments
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.after_hash_execute
