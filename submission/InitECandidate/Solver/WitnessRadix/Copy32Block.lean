import InitECandidate.Solver.WitnessRadix.Copy32Program

namespace InitECandidate.Solver.WitnessRadix.Copy32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def post {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (words : Fin 4 → BitVec 64) : PanSemStateFiniteExact 64 F :=
  QueryBranch.bind { source with memory := memory source.memory dst words } "i" 32#64

/-- The fixed memcpy block reads four original words, writes their four
separate destination cells and advances i from zero to 32, with no clock cost. -/
theorem block_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (words : Fin 4 → BitVec 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (view : MemoryBytes.WordView source src words)
    (mapped : ∀ limb : Fin 4, source.memaddrs (dst + BitVec.ofNat 64 (8 * limb.val)))
    (separate : ∀ read write : Fin 4, src + BitVec.ofNat 64 (8 * read.val) ≠ dst + BitVec.ofNat 64 (8 * write.val)) :
    evaluateHOLFiniteState source wordBody = (none, post source dst words) := by
  classical
  simp [ofString] at srcLocal dstLocal indexLocal
  have s0 := view.stored 0
  have s1 := view.stored 1
  have s2 := view.stored 2
  have s3 := view.stored (⟨3, by decide⟩ : Fin 4)
  have r0 := view.mapped 0
  have r1 := view.mapped 1
  have r2 := view.mapped 2
  have r3 := view.mapped (⟨3, by decide⟩ : Fin 4)
  have d0 := mapped 0
  have d1 := mapped 1
  have d2 := mapped 2
  have d3 := mapped (⟨3, by decide⟩ : Fin 4)
  have a10 : src + 8#64 ≠ dst := by simpa using separate 1 0
  have a20 : src + 16#64 ≠ dst := by simpa using separate 2 0
  have a21 : src + 16#64 ≠ dst + 8#64 := by simpa using separate 2 1
  have a30 : src + 24#64 ≠ dst := by simpa using separate (⟨3, by decide⟩ : Fin 4) 0
  have a31 : src + 24#64 ≠ dst + 8#64 := by simpa using separate (⟨3, by decide⟩ : Fin 4) 1
  have a32 : src + 24#64 ≠ dst + 16#64 := by simpa using separate (⟨3, by decide⟩ : Fin 4) 2
  simp at s0 s1 s2 s3 r0 r1 r2 r3 d0 d1 d2 d3
  simp [wordBody, wordStore, address, QueryBranch.localVar, QueryBranch.addConst,
    evaluateHOLFiniteState_seq, evaluateHOLFiniteState_assign, evaluateHOLFiniteState_store,
    evalHOLExact, evalListHOLExact, toExact, isValidValueHOLFinite, lookupKvarHOLFinite,
    setKvarHOLFinite, setVarHOLFinite, QueryBranch.bind, HolFiniteMapExact.update, FUPDATE, ofString,
    srcLocal, dstLocal, indexLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
    shapeOfHOLExact, shapeEqHOL, isWfShapeExactHOL, memLoadHOLExact, flattenHOL, panMemStoresHOL, panMemStoreHOL,
    r0, r1, r2, r3, d0, d1, d2, d3, s0, s1, s2, s3, a10, a20, a21, a30, a31, a32,
    fixClockHOLFinite, post, memory, writes, WordWrites.write, StoreWord.put]
  rfl

end InitECandidate.Solver.WitnessRadix.Copy32

#print axioms InitECandidate.Solver.WitnessRadix.Copy32.block_execute
