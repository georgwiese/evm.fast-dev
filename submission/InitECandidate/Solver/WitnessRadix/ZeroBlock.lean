import InitECandidate.Solver.WitnessRadix.ZeroProgram
import InitECandidate.Solver.WitnessRadix.Copy32Block

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def blockPost {F : Type} (source : PanSemStateFiniteExact 64 F) (dst index : BitVec 64) : PanSemStateFiniteExact 64 F :=
  bind { source with memory := Copy32.memory source.memory (dst + index) (fun _ => 0#64) } "i" (index + 32#64)

theorem block32_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (dst index : BitVec 64)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (mapped : ∀ limb : Fin 4, source.memaddrs (dst + index + BitVec.ofNat 64 (8 * limb.val))) :
    evaluateHOLFiniteState source block32 = (none, blockPost source dst index) := by
  classical
  simp [ofString] at dstLocal indexLocal
  have d0 := mapped 0
  have d1 := mapped 1
  have d2 := mapped 2
  have d3 := mapped (⟨3, by decide⟩ : Fin 4)
  simp at d0 d1 d2 d3
  simp only [BitVec.add_assoc] at d1 d2 d3
  simp [block32, wordStore, Copy32.address, increment, localVar, addConst,
    evaluateHOLFiniteState_seq, evaluateHOLFiniteState_assign, evaluateHOLFiniteState_store,
    evalHOLExact, evalListHOLExact, toExact, isValidValueHOLFinite, lookupKvarHOLFinite,
    setKvarHOLFinite, setVarHOLFinite, QueryBranch.bind, HolFiniteMapExact.update, FUPDATE, ofString,
    dstLocal, indexLocal, valueIsWord, valueWord, wordOpHOL, wordOp, shapeOfHOLExact, shapeEqHOL,
    flattenHOL, panMemStoresHOL, panMemStoreHOL, d0, d1, d2, d3, fixClockHOLFinite,
    blockPost, Copy32.memory, Copy32.writes, WordWrites.write, StoreWord.put, BitVec.add_assoc]
  rfl

def wordPost {F : Type} (source : PanSemStateFiniteExact 64 F) (dst index : BitVec 64) : PanSemStateFiniteExact 64 F :=
  bind { source with memory := StoreWord.put source.memory (dst + index) 0#64 } "i" (index + 8#64)

theorem blockWord_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (dst index : BitVec 64)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (mapped : source.memaddrs (dst + index)) :
    evaluateHOLFiniteState source blockWord = (none, wordPost source dst index) := by
  classical
  simp [ofString] at dstLocal indexLocal
  simp [blockWord, wordStore, Copy32.address, increment, localVar, addConst,
    evaluateHOLFiniteState_seq, evaluateHOLFiniteState_assign, evaluateHOLFiniteState_store,
    evalHOLExact, evalListHOLExact, toExact, isValidValueHOLFinite, lookupKvarHOLFinite,
    setKvarHOLFinite, setVarHOLFinite, QueryBranch.bind, HolFiniteMapExact.update, FUPDATE, ofString,
    dstLocal, indexLocal, valueIsWord, valueWord, wordOpHOL, wordOp, shapeOfHOLExact, shapeEqHOL,
    flattenHOL, panMemStoresHOL, panMemStoreHOL, mapped, fixClockHOLFinite, wordPost, StoreWord.put]
  rfl

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.block32_execute
#print axioms InitECandidate.Solver.WitnessRadix.Zero.blockWord_execute
