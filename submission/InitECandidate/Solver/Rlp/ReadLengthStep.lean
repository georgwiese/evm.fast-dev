import InitECandidate.Solver.Rlp.ReadLengthProgram
import InitECandidate.Solver.WitnessRadix.BindingLookup
import InitECandidate.Solver.Input.ScalarAssignNormal
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Rlp.ReadLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

noncomputable def byte (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address : BitVec 64) : Option UInt8 :=
  @panMemLoadByteHOL 64 _ source.memory source.memaddrs
    (fun query => Classical.propDecidable (source.memaddrs query)) source.be address

structure Locals (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length index value : BitVec 64) : Prop where
  pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length))
  indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))
  valueCell : source.locals.lookup (ofString "v")=some (.val (.word value))

def stepPost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (index value : BitVec 64) (loaded : UInt8) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind (bind source "v" ((value <<< (8 : Nat)) ||| BitVec.ofNat 64 loaded.toNat)) "i" (index+1#64)

theorem step_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length index value : BitVec 64) (loaded : UInt8) (view : Locals source pointer length index value) :
    Locals (stepPost source index value loaded) pointer length (index+1#64)
      ((value <<< (8 : Nat)) ||| BitVec.ofNat 64 loaded.toNat) := by
  refine ⟨?_,?_,bind_lookup_same _ _ _,?_⟩
  · exact (bind_lookup_other _ "i" "p" _ (by decide)).trans
      ((bind_lookup_other _ "v" "p" _ (by decide)).trans view.pointerCell)
  · exact (bind_lookup_other _ "i" "n" _ (by decide)).trans
      ((bind_lookup_other _ "v" "n" _ (by decide)).trans view.lengthCell)
  · exact (bind_lookup_other _ "i" "v" _ (by decide)).trans (bind_lookup_same _ _ _)

/-- A real normal reader iteration exposes its actual byte and both exact
local updates. Byte mapping and successful evaluation are conclusions. -/
theorem step_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length index value : BitVec 64) (view : Locals source pointer length index value)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    ∃ loaded : UInt8, byte source (pointer+index)=some loaded ∧ target=stepPost source index value loaded := by
  classical
  obtain ⟨middle,first,second⟩ := Input.sequence_none source target accumulate increment normal
  obtain ⟨actual,read,middleEq⟩ := Input.scalar_assign_none source middle "v" _ value view.valueCell first
  cases loadedRead : byte source (pointer+index) with
  | none =>
    simp [byte] at loadedRead
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,view.pointerCell,
      view.indexCell,view.valueCell,valueIsWord,valueWord,wordOpHOL,wordOp,loadedRead] at read
  | some loaded =>
    have accumulated : eval source (.op .or
        [.shift .lsl (localVar "v") (.const 8#64),.loadByte (.op .add [localVar "p",localVar "i"])])=
        some (.val (.word ((value <<< (8 : Nat)) ||| BitVec.ofNat 64 loaded.toNat))) := by
      have actualByte : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
          (fun query => Classical.propDecidable (source.memaddrs query)) source.be (pointer+index)=some loaded := loadedRead
      simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,view.pointerCell,
        view.indexCell,view.valueCell,valueIsWord,valueWord,wordOpHOL,wordOp,wordShiftHOL,OrOp.or,actualByte]
    have valueEq : actual=(value <<< (8 : Nat)) ||| BitVec.ofNat 64 loaded.toNat := by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans accumulated
    rw [valueEq] at middleEq
    have indexCell : middle.locals.lookup (ofString "i")=some (.val (.word index)) := by
      rw [middleEq]
      exact (bind_lookup_other _ "v" "i" _ (by decide)).trans view.indexCell
    have nextRead : eval middle (.op .add [localVar "i",.const 1#64])=some (.val (.word (index+1#64))) := by
      simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have targetEq := Input.assign_none middle target "i" _ (index+1#64) nextRead second
    exact ⟨loaded,rfl,by rw [targetEq,middleEq]; rfl⟩

end InitECandidate.Solver.Rlp.ReadLength

#print axioms InitECandidate.Solver.Rlp.ReadLength.step_locals
#print axioms InitECandidate.Solver.Rlp.ReadLength.step_none
