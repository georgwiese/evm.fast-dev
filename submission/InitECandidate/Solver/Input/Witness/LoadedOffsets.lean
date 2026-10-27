import InitECandidate.Solver.Input.Witness.OffsetProgram
import InitECandidate.Solver.Input.RequestOffsetsStores
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
open WitnessRadix.ProgramPrefix

def firstLoaded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (start : Nat):=
  bind source "w0" (offsetWord input start 0)
def secondLoaded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (start : Nat):=
  bind (firstLoaded source input start) "w1" (offsetWord input start 1)
def loadedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (start : Nat):=
  bind (secondLoaded source input start) "w2" (offsetWord input start 2)
def restoreLoaded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (start : Nat)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory):=
  restore source "w0" (restore (firstLoaded source input start) "w1" (restore (secondLoaded source input start) "w2" target))

theorem load_word_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (expression : ExpHOL 64)
    (address value : BitVec 64) (read : eval source expression=some (.val (.word address)))
    (mapped : source.memaddrs address) (cell : source.memory address=.word value) :
    eval source (.load .one expression)=some (.val (.word value)) := by
  classical
  simp only [eval] at read ⊢
  simp [evalHOLExact,read,memLoadHOLExact,isWfShapeExactHOL,toExact,mapped,cell]

/-- The actual three mapped offset loads enter the real node-list call with
all declaration scopes retained; no memory or source clock changes. -/
theorem loaded_offsets_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (array : BitVec 64) (start : Nat)
    (offsets : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (mapped : ∀ position<3,source.memaddrs (byteAddress array (8*position)))
    (cells : ∀ position<3,source.memory (byteAddress array (8*position))=.word (offsetWord input start position)) :
    evaluateHOLFiniteState source loadedBody=
      (let output:=evaluateHOLFiniteState (loadedState source input start) nodeCall;
        (output.1,restoreLoaded source input start output.2)) := by
  have read0:=load_word_read source Header.offsets array (offsetWord input start 0) (Request.offsets_global source array offsets)
    (by simpa [byteAddress] using mapped 0 (by decide)) (by simpa [byteAddress] using cells 0 (by decide))
  have read1:=load_word_read (firstLoaded source input start) (Scalar.plus Header.offsets 8) (byteAddress array 8) (offsetWord input start 1)
    (Scalar.plus_read _ Header.offsets array 8 (Request.offsets_global _ array offsets)) (mapped 1 (by decide)) (cells 1 (by decide))
  have read2:=load_word_read (secondLoaded source input start) (Scalar.plus Header.offsets 16) (byteAddress array 16) (offsetWord input start 2)
    (Scalar.plus_read _ Header.offsets array 16 (Request.offsets_global _ array offsets)) (mapped 2 (by decide)) (cells 2 (by decide))
  have setup : Executes source [.declare "w0" (.load .one Header.offsets),
      .declare "w1" (.load .one (Scalar.plus Header.offsets 8)),.declare "w2" (.load .one (Scalar.plus Header.offsets 16))]
      (loadedState source input start) (restoreLoaded source input start) := by
    unfold restoreLoaded
    refine Executes.declare (restoreRest:=fun target=>restore (firstLoaded source input start) "w1" (restore (secondLoaded source input start) "w2" target)) _ read0 ?_
    refine Executes.declare (restoreRest:=fun target=>restore (secondLoaded source input start) "w2" target) _ read1 ?_
    refine Executes.declare (restoreRest:=id) _ read2 ?_
    exact Executes.done _
  rw [offset_shapes.2.2.2]
  exact WitnessRadix.ProgramPrefix.execute setup nodeCall

theorem loaded_offset_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (start : Nat) :
    (loadedState source input start).locals.lookup (ofString "w0")=some (.val (.word (offsetWord input start 0))) ∧
      (loadedState source input start).locals.lookup (ofString "w1")=some (.val (.word (offsetWord input start 1))) ∧
      (loadedState source input start).locals.lookup (ofString "w2")=some (.val (.word (offsetWord input start 2))) := by
  exact ⟨(bind_lookup_other _ "w2" "w0" _ (by decide)).trans
      ((bind_lookup_other _ "w1" "w0" _ (by decide)).trans (bind_lookup_same _ _ _)),
    (bind_lookup_other _ "w2" "w1" _ (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _⟩

theorem loaded_other_local (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (start : Nat) (name : MlS)
    (different : name≠ofString "w0" ∧ name≠ofString "w1" ∧ name≠ofString "w2") :
    (loadedState source input start).locals.lookup name=source.locals.lookup name := by
  change (((source.locals.update _).update _).update _).lookup name=_
  simp [HolFiniteMapExact.lookup_update,FUPDATE,
    show (ofString "w0"==name)=false from beq_eq_false_iff_ne.mpr (Ne.symm different.1),
    show (ofString "w1"==name)=false from beq_eq_false_iff_ne.mpr (Ne.symm different.2.1),
    show (ofString "w2"==name)=false from beq_eq_false_iff_ne.mpr (Ne.symm different.2.2)]

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.load_word_read
#print axioms InitECandidate.Solver.Input.Witness.loaded_offsets_execute
#print axioms InitECandidate.Solver.Input.Witness.loaded_offset_locals
#print axioms InitECandidate.Solver.Input.Witness.loaded_other_local
