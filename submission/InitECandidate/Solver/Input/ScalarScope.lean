import InitECandidate.Solver.Input.HeapFrame
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.Input.ScalarScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

/-- Actual scalar declaration and lexical restoration, abstracted before
instantiating large symbolic post-states in decoder loop proofs. -/
theorem declare_execute {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String)
    (expression : ExpHOL 64) (word : BitVec 64) (body : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (read : eval source expression=some (.val (.word word)))
    (run : evaluateHOLFiniteState (bind source name word) body=(result,target)) :
    evaluateHOLFiniteState source (.dec (ofString name) .one expression body)=(result,restore source name target) := by
  have setup : Executes source [.declare name expression] (bind source name word) (fun post=>restore source name post) :=
    Executes.declare (restoreRest:=id) word read (Executes.done _)
  have actual:=WitnessRadix.ProgramPrefix.execute setup body
  rw [run] at actual
  exact actual

end InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Input.Blob
open Flapjack PanSemStateFiniteExact WitnessRadix.QueryBranch

theorem HeapInput.bind (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (name : String) (word : BitVec 64) (heap : HeapInput source input pointer) :
    HeapInput (WitnessRadix.QueryBranch.bind source name word) input pointer :=
  HeapInput.of_fields source _ input pointer rfl rfl rfl heap

theorem HeapInput.restore (saved source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (name : String) (heap : HeapInput source input pointer) :
    HeapInput (WitnessRadix.QueryBranch.restore saved name source) input pointer :=
  HeapInput.of_fields source _ input pointer rfl rfl rfl heap

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.ScalarScope.declare_execute
#print axioms InitECandidate.Solver.Input.Blob.HeapInput.bind
#print axioms InitECandidate.Solver.Input.Blob.HeapInput.restore
