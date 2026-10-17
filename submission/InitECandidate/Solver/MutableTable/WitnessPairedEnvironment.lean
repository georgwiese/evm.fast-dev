import InitECandidate.Solver.MutableTable.WitnessNextEnvironment
import InitECandidate.Solver.MutableTable.WitnessCallResult

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Fixed metadata for the original and replacement constructors. No decoded
array, allocation cursor, public-memory agreement or clock is included. -/
structure PairedEnvironment (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pad scratch : BitVec 64) : Prop where
  entry : EntryEnvironment source stp pad scratch
  rightEnvironment : Keccak256.Environment right stp pad
  leftCode : source.code.lookup (ofString "nodedb_build")=some (Constructor.formals,body,.one)
  rightCode : right.code.lookup (ofString "nodedb_build")=some (Constructor.formals,Constructor.body,.one)
  leftTableCode : source.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one)
  rightTableCode : right.code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one)
  leftAllocCode : source.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one)
  rightAllocCode : right.code.lookup (ofString "alloc")=some (PersistentAlloc.formals,PersistentAlloc.body,.one)
  rightHashCode : right.code.lookup (ofString "keccak256")=some (Keccak256.formals,Keccak256.body,.one)
  helperCode : right.code.lookup (ofString "solver_radix_index")=some (BuildEntry.formals,BuildProgram.body,.one)

/-- Exact control frames of a real constructor call preserve all fixed metadata
needed to invoke the next constructor, even when the selected count is zero. -/
theorem PairedEnvironment.after_constructor (source right leftTarget rightTarget : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leftArguments rightArguments : List (ExpHOL 64)) {records table count : Nat}
    (observation : DictionaryObservation records table count) (sliceFor : BitVec 64 → Graph.Slice)
    (stp pad scratch : BitVec 64) (maximum : Nat) (region safe : BitVec 64 → Prop)
    (result : ConstructorPairResult source right leftTarget rightTarget leftArguments rightArguments observation sliceFor scratch maximum region safe)
    (environment : PairedEnvironment source right stp pad scratch) : PairedEnvironment leftTarget rightTarget stp pad scratch := by
  have leftFields:=ConstructorReturn.fields source leftTarget leftArguments table result.leftCall
  have rightFields:=ConstructorReturn.fields right rightTarget rightArguments table result.rightCall
  refine ⟨EntryEnvironment.after_constructor source leftTarget observation.plan stp pad scratch result.leftControl environment.entry,
    Keccak256.Environment.of_control (Constructor.preparedState right observation.plan) rightTarget stp pad result.rightControl
      (Constructor.prepared_environment right observation.plan stp pad environment.rightEnvironment),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [leftFields.2.2.2];exact environment.leftCode
  · rw [rightFields.2.2.2];exact environment.rightCode
  · rw [leftFields.2.2.2];exact environment.leftTableCode
  · rw [rightFields.2.2.2];exact environment.rightTableCode
  · rw [leftFields.2.2.2];exact environment.leftAllocCode
  · rw [rightFields.2.2.2];exact environment.rightAllocCode
  · rw [rightFields.2.2.2];exact environment.rightHashCode
  · rw [rightFields.2.2.2];exact environment.helperCode

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.PairedEnvironment.after_constructor
