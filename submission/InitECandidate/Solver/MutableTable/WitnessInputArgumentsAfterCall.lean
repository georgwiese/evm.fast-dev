import InitECandidate.Solver.MutableTable.WitnessCallResult
import InitECandidate.Solver.MutableTable.WitnessInitialization
import InitECandidate.Solver.WitnessRadix.AllocatedAway

namespace InitECandidate.Solver.MutableTable.WitnessRunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessBuild WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

theorem input_field_geometry (si stp pad out : BitVec 64) (boundary table offset : Nat)
    (siArena : Arena si 96) (siBefore : si.toNat+96≤boundary) (boundaryBefore : boundary≤table)
    (stateArena : Arena stp 200) (paddingArena : Arena pad 136) (outputArena : Arena out 32)
    (buffersBefore : stp.toNat+200≤si.toNat ∧ pad.toNat+136≤si.toNat ∧ out.toNat+32≤si.toNat)
    (inside : offset<96) :
    (byteAddress si offset).toNat<boundary ∧
      ((byteAddress si offset).toNat<table ∧ Keccak256.Protected stp pad out (byteAddress si offset)) := by
  have number:=byteAddress_toNat si offset (by have:=siArena.upper;omega)
  refine ⟨by rw [number];omega,by rw [number];omega,?_,?_,?_⟩
  · exact Arena.away_above stp _ 200 stateArena (by rw [number];have:=buffersBefore.1;omega)
  · exact Arena.away_above pad _ 136 paddingArena (by rw [number];have:=buffersBefore.2.1;omega)
  · exact Arena.away_above out _ 32 outputArena (by rw [number];have:=buffersBefore.2.2;omega)

/-- The first constructor preserves the actual input-structure fields used by
the second constructor. Both real post-call argument loads agree, after the
nodedb declaration is bound, using only actual frames and public agreement. -/
theorem arguments_after_constructor (source right leftTarget rightTarget : PanSemStateFiniteExact 64 Guest.HostMemory)
    (firstLeftArguments firstRightArguments : List (ExpHOL 64)) {records table count : Nat}
    (observation : DictionaryObservation records table count) (sliceFor : BitVec 64 → Graph.Slice)
    (stp pad scratch : BitVec 64) (maximum boundary : Nat)
    (firstCall : ConstructorPairResult source right leftTarget rightTarget firstLeftArguments firstRightArguments observation sliceFor scratch maximum
      (fun query=>query.toNat<boundary) (fun query=>query.toNat<table ∧ Keccak256.Protected stp pad scratch query))
    (si : BitVec 64) (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (locals : source.locals=right.locals) (domain : source.memaddrs=InitE.ordinaryDomain) (domains : right.memaddrs=source.memaddrs)
    (siArena : Arena si 96) (siAligned : si.toNat%8=0) (siBefore : si.toNat+96≤boundary) (boundaryBefore : boundary≤table)
    (stateArena : Arena stp 200) (paddingArena : Arena pad 136) (outputArena : Arena scratch 32)
    (buffersBefore : stp.toNat+200≤si.toNat ∧ pad.toNat+136≤si.toNat ∧ scratch.toNat+32≤si.toNat)
    (offset secondRecords secondCount : Nat) (inside : offset+16≤96) (offsetAligned : offset%8=0)
    (pointerWord : source.memory (byteAddress si offset)=.word (BitVec.ofNat 64 secondRecords))
    (countWord : source.memory (byteAddress si (offset+8))=.word (BitVec.ofNat 64 secondCount)) :
    evalListHOLFinite (withTable leftTarget "nodedb" table)
      (h:=fun q=>Classical.propDecidable ((withTable leftTarget "nodedb" table).memaddrs q)) (arguments offset)=
        some (Constructor.values secondRecords secondCount) ∧
    evalListHOLFinite (withTable rightTarget "nodedb" table)
      (h:=fun q=>Classical.propDecidable ((withTable rightTarget "nodedb" table).memaddrs q)) (arguments offset)=
        some (Constructor.values secondRecords secondCount) := by
  have firstField:=input_field_geometry si stp pad scratch boundary table offset siArena siBefore boundaryBefore
    stateArena paddingArena outputArena buffersBefore (by omega)
  have secondField:=input_field_geometry si stp pad scratch boundary table (offset+8) siArena siBefore boundaryBefore
    stateArena paddingArena outputArena buffersBefore (by omega)
  have leftFields:=ConstructorReturn.fields source leftTarget firstLeftArguments table firstCall.leftCall
  have rightFields:=ConstructorReturn.fields right rightTarget firstRightArguments table firstCall.rightCall
  have leftSi : (withTable leftTarget "nodedb" table).locals.lookup (ofString "si")=some (.val (.word si)) := by
    have old : leftTarget.locals.lookup (ofString "si")=some (.val (.word si)) := by rw [firstCall.leftCall.locals];exact siLocal
    exact (bind_lookup_other leftTarget "nodedb" "si" (BitVec.ofNat 64 table) (by decide)).trans old
  have rightSi : (withTable rightTarget "nodedb" table).locals.lookup (ofString "si")=some (.val (.word si)) := by
    have old : rightTarget.locals.lookup (ofString "si")=some (.val (.word si)) := by rw [firstCall.rightCall.locals,←locals];exact siLocal
    exact (bind_lookup_other rightTarget "nodedb" "si" (BitVec.ofNat 64 table) (by decide)).trans old
  have nextDomains : (withTable rightTarget "nodedb" table).memaddrs=(withTable leftTarget "nodedb" table).memaddrs:=
    rightFields.1.trans (domains.trans leftFields.1.symm)
  have pointerMapped : (withTable leftTarget "nodedb" table).memaddrs (byteAddress si offset) := by
    change leftTarget.memaddrs _
    rw [leftFields.1]
    exact word_mapped source si 96 offset domain siArena (by omega) siAligned offsetAligned
  have countMapped : (withTable leftTarget "nodedb" table).memaddrs (byteAddress si (offset+8)) := by
    change leftTarget.memaddrs _
    rw [leftFields.1]
    exact word_mapped source si 96 (offset+8) domain siArena (by omega) siAligned (by omega)
  exact paired_input_arguments (withTable leftTarget "nodedb" table) (withTable rightTarget "nodedb" table)
    si offset secondRecords secondCount leftSi rightSi nextDomains pointerMapped countMapped
    ((firstCall.leftFrame _ firstField.2).trans pointerWord) ((firstCall.leftFrame _ secondField.2).trans countWord)
    (fun query=>query.toNat<boundary) firstCall.memory firstField.1 secondField.1

end InitECandidate.Solver.MutableTable.WitnessRunAttempt

#print axioms InitECandidate.Solver.MutableTable.WitnessRunAttempt.input_field_geometry
#print axioms InitECandidate.Solver.MutableTable.WitnessRunAttempt.arguments_after_constructor
