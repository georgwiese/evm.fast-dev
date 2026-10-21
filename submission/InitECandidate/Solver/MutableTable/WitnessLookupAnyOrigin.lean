import InitECandidate.Solver.MutableTable.WitnessRuntimeTable
import InitECandidate.Solver.MutableTable.GetAnyOrigin
import InitECandidate.Solver.MutableTable.NodeDbFlagTail
import InitECandidate.Solver.MutableTable.NodeDbOriginalCode
import InitECandidate.Solver.MutableTable.WitnessBuildOriginalHelpers

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def OccupiedRecord (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan) (query record : BitVec 64) : Prop :=
  ∃ slot : BitVec 64,slot.toNat<(Layout32.parameters plan query).capacity.toNat ∧
    (∃ byte : UInt8,byte≠0 ∧ Find.usedByte source (Layout32.parameters plan query) slot=some byte) ∧
    source.memory (BitVec.ofNat 64 (Layout32.base plan .values)+slot*8#64)=.word record

/-- Observe the real original witness lookup result from physical getter
provenance. Only an actually occupied value word can select a record; no
logical query key or successful future record read is assumed. -/
theorem runtime_lookup_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (query : BitVec 64) (bits : Nat) (order : List Nat) (runtime : RuntimeTable source plan query bits order)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word (BitVec.ofNat 64 plan.table))))
    (hashCell : source.locals.lookup (ofString "hash")=some (.val (.word query)))
    (slices : BitVec 64→NodeDb.Slice)
    (records : ∀ record,OccupiedRecord source plan query record→source.memaddrs record ∧ source.memaddrs (record+8#64) ∧
      source.memory record=.word (slices record).1 ∧ source.memory (record+8#64)=.word (slices record).2)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source NodeDb.body=(some (.returned value),post)) :
    ∃ answer : Option (BitVec 64),value=NodeDb.output (answer.map slices) ∧ ∀ record,answer=some record→OccupiedRecord source plan query record := by
  let p:=Layout32.parameters plan query
  let vals:=BitVec.ofNat 64 (Layout32.base plan .values)
  have helpers:=original_helpers source.code installed
  have getCode:=NodeDb.original_get_code source.code installed
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [QueryBranch.localVar "db",QueryBranch.localVar "hash"]=
      some [.val (.word (BitVec.ofNat 64 plan.table)),.val (.word query)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,QueryBranch.localVar,toExact,dbCell,hashCell]
  obtain ⟨callee,called,tCell,keyCell⟩ := Get.environment source.code.lookup (BitVec.ofNat 64 plan.table) query getCode
  let entry:=callEntryStateHOLFinite source callee
  have cells : Find.HeaderCells entry (BitVec.ofNat 64 plan.table) p :=
    ⟨tCell,keyCell,runtime.header.mapped,runtime.header.capacity,runtime.header.keyLength,runtime.header.stride,runtime.header.keys,runtime.header.used⟩
  rw [NodeDb.body_shape] at normal
  obtain ⟨funded,target,returned,inner,bodyRun,checked,continued,endpoint⟩ := Input.CallNormal.scoped_normal source post "r" Get.pairShape (ofString "htab_get")
    [QueryBranch.localVar "db",QueryBranch.localVar "hash"] _ Get.body NodeDb.afterGet callee Get.pairShape args called value normal
  obtain ⟨flag,record,binary,returnedEq,origin⟩ := Get.any_body_origin entry target (BitVec.ofNat 64 plan.table) p cells rfl bits runtime.small runtime.capacity order runtime.room
    runtime.binary runtime.covered runtime.fits runtime.mapped helpers.hashCode helpers.compareCode helpers.findCode vals runtime.valsMapped runtime.valsCell runtime.values returned bodyRun
  have positiveRecord : flag=1#64→OccupiedRecord source plan query record := by
    intro one
    rcases origin with zero|⟨slot,inside,⟨byte,nonzero,loaded⟩,stored⟩
    · exact ((by decide : (1#64 : BitVec 64)≠0#64) (one.symm.trans zero)).elim
    · refine ⟨slot,inside,⟨byte,nonzero,?_⟩,stored⟩
      rw [← Find.usedByte_of_fields entry source p slot rfl rfl rfl]
      exact loaded
  have pure:=Get.any_body_readonly source.code helpers.hashCode helpers.compareCode helpers.findCode entry rfl
  rw [bodyRun] at pure
  have targetFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase source := pure
  rw [returnedEq] at continued
  let current:=Input.CallNormal.continuationEntry source target "r" (Get.pair flag record)
  have currentFrame : Input.LocalEffects.erase current=Input.LocalEffects.erase source :=
    (Input.CallNormal.continuation_erase source target "r" (Get.pair flag record)).trans targetFrame
  have memory:=Input.LocalEffects.memory_of_erase source current currentFrame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs currentFrame
  change current.memaddrs=source.memaddrs at domain
  have currentR : current.locals.lookup (ofString "r")=some (Get.pair flag record) := Input.CallNormal.continuation_lookup_same _ _ _ _
  have reads : flag=1#64→current.memaddrs record ∧ current.memaddrs (record+8#64) ∧
      current.memory record=.word (slices record).1 ∧ current.memory (record+8#64)=.word (slices record).2 := by
    intro one
    rw [domain,memory]
    exact records record (positiveRecord one)
  let answer : Option (BitVec 64):=if flag=0#64 then none else some record
  have tailRun:=NodeDb.flag_tail_execute current flag record slices currentR binary reads
  have valueEq : value=NodeDb.output (answer.map slices) := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst (continued.symm.trans tailRun)
  refine ⟨answer,valueEq,?_⟩
  intro selected hit
  by_cases zero : flag=0#64
  · simp only [answer,if_pos zero] at hit
    cases hit
  · have same : record=selected := Option.some.inj (by simpa only [answer,if_neg zero] using hit)
    rw [← same]
    exact positiveRecord (binary.resolve_left zero)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.runtime_lookup_returned
