import InitECandidate.Solver.Mpt.WitnessDecodeRecordProgram
import InitECandidate.Solver.Mpt.WitnessRecordArena
import InitECandidate.Solver.Arenas.ScopedTrace

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive RecordKind where | extension | branch
def RecordKind.name : RecordKind→String | .extension=>"rec" | .branch=>"rec2"
def RecordKind.fields : RecordKind→(String→BitVec 64)→List LocalFields.Field
  | .extension=>extensionFields | .branch=>branchFields
def RecordKind.tail : RecordKind→ProgHOL 64 | .extension=>afterExtension | .branch=>afterBranchRecord
def RecordKind.call : RecordKind→ProgHOL 64 | .extension=>extensionAllocate | .branch=>branchRecord

theorem RecordKind.call_shape (kind : RecordKind) :
    kind.call=.decCall (ofString kind.name) .one (ofString "scratch_alloc") [.const 88#64] kind.tail := by
  cases kind with
  | extension=>simp only [RecordKind.call,extensionAllocate,extension_shape,seqRest,RecordKind.name,RecordKind.tail]
  | branch=>simp only [RecordKind.call,branchRecord,branchAllocate,branch_shape,seqRest,callRest,RecordKind.name,RecordKind.tail]

theorem RecordKind.tail_shape (kind : RecordKind) (words : String→BitVec 64) :
    kind.tail=LocalFields.program kind.name (kind.fields words) (returnPair 1#64 kind.name) := by
  cases kind with
  | extension=>exact extension_tail_shape words
  | branch=>exact branch_tail_shape words

theorem RecordKind.geometry (kind : RecordKind) (words : String→BitVec 64) :
    ∀ field∈kind.fields words,field.offset+8≤88 ∧ field.offset%8=0 := by
  cases kind with
  | extension=>exact extension_geometry words
  | branch=>exact branch_geometry words

theorem RecordKind.fields_distinct (kind : RecordKind) (words : String→BitVec 64) (record : BitVec 64) :
    ((LocalFields.writes record (kind.fields words)).map Prod.fst).Nodup := by
  have offsets : ((kind.fields words).map (fun field=>BitVec.ofNat 64 field.offset)).Nodup:=by
    cases kind <;> simp only [RecordKind.fields,extensionFields,branchFields,List.map_cons,List.map_nil] <;> decide
  have injective : Function.Injective (fun offset : BitVec 64=>record+offset):=by
    intro first second same
    exact (BitVec.add_right_inj record).1 same
  simpa only [List.Nodup,LocalFields.writes,List.map_map,Function.comp_def] using offsets.map (fun offset : BitVec 64=>record+offset) (fun first second different same=>different (injective same))

/-- Genuine normal execution of either original record allocation derives
room, the fresh physical record and the decrease of its actual allowance.
The entry bindings supply only current scalar/tuple reads, not future stores. -/
theorem record_call_normal (kind : RecordKind)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (words : String→BitVec 64) (arena : Rlp.Validation.Arena source cursor limit)
    (ready : ∀ field∈kind.fields words,field.value.Ready (bind source kind.name (WitnessRecord.pointer cursor)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.call=(some (.returned value),target)) :
    Arenas.Room .down cursor limit 88#64 ∧
      AllocatedBytes.Arena (WitnessRecord.pointer cursor) 88 ∧
      Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit ∧
      (WitnessRecord.pointer cursor).toNat+88≤cursor.toNat ∧
      ((WitnessRecord.pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88 ∧
      value=.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))] ∧
      1≤source.clock ∧ emptyLocalsHOLFinite target=emptyLocalsHOLFinite
        {Arenas.post {source with clock:=source.clock-1} .down cursor 88#64 with
          memory:=WordWrites.write source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (kind.fields words))} := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 88#64]=some [.val (.word 88#64)]:=rfl
  rw [kind.call_shape] at normal
  obtain ⟨funded,room,inner,tailRun,endpoint⟩:=Arenas.scoped_normal source target .down kind.name [.const 88#64] kind.tail cursor limit 88#64
    args installed arena.cursorGlobal arena.limitGlobal arena.ordered arena.aligned value normal
  let current:=bind (Arenas.post {source with clock:=source.clock-1} .down cursor 88#64) kind.name (WitnessRecord.pointer cursor)
  change evaluateHOLFiniteState current kind.tail=(some (.returned value),inner) at tailRun
  have baseCell : current.locals.lookup (ofString kind.name)=some (.val (.word (WitnessRecord.pointer cursor))):=bind_lookup_same _ _ _
  have currentReady : ∀ field∈kind.fields words,field.value.Ready current:=by
    intro field member
    have initial:=ready field member
    cases operandEq : field.value with
    | literal word=>trivial
    | saved name word=>rw [operandEq] at initial; exact initial
    | selected name index word=>rw [operandEq] at initial; exact initial
  have mapped : ∀ field∈kind.fields words,current.memaddrs (WitnessRecord.pointer cursor+BitVec.ofNat 64 field.offset):=by
    intro field member
    obtain ⟨inside,aligned⟩:=kind.geometry words field member
    exact WitnessRecord.allocation_mapped source cursor limit arena room field.offset (by omega) aligned
  rw [kind.tail_shape words,LocalFields.execute current kind.name (WitnessRecord.pointer cursor) (kind.fields words) baseCell currentReady mapped] at tailRun
  obtain ⟨read,innerEq⟩:=Input.return_normal _ inner (.rstruct [.const 1#64,localVar kind.name]) value tailRun
  have expected : eval {current with memory:=WordWrites.write current.memory (LocalFields.writes (WitnessRecord.pointer cursor) (kind.fields words))}
      (.rstruct [.const 1#64,localVar kind.name])=some (.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))]):=by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,baseCell]
  have valueEq:=Option.some.inj (read.symm.trans expected)
  have targetEq : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {Arenas.post {source with clock:=source.clock-1} .down cursor 88#64 with
        memory:=WordWrites.write source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (kind.fields words))}:=by
    rw [endpoint,innerEq]
    rfl
  obtain ⟨recordArena,lower,upper,aligned,nonzero⟩:=WitnessRecord.allocation_bounds source cursor limit arena room
  have nextArena:=WitnessRecord.after_allocation source cursor limit arena room
  have domainEq:=congrArg PanSemStateFiniteExact.memaddrs targetEq
  have globalsEq:=congrArg PanSemStateFiniteExact.globals targetEq
  have finalArena : Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit:=by
    apply Rlp.Validation.Arena.of_fields _ target _ _ nextArena
    · exact domainEq
    · exact globalsEq
  exact ⟨room,recordArena,finalArena,upper,WitnessRecord.allowance_decreases source cursor limit arena room,valueEq,funded,targetEq⟩

/-- Every initialized field in a real returned record has its actual
stored value, including the original kind, child-array and branch index. -/
theorem record_call_cells (kind : RecordKind)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (words : String→BitVec 64) (arena : Rlp.Validation.Arena source cursor limit)
    (ready : ∀ field∈kind.fields words,field.value.Ready (bind source kind.name (WitnessRecord.pointer cursor)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.call=(some (.returned value),target)) :
    ∀ field∈kind.fields words,target.memory (WitnessRecord.pointer cursor+BitVec.ofNat 64 field.offset)=.word field.value.word := by
  obtain ⟨room,recordArena,nextArena,upper,decreases,valueEq,funded,targetEq⟩:=record_call_normal kind source target cursor limit words arena ready installed value normal
  have memory:=congrArg PanSemStateFiniteExact.memory targetEq
  change target.memory=WordWrites.write source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (kind.fields words)) at memory
  intro field member
  rw [memory]
  exact WordWrites.write_unique source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (kind.fields words))
    (WitnessRecord.pointer cursor+BitVec.ofNat 64 field.offset,field.value.word) (kind.fields_distinct words _) (List.mem_map.mpr ⟨field,member,rfl⟩)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.RecordKind.call_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.RecordKind.tail_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.RecordKind.geometry
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.RecordKind.fields_distinct
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.record_call_normal
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.record_call_cells
