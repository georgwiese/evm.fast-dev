import InitECandidate.Solver.WitnessRadix.WordWrites
import InitECandidate.Solver.WitnessRadix.StateSteps
import InitECandidate.Solver.Input.QuietClock
import InitECandidate.Solver.MutableTable.MemoryRegion

namespace InitECandidate.Solver.Mpt.LocalFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Analysis data for actual scalar stores sourced from caller locals or
their tuple projections. Expected words are proof data, not guest changes. -/
inductive Operand where
  | literal (word : BitVec 64)
  | saved (name : String) (word : BitVec 64)
  | selected (name : String) (index : Nat) (word : BitVec 64)
def Operand.word : Operand→BitVec 64 | .literal word | .saved _ word | .selected _ _ word=>word
def Operand.expression : Operand→ExpHOL 64
  | .literal word=>.const word | .saved name _=>localVar name | .selected name index _=>.rfield index (localVar name)
def Operand.Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Operand→Prop
  | .literal _=>True
  | .saved name word=>source.locals.lookup (ofString name)=some (.val (.word word))
  | .selected name index word=>eval source (.rfield index (localVar name))=some (.val (.word word))
structure Field where
  offset : Nat
  value : Operand
def address (baseName : String) (offset : Nat) : ExpHOL 64:=addConst (localVar baseName) (BitVec.ofNat 64 offset)
def program (baseName : String) : List Field→ProgHOL 64→ProgHOL 64
  | [],rest=>rest
  | field::tail,rest=>.seq (.store (address baseName field.offset) field.value.expression) (program baseName tail rest)
def writes (base : BitVec 64) (fields : List Field) : List (BitVec 64×BitVec 64):=
  fields.map (fun field=>(base+BitVec.ofNat 64 field.offset,field.value.word))

theorem Operand.read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : Operand) (ready : value.Ready source) :
    eval source value.expression=some (.val (.word value.word)) := by
  cases value with
  | literal word=>rfl
  | saved name word=>simpa [Ready,expression,Operand.word,eval,evalHOLExact,localVar,toExact] using ready
  | selected name index word=>exact ready

theorem Operand.ready_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (memory : WordWrites.Memory) (value : Operand)
    (ready : value.Ready source) : value.Ready {source with memory:=memory} := by
  cases value with
  | literal word=>trivial
  | saved name word=>exact ready
  | selected name index word=>exact ready

/-- Execute the real local/tuple field stores. All actual reads follow
from current bindings and survive preceding writes; no future store result
or speculative final memory is an entry premise. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (baseName : String) (base : BitVec 64) (fields : List Field)
    (baseLocal : source.locals.lookup (ofString baseName)=some (.val (.word base)))
    (ready : ∀ field∈fields,field.value.Ready source)
    (mapped : ∀ field∈fields,source.memaddrs (base+BitVec.ofNat 64 field.offset)) (rest : ProgHOL 64) :
    evaluateHOLFiniteState source (program baseName fields rest)=
      evaluateHOLFiniteState {source with memory:=WordWrites.write source.memory (writes base fields)} rest := by
  induction fields generalizing source with
  | nil=>rfl
  | cons field tail ih=>
    let middle:={source with memory:=StoreWord.put source.memory (base+BitVec.ofNat 64 field.offset) field.value.word}
    have addressRead : eval source (address baseName field.offset)=some (.val (.word (base+BitVec.ofNat 64 field.offset))):=by
      simp [eval,address,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,baseLocal,valueIsWord,valueWord,wordOpHOL,wordOp]
    have stored:=StoreWord.execute source (address baseName field.offset) field.value.expression _ _ addressRead
      (field.value.read source (ready field (by simp))) (mapped field (by simp))
    have nextReady : ∀ next∈tail,next.value.Ready middle:=by
      intro next member
      exact next.value.ready_memory source _ (ready next (by simp [member]))
    rw [program,StateSteps.next_sequence source middle _ _ stored (Nat.le_refl _),ih middle baseLocal nextReady (by intro next member; exact mapped next (by simp [member]))]
    rfl

theorem quiet (code) (baseName : String) (fields : List Field) (rest : ProgHOL 64) (quietRest : Input.QuietClock.Preserves code rest) :
    Input.QuietClock.Preserves code (program baseName fields rest) := by
  induction fields with
  | nil=>exact quietRest
  | cons field tail ih=>exact Input.QuietClock.sequence code _ _ (Input.QuietClock.store code _ _) ih

theorem writes_outside (memory : WordWrites.Memory) (region : MutableTable.MemoryRegion.Region) (valid : MutableTable.MemoryRegion.Valid region)
    (fields : List Field) (inside : ∀ field∈fields,field.offset<region.length) (query : BitVec 64)
    (outside : query.toNat<region.start ∨ region.start+region.length≤query.toNat) :
    WordWrites.write memory (writes (MutableTable.MemoryRegion.pointer region) fields) query=memory query := by
  apply WordWrites.write_away
  intro member
  simp only [writes,List.map_map,Function.comp_def] at member
  obtain ⟨field,inFields,same⟩:=List.mem_map.mp member
  have number : (MutableTable.MemoryRegion.pointer region+BitVec.ofNat 64 field.offset).toNat=region.start+field.offset:=by
    change (byteAddress (MutableTable.MemoryRegion.pointer region) field.offset).toNat=_
    rw [MutableTable.MemoryRegion.byte_address,MutableTable.MemoryRegion.address_number region valid field.offset (by have bound:=inside field inFields; omega)]
  have numeric:=congrArg BitVec.toNat same
  rw [number] at numeric
  have bound:=inside field inFields
  omega

end InitECandidate.Solver.Mpt.LocalFields

#print axioms InitECandidate.Solver.Mpt.LocalFields.Operand.read
#print axioms InitECandidate.Solver.Mpt.LocalFields.Operand.ready_memory
#print axioms InitECandidate.Solver.Mpt.LocalFields.execute
#print axioms InitECandidate.Solver.Mpt.LocalFields.quiet
#print axioms InitECandidate.Solver.Mpt.LocalFields.writes_outside
