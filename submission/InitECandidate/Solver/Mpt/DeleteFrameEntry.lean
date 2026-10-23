import InitECandidate.Solver.Mpt.DeleteFrameStack
import InitECandidate.Solver.Rlp.ValidationArena

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def allocated (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) :=
  QueryBranch.bind (Arenas.post {source with clock:=source.clock-1} .down cursor 40#64) kind.name (Arenas.resultWord .down cursor 40#64)
def stored (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (words : String→BitVec 64) :=
  {allocated kind source cursor with memory:=written kind source.memory (Arenas.resultWord .down cursor 40#64) words}

/-- A genuinely continuing original allocation/push derives room and
all initialized fields, then exposes the actual child/level advance.
The entry ready facts are only existing local scalar bindings. -/
theorem push_entry (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor frame : BitVec 64) (words : String→BitVec 64)
    (arena : Rlp.Validation.Arena source cursor frame) (before : cursor.toNat≤ceiling)
    (ready : ∀ field∈kind.fields words,field.value.Ready
      (QueryBranch.bind source kind.name (Arenas.resultWord .down cursor 40#64)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source kind.call=(none,target)) :
    let record:=Arenas.resultWord .down cursor 40#64
    let current:=stored kind source cursor words
    Arenas.Room .down cursor frame 40#64 ∧ 1≤source.clock ∧
      Saved.View current ⟨record,kind,words⟩ ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat→current.memory query=source.memory query) ∧
      current.clock=source.clock-1 ∧ current.memaddrs=source.memaddrs ∧ current.be=source.be ∧ current.code=source.code ∧
      ∃ inner,evaluateHOLFiniteState current kind.advance=(none,inner) ∧ target=restore source kind.name inner := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 40#64]=some [.val (.word 40#64)]:=rfl
  rw [kind.call_shape] at normal
  obtain ⟨room,funded,inner,continued,endpoint⟩:=Arenas.scoped_none source target .down kind.name [.const 40#64] kind.push cursor frame 40#64
    args arena.cursorGlobal arena.limitGlobal arena.ordered arena.aligned installed normal
  let record:=Arenas.resultWord .down cursor 40#64
  let entered:=allocated kind source cursor
  have baseCell : entered.locals.lookup (ofString kind.name)=some (.val (.word record)):=bind_lookup_same _ _ _
  have currentReady : ∀ field∈kind.fields words,field.value.Ready entered:=by
    intro field member
    have initial:=ready field member
    cases operandEq : field.value with
    | literal word=>trivial
    | saved name word=>rw [operandEq] at initial; exact initial
    | selected name index word=>rw [operandEq] at initial; exact initial
  obtain ⟨recordArena,recordAligned,recordLower,recordBefore,_,_⟩:=allocated_bounds cursor frame arena.lower before arena.aligned room
  have mapped : ∀ field∈kind.fields words,entered.memaddrs (record+BitVec.ofNat 64 field.offset):=by
    intro field member
    obtain ⟨inside,wordAligned⟩:=kind.geometry words field member
    exact field_mapped entered record recordArena recordAligned arena.domain field.offset (by omega) wordAligned
  change evaluateHOLFiniteState entered kind.push=(none,inner) at continued
  rw [kind.push_shape words,LocalFields.execute entered kind.name record (kind.fields words) baseCell currentReady mapped] at continued
  have view : Saved.View (stored kind source cursor words) ⟨record,kind,words⟩:=
    Saved.View.of_written entered ⟨record,kind,words⟩ recordArena recordAligned (recordBefore.trans before)
  refine ⟨room,funded,view,?_,rfl,rfl,rfl,rfl,inner,continued,endpoint⟩
  intro query above
  exact allocated_writes_above kind source.memory cursor frame words arena.lower before arena.aligned room query above

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.push_entry
