import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.InitializerControl
import InitECandidate.Solver.WitnessRadix.ByteStore

namespace InitECandidate.Solver.Input.InitializerBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def address (kind : VarKind) (name : String) (offset : Nat) : ExpHOL 64 :=
  if offset = 0 then .var kind (ofString name) else .op .add [.var kind (ofString name),.const (BitVec.ofNat 64 offset)]
def stores (kind : VarKind) (name : String) : Nat → List (BitVec 8) → ProgHOL 64 → ProgHOL 64
  | _,[],tail => tail
  | offset,byte :: rest,tail => .seq (.storeByte (address kind name offset) (.const (BitVec.ofNat 64 byte.toNat))) (stores kind name (offset + 1) rest tail)
def write (memory : WordWrites.Memory) (endian : Bool) (pointer : BitVec 64) : Nat → List (BitVec 8) → WordWrites.Memory
  | _,[] => memory
  | offset,byte :: rest => write (ByteStore.put memory endian (byteAddress pointer offset) byte) endian pointer (offset + 1) rest
def written (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (bytes : List (BitVec 8)) :=
  {source with memory := write source.memory source.be pointer offset bytes}

private theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : VarKind) (name : String) (pointer : BitVec 64) (offset : Nat)
    (binding : lookupKvarHOLFinite kind (ofString name) source = some (.val (.word pointer))) :
    QueryBranch.eval source (address kind name offset) = some (.val (.word (pointer + BitVec.ofNat 64 offset))) := by
  cases kind
  all_goals simp only [lookupKvarHOLFinite] at binding
  all_goals by_cases zero : offset = 0
  all_goals simp [address,zero,QueryBranch.eval,evalHOLExact,evalListHOLExact,toExact,binding,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Real literal byte stores in order, retaining each actual partial-word
update and resuming the literal suffix at the same source clock. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : VarKind) (name : String) (pointer : BitVec 64)
    (offset extent : Nat) (bytes : List (BitVec 8)) (tail : ProgHOL 64)
    (binding : lookupKvarHOLFinite kind (ofString name) source = some (.val (.word pointer)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer extent)
    (inside : offset + bytes.length ≤ extent) :
    evaluateHOLFiniteState source (stores kind name offset bytes tail) = evaluateHOLFiniteState (written source pointer offset bytes) tail := by
  induction bytes generalizing source offset with
  | nil => rfl
  | cons byte rest ih =>
    have mapped := AllocatedBytes.byte_mapped source pointer extent offset domain arena (by simp only [List.length_cons] at inside; omega)
    have first := ByteStore.execute source (address kind name offset) (.const (BitVec.ofNat 64 byte.toNat)) (byteAddress pointer offset) byte
      (address_read source kind name pointer offset binding) rfl mapped
    let middle := {source with memory := ByteStore.put source.memory source.be (byteAddress pointer offset) byte}
    have currentBinding : lookupKvarHOLFinite kind (ofString name) middle = some (.val (.word pointer)) := by
      cases kind <;> exact binding
    rw [stores,StateSteps.next_sequence source middle _ _ first (Nat.le_refl _)]
    have following := ih middle (offset + 1) currentBinding domain (by simp only [List.length_cons] at inside; omega)
    exact following

theorem written_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (bytes : List (BitVec 8)) (clock : Nat) :
    written {source with clock := clock} pointer offset bytes = {written source pointer offset bytes with clock := clock} := rfl

theorem written_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (bytes : List (BitVec 8)) :
    InitializerAllocations.context (written source pointer offset bytes) = InitializerAllocations.context source := InitializerAllocations.context_memory source _

theorem written_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (bytes : List (BitVec 8)) :
    (written source pointer offset bytes).globals = source.globals := rfl

theorem written_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (bytes : List (BitVec 8)) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    written {source with locals := locals} pointer offset bytes = {written source pointer offset bytes with locals := locals} := rfl

end InitECandidate.Solver.Input.InitializerBytes

#print axioms InitECandidate.Solver.Input.InitializerBytes.execute
#print axioms InitECandidate.Solver.Input.InitializerBytes.written_clock
#print axioms InitECandidate.Solver.Input.InitializerBytes.written_context
#print axioms InitECandidate.Solver.Input.InitializerBytes.written_globals
#print axioms InitECandidate.Solver.Input.InitializerBytes.written_locals
