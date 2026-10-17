import InitECandidate.Solver.MutableTable.FindMemory32
import InitECandidate.Solver.MutableTable.Placement

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
attribute [local instance] Classical.propDecidable

abbrev Key32:=WitnessRadix.ByteKeys.Key
abbrev Model32 (Value : Type):=Placement.Table Key32 Value

/-- The physical used bytes and stored-key views represent a logical table.
A complete table invariant must also represent values, counts and ownership. -/
structure KeyModel32 {Value : Type} (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (capacity : Nat) (table : Model32 Value) : Prop where
  used : ∀ i<capacity,usedByte snapshot p (BitVec.ofNat 64 i)=
    (match table i with | none=>some 0 | some _=>some 1)
  view : ∀ i<capacity,∀ key value,table i=some (key,value)→
    WitnessRadix.MemoryBytes.ByteView snapshot (p.keys+BitVec.ofNat 64 i*p.stride) key

def logicalAnswer {Value : Type} (result : Option (Nat×Value)) : Option (BitVec 64):=
  result.map (fun pair=>BitVec.ofNat 64 pair.1)

/-- The byte-level chain's actual comparator decisions are the logical first
match search. This bridge assumes physical table representation, not a run. -/
theorem chain_answer_model {Value : Type} (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (table : Model32 Value) (model : KeyModel32 snapshot p (2^bits) table)
    (index : BitVec 64) (length : Nat) (chain : Chain32 snapshot p index length)
    (query : Key32) (start offset fuel : Nat) (indices : index=pathIndex bits start offset) (enough : length<fuel) :
    answer chain query=logicalAnswer (Placement.lookupFrom table (2^bits) start query offset fuel) := by
  classical
  induction chain generalizing offset fuel with
  | empty index loaded=>
    have inside : Probe.slot (2^bits) start offset<2^bits:=Nat.mod_lt _ (Nat.two_pow_pos bits)
    have atSlot : usedByte snapshot p (BitVec.ofNat 64 (Probe.slot (2^bits) start offset))=some 0 := by
      simpa only [indices,pathIndex] using loaded
    rw [model.used _ inside] at atSlot
    cases cell : table (Probe.slot (2^bits) start offset) with
    | none=>
      cases fuel with
      | zero=>omega
      | succ fuel=>simp [answer,logicalAnswer,Placement.lookupFrom,cell]
    | some pair=>simp [cell] at atSlot
  | occupied index key length loaded view fits tail ih=>
    have inside : Probe.slot (2^bits) start offset<2^bits:=Nat.mod_lt _ (Nat.two_pow_pos bits)
    have atSlot : usedByte snapshot p (BitVec.ofNat 64 (Probe.slot (2^bits) start offset))=some 1 := by
      simpa only [indices,pathIndex] using loaded
    rw [model.used _ inside] at atSlot
    cases cell : table (Probe.slot (2^bits) start offset) with
    | none=>simp [cell] at atSlot
    | some pair=>
      obtain ⟨storedKey,value⟩:=pair
      have expectedView:=model.view _ inside storedKey value cell
      have actualView : WitnessRadix.MemoryBytes.ByteView snapshot
          (p.keys+BitVec.ofNat 64 (Probe.slot (2^bits) start offset)*p.stride) key := by
        simpa only [indices,pathIndex] using view
      have equal:=WitnessRadix.MemoryBytes.byteView_unique snapshot _ storedKey key expectedView actualView
      subst storedKey
      cases fuel with
      | zero=>omega
      | succ fuel=>
        by_cases same : key=query
        · simp only [answer,if_pos same,Placement.lookupFrom,cell,logicalAnswer,Option.map_some]
          exact congrArg some indices
        · have nextEq : next p index=pathIndex bits start (offset+1) := by
            rw [indices,path_advance p bits start offset small capacity]
          have recursive:=ih (offset+1) fuel nextEq (by omega)
          simpa only [answer,if_neg same,Placement.lookupFrom,cell,logicalAnswer] using recursive

/-- A physically represented and well-placed table makes an actual chain
absent exactly when the represented dictionary has no query entry. -/
theorem chain_absent_iff {Value : Type} (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (table : Model32 Value) (model : KeyModel32 snapshot p (2^bits) table)
    (home : Key32→Nat) (homes : ∀ key,home key<2^bits) (placed : Placement.NoGaps (2^bits) home table)
    (dictionary : Key32→Option Value) (rep : Placement.Represents (2^bits) table dictionary)
    (query : Key32) (length : Nat) (chain : Chain32 snapshot p (pathIndex bits (home query) 0) length)
    (bounded : length<2^bits) : answer chain query=none ↔ dictionary query=none := by
  have bridge:=chain_answer_model snapshot p bits small capacity table model _ length chain query (home query) 0 (2^bits) rfl bounded
  have dictionaryEq:=Placement.lookup_dictionary (2^bits) (Nat.two_pow_pos bits) home homes table dictionary placed rep query
  rw [bridge,logicalAnswer,← dictionaryEq]
  simp only [Option.map_eq_none_iff]

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.chain_answer_model
#print axioms InitECandidate.Solver.MutableTable.Find.chain_absent_iff
