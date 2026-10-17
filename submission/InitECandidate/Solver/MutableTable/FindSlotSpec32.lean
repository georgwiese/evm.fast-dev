import InitECandidate.Solver.MutableTable.FindModel32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
attribute [local instance] Classical.propDecidable

/-- Semantic result of find_slot: sentinel for absence, otherwise the native
index of a represented query entry. Values are logical until get's cell load. -/
def SlotSpec32 {Value : Type} (capacity : Nat) (sentinel word : BitVec 64) (table : Model32 Value)
    (dictionary : Key32→Option Value) (query : Key32) : Prop:=
  (word=sentinel ∧ dictionary query=none) ∨
    ∃ index value,index<capacity ∧ word.toNat=index ∧ table index=some (query,value) ∧ dictionary query=some value

theorem chain_slot_spec {Value : Type} (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (bits : Nat) (small : bits<64) (capacity : p.capacity=BitVec.ofNat 64 (2^bits))
    (table : Model32 Value) (model : KeyModel32 snapshot p (2^bits) table)
    (home : Key32→Nat) (homes : ∀ key,home key<2^bits) (placed : Placement.NoGaps (2^bits) home table)
    (dictionary : Key32→Option Value) (rep : Placement.Represents (2^bits) table dictionary)
    (query : Key32) (length : Nat) (chain : Chain32 snapshot p (pathIndex bits (home query) 0) length)
    (bounded : length<2^bits) :
    SlotSpec32 (2^bits) p.capacity ((answer chain query).getD p.capacity) table dictionary query := by
  classical
  have bridge:=chain_answer_model snapshot p bits small capacity table model _ length chain query (home query) 0 (2^bits) rfl bounded
  have dictionaryEq:=Placement.lookup_dictionary (2^bits) (Nat.two_pow_pos bits) home homes table dictionary placed rep query
  cases actual : Placement.lookupFrom table (2^bits) (home query) query 0 (2^bits) with
  | none=>
    rw [actual] at bridge dictionaryEq
    simp only [logicalAnswer,Option.map_none] at bridge
    simp only [Option.map_none] at dictionaryEq
    exact Or.inl ⟨by rw [bridge];rfl,dictionaryEq.symm⟩
  | some pair=>
    obtain ⟨index,value⟩:=pair
    have inside:=Placement.lookup_index_bound table (2^bits) (home query) query (Nat.two_pow_pos bits) 0 (2^bits) index value actual
    have cell:=Placement.lookup_sound table (2^bits) (home query) query 0 (2^bits) index value actual
    have represented:=rep.1 index inside query value cell
    rw [actual] at bridge
    simp only [logicalAnswer,Option.map_some] at bridge
    refine Or.inr ⟨index,value,inside,?_,cell,represented⟩
    rw [bridge,Option.getD_some,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have capSmall : 2^bits<2^64:=Nat.pow_lt_pow_right (by decide) small
    omega

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.chain_slot_spec
