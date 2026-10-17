import InitECandidate.Solver.WitnessRadix.ScatterPost

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def wordAddress (dst : BitVec 64) (cursor : Nat) : BitVec 64 :=
  dst + BitVec.ofNat 64 cursor * 8#64
def flagWord (selected : Bool) : BitVec 64 := if selected then 1#64 else 0#64

theorem destination_flag (dst : BitVec 64) (selected : Bool) (zero one : Nat) :
    destination dst (flagWord selected) (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) =
      wordAddress dst (if selected then one else zero) := by
  cases selected <;> simp [destination, flagWord, wordAddress]

/-- Read-side ownership and separation from the entire writable destination
interval. This is stable under each concrete scatter store. -/
structure Ready {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src dst start keys : BitVec 64) (keyFor : BitVec 64 → ByteKeys.Key)
    (input : List (BitVec 64)) (index limit : Nat) : Prop where
  rows : BuildCopy.Rows source.memory source.memaddrs src start index input
  views : ∀ ordinal ∈ input, MemoryBytes.ByteView source (keys + ordinal * 32#64) (keyFor ordinal)
  mapped : ∀ cursor < limit, source.memaddrs (wordAddress dst cursor)
  wordAway : ∀ cursor < limit, ∀ offset < input.length,
    BuildCopy.row src start (BitVec.ofNat 64 (index + offset)) ≠ wordAddress dst cursor
  byteAway : ∀ cursor < limit, ∀ ordinal ∈ input, ∀ byte : Fin 32,
    panByteAlignHOL (width := 64) (keys + ordinal * 32#64 + BitVec.ofNat 64 byte.val) ≠ wordAddress dst cursor

theorem ready_of_fields {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs)
    (endian : source.be = target.be) (src dst start keys : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (input : List (BitVec 64)) (index limit : Nat)
    (ready : Ready source src dst start keys keyFor input index limit) :
    Ready target src dst start keys keyFor input index limit := by
  refine ⟨?_, ?_, ?_, ready.wordAway, ready.byteAway⟩
  · rw [← memory, ← domain]
    exact ready.rows
  · intro ordinal member
    exact MemoryBytes.byteView_of_fields source target memory domain endian _ _ (ready.views ordinal member)
  · intro cursor inside
    rw [← domain]
    exact ready.mapped cursor inside

theorem ready_next {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src dst start keys ordinal : BitVec 64) (keyFor : BitVec 64 → ByteKeys.Key)
    (rest : List (BitVec 64)) (index limit zero one : Nat) (selected : Bool)
    (ready : Ready source src dst start keys keyFor (ordinal :: rest) index limit)
    (room : (if selected then one else zero) < limit) :
    Ready (post source dst (flagWord selected) ordinal (BitVec.ofNat 64 zero)
      (BitVec.ofNat 64 one) (BitVec.ofNat 64 index))
      src dst start keys keyFor rest (index + 1) limit := by
  have frame := post_frame source dst (flagWord selected) ordinal
    (BitVec.ofNat 64 zero) (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)
  have domainEq : (post source dst (flagWord selected) ordinal (BitVec.ofNat 64 zero)
      (BitVec.ofNat 64 one) (BitVec.ofNat 64 index)).memaddrs = source.memaddrs :=
    congrArg (fun state => state.memaddrs) frame
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply post_rows
    · exact ready.rows.2.2
    · intro offset inside
      rw [destination_flag]
      have away := ready.wordAway _ room (offset + 1) (by simp only [List.length_cons]; omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using away
  · intro value member
    apply post_byteView
    · exact ready.views value (List.mem_cons_of_mem ordinal member)
    · intro byte
      rw [destination_flag]
      exact ready.byteAway _ room value (List.mem_cons_of_mem ordinal member) byte
  · intro cursor inside
    rw [domainEq]
    exact ready.mapped cursor inside
  · intro cursor inside offset offsetInside
    have away := ready.wordAway cursor inside (offset + 1) (by simp only [List.length_cons]; omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using away
  · intro cursor inside value member byte
    exact ready.byteAway cursor inside value (List.mem_cons_of_mem ordinal member) byte

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.ready_next
