import InitECandidate.Solver.MutableTable.TableRuntime.ModelHeader
import InitECandidate.Solver.MutableTable.ZeroBytes

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem cleared_byte (memory : WordWrites.Memory) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (shape : capacity = 4 ∨ capacity % 8 = 0)
    (offset : Nat) (inside : offset < capacity) :
    ZeroBytes.read (clearMemory memory false kind start capacity) (usedAddress kind start capacity + BitVec.ofNat 64 offset) = 0 := by
  by_cases four : capacity = 4
  · simpa only [clearMemory, if_pos four, Nat.zero_add] using
      ZeroBytes.memoryByte_cell memory (usedAddress kind start capacity) 0 capacity offset inside
  · simp only [clearMemory, if_neg four]
    have number : (usedAddress kind start capacity).toNat = start + 72 + stride kind * capacity + 8 * capacity := base_number kind _ valid .used
    have high := valid.upper .used
    have roundBound := (rounded_bounds capacity).1
    exact ZeroBytes.final_byte memory _ capacity offset (shape.resolve_left four) inside
      (by rw [number]; exact valid.aligned .used)
      (by rw [number]; change start + 72 + stride kind * capacity + 8 * capacity + rounded capacity ≤ 33806089496 at high; omega)

/-- The three final metadata stores preserve all actual zeroed used bytes. -/
theorem result_byte (memory : WordWrites.Memory) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (shape : capacity = 4 ∨ capacity % 8 = 0)
    (offset : Nat) (inside : offset < capacity) :
    ZeroBytes.read (resultMemory memory false kind start capacity) (usedAddress kind start capacity + BitVec.ofNat 64 offset) = 0 := by
  have usedInside : offset < size kind (fresh kind start capacity) .used := used_offset_inside kind _ offset inside
  have queryCell : panByteAlignHOL (width := 64) (usedAddress kind start capacity + BitVec.ofNat 64 offset) =
      cell (fresh kind start capacity) .used (8 * (offset / 8)) := by
    change panByteAlignHOL (width := 64) (byteAddress (cell (fresh kind start capacity) .used 0) offset) = _
    rw [offset_cell, byte_cell kind _ valid .used offset usedInside]
  have away : panByteAlignHOL (width := 64) (usedAddress kind start capacity + BitVec.ofNat 64 offset) ∉ (afterWrites kind start capacity).map Prod.fst := by
    rw [after_cells, queryCell]
    intro member
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp member
    have headerInside : other < 72 := by
      simp only [afterSites, List.mem_cons, List.not_mem_nil, or_false] at otherMember
      rcases otherMember with rfl | rfl | rfl <;> decide
    exact separate kind _ valid .header .used (by decide) other _ headerInside (by omega) same
  unfold ZeroBytes.read resultMemory
  rw [WordWrites.write_away _ _ _ away]
  exact cleared_byte _ kind start capacity valid shape offset inside

/-- A real mapped load from the completed constructor reads zero. -/
theorem result_load {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (shape : capacity = 4 ∨ capacity % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false) (offset : Nat) (inside : offset < capacity) :
    @panMemLoadByteHOL 64 _ (resultMemory source.memory source.be kind start capacity) source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (usedAddress kind start capacity + BitVec.ofNat 64 offset) = some 0 := by
  classical
  have mapped : source.memaddrs (panByteAlignHOL (width := 64) (usedAddress kind start capacity + BitVec.ofNat 64 offset)) := by
    rw [domain]
    change InitE.ordinaryDomain (panByteAlignHOL (width := 64) (byteAddress (cell (fresh kind start capacity) .used 0) offset))
    rw [offset_cell]
    exact byte_mapped kind _ valid .used offset (used_offset_inside kind _ offset inside)
  have read := result_byte source.memory kind start capacity valid shape offset inside
  rw [little]
  cases stored : resultMemory source.memory false kind start capacity (panByteAlignHOL (width := 64) (usedAddress kind start capacity + BitVec.ofNat 64 offset)) with
  | word value =>
    simp only [ZeroBytes.read, stored, MemoryBytes.wordBits] at read
    simp only [panMemLoadByteHOL, stored, if_pos mapped, read]

/-- Actual constructor result establishes the empty occupied/order model. -/
theorem entered_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (shape : capacity = 4 ∨ capacity % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false) :
    MemoryModel.Occupied (enteredState source kind start capacity) kind (fresh kind start capacity) [] := by
  constructor
  · exact List.nodup_nil
  · intro slot impossible; cases impossible
  · intro slot inside
    change @panMemLoadByteHOL 64 _ (enteredState source kind start capacity).memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (usedAddress kind start capacity + BitVec.ofNat 64 slot) = some 0
    rw [entered_memory]
    exact result_load source kind start capacity valid shape domain little slot inside
  · intro index; exact Fin.elim0 index
  · intro index; exact Fin.elim0 index

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.cleared_byte
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.result_byte
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.result_load
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.entered_model
