import InitECandidate.Solver.GasBudget.DirectStackInvariant

namespace InitECandidate.Solver.GasBudget.DirectStackOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Physical entry after real stack pops and a regular charge. Callers must
derive these actual effects, rather than assume a future entry model. -/
def Entry.after_charge (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : Entry source frame) (pops : Nat)
    (effect : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := target.clock})
    (budget : regularBudget target.memory frame = regularBudget source.memory frame)
    (depth : (wordAt target.memory (frame + 16#64)).toNat + pops = entry.sp.toNat)
    (outside : ∀ address, address ≠ frame + 16#64 → address ≠ frame + 64#64 → address ≠ frame + 184#64 → target.memory address = source.memory address) :
    Entry target frame := by
  have header (offset : BitVec 64) (notSP : offset ≠ 16#64) (notGas : offset ≠ 64#64) (notUsed : offset ≠ 184#64) :
      target.memory (frame + offset) = source.memory (frame + offset) :=
    outside (frame + offset) (offsets_ne frame offset 16#64 notSP) (offsets_ne frame offset 64#64 notGas) (offsets_ne frame offset 184#64 notUsed)
  have capCell := (header 232#64 (by decide) (by decide) (by decide)).trans entry.capCell
  have baseCell := (header 8#64 (by decide) (by decide) (by decide)).trans entry.baseCell
  have bounded := entry.depthBound
  exact Entry.advance source target frame entry effect budget capCell baseCell (by omega)

/-- Physical entry through a real read-only arithmetic scope. Only locals
and clock can differ; every physical stack/gas/code fact is transported. -/
def Entry.after_local (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : Entry source frame)
    (effect : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := target.clock}) : Entry target frame := by
  have memoryEq := congrArg PanSemStateFiniteExact.memory effect
  change target.memory = source.memory at memoryEq
  have canonical : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := target.clock} := by
    simpa only [memoryEq] using effect
  have budget : regularBudget target.memory frame = regularBudget source.memory frame := by rw [memoryEq]
  have capCell : target.memory (frame + 232#64) = .word entry.capacity := by rw [memoryEq]; exact entry.capCell
  have baseCell : target.memory (frame + 8#64) = .word entry.base := by rw [memoryEq]; exact entry.baseCell
  have depthBound : (wordAt target.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat := by
    rw [memoryEq]
    simpa only [wordAt, entry.spCell, WitnessRadix.MemoryBytes.wordBits] using entry.depthBound
  exact Entry.advance source target frame entry canonical budget capCell baseCell depthBound

end InitECandidate.Solver.GasBudget.DirectStackOpcode

#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.Entry.after_charge
#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.Entry.after_local
