import InitE.SourceSemantics
import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Input.CurrentDomain
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- No wrapped address below sourceBase belongs to the actual fixed compiler
installation domain. The concrete cell count keeps the whole range below 2^64. -/
theorem ordinary_lower (address : BitVec 64) (mapped : InitE.ordinaryDomain address) :
    InitE.sourceBase ≤ address.toNat := by
  change Compiler.Backend.StackRemove.addresses 2701131776#64 3888119741 address at mapped
  obtain ⟨index, inside, same⟩ := (Compiler.Backend.StackRemove.mem_addresses _ _ _).mp mapped
  change address = 2701131776#64 + BitVec.ofNat 64 index * 8#64 at same
  have offset : (BitVec.ofNat 64 index * 8#64).toNat = index * 8 := by
    rw [← BitVec.ofNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have number : (2701131776#64 + BitVec.ofNat 64 index * 8#64).toNat = 2701131776 + index * 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [offset]; change 2701131776 + index * 8 < 2^64; omega), offset]
    rfl
  have actual := congrArg BitVec.toNat same
  rw [number] at actual
  change 2701131776 ≤ address.toNat
  omega

theorem unmapped_below_base (address : BitVec 64) (below : address.toNat < InitE.sourceBase) :
    ¬ InitE.ordinaryDomain address := by
  intro mapped
  have lower := ordinary_lower address mapped
  omega

/-- A real scalar store below the compiler's source base fails immediately.
This alone does not establish that a particular whole-program path reaches it. -/
theorem store_below_base_error {F : Type} (source : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (address value : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (below : address.toNat < InitE.sourceBase)
    (addressRead : eval source destination = some (.val (.word address)))
    (valueRead : eval source expression = some (.val (.word value))) :
    evaluateHOLFiniteState source (.store destination expression) = (some .error, source) := by
  classical
  have absent : ¬ source.memaddrs address := by rw [domain]; exact unmapped_below_base address below
  simp only [eval] at addressRead valueRead
  rw [evaluateHOLFiniteState_store, addressRead, valueRead]
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, if_neg absent]

end InitECandidate.Solver.Input.CurrentDomain

#print axioms InitECandidate.Solver.Input.CurrentDomain.ordinary_lower
#print axioms InitECandidate.Solver.Input.CurrentDomain.unmapped_below_base
#print axioms InitECandidate.Solver.Input.CurrentDomain.store_below_base_error
