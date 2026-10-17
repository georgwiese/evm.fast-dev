import InitECandidate.Solver.WitnessRadix.TableCall
import InitECandidate.Solver.WitnessRadix.TableRecords
import InitECandidate.Solver.WitnessRadix.ConstructorTransport

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack PanSemStateFiniteExact BackingLayout

theorem call_fixed_data {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain)
    (sliceFor : BitVec 64 → Graph.Slice)
    (pointers : ∀ index < plan.count, source.memory (cell (AllocatedLayout.layout plan) .records (16 * index)) =
      .word (sliceFor (BitVec.ofNat 64 index)).1)
    (lengths : ∀ index < plan.count, source.memory (cell (AllocatedLayout.layout plan) .records (16 * index + 8)) =
      .word (sliceFor (BitVec.ofNat 64 index)).2) :
    Constructor.FixedData (callState source name plan) (AllocatedLayout.layout plan) sliceFor :=
  Constructor.fixed_of_fields (enteredState source plan) (callState source name plan) (AllocatedLayout.layout plan) sliceFor
    (entered_memory source plan) rfl (entered_fixed_data source plan ready domain sliceFor pointers lengths)

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.call_fixed_data
