import InitECandidate.Solver.MutableTable.InsertLookup

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix

def scanPrice (kind : KeyHash.Kind) : Nat := KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2
def tailPrice (kind : KeyHash.Kind) (count : Nat) : Nat := scanPrice kind * (count - 1) + 1
def modelPrice (kind : KeyHash.Kind) (count : Nat) : Nat := Insert.findPrice kind count + tailPrice kind count
def modelCallState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (paid : Nat) (memory : WordWrites.Memory) :=
  {source with memory := memory, clock := source.clock - paid}

end InitECandidate.Solver.MutableTable.Delete
