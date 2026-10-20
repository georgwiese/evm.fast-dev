import InitECandidate.Solver.Input.BnModmulCall

namespace InitECandidate.Solver.Input.BnModmul
open Flapjack PanSemStateFiniteExact

theorem Environment.clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (entry : Environment source pointer) (clock : Nat) : Environment {source with clock := clock} pointer :=
  ⟨entry.installed,entry.params,entry.a,entry.b,entry.d,entry.oracle,entry.domain,entry.arena,entry.aligned,entry.little,entry.modulus⟩

end InitECandidate.Solver.Input.BnModmul

#print axioms InitECandidate.Solver.Input.BnModmul.Environment.clock
