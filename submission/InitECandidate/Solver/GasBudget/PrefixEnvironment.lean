import InitECandidate.Solver.GasBudget.StackPopPrefixEffect

namespace InitECandidate.Solver.GasBudget
open Flapjack PanSemStateFiniteExact

theorem StackPop.PrefixEffect.code_eq {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : StackPop.PrefixEffect source target frame paid) : target.code = source.code := by
  have fields := congrArg PanSemStateFiniteExact.code effect.fields
  exact fields

theorem StackPop.PrefixEffect.globals_eq {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : StackPop.PrefixEffect source target frame paid) : target.globals = source.globals := by
  have fields := congrArg PanSemStateFiniteExact.globals effect.fields
  exact fields

theorem StackPop.PrefixEffect.eshapes_eq {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : StackPop.PrefixEffect source target frame paid) : target.eshapes = source.eshapes := by
  have fields := congrArg PanSemStateFiniteExact.eshapes effect.fields
  exact fields

theorem StackPop.PrefixEffect.memaddrs_eq {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame : BitVec 64} {paid : Nat}
    (effect : StackPop.PrefixEffect source target frame paid) : target.memaddrs = source.memaddrs := by
  have fields := congrArg PanSemStateFiniteExact.memaddrs effect.fields
  exact fields

theorem memory_word (memory : BitVec 64 → HolWordLab 64) (address : BitVec 64) :
    memory address = .word (wordAt memory address) := by
  cases cell : memory address with
  | word value => simp [wordAt, cell, WitnessRadix.MemoryBytes.wordBits]

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.code_eq
#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.globals_eq
#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.eshapes_eq
#print axioms InitECandidate.Solver.GasBudget.StackPop.PrefixEffect.memaddrs_eq
#print axioms InitECandidate.Solver.GasBudget.memory_word
