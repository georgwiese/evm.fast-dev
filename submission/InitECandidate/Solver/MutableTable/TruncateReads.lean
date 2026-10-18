import InitECandidate.Solver.MutableTable.TruncateProgram
import InitECandidate.Solver.MutableTable.MemoryModelReads

namespace InitECandidate.Solver.MutableTable.Truncate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (count : Nat) (room : count < plan.capacity)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count)) (limit : BitVec 64)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (limitLocal : source.locals.lookup (ofString "n") = some (.val (.word limit))) :
    eval source condition = some (.val (.word (if limit.toNat < count then 1#64 else 0#64))) := by
  have countSmall := Nat.lt_trans room (capacity_small kind plan valid)
  norm_num only [Nat.reducePow] at countSmall
  have read := MemoryModel.Header.read source kind plan valid domain _ header tableLocal 24 (by decide) (by decide) (BitVec.ofNat 64 count) (by simp [MemoryModel.headerEntries])
  simp only [eval] at read
  by_cases active : limit.toNat < count <;>
    simp [eval, condition, localVar, evalHOLExact, toExact, read, limitLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt countSmall, active]

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.condition_read
