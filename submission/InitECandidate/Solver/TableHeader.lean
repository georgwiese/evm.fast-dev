import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.WitnessRadix.BuildEntry
open Flapjack PanSemStateFiniteExact

structure Header {F : Type} (source : PanSemStateFiniteExact 64 F)
    (table keys vals src dst : BitVec 64) : Prop where
  keysMapped : source.memaddrs (table + 32#64)
  keysWord : source.memory (table + 32#64) = .word keys
  valsMapped : source.memaddrs (table + 40#64)
  valsWord : source.memory (table + 40#64) = .word vals
  srcMapped : source.memaddrs (table + 56#64)
  srcWord : source.memory (table + 56#64) = .word src
  dstMapped : source.memaddrs (table + 64#64)
  dstWord : source.memory (table + 64#64) = .word dst


end InitECandidate.Solver.WitnessRadix.BuildEntry
