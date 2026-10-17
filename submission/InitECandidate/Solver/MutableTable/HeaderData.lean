import InitECandidate.Solver.MutableTable.FindDictionaryCall32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Physical header data independent of the caller's parameter names. -/
structure HeaderData (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters) : Prop where
  mapped : ∀ offset∈([0,8,16,32,48] : List Nat),source.memaddrs (table+BitVec.ofNat 64 offset)
  capacity : source.memory (table+16#64)=.word p.capacity
  keyLength : source.memory table=.word p.keyLength
  stride : source.memory (table+8#64)=.word p.stride
  keys : source.memory (table+32#64)=.word p.keys
  used : source.memory (table+48#64)=.word p.used

theorem HeaderData.with_locals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Parameters)
    (data : HeaderData source table p) (memory : source.memory=target.memory) (domain : source.memaddrs=target.memaddrs)
    (tLocal : target.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyLocal : target.locals.lookup (ofString "key")=some (.val (.word p.key))) : HeaderCells target table p := by
  refine ⟨tLocal,keyLocal,?_,?_,?_,?_,?_,?_⟩
  · intro offset member;rw [← domain];exact data.mapped offset member
  all_goals rw [← memory]
  · exact data.capacity
  · exact data.keyLength
  · exact data.stride
  · exact data.keys
  · exact data.used

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.HeaderData.with_locals
