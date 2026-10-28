import InitECandidate.Solver.Input.CurrentTable.NewNode.NoGrow
import InitECandidate.Solver.Input.CurrentTable.NewContext

namespace InitECandidate.Solver.Input.CurrentTable.NewNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Current mapped metadata and the actual available next index. This is
an entry condition to derive from the constructor and insertion history. -/
structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table next cap : BitVec 64) : Prop where
  domain : source.memaddrs = InitE.ordinaryDomain
  arena : AllocatedBytes.Arena table 88
  aligned : table.toNat%8 = 0
  freeCell : source.memory (table+72#64) = .word 0#64
  nextCell : source.memory (table+64#64) = .word next
  capCell : source.memory (table+80#64) = .word cap
  room : next.toNat ≤ cap.toNat

theorem Context.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table next cap : BitVec 64} (ready : Context source table next cap)
    (frame : LocalEffects.erase target = LocalEffects.erase source) : Context target table next cap := by
  have memory := LocalEffects.memory_of_erase source target frame
  have domain := congrArg PanSemStateFiniteExact.memaddrs frame
  change target.memaddrs = source.memaddrs at domain
  exact ⟨domain.trans ready.domain,ready.arena,ready.aligned,by rw [memory]; exact ready.freeCell,
    by rw [memory]; exact ready.nextCell,by rw [memory]; exact ready.capCell,ready.room⟩

theorem Context.execute {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table next cap : BitVec 64}
    (ready : Context source table next cap)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table))) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word next))),returnedState source table next) :=
  body_execute source table next cap ready.domain ready.arena ready.aligned tableCell ready.freeCell ready.nextCell ready.capCell ready.room

theorem Context.price {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table next cap : BitVec 64}
    (ready : Context source table next cap)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock ≤ 0 := by
  rw [ready.execute tableCell,(returned_frame source table next).2]
  omega

theorem Context.returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table next cap : BitVec 64}
    (ready : Context source table next cap)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value),post)) :
    value = .val (.word next) ∧
      LocalEffects.erase post = LocalEffects.erase (New.putField source table 64 (next+1#64)) ∧ post.clock = source.clock := by
  rw [ready.execute tableCell] at normal
  have resultEq := congrArg Prod.fst normal
  have valueEq : .val (.word next) = value := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq
  have endpoint := congrArg Prod.snd normal
  dsimp only at endpoint
  exact ⟨valueEq.symm,by rw [←endpoint]; exact (returned_frame source table next).1,
    by rw [←endpoint]; exact (returned_frame source table next).2⟩

/-- The real new-table result already funds its first actual node index. -/
theorem from_constructor {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table cap stp pad : BitVec 64} (returned : New.Returned source post table cap stp pad) : Context post table 1#64 cap := by
  have freeCell := returned.fields (table+72#64,0#64) (by simp [New.writes])
  have nextCell := returned.fields (table+64#64,1#64) (by simp [New.writes])
  have capCell := returned.fields (table+80#64,cap) (by simp [New.writes])
  exact ⟨returned.arena.domain,returned.geometry.table,returned.tableAligned,freeCell,nextCell,capCell,by have := returned.capLower; change 1≤cap.toNat; omega⟩

end InitECandidate.Solver.Input.CurrentTable.NewNode

#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.Context.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.Context.returned
#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.from_constructor
