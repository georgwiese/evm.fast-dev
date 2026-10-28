import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Entry
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Exit
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Reached physical current traversal entry. The insertion proof must
supply its node image; key-byte mapping and future leaf success are absent. -/
structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table base root : BitVec 64)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64) : Prop where
  image : Nodes source base valid bits left right
  present : root=0#64 ∨ valid root
  domain : source.memaddrs=InitE.ordinaryDomain
  arena : AllocatedBytes.Arena table 88
  aligned : table.toNat%8=0
  keyCell : source.memory table=.word 32#64
  nodesCell : source.memory (table+40#64)=.word base
  rootCell : source.memory (table+56#64)=.word root

theorem Context.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table base root : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (ready : Context source table base root valid bits left right) (same : LocalEffects.erase target=LocalEffects.erase source) :
    Context target table base root valid bits left right := by
  have memory:=LocalEffects.memory_of_erase source target same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs=source.memaddrs at domain
  exact ⟨ready.image.of_frame same,ready.present,domain.trans ready.domain,ready.arena,ready.aligned,
    by rw [memory]; exact ready.keyCell,by rw [memory]; exact ready.nodesCell,by rw [memory]; exact ready.rootCell⟩

theorem Context.price {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table base root : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (ready : Context source table base root valid bits left right)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤257 :=
  body_cost source table base root valid bits left right ready.image ready.present ready.domain ready.arena ready.aligned tableCell ready.keyCell ready.nodesCell ready.rootCell

/-- Any genuine returned value is zero or an actual leaf marked256 in the
same node image; all physical memory/globals remain intact. -/
theorem Context.returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table base root : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (ready : Context source table base root valid bits left right)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ leaf,value=.val (.word leaf) ∧ (leaf=0#64 ∨ valid leaf ∧ bits leaf=256) ∧ LocalEffects.erase post=LocalEffects.erase source := by
  have original:=normal
  rw [setup_execute source table base root ready.domain ready.arena ready.aligned tableCell ready.keyCell ready.nodesCell ready.rootCell] at normal
  let afterPost:=(evaluateHOLFiniteState (rootEntry source base root) afterRoot).2
  have observed:=congrArg Prod.fst normal
  dsimp only at observed
  have afterRun : evaluateHOLFiniteState (rootEntry source base root) afterRoot=(some (.returned value),afterPost) := Prod.ext observed rfl
  have initial : Invariant source base valid (rootEntry source base root) := ⟨root,root_state source base root,ready.present⟩
  rw [body_shapes.2.2.2] at afterRun
  obtain ⟨loopPost,loopRun,returnedRun⟩:=sequence_returned (rootEntry source base root) afterPost loop (.return (localVar "n")) value
    (loop_never ready.image initial) afterRun
  obtain ⟨leaf,state,finished⟩:=loop_finished ready.image initial loopRun
  have expected : evaluateHOLFiniteState loopPost (.return (localVar "n"))=
      (some (.returned (.val (.word leaf))),emptyLocalsHOLFinite loopPost) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,state.nodeCell,shapeOfHOLExact]
  rw [expected] at returnedRun
  have answer : value=.val (.word leaf) := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst returnedRun).symm
  have frame:=body_readonly source.code source rfl
  rw [original] at frame
  exact ⟨leaf,answer,finished,frame⟩

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context.price
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context.returned
