import InitECandidate.Solver.Input.CurrentTable.Set.FreshReady
import InitECandidate.Solver.Input.CurrentTable.Set.SpliceTransport

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix QueryBranch

/-- A real normal fresh-insertion caller executes both genuine
constructors and original splice, returns zero and retains the complete
new physical image in that same caller post-state. -/
theorem fresh_returned {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value node parent : BitVec 64}
    {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (locals : Locals source table pointer value) (scope : SeekState origin source (New.nodesPointer table cap) node parent pointer difference)
    (installed : OriginalCode.Installed source.code) (answer : ValueHOL 64)
    (normal : evaluateHOLFiniteState source newLeafCall = (some (.returned answer),post)) :
    answer = .val (.word 0#64) ∧
      LocalEffects.erase post = LocalEffects.erase (insertedState source table cap node parent pointer value next count difference query left) ∧
      Image post table cap (insertedRoot root parent next) (next+2) (count+1)
        (Splice.valid valid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)))
        (Splice.bits bits (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) difference)
        (Splice.side left (BitVec.ofNat 64 (next+1)) parent node (Splice.choice (BitVec.ofNat 64 next) node query difference false))
        (Splice.side right (BitVec.ofNat 64 (next+1)) parent node (Splice.choice (BitVec.ofNat 64 next) node query difference true))
        (Splice.keys keys (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) node query) ValueOf := by
  rcases fresh_allocation_trace query data.image data.available locals scope.differenceCell installed data.little data.aligned data.beforeTable data.view
    (some (.returned answer)) normal with stopped | reached
  · exact (stopped.2 answer rfl).elim
  · obtain ⟨leafTarget,leafPost,internalTarget,inner,frame,forward,cost,called,innerEndpoint,endpoint⟩ := reached
    let resumed := CallNormal.continuationEntry (CallNormal.continuationEntry source leafTarget "nl" (.val (.word (BitVec.ofNat 64 next))))
      internalTarget "ni" (.val (.word (BitVec.ofNat 64 (next+1))))
    have physical : LocalEffects.erase resumed = LocalEffects.erase (freshModel source table cap pointer value next count difference) := frame
    obtain ⟨domain,nodesCell,leftCell,view⟩ := fresh_ready data physical
    obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
    have spliceLocals := SpliceLocals.from_scoped source leafTarget internalTarget table (New.nodesPointer table cap) node parent
      (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) pointer difference locals.tableCell scope.cursor.baseCell scope.cursor.nodeCell scope.parentCell locals.keyCell scope.differenceCell
    have execution := splice_execute resumed table cap node parent (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) pointer (left parent) difference query
      domain data.image.geometry data.image.aligned data.node_inside data.parent_inside leafInside internalInside data.parent_not_internal spliceLocals nodesCell leftCell data.fresh.inside data.beforeTable view
    change evaluateHOLFiniteState resumed splice = (some (.returned answer),inner) at called
    rw [execution] at called
    have returned := congrArg Prod.fst called
    have answerEq : .val (.word 0#64) = answer := by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using returned
    have innerEq := congrArg Prod.snd called
    dsimp only at innerEq
    have finalFrame : LocalEffects.erase post = LocalEffects.erase (insertedState source table cap node parent pointer value next count difference query left) := by
      rw [endpoint,innerEndpoint,←innerEq]
      exact splice_frame _ resumed table cap node parent (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) (left parent) query difference physical
    exact ⟨answerEq.symm,finalFrame,(inserted_image data).of_frame finalFrame⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_returned
