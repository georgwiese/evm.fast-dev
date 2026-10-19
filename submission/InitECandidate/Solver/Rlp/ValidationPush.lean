import InitECandidate.Solver.Rlp.ValidationArena
import InitECandidate.Solver.Rlp.ValidationPushMemory
import InitECandidate.Solver.Rlp.ValidationMoves
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def pushPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor position ending previous payload after : BitVec 64) :=
  let pointer := Arenas.rounded .down cursor 24#64
  let ready := bind (Arenas.post {source with clock:=source.clock-1} .down cursor 24#64) "rec" pointer
  restore source "rec" (movesPost (recordPost ready pointer after ending previous) pointer payload after)

/-- A real successful push determines its exact fresh record and local
updates. Room is derived from the allocator's actual normal return. -/
theorem push_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor limit position ending previous payload after : BitVec 64)
    (arena : Arena source cursor limit)
    (positionCell : source.locals.lookup (ofString "pos")=some (.val (.word position)))
    (endCell : source.locals.lookup (ofString "end")=some (.val (.word ending)))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word previous)))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word payload)))
    (afterCell : source.locals.lookup (ofString "after")=some (.val (.word after)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source push=(none,target)) :
    Arenas.Room .down cursor limit 24#64 ∧ 1≤source.clock ∧
      target=pushPost source cursor position ending previous payload after := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 24#64]=some [.val (.word 24#64)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact]
  obtain ⟨room,positive,inner,continuation,restored⟩ := Arenas.scoped_none source target .down "rec" [.const 24#64] pushStores cursor limit 24#64 args arena.cursorGlobal arena.limitGlobal arena.ordered arena.aligned installed normal
  let pointer := Arenas.rounded .down cursor 24#64
  let ready := bind (Arenas.post {source with clock:=source.clock-1} .down cursor 24#64) "rec" pointer
  change evaluateHOLFiniteState ready pushStores=(none,inner) at continuation
  have recCell : ready.locals.lookup (ofString "rec")=some (.val (.word pointer)) := bind_lookup_same _ _ _
  have afterReady : ready.locals.lookup (ofString "after")=some (.val (.word after)) :=
    (bind_lookup_other _ "rec" "after" pointer (by decide)).trans afterCell
  have endReady : ready.locals.lookup (ofString "end")=some (.val (.word ending)) :=
    (bind_lookup_other _ "rec" "end" pointer (by decide)).trans endCell
  have topReady : ready.locals.lookup (ofString "top")=some (.val (.word previous)) :=
    (bind_lookup_other _ "rec" "top" pointer (by decide)).trans topCell
  have positionReady : ready.locals.lookup (ofString "pos")=some (.val (.word position)) :=
    (bind_lookup_other _ "rec" "pos" pointer (by decide)).trans positionCell
  have payloadReady : ready.locals.lookup (ofString "payload")=some (.val (.word payload)) :=
    (bind_lookup_other _ "rec" "payload" pointer (by decide)).trans payloadCell
  have mapped0 : ready.memaddrs pointer := by
    change source.memaddrs (Arenas.rounded .down cursor 24#64)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using Arena.record_mapped source cursor limit arena room 0 (by decide) (by decide)
  have mapped8 : ready.memaddrs (pointer+8#64) := Arena.record_mapped source cursor limit arena room 8 (by decide) (by decide)
  have mapped16 : ready.memaddrs (pointer+16#64) := Arena.record_mapped source cursor limit arena room 16 (by decide) (by decide)
  have stores := record_execute ready pointer after ending previous recCell afterReady endReady topReady mapped0 mapped8 mapped16
  have moves := moves_execute (recordPost ready pointer after ending previous) position ending previous pointer payload after positionReady endReady topReady recCell payloadReady afterReady
  rw [stores,moves] at continuation
  have same : inner=movesPost (recordPost ready pointer after ending previous) pointer payload after := (Prod.mk.inj continuation).2.symm
  exact ⟨room,positive,restored.trans (congrArg (restore source "rec") same)⟩

theorem push_post_arena (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor limit position ending previous payload after : BitVec 64)
    (arena : Arena source cursor limit) (room : Arenas.Room .down cursor limit 24#64) :
    Arena (pushPost source cursor position ending previous payload after) (Arenas.rounded .down cursor 24#64) limit := by
  have initial := Arena.of_fields source {source with clock:=source.clock-1} cursor limit arena rfl rfl
  exact Arena.of_fields _ _ _ _ (Arena.after_allocation _ cursor limit initial room) rfl rfl

theorem push_post_pending (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor limit rootEnd position ending payload after : BitVec 64) (frames : List Frame)
    (arena : Arena source cursor limit) (room : Arenas.Room .down cursor limit 24#64)
    (pending : Pending source.memory source.memaddrs cursor.toNat rootEnd frames ending)
    (within : after.toNat≤ending.toNat) :
    let pointer := Arenas.rounded .down cursor 24#64
    let post := pushPost source cursor position ending (topOf frames) payload after
    Pending post.memory post.memaddrs pointer.toNat rootEnd ({pointer:=pointer,resume:=after,parentEnd:=ending}::frames) after := by
  obtain ⟨active,fits,below,lower,aligned⟩ := Arena.record_bounds source cursor limit arena room
  let pointer := Arenas.rounded .down cursor 24#64
  let ready := bind (Arenas.post {source with clock:=source.clock-1} .down cursor 24#64) "rec" pointer
  have mapped0 : ready.memaddrs pointer := by
    change source.memaddrs (Arenas.rounded .down cursor 24#64)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using Arena.record_mapped source cursor limit arena room 0 (by decide) (by decide)
  exact Pending.after_record ready cursor.toNat rootEnd ending pointer after frames pending active fits below within mapped0
    (Arena.record_mapped source cursor limit arena room 8 (by decide) (by decide))
    (Arena.record_mapped source cursor limit arena room 16 (by decide) (by decide))

theorem push_post_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor position ending previous payload after : BitVec 64) :
    let post := pushPost source cursor position ending previous payload after
    post.locals.lookup (ofString "pos")=some (.val (.word payload)) ∧
    post.locals.lookup (ofString "end")=some (.val (.word after)) ∧
    post.locals.lookup (ofString "top")=some (.val (.word (Arenas.rounded .down cursor 24#64))) ∧
    post.locals.lookup (ofString "go")=source.locals.lookup (ofString "go") := by
  dsimp only [pushPost]
  rw [restore_lookup_other _ _ "rec" "pos" (by decide),restore_lookup_other _ _ "rec" "end" (by decide),
    restore_lookup_other _ _ "rec" "top" (by decide),restore_lookup_other _ _ "rec" "go" (by decide)]
  exact ⟨moves_position _ _ _ _,moves_end _ _ _ _,moves_top _ _ _ _,
    (moves_go _ _ _ _).trans (bind_lookup_other _ "rec" "go" _ (by decide))⟩

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.push_none
#print axioms InitECandidate.Solver.Rlp.Validation.push_post_arena
#print axioms InitECandidate.Solver.Rlp.Validation.push_post_pending
#print axioms InitECandidate.Solver.Rlp.Validation.push_post_locals
