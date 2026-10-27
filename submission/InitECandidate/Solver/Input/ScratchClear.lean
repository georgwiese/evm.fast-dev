import InitECandidate.Solver.Input.ZeroUnmappedCall
import InitECandidate.Solver.Arenas.Normal
import InitECandidate.Solver.Input.NormalCallClock
import InitECandidate.Solver.Input.TrapCost

namespace InitECandidate.Solver.Input.ScratchClear
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 100000 in
theorem allocator_installed (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one) := by
  have found := OriginalCode.indexed code installed 8
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_scratch_alloc) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Arenas.body, Arenas.formals,
    Guest.Software.guestFn_scratch_alloc, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using found

/-- A genuine scratch allocation followed by its real memzero cannot return
under the actual compiler memory domain and current ordered arena cursors.
This includes allocator failure and missing clocks: no future room, allocation
return or successful clear is a premise. -/
theorem allocated_clear_no_return {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (pointer limit : BitVec 64) (length : Nat) (name : String) (rest : ProgHOL 64) (value : ValueHOL 64)
    (small : length + 32 < 2^64) (large : 32 ≤ length)
    (pointerBound : pointer.toNat ≤ InitE.scratchEnd) (ordered : limit ≤ pointer)
    (aligned : limit.toNat % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain)
    (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    evaluateHOLFiniteState source
      (.decCall (ofString name) .one (ofString "scratch_alloc") [.const (BitVec.ofNat 64 length)]
        (.seq (.call (some (none, none)) (ofString "memzero") [localVar name, .const (BitVec.ofNat 64 length)]) rest)) ≠
      (some (.returned value), post) := by
  intro normal
  let amount := BitVec.ofNat 64 length
  let tail : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "memzero")
    [localVar name, .const amount]) rest
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [.const amount] = some [.val (.word amount)] := rfl
  have positive := CallNormal.normal_clock source post (ofString name) .one (ofString "scratch_alloc")
    [.const amount] tail value normal
  obtain ⟨callee, called, amountCell⟩ := CallNormal.unary_environment source.code.lookup (ofString "scratch_alloc")
    "n" (Arenas.body .down) amount (allocator_installed source.code installed)
  obtain ⟨target, returned, actual⟩ := CallNormal.callee_return source post (ofString name) .one (ofString "scratch_alloc")
    [.const amount] [.val (.word amount)] (Arenas.body .down) tail callee .one args called positive value normal
  have room := Arenas.room_of_normal (callEntryStateHOLFinite source callee) target .down pointer limit amount
    amountCell pointerGlobal limitGlobal ordered (Trap.original_code source.code installed) returned actual
  have guards := Arenas.downward_guards pointer limit amount aligned room
  let q := Arenas.resultWord .down pointer amount
  have qAligned : q.toNat % 8 = 0 := guards.2.2.2.2.2
  have qBelow : q.toNat < InitE.sourceBase := by
    have earlier := guards.2.2.2.1
    dsimp [InitE.scratchEnd, InitE.sourceBase] at pointerBound ⊢
    change (Arenas.rounded .down pointer amount).toNat < 2701131776
    omega
  have resumed := Arenas.call_execute source .down name [.const amount] tail pointer limit amount args
    (allocator_installed source.code installed) pointerGlobal limitGlobal aligned room positive
  simp only [Arenas.functionName, tail, amount] at resumed
  rw [resumed] at normal
  let ready := bind (Arenas.post {source with clock := source.clock - 1} .down pointer amount) name q
  let output := evaluateHOLFiniteState ready tail
  have resultEq : output.1 = some (.returned value) := congrArg Prod.fst normal
  have tailRun : evaluateHOLFiniteState ready tail = (some (.returned value), output.2) := Prod.ext resultEq rfl
  have safe : LocalPrefix (ofString "saved") (.call (some (none, none)) (ofString "memzero")
      [localVar name, .const amount]) := .call none _ _ (by intro key impossible; cases impossible)
  obtain ⟨middle, clearRun, restRun, frame⟩ := safe.normal_continue ready output.2 rest value tailRun
  have qCell : ready.locals.lookup (ofString name) = some (.val (.word q)) := bind_lookup_same _ _ _
  have clearArgs : evalListHOLFinite ready (h := fun address => Classical.propDecidable (ready.memaddrs address))
      [localVar name, .const amount] = some (WitnessRadix.Zero.values q length) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, qCell, WitnessRadix.Zero.values, amount]
  exact ZeroUnmapped.call_not_normal ready middle _ q length small large qAligned domain qBelow installed clearArgs clearRun

end InitECandidate.Solver.Input.ScratchClear

#print axioms InitECandidate.Solver.Input.ScratchClear.allocator_installed
#print axioms InitECandidate.Solver.Input.ScratchClear.allocated_clear_no_return
