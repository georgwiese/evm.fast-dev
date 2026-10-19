import InitECandidate.Solver.GasBudget.StackPushGrowthProgram
import InitECandidate.Solver.Arenas.Prefix
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

private theorem undo_local (locals : HolFiniteMapExact MlS (ValueHOL 64)) (name : MlS) (value : ValueHOL 64) :
    HolFiniteMapExact.resVarEq (locals.update (name, value)) (name, locals.lookup name) = locals := by
  apply HolFiniteMapExact.ext
  funext query
  rw [lookup_resVarEq_toExact]
  by_cases same : query = name
  · subst query
    cases old : locals.lookup name <;>
      simp [resVarHOLExact, old, HolFiniteMapExact.update, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL]
  · have reverse : name ≠ query := Ne.symm same
    cases old : locals.lookup name <;>
      simp [resVarHOLExact, old, HolFiniteMapExact.update, FUPDATE, FUPDATE_HOL, FDOMSUB_HOL, same, reverse]

def growActions : List ProgramPrefix.Action := [.command growGuard,
  .declare "ncap" (.panop .mul [localVar "cap", .const 2#64]), .command growClamp,
  .allocate "ns" (.panop .mul [localVar "ncap", .const 32#64]), .command growCopy]

theorem grow_actions_shape : growBranch = Arenas.Prefix.program .down growActions growStores := by
  rw [grow_branch_shape]
  rfl

def growDestination (scratch capacity : BitVec 64) : BitVec 64 :=
  Arenas.rounded .down scratch ((capacity * 2#64) * 32#64)
noncomputable def growReady (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch capacity : BitVec 64) :=
  bind (Arenas.post {bind source "ncap" (capacity * 2#64) with clock := source.clock - 1}
    .down scratch ((capacity * 2#64) * 32#64)) "ns" (growDestination scratch capacity)
noncomputable def growCopied (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base scratch capacity : BitVec 64) :=
  CopyGeneral.callState (growReady source scratch capacity) base (growDestination scratch capacity) (32 * capacity.toNat)
noncomputable def growFinal (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch capacity : BitVec 64) :=
  {growCopied source base scratch capacity with
    locals := source.locals
    memory := StoreWord.put (StoreWord.put (growCopied source base scratch capacity).memory
      (frame + 8#64) (growDestination scratch capacity)) (frame + 232#64) (capacity * 2#64)}

/-- Exact original growth branch, including allocation, aligned copy and both
header stores. Source mapping/arena ownership are current physical premises.
The actual branch pays capacity+2 clocks; no helper execution is assumed. -/
theorem grow_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch memory capacity : BitVec 64)
    (positive : 0 < capacity.toNat) (bounded : capacity.toNat ≤ 512)
    (spLocal : source.locals.lookup (ofString "sp") = some (.val (.word capacity)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (baseMapped : source.memaddrs (frame + 8#64)) (baseCell : source.memory (frame + 8#64) = .word base)
    (capMapped : source.memaddrs (frame + 232#64))
    (scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory)))
    (arenaAligned : memory.toNat % 8 = 0)
    (room : memory.toNat + ((capacity * 2#64) * 32#64).toNat ≤ scratch.toNat)
    (allocCode : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (mapped : CopyContext.Mapped source base (growDestination scratch capacity) (32 * capacity.toNat))
    (aligned : CopyGeneral.aligned base (growDestination scratch capacity))
    (enough : capacity.toNat + 2 ≤ source.clock) :
    evaluateHOLFiniteState source growBranch = (none, growFinal source frame base scratch capacity) := by
  classical
  obtain ⟨doubled, more, capBound, allocation, copied⟩ := grow_numbers capacity positive bounded
  let declared := bind source "ncap" (capacity * 2#64)
  let ready := growReady source scratch capacity
  let middle := growCopied source base scratch capacity
  have capBelow : ¬1024#64 ≤ capacity := by change ¬1024 ≤ capacity.toNat; omega
  have doubledBelow : ¬1024#64 < capacity * 2#64 := by change ¬1024 < (capacity * 2#64).toNat; omega
  have guardRun : evaluateHOLFiniteState source growGuard = (none, source) := by
    rw [growGuard, evaluateHOLFiniteState_ite]
    simp [evalHOLExact, toExact, localVar, capLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, capBelow,
      evaluateHOLFiniteState_skip]
  have doubleRead : eval source (.panop .mul [localVar "cap", .const 2#64]) = some (.val (.word (capacity * 2#64))) := by
    simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, capLocal, valueIsWord, valueWord, panOpHOL]
  have doubledLocal : declared.locals.lookup (ofString "ncap") = some (.val (.word (capacity * 2#64))) := bind_lookup_same _ _ _
  have clampRun : evaluateHOLFiniteState declared growClamp = (none, declared) := by
    rw [growClamp, evaluateHOLFiniteState_ite]
    simp [evalHOLExact, toExact, localVar, doubledLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, doubledBelow,
      evaluateHOLFiniteState_skip]
  have amountRead : eval declared (.panop .mul [localVar "ncap", .const 32#64]) = some (.val (.word ((capacity * 2#64) * 32#64))) := by
    simp [eval, evalHOLExact, evalListHOLExact, toExact, localVar, doubledLocal, valueIsWord, valueWord, panOpHOL]
  have readyEV : ready.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    simpa [ready, growReady, Arenas.post, Arenas.pointerName, QueryBranch.bind, setVarHOLFinite,
      HolFiniteMapExact.update, FUPDATE, ofString] using ev
  have readySP : ready.locals.lookup (ofString "sp") = some (.val (.word capacity)) := by
    exact (bind_lookup_other _ "ns" "sp" _ (by decide)).trans ((bind_lookup_other _ "ncap" "sp" _ (by decide)).trans spLocal)
  have readyNS : ready.locals.lookup (ofString "ns") = some (.val (.word (growDestination scratch capacity))) := bind_lookup_same _ _ _
  have baseRead : eval ready (frameLoad 8#64) = some (.val (.word base)) := frame_read ready frame 8#64 base readyEV baseMapped baseCell
  have copyArgs : evalListHOLFinite ready (h := fun address => Classical.propDecidable (ready.memaddrs address))
      [localVar "ns", frameLoad 8#64, .panop .mul [localVar "sp", .const 32#64]] =
      some (CopyGeneral.values (growDestination scratch capacity) base (32 * capacity.toNat)) := by
    have countEq : capacity * 32#64 = BitVec.ofNat 64 (32 * capacity.toNat) := by
      apply BitVec.eq_of_toNat_eq
      rw [copied, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]
    simp only [eval] at baseRead
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, readyNS, readySP, baseRead,
      valueIsWord, valueWord, panOpHOL, countEq, CopyGeneral.values]
  have price := grow_copy_price base (growDestination scratch capacity) capacity.toNat aligned
  have copyRun : evaluateHOLFiniteState ready growCopy = (none, middle) :=
    CopyGeneral.call_execute ready _ base _ _ copyArgs copyCode (mapped.of_domain source ready _ _ _ rfl)
      (by omega) (by change CopyGeneral.cost base _ _ + 1 ≤ source.clock - 1; rw [price]; omega)
  have setup : Arenas.Prefix.Executes .down source growActions middle
      (fun target => restore source "ncap" (restore declared "ns" target)) :=
    .command guardRun (Nat.le_refl _) (.declare _ doubleRead (.command clampRun (Nat.le_refl _)
      (.allocate scratch memory _ amountRead allocCode scratchGlobal memoryGlobal arenaAligned room (by change 1 ≤ source.clock; omega)
        (.command copyRun (by change source.clock - 1 - _ ≤ source.clock - 1; exact Nat.sub_le _ _) (.done _)))))
  have middleEV : middle.globals.lookup (ofString "ev") = some (.val (.word frame)) := readyEV
  have middleNS : middle.locals.lookup (ofString "ns") = some (.val (.word (growDestination scratch capacity))) := readyNS
  have middleCap : middle.locals.lookup (ofString "ncap") = some (.val (.word (capacity * 2#64))) :=
    (bind_lookup_other _ "ns" "ncap" _ (by decide)).trans doubledLocal
  have firstRun := StoreWord.execute middle (frameAddress 8#64) (localVar "ns") (frame + 8#64)
    (growDestination scratch capacity) (address_read middle frame 8#64 middleEV) (by simpa [eval, localVar, evalHOLExact, toExact] using middleNS) baseMapped
  let stored := {middle with memory := StoreWord.put middle.memory (frame + 8#64) (growDestination scratch capacity)}
  have secondRun := StoreWord.execute stored (frameAddress 232#64) (localVar "ncap") (frame + 232#64)
    (capacity * 2#64) (address_read stored frame 232#64 middleEV) (by simpa [eval, localVar, evalHOLExact, toExact] using middleCap) capMapped
  have storesRun : evaluateHOLFiniteState middle growStores = (none,
      {stored with memory := StoreWord.put stored.memory (frame + 232#64) (capacity * 2#64)}) := by
    rw [growStores, StateSteps.next_sequence _ _ _ _ firstRun (Nat.le_refl _)]
    exact secondRun
  rw [grow_actions_shape, Arenas.Prefix.execute setup, storesRun]
  dsimp only
  apply Prod.ext
  · rfl
  simp only [restore, growFinal, stored]
  congr 1
  change HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq
    ((source.locals.update (ofString "ncap", .val (.word (capacity * 2#64)))).update
      (ofString "ns", .val (.word (growDestination scratch capacity))))
    (ofString "ns", (source.locals.update (ofString "ncap", .val (.word (capacity * 2#64)))).lookup (ofString "ns")))
    (ofString "ncap", source.locals.lookup (ofString "ncap")) = source.locals
  rw [undo_local, undo_local]

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.grow_actions_shape
#print axioms InitECandidate.Solver.GasBudget.StackPush.grow_execute
