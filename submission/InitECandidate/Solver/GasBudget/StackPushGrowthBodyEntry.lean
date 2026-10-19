import InitECandidate.Solver.GasBudget.StackPushGrowthControl
import InitECandidate.Solver.GasBudget.StackPushNonGrowthEntry

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Current physical inputs to a push into a full, still growable stack.
Reaching these ownership facts from initialization remains a global obligation. -/
structure GrowthView (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch memory capacity : BitVec 64) : Prop where
  positive : 0 < capacity.toNat
  bounded : capacity.toNat ≤ 512
  ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))
  spCell : source.memory (frame + 16#64) = .word capacity
  capCell : source.memory (frame + 232#64) = .word capacity
  baseMapped : source.memaddrs (frame + 8#64)
  baseCell : source.memory (frame + 8#64) = .word base
  scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  memoryGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word memory))
  arenaAligned : memory.toNat % 8 = 0
  room : memory.toNat + ((capacity * 2#64) * 32#64).toNat ≤ scratch.toNat
  allocCode : source.code.lookup (ofString "scratch_alloc") = some (Arenas.formals, Arenas.body .down, .one)
  copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one)
  mapped : CopyContext.Mapped source base (growDestination scratch capacity) (32 * capacity.toNat)
  aligned : CopyGeneral.aligned base (growDestination scratch capacity)

theorem growth_body_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base scratch memory capacity : BitVec 64)
    (view : GrowthView source frame base scratch memory capacity) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ inner, capacity.toNat + 2 ≤ source.clock ∧ source.memaddrs (frame + 16#64) ∧ source.memaddrs (frame + 232#64) ∧
      evaluateHOLFiniteState (growFinal (entered source capacity capacity) frame base scratch capacity) writes = (some (.returned value), inner) ∧
      post = restore source "sp" (restore (bind source "sp" capacity) "cap" inner) := by
  rw [body_shape] at normal
  obtain ⟨spValue, spPost, spRead, spTyped, spRun, spPostEq⟩ :=
    Input.CallNormal.declaration_normal_entry source post "sp" .one (frameLoad 16#64) afterSP value normal
  have spMapped := Input.load_one_mapped source (frameAddress 16#64) (frame + 16#64) spValue (address_read source frame 16#64 view.ev) spRead
  have spActual := frame_read source frame 16#64 capacity view.ev spMapped view.spCell
  have spEq : spValue = .val (.word capacity) := Option.some.inj (spRead.symm.trans spActual)
  subst spValue
  let first := bind source "sp" capacity
  rw [cap_shape] at spRun
  obtain ⟨capValue, capPost, capRead, capTyped, capRun, capPostEq⟩ :=
    Input.CallNormal.declaration_normal_entry first spPost "cap" .one (frameLoad 232#64) afterCap value spRun
  have capMapped := Input.load_one_mapped first (frameAddress 232#64) (frame + 232#64) capValue (address_read first frame 232#64 view.ev) capRead
  have capActual := frame_read first frame 232#64 capacity view.ev capMapped view.capCell
  have capEq : capValue = .val (.word capacity) := Option.some.inj (capRead.symm.trans capActual)
  subst capValue
  let entry := entered source capacity capacity
  have spLocal : entry.locals.lookup (ofString "sp") = some (.val (.word capacity)) :=
    (bind_lookup_other _ "cap" "sp" _ (by decide)).trans (bind_lookup_same _ _ _)
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word capacity)) := bind_lookup_same _ _ _
  change evaluateHOLFiniteState entry afterCap = (some (.returned value), capPost) at capRun
  rw [growth_shape] at capRun
  obtain ⟨grown, growthResult, growthRun, growthControl, rest⟩ :=
    Input.sequence_control_first entry capPost growth (.seq overflow writes) (some (.returned value)) (.returned value) capRun
  rw [growth_taken entry capacity spLocal capLocal] at growthRun
  have ordinary := grow_control_none entry grown capacity capLocal view.bounded growthResult growthControl growthRun
  subst growthResult
  obtain ⟨funded, grownEq⟩ := grow_normal entry grown frame base scratch memory capacity view.positive view.bounded spLocal capLocal
    view.ev view.baseMapped view.baseCell capMapped view.scratchGlobal view.memoryGlobal view.arenaAligned view.room
    view.allocCode view.copyCode (view.mapped.of_domain source entry _ _ _ rfl) view.aligned growthRun
  have restRun := rest rfl
  rw [grownEq] at restRun
  let ready := growFinal entry frame base scratch capacity
  obtain ⟨doubled, room, bounded, allocation, copied⟩ := grow_numbers capacity view.positive view.bounded
  have roomWord : capacity < capacity * 2#64 := room
  have readySP : ready.locals.lookup (ofString "sp") = some (.val (.word capacity)) := spLocal
  have overflowRun := no_overflow ready capacity (capacity * 2#64) readySP roomWord bounded
  rw [StateSteps.next_sequence ready ready overflow writes overflowRun (Nat.le_refl _)] at restRun
  refine ⟨capPost, funded, spMapped, capMapped, restRun, ?_⟩
  rw [spPostEq, capPostEq]

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.growth_body_entry
