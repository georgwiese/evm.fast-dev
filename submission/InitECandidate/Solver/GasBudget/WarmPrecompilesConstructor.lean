import InitECandidate.Solver.GasBudget.WarmPrecompilesSender
import InitECandidate.Solver.GasBudget.WarmPrecompilesLoop
import InitECandidate.Solver.MutableTable.TableRuntime.NormalRoom
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.CounterLoopLocal

namespace InitECandidate.Solver.GasBudget.WarmPrecompiles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem initial_price : TableRuntime.price 64 + 1 = 10 := by decide
theorem loop_price : price 1 18 = 1773 := by decide

/-- The original account-table constructor, sender warming, reset and all
18 precompile warm-ups. Allocation room, empty representation and mutation
count are derived from the actual successful caller execution. -/
theorem constructor_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (cursor start : Nat) (sender : BitVec 64) (environment : WarmKeys.Environment source)
    (lower : 2701131776 ≤ cursor) (bounded : cursor ≤ 33806089496) (aligned : cursor % 8 = 0)
    (inputValid : MemoryRegion.Valid ⟨start, 360⟩)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (keys : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word (BitVec.ofNat 64 start))))
    (senderLocal : source.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (queryFits : sender.toNat + 20 < 2 ^ 64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress sender offset)))
    (newCode : source.code.lookup (ofString "htab_new") = some (WitnessRadix.TableNew.formals, WitnessRadix.TableNew.body, .one))
    (normal : evaluateHOLFiniteState source constructorSite = (some (.returned value), post)) :
    ∃ paid slots warmed finish, paid ≤ 1795 ∧ paid ≤ source.clock ∧ warmed.clock = source.clock - paid ∧
      emptyLocalsHOLFinite warmed = emptyLocalsHOLFinite {TableRuntime.callState source "aa" .account cursor 64 with memory := warmed.memory, clock := source.clock - paid} ∧
      MemoryModel.Header warmed.memory .account (fresh .account cursor 64) (BitVec.ofNat 64 slots.length) ∧
      MemoryModel.Occupied warmed .account (fresh .account cursor 64) slots ∧ slots.length ≤ 19 ∧
      Locals warmed (cell (fresh .account cursor 64) .header 0) start 18 ∧
      evaluateHOLFiniteState warmed afterLoop = (some (.returned value), finish) ∧ post = restore source "aa" finish ∧
      (∀ address : BitVec 64, address.toNat < cursor → warmed.memory address = source.memory address) ∧
      ∀ key : MlS, key ≠ ofString "aa" → key ≠ ofString "i" → warmed.locals.lookup key = source.locals.lookup key := by
  rw [constructor_shape] at normal
  have valid := TableRuntime.normal_call_layout source post .account cursor 64 "aa" newArguments afterNew
    (by decide) lower bounded aligned (by decide) (by decide) (by decide) (by decide) environment.domain rfl newCode heap
    environment.allocCode environment.trapCode environment.zeroCode value normal
  obtain ⟨funded, inner, afterNewRun, restored⟩ := TableRuntime.call_normal source post .account cursor 64 "aa" newArguments afterNew valid environment.domain
    (Or.inr (by decide)) rfl newCode heap environment.allocCode environment.zeroCode value normal
  rw [initial_price] at funded
  let constructed := TableRuntime.callState source "aa" .account cursor 64
  let plan := fresh .account cursor 64
  let newCursor := freshEnd .account cursor 64
  have skipLeft (state : PanSemStateFiniteExact 64 Guest.HostMemory) (rest : ProgHOL 64) :
      evaluateHOLFiniteState state (.seq .skip rest) = evaluateHOLFiniteState state rest := WitnessRadix.StateSteps.next_sequence state state .skip rest (by rw [evaluateHOLFiniteState_skip]) (Nat.le_refl _)
  rw [afterNew, skipLeft] at afterNewRun
  have senderSafe : Input.LocalPrefix (ofString "m") senderCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle, senderRun, afterSender, _⟩ := senderSafe.normal_continue constructed inner _ value afterNewRun
  have endBound : newCursor ≤ 33806089496 := valid.upper .position
  have endAligned : newCursor % 8 = 0 := by simpa [newCursor, freshEnd, stride, KeyHash.keySize, rounded, Nat.add_mod] using aligned
  have constructedHeap : constructed.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 newCursor))) := by
    simp [constructed, TableRuntime.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, newCursor]
  have constructedEnvironment : WarmKeys.Environment constructed := environment.of_fields rfl rfl rfl
  have constructedSender : constructed.locals.lookup (ofString "sender") = some (.val (.word sender)) := (bind_lookup_other _ "aa" "sender" _ (by decide)).trans senderLocal
  obtain ⟨senderPaid, senderSlots, senderBound, senderFits, senderFrame, senderHeader, senderModel, sameLocals, senderCount, senderFootprint⟩ :=
    sender_normal constructed middle newCursor plan sender constructedEnvironment valid rfl (fun pool => (fresh_bounds .account cursor 64 pool).2) endBound endAligned constructedHeap
      (TableRuntime.caller_header source "aa" .account cursor 64 valid)
      (TableRuntime.caller_model source "aa" .account cursor 64 valid (Or.inr (by decide)) environment.domain environment.little)
      (bind_lookup_same _ _ _) constructedSender queryFits queryMapped senderRun
  rw [skipLeft] at afterSender
  have resetSafe : Input.LocalPrefix (ofString "m") resetIndex := .assign _ _ (by decide)
  obtain ⟨reset, resetRun, siteRun, _⟩ := resetSafe.normal_continue middle inner site value afterSender
  have resetEq := Input.assign_none middle reset "i" (.const 0#64) 0#64 rfl resetRun
  let ready := bind middle "i" 0#64
  change reset = ready at resetEq
  subst reset
  rw [site_shape] at siteRun
  have loopSafe : Input.LocalPrefix (ofString "m") loop := .loop _ body_safe
  obtain ⟨warmed, loopRun, restRun, _⟩ := loopSafe.normal_continue ready inner afterLoop value siteRun
  have codes := congrArg PanSemStateFiniteExact.code senderFrame
  have domain := congrArg PanSemStateFiniteExact.memaddrs senderFrame
  have endian := congrArg PanSemStateFiniteExact.be senderFrame
  have globals := congrArg PanSemStateFiniteExact.globals senderFrame
  have middleClock := congrArg PanSemStateFiniteExact.clock senderFrame
  change middle.code = source.code at codes
  change middle.memaddrs = source.memaddrs at domain
  change middle.be = source.be at endian
  change middle.globals = constructed.globals at globals
  change middle.clock = constructed.clock - senderPaid at middleClock
  have readyEnvironment : WarmKeys.Environment ready := environment.of_fields codes domain endian
  have readyHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 newCursor))) := by change middle.globals.lookup _ = _; rw [globals]; exact constructedHeap
  have readyLocals : Locals ready (cell plan .header 0) start 0 := by
    refine ⟨?_, ?_, bind_lookup_same _ _ _⟩
    · rw [bind_lookup_other _ "i" "aa" _ (by decide), sameLocals]
      exact bind_lookup_same _ _ _
    · change middle.globals.lookup (ofString "precompile_addrs") = _
      rw [globals]
      exact keys
  have readyModel := MemoryModel.Occupied.of_fields middle ready .account plan senderSlots senderModel rfl rfl rfl
  obtain ⟨loopPaid, finalSlots, loopBound, loopFits, loopFrame, finalHeader, finalModel, finalLocals, finalLower, finalUpper, loopFootprint⟩ :=
    loop_normal 18 ready warmed start 0 newCursor plan senderSlots inputValid rfl readyEnvironment valid rfl (by omega)
      (fun pool => (fresh_bounds .account cursor 64 pool).2) endBound endAligned readyHeap senderHeader readyModel readyLocals loopRun
  have smallPrice := price_mono senderSlots.length 1 18 senderCount
  rw [loop_price] at smallPrice
  have constructedClock : constructed.clock = source.clock - 10 := by change source.clock - (TableRuntime.price 64 + 1) = _; rw [initial_price]
  have finalClock := congrArg PanSemStateFiniteExact.clock loopFrame
  change warmed.clock = middle.clock - loopPaid at finalClock
  change loopPaid ≤ middle.clock at loopFits
  have spent : warmed.clock = source.clock - (10 + senderPaid + loopPaid) := by omega
  have composite := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := warmed.memory, clock := warmed.clock}) senderFrame
  change emptyLocalsHOLFinite {ready with memory := warmed.memory, clock := warmed.clock} = emptyLocalsHOLFinite {constructed with memory := warmed.memory, clock := warmed.clock} at composite
  change emptyLocalsHOLFinite warmed = emptyLocalsHOLFinite {ready with memory := warmed.memory, clock := middle.clock - loopPaid} at loopFrame
  rw [← finalClock] at loopFrame
  have finalFrame := loopFrame.trans composite
  rw [spent] at finalFrame
  refine ⟨10 + senderPaid + loopPaid, finalSlots, warmed, inner, by omega, by omega, spent, finalFrame,
    finalHeader, finalModel, by omega, finalLocals, restRun, restored, ?_, ?_⟩
  · intro address before
    have outside : TableFootprint.Outside .account plan address := by
      intro pool offset inside
      exact fresh_cell_away .account cursor 64 valid address (Or.inl before) pool offset inside
    exact (loopFootprint address outside).trans ((senderFootprint address outside).trans
      (TableRuntime.caller_memory_away source "aa" .account cursor 64 valid address (Or.inl before)))
  · intro key notTable notIndex
    have same := Input.counter_loop_local ready warmed condition (ofString "htab_set") [localVar "aa", query, .const 1#64] "i" (.op .add [localVar "i", .const 1#64]) key notIndex loopRun
    calc
      warmed.locals.lookup key = ready.locals.lookup key := same
      _ = middle.locals.lookup key := by simp [ready, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notIndex, Ne.symm notIndex]
      _ = constructed.locals.lookup key := by rw [sameLocals]
      _ = source.locals.lookup key := by simp [constructed, TableRuntime.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notTable, Ne.symm notTable]

end InitECandidate.Solver.GasBudget.WarmPrecompiles

#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.initial_price
#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.loop_price
#print axioms InitECandidate.Solver.GasBudget.WarmPrecompiles.constructor_normal
