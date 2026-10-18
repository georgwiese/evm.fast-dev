import InitECandidate.Solver.GasBudget.ArithmeticStackProgram
import InitECandidate.Solver.GasBudget.OpcodeEntry

namespace InitECandidate.Solver.GasBudget.ArithmeticStackOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete original arithmetic/shift bodies. Real pop depth derives free
stack room; real priced helper chains preserve memory and gas; real push/pc
calls finish the opcode. Every consumed clock and helper return is derived. -/
theorem body_normal (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : DirectStackOpcode.Entry source frame) (environment : ArithmeticEffects.Environment source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source kind.site.body = (some (.returned value), post)) :
    ∃ paid, paid ≤ kind.bodyPrice ∧ paid ≤ source.clock ∧ value = .val (.word 0#64) ∧ post.clock = source.clock - paid ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - paid} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + kind.site.fee ∧
      (wordAt post.memory (frame + 16#64)).toNat + kind.site.names.length = entry.sp.toNat + 1 ∧
      (wordAt post.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat ∧
      DirectStackOpcode.Footprint source.memory post.memory frame entry.base entry.sp kind.site.names.length ∧
      kind.site.names.length ≤ entry.sp.toNat := by
  obtain ⟨charged, scopePost, prefixFits, prefixClock, prefixFrame, suffixRun, scopeEq, prefixBudget, credit, progress, depth, outside⟩ :=
    OpcodeChargeSites.normal kind.site source post frame entry.popCode entry.chargeCode entry.ev entry.gasCap value normal
  have oldDepth : (wordAt charged.memory (frame + 16#64)).toNat + kind.site.names.length = entry.sp.toNat := by
    simpa only [wordAt, entry.spCell, WitnessRadix.MemoryBytes.wordBits] using depth
  have chargeEffect : emptyLocalsHOLFinite charged = emptyLocalsHOLFinite {source with memory := charged.memory, clock := charged.clock} := by
    simpa only [prefixClock] using prefixFrame
  let chargedEntry := entry.after_charge source charged frame kind.site.names.length chargeEffect prefixBudget oldDepth outside
  have chargedCode := congrArg PanSemStateFiniteExact.code prefixFrame
  change charged.code = source.code at chargedCode
  have chargedEnvironment : ArithmeticEffects.Environment charged.code := by rw [chargedCode]; exact environment
  rw [suffix_shape] at suffixRun
  obtain ⟨calcPaid, ready, inner, calcBound, calcFits, calcClock, calcFrame, finishRun, calcScope⟩ :=
    ArithmeticCalls.normal kind.calls charged scopePost chargedEnvironment (StackPush.finish [localVar "r"]) value suffixRun
  have calcEffect : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {charged with clock := ready.clock} := by
    simpa only [calcClock] using calcFrame
  let readyEntry := chargedEntry.after_local charged ready frame calcEffect
  have memoryEq := congrArg PanSemStateFiniteExact.memory calcFrame
  change ready.memory = charged.memory at memoryEq
  have readyDepth : readyEntry.sp.toNat + kind.site.names.length = entry.sp.toNat := by
    change (wordAt ready.memory (frame + 16#64)).toNat + kind.site.names.length = _
    rw [memoryEq]
    exact oldDepth
  have positivePops : 0 < kind.site.names.length := by cases kind <;> decide
  have room : readyEntry.sp < readyEntry.capacity := by
    change readyEntry.sp.toNat < entry.capacity.toNat
    have bounded := entry.depthBound
    omega
  have separated : ∀ offset ∈ ([64, 184, 192] : List Nat), ∀ index < 4,
      frame + BitVec.ofNat 64 offset ≠ (readyEntry.base + readyEntry.sp * 32#64) + BitVec.ofNat 64 (8 * index) := by
    intro offset member index inside
    have actual := readyEntry.separate readyEntry.sp.toNat room offset member index inside
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using actual
  obtain ⟨finishFits, returned, finishClock, finishFrame, finishBudget, usedSame, spFinal, finalDepth, finishOutside⟩ :=
    StackPush.finish_normal ready inner frame readyEntry.base readyEntry.sp readyEntry.capacity [localVar "r"] readyEntry.pushCode readyEntry.pcCode readyEntry.ev
      readyEntry.spCell readyEntry.capCell readyEntry.baseMapped readyEntry.baseCell room readyEntry.capBound separated value finishRun
  have allScope := scopeEq.trans calcScope
  have postMemory := congrArg PanSemStateFiniteExact.memory allScope
  change post.memory = inner.memory at postMemory
  have postClock := congrArg PanSemStateFiniteExact.clock allScope
  change post.clock = inner.clock at postClock
  let paid := kind.site.names.length + calcPaid + 3
  have funded : paid ≤ source.clock := by dsimp only [paid]; omega
  have priceBound : paid ≤ kind.bodyPrice := by dsimp only [paid, Kind.bodyPrice]; omega
  have finalClock : post.clock = source.clock - paid := by dsimp only [paid]; omega
  have canonical := allScope.trans (congrArg emptyLocalsHOLFinite finishFrame)
  change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {ready with memory := inner.memory, clock := ready.clock - 2} at canonical
  rw [← postMemory, show ready.clock - 2 = post.clock from by omega] at canonical
  have calcTransport := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := post.memory, clock := post.clock}) calcFrame
  have chargeTransport := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := post.memory, clock := post.clock}) prefixFrame
  have fullFrame := canonical.trans (calcTransport.trans chargeTransport)
  rw [finalClock] at fullFrame
  refine ⟨paid, priceBound, funded, returned, finalClock, fullFrame, ?_, ?_, ?_, ?_, ?_, by omega⟩
  · rw [postMemory, finishBudget, memoryEq, prefixBudget]
  · change (WitnessRadix.MemoryBytes.wordBits (post.memory (frame + 184#64))).toNat = _
    rw [postMemory, usedSame, memoryEq]
    exact credit
  · rw [postMemory, finalDepth]
    omega
  · rw [postMemory, finalDepth]
    change readyEntry.sp.toNat < entry.capacity.toNat at room
    omega
  · intro address notPC notSP notGas notUsed away
    have currentSPWord : BitVec.ofNat 64 (entry.sp.toNat - kind.site.names.length) = readyEntry.sp := by
      have difference : entry.sp.toNat - kind.site.names.length = readyEntry.sp.toNat := by omega
      rw [difference, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have awaySlot : ∀ index < 4, address ≠ (readyEntry.base + readyEntry.sp * 32#64) + BitVec.ofNat 64 (8 * index) := by
      change ∀ index < 4, address ≠ (entry.base + readyEntry.sp * 32#64) + BitVec.ofNat 64 (8 * index)
      simpa only [currentSPWord] using away
    rw [postMemory]
    exact (finishOutside address notPC notSP awaySlot).trans ((congrFun memoryEq address).trans (outside address notSP notGas notUsed))

end InitECandidate.Solver.GasBudget.ArithmeticStackOpcode

#print axioms InitECandidate.Solver.GasBudget.ArithmeticStackOpcode.body_normal
