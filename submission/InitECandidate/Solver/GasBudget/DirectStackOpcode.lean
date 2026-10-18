import InitECandidate.Solver.GasBudget.StackPushFinish
import InitECandidate.Solver.GasBudget.OpcodeChargeSites

namespace InitECandidate.Solver.GasBudget.DirectStackOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Kind where | op_and | op_or | op_xor | op_not

def Kind.site : Kind → OpcodeChargeSites.Kind
  | .op_and => .op_and | .op_or => .op_or | .op_xor => .op_xor | .op_not => .op_not

def Kind.arguments (kind : Kind) : List (ExpHOL 64) :=
  match kind.site.suffix with | .seq (.call _ _ arguments) _ => arguments | _ => []

theorem suffix_shape (kind : Kind) : kind.site.suffix = StackPush.finish kind.arguments := by
  cases kind <;> simp only [Kind.site, Kind.arguments, OpcodeChargeSites.Kind.suffix, OpcodeChargeSites.stripPops,
    OpcodeChargeSites.Kind.body, OpcodeChargeSites.Kind.names, Guest.guestFn_op_and, Guest.guestFn_op_or, Guest.guestFn_op_xor,
    Guest.guestFn_op_not, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, StackPush.finish] <;> rfl

structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64) where
  base : BitVec 64
  sp : BitVec 64
  capacity : BitVec 64
  ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))
  popCode : source.code.lookup (ofString "stack_pop") = some ([], StackPop.body, StackPop.shape)
  chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one)
  pushCode : source.code.lookup (ofString "stack_push") = some (StackPush.formals, StackPush.body, .one)
  pcCode : source.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one)
  spCell : source.memory (frame + 16#64) = .word sp
  capCell : source.memory (frame + 232#64) = .word capacity
  baseMapped : source.memaddrs (frame + 8#64)
  baseCell : source.memory (frame + 8#64) = .word base
  depthBound : sp.toNat ≤ capacity.toNat
  capBound : capacity.toNat ≤ 1024
  gasCap : regularBudget source.memory frame ≤ 16777216
  separate : ∀ slot < capacity.toNat, ∀ offset ∈ ([64, 184, 192] : List Nat), ∀ index < 4,
    frame + BitVec.ofNat 64 offset ≠ (base + BitVec.ofNat 64 slot * 32#64) + BitVec.ofNat 64 (8 * index)

/-- Full original AND/OR/XOR/NOT bodies: real pops, charge3, tuple push,
pc advance, return and scopes. Existing free stack room is derived from the
actual pop depth and incoming bounded stack; no future-room premise. -/
theorem body_normal (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (entry : Entry source frame) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.site.body = (some (.returned value), post)) :
    kind.site.names.length + 3 ≤ source.clock ∧ value = .val (.word 0#64) ∧
      post.clock = source.clock - (kind.site.names.length + 3) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (kind.site.names.length + 3)} ∧
      regularBudget post.memory frame = regularBudget source.memory frame ∧
      (wordAt post.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + 3 ∧
      (wordAt post.memory (frame + 16#64)).toNat + kind.site.names.length = entry.sp.toNat + 1 ∧
      (wordAt post.memory (frame + 16#64)).toNat ≤ entry.capacity.toNat := by
  obtain ⟨ready, inner, prefixFits, prefixClock, prefixFrame, suffixRun, scopeEq, prefixBudget, credit, progress, depth, outside⟩ :=
    OpcodeChargeSites.normal kind.site source post frame entry.popCode entry.chargeCode entry.ev entry.gasCap value normal
  have readyGlobals := congrArg PanSemStateFiniteExact.globals prefixFrame
  change ready.globals = source.globals at readyGlobals
  have readyCode := congrArg PanSemStateFiniteExact.code prefixFrame
  change ready.code = source.code at readyCode
  have readyDomain := congrArg PanSemStateFiniteExact.memaddrs prefixFrame
  change ready.memaddrs = source.memaddrs at readyDomain
  have readyEV : ready.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [readyGlobals]; exact entry.ev
  have readyPush : ready.code.lookup (ofString "stack_push") = some (StackPush.formals, StackPush.body, .one) := by rw [readyCode]; exact entry.pushCode
  have readyPC : ready.code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one) := by rw [readyCode]; exact entry.pcCode
  have readyBaseMapped : ready.memaddrs (frame + 8#64) := by rw [readyDomain]; exact entry.baseMapped
  have header (offset : BitVec 64) (notSP : offset ≠ 16#64) (notGas : offset ≠ 64#64) (notUsed : offset ≠ 184#64) :
      ready.memory (frame + offset) = source.memory (frame + offset) :=
    outside (frame + offset) (offsets_ne frame offset 16#64 notSP) (offsets_ne frame offset 64#64 notGas) (offsets_ne frame offset 184#64 notUsed)
  have readyBase : ready.memory (frame + 8#64) = .word entry.base := (header 8#64 (by decide) (by decide) (by decide)).trans entry.baseCell
  have readyCap : ready.memory (frame + 232#64) = .word entry.capacity := (header 232#64 (by decide) (by decide) (by decide)).trans entry.capCell
  have positivePops : 0 < kind.site.names.length := by cases kind <;> decide
  have fee : kind.site.fee = 3 := by cases kind <;> rfl
  cases currentSPCell : ready.memory (frame + 16#64) with
  | word currentSP =>
    have depthNow : currentSP.toNat + kind.site.names.length = entry.sp.toNat := by
      simpa only [wordAt, currentSPCell, entry.spCell, WitnessRadix.MemoryBytes.wordBits] using depth
    have room : currentSP < entry.capacity := by change currentSP.toNat < entry.capacity.toNat; have bounded := entry.depthBound; omega
    have separated : ∀ offset ∈ ([64, 184, 192] : List Nat), ∀ index < 4,
        frame + BitVec.ofNat 64 offset ≠ (entry.base + currentSP * 32#64) + BitVec.ofNat 64 (8 * index) := by
      intro offset member index inside
      have actual := entry.separate currentSP.toNat room offset member index inside
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using actual
    rw [suffix_shape] at suffixRun
    obtain ⟨finishFits, returned, finishClock, finishFrame, finishBudget, usedSame, spFinal, finalDepth⟩ :=
      StackPush.finish_normal ready inner frame entry.base currentSP entry.capacity kind.arguments readyPush readyPC readyEV currentSPCell readyCap
        readyBaseMapped readyBase room entry.capBound separated value suffixRun
    have postMemory := congrArg PanSemStateFiniteExact.memory scopeEq
    change post.memory = inner.memory at postMemory
    have postClock := congrArg PanSemStateFiniteExact.clock scopeEq
    change post.clock = inner.clock at postClock
    have sub : source.clock - (kind.site.names.length + 1) - 2 = source.clock - (kind.site.names.length + 3) := by omega
    have canonical := scopeEq.trans (congrArg emptyLocalsHOLFinite finishFrame)
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {ready with memory := inner.memory, clock := ready.clock - 2} at canonical
    rw [← postMemory, prefixClock, sub] at canonical
    have transport := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
      {state with memory := post.memory, clock := source.clock - (kind.site.names.length + 3)}) prefixFrame
    refine ⟨by omega, returned, by omega, canonical.trans transport, ?_, ?_, ?_, ?_⟩
    · rw [postMemory, finishBudget, prefixBudget]
    · change (WitnessRadix.MemoryBytes.wordBits (post.memory (frame + 184#64))).toNat = _
      rw [postMemory, usedSame]
      rw [fee] at credit
      exact credit
    · rw [postMemory, finalDepth]
      omega
    · rw [postMemory, finalDepth]
      change currentSP.toNat < entry.capacity.toNat at room
      omega

end InitECandidate.Solver.GasBudget.DirectStackOpcode

#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.suffix_shape
#print axioms InitECandidate.Solver.GasBudget.DirectStackOpcode.body_normal
