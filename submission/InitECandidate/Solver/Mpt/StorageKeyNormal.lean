import InitECandidate.Solver.Input.CopyAnyCost
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Mpt.StorageKeyExecution
import InitECandidate.Solver.ClockPaddingFull

namespace InitECandidate.Solver.Mpt.StorageKey
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem result_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64) :
    (resultState source address key scratch).clock = source.clock - price address key scratch := by
  simp [resultState,CopyGeneral.callState,price,Nat.sub_sub,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega

theorem result_padding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64) (extra : Nat) :
    resultState {source with clock := source.clock + extra} address key scratch =
      {resultState source address key scratch with clock := source.clock + extra - price address key scratch} := by
  simp [resultState,CopyGeneral.callState,price,Nat.sub_sub,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (addressArena : AllocatedBytes.Arena address 20) (keyArena : AllocatedBytes.Arena key 32)
    (scratchArena : AllocatedBytes.Arena scratch 52) (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 12 := by
  have bound := price_bound address key scratch
  by_cases enough : price address key scratch ≤ source.clock
  · rw [execute source address key scratch addressLocal keyLocal scratchGlobal domain addressArena keyArena scratchArena installed enough]
    change source.clock - (resultState source address key scratch).clock ≤ 12
    rw [result_clock]
    omega
  · omega

theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (addressArena : AllocatedBytes.Arena address 20) (keyArena : AllocatedBytes.Arena key 32)
    (scratchArena : AllocatedBytes.Arena scratch 52) (installed : Input.OriginalCode.Installed source.code)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned),post)) :
    price address key scratch ≤ source.clock ∧ returned = .val (.word scratch) ∧
      post = emptyLocalsHOLFinite (resultState source address key scratch) := by
  let extra := price address key scratch
  let padded := {source with clock := source.clock + extra}
  let model := emptyLocalsHOLFinite (resultState source address key scratch)
  have actual := execute padded address key scratch addressLocal keyLocal scratchGlobal domain addressArena keyArena scratchArena installed
    (by change extra ≤ source.clock + extra; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned returned)) post extra
    ⟨normal,by intro impossible; cases impossible⟩
  have resultEq := congrArg Prod.fst (lifted.symm.trans actual)
  have postEq := congrArg Prod.snd (lifted.symm.trans actual)
  change {post with clock := post.clock + extra} = emptyLocalsHOLFinite (resultState padded address key scratch) at postEq
  have frame : {post with clock := post.clock + extra} = {model with clock := source.clock + extra - price address key scratch} := by
    rw [postEq]
    dsimp only [padded]
    rw [result_padding]
    rfl
  obtain ⟨funded,next⟩ := InitECandidate.Solver.strip_full_clock_padding source post model (price address key scratch) extra (by omega) frame
  have clock : model.clock = source.clock - price address key scratch := result_clock source address key scratch
  rw [← clock] at next
  exact ⟨funded,by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq,next⟩

end InitECandidate.Solver.Mpt.StorageKey

#print axioms InitECandidate.Solver.Mpt.StorageKey.result_clock
#print axioms InitECandidate.Solver.Mpt.StorageKey.result_padding
#print axioms InitECandidate.Solver.Mpt.StorageKey.body_cost
#print axioms InitECandidate.Solver.Mpt.StorageKey.body_normal


namespace InitECandidate.Solver.Mpt.StorageKey.Current
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch Input
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Price the actual20/32byte copies on every outcome, without assuming
that either input is mapped or that either copy will finish normally. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (scratchCell : source.globals.lookup (ofString "sk_buf")=some (.val (.word scratch)))
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤67 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
      [buffer,localVar "addr",.const 20#64]=some (CopyGeneral.values scratch address 20):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,buffer,localVar,toExact,addressCell,scratchCell,CopyGeneral.values]
  have first:=CopyAny.call_cost source _ scratch address 20 (by decide) args (CopyGeneral.original_code source.code installed)
  change source.clock-(evaluateHOLFiniteState source firstCopy).2.clock≤CopyAny.price 20+1 at first
  have firstPrice : source.clock-(evaluateHOLFiniteState source firstCopy).2.clock≤25:=by simpa [CopyAny.price] using first
  rw [body_shape]
  apply ClockCost.sequence_reached_current source firstCopy (.seq secondCopy (.return buffer)) 25 42 firstPrice
  intro middle normal
  obtain ⟨frame,locals⟩:=CopyAny.call_span_normal source middle scratch address 20 (by decide) _ args installed normal
  have globals:=congrArg PanSemStateFiniteExact.globals frame.fields
  change middle.globals=source.globals at globals
  have nextCode:=MemoryMetadata.code frame.fields
  have nextInstalled : OriginalCode.Installed middle.code:=by rw [nextCode]; exact installed
  have nextArgs : evalListHOLFinite middle (h:=fun query=>Classical.propDecidable (middle.memaddrs query))
      [.op .add [buffer,.const 20#64],localVar "key",.const 32#64]=some (CopyGeneral.values (scratch+20#64) key 32):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,buffer,localVar,toExact,locals,globals,keyCell,scratchCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,CopyGeneral.values]
  have second:=CopyAny.call_cost middle _ (scratch+20#64) key 32 (by decide) nextArgs (CopyGeneral.original_code middle.code nextInstalled)
  change middle.clock-(evaluateHOLFiniteState middle secondCopy).2.clock≤CopyAny.price 32+1 at second
  have secondPrice : middle.clock-(evaluateHOLFiniteState middle secondCopy).2.clock≤42:=by simpa [CopyAny.price] using second
  simpa only [Nat.add_zero] using ClockCost.sequence_current middle secondCopy (.return buffer) 42 0 secondPrice (ClockCost.returned middle.code _)

/-- Every actual normal key construction writes only its52byte buffer.
The frame is derived from the two real copies without input-arena premises. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address key scratch : BitVec 64)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (scratchCell : source.globals.lookup (ofString "sk_buf")=some (.val (.word scratch)))
    (installed : OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word scratch) ∧ Copy32Span.Frame source post scratch 52 := by
  rw [body_shape] at normal
  have firstSafe : LocalPrefix (ofString "_") firstCopy:=.call none _ _ (by simp)
  obtain ⟨middle,firstRun,continued,preserved⟩:=firstSafe.normal_continue source post (.seq secondCopy (.return buffer)) value normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
      [buffer,localVar "addr",.const 20#64]=some (CopyGeneral.values scratch address 20):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,buffer,localVar,toExact,addressCell,scratchCell,CopyGeneral.values]
  obtain ⟨firstFrame,firstLocals⟩:=CopyAny.call_span_normal source middle scratch address 20 (by decide) _ args installed firstRun
  have firstGlobals:=congrArg PanSemStateFiniteExact.globals firstFrame.fields
  change middle.globals=source.globals at firstGlobals
  have nextCode:=MemoryMetadata.code firstFrame.fields
  have nextInstalled : OriginalCode.Installed middle.code:=by rw [nextCode]; exact installed
  have nextArgs : evalListHOLFinite middle (h:=fun query=>Classical.propDecidable (middle.memaddrs query))
      [.op .add [buffer,.const 20#64],localVar "key",.const 32#64]=some (CopyGeneral.values (scratch+20#64) key 32):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,buffer,localVar,toExact,firstLocals,firstGlobals,keyCell,scratchCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,CopyGeneral.values]
  have secondSafe : LocalPrefix (ofString "_") secondCopy:=.call none _ _ (by simp)
  obtain ⟨last,secondRun,returned,preserved⟩:=secondSafe.normal_continue middle post (.return buffer) value continued
  obtain ⟨secondFrame,secondLocals⟩:=CopyAny.call_span_normal middle last (scratch+20#64) key 32 (by decide) _ nextArgs nextInstalled secondRun
  have secondGlobals:=congrArg PanSemStateFiniteExact.globals secondFrame.fields
  change last.globals=middle.globals at secondGlobals
  obtain ⟨read,endpoint⟩:=return_normal last post buffer value returned
  have actual : eval last buffer=some (.val (.word scratch)):=by
    simp [buffer,eval,evalHOLExact,secondGlobals,firstGlobals,scratchCell]
  refine ⟨Option.some.inj (read.symm.trans actual),⟨?_,?_⟩⟩
  · rw [endpoint]
    exact secondFrame.fields.trans firstFrame.fields
  · intro query away
    have leftAway : CopyGeneral.Away scratch query 20:=by intro offset inside; exact away offset (by omega)
    have rightAway : CopyGeneral.Away (scratch+20#64) query 32:=by
      intro offset inside
      have current:=away (20+offset) (by omega)
      simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc,show BitVec.ofNat 64 20=20#64 from rfl] using current
    rw [endpoint]
    exact (secondFrame.memory query rightAway).trans (firstFrame.memory query leftAway)

end InitECandidate.Solver.Mpt.StorageKey.Current

#print axioms InitECandidate.Solver.Mpt.StorageKey.Current.body_cost
#print axioms InitECandidate.Solver.Mpt.StorageKey.Current.body_normal
