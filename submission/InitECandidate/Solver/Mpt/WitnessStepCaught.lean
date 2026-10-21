import InitECandidate.Solver.Mpt.WitnessStepProgram
import InitECandidate.Solver.Mpt.AccountDecodeCaught
import InitECandidate.Solver.Rlp.ItemBodyFrame

namespace InitECandidate.Solver.Mpt.WitnessStep
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem caught_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length) := by
  simp [arguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]

theorem rlp_cost (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (rlpBody kind)).2.clock≤60*length.toNat+43 := by
  cases kind with
  | resolve=>exact (Rlp.Item.body_cost source pointer length cursor limit pointerCell lengthCell arena fits installed).trans (by omega)
  | decode=>exact Rlp.Decode.body_cost source pointer length cursor limit pointerCell lengthCell arena fits installed

theorem rlp_normal (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (answer : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (rlpBody kind)=(some (.returned answer),post)) :
    parsed kind pointer length answer ∧ Rlp.Validation.Arena post cursor limit ∧
    Rlp.Validation.Above source post cursor.toNat ∧ post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code ∧
    post.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
    (∀ key,post.globals.lookup key=source.globals.lookup key) ∧ source.clock-post.clock≤60*length.toNat+43 := by
  have fields:=Input.evaluation_fields source post (rlpBody kind) (some (.returned answer)) normal
  have heapFrame : post.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") := by
    have effects:=Rlp.Decode.globals (ofString "heap_ptr") source.code installed (by decide)
    cases kind with
    | resolve=>
      have frame:=Rlp.Item.globals (ofString "heap_ptr") source.code installed (by decide) source rfl
      change evaluateHOLFiniteState source Rlp.Item.body=(some (.returned answer),post) at normal
      rw [normal] at frame
      exact congrArg Prod.snd frame
    | decode=>
      have frame:=effects source rfl
      change evaluateHOLFiniteState source Rlp.Decode.body=(some (.returned answer),post) at normal
      rw [normal] at frame
      exact congrArg Prod.snd frame
  have result : parsed kind pointer length answer ∧ Rlp.Validation.Arena post cursor limit ∧
      Rlp.Validation.Above source post cursor.toNat ∧ source.clock-post.clock≤60*length.toNat+43 := by
    cases kind with
    | resolve=>
      obtain ⟨valid,nextArena,above,price⟩:=Rlp.Item.body_normal_above source post pointer length cursor limit pointerCell lengthCell arena fits installed answer normal
      exact ⟨valid,nextArena,above,price.trans (by omega)⟩
    | decode=>exact Rlp.Decode.body_normal_above source post pointer length cursor limit pointerCell lengthCell arena fits installed answer normal
  have globalCells (key : MlS) : post.globals.lookup key=source.globals.lookup key := by
    by_cases scratch : key=ofString "scratch_ptr"
    · subst key
      exact result.2.1.cursorGlobal.trans arena.cursorGlobal.symm
    · cases kind with
      | resolve=>
        have frame:=Rlp.Item.globals key source.code installed scratch source rfl
        change evaluateHOLFiniteState source Rlp.Item.body=(some (.returned answer),post) at normal
        rw [normal] at frame
        exact congrArg Prod.snd frame
      | decode=>
        have frame:=Rlp.Decode.globals key source.code installed scratch source rfl
        change evaluateHOLFiniteState source Rlp.Decode.body=(some (.returned answer),post) at normal
        rw [normal] at frame
        exact congrArg Prod.snd frame
  exact ⟨result.1,result.2.1,result.2.2.1,fields.1,fields.2.1,fields.2.2.2,heapFrame,globalCells,result.2.2.2⟩

theorem caught_cost (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (caught kind)).2.clock≤60*length.toNat+45 := by
  have args:=caught_arguments source pointer length pointerCell lengthCell
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString (rlpName kind)) (rlpBody kind) Rlp.Item.resultShape pointer length (rlp_code kind source.code installed)
  have priced:=rlp_cost kind (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal
    (Rlp.Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed
  exact Input.ClockCost.caught_destination_current source (some (.local,ofString "it")) (ofString (rlpName kind)) arguments _ (rlpBody kind) callee Rlp.Item.resultShape
    (ofString "RlpErr") (ofString "e") handler (60*length.toNat+43) 1 args called priced (Fail.call_price source.code installed [.const 3#64])

/-- Normal passage through the genuine caught RLP prefix restores the
current scratch cursor and protects every byte above it. The MPT error
handler cannot pass, so no successful future call is assumed. -/
theorem caught_none (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (normal : evaluateHOLFiniteState source (caught kind)=(none,target)) :
    1≤source.clock ∧ ∃ calleePost answer,
      parsed kind pointer length answer ∧ Rlp.Validation.Arena calleePost cursor limit ∧
      Rlp.Validation.Above source calleePost cursor.toNat ∧ calleePost.memaddrs=source.memaddrs ∧ calleePost.be=source.be ∧ calleePost.code=source.code ∧
      calleePost.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      (∀ key,calleePost.globals.lookup key=source.globals.lookup key) ∧
      source.clock-calleePost.clock≤60*length.toNat+44 ∧ target=Input.CallNormal.continuationEntry source calleePost "it" answer := by
  have args:=caught_arguments source pointer length pointerCell lengthCell
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString (rlpName kind)) (rlpBody kind) Rlp.Item.resultShape pointer length (rlp_code kind source.code installed)
  have stops : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→(evaluateHOLFiniteState current handler).1≠none := by
    intro current codeEq passed
    have currentInstalled : Input.OriginalCode.Installed current.code := by rw [codeEq]; exact installed
    exact Fail.call_not_normal current _ currentInstalled [.const 3#64] (Prod.ext passed rfl)
  obtain ⟨positive,calleePost,answer,bodyRun,checked,targetEq⟩:=Input.CallNormal.assigned_caught_stops source target (ofString "it") (ofString (rlpName kind)) arguments _ (rlpBody kind) callee Rlp.Item.resultShape
    (ofString "RlpErr") (ofString "e") handler args called stops normal
  obtain ⟨parsed,nextArena,above,domain,endian,codeEq,heapEq,globalCells,price⟩:=rlp_normal kind (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
    (Rlp.Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed answer bodyRun
  have clock:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) (rlpBody kind)
  rw [bodyRun] at clock
  change calleePost.clock≤source.clock-1 at clock
  change source.clock-1-calleePost.clock≤60*length.toNat+43 at price
  exact ⟨positive,calleePost,answer,parsed,nextArena,above,domain,endian,codeEq,heapEq,globalCells,by omega,targetEq⟩

end InitECandidate.Solver.Mpt.WitnessStep

#print axioms InitECandidate.Solver.Mpt.WitnessStep.caught_arguments
#print axioms InitECandidate.Solver.Mpt.WitnessStep.rlp_cost
#print axioms InitECandidate.Solver.Mpt.WitnessStep.rlp_normal
#print axioms InitECandidate.Solver.Mpt.WitnessStep.caught_cost
#print axioms InitECandidate.Solver.Mpt.WitnessStep.caught_none
