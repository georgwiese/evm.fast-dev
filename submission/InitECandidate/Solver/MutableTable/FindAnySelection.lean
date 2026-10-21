import InitECandidate.Solver.MutableTable.FindAnyReturned
import InitECandidate.Solver.MutableTable.FindGeneralChain
import InitECandidate.Solver.Input.WhileActive

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real normal scan returns the absent sentinel or a physically occupied
slot, including arbitrary query reads. This is a physical selection fact;
it does not assume a logical query key or a collision property. -/
theorem any_chain_selection (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (index : BitVec 64) (length : Nat) (chain : GeneralChain snapshot p .word index length)
    (keyLength : p.keyLength=32#64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (locals : Locals source p index)
    (same : Input.LocalEffects.erase source=Input.LocalEffects.erase snapshot)
    (code : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterIndex=(some (.returned value),post)) :
    ∃ answer,value=.val (.word answer) ∧ Selection snapshot p answer := by
  induction chain generalizing source post value with
  | empty index inside loaded =>
    have memory:=Input.LocalEffects.memory_of_erase snapshot source same
    have domain:=congrArg PanSemStateFiniteExact.memaddrs same
    have endian:=congrArg PanSemStateFiniteExact.be same
    have actual : usedByte source p index=some 0 := by
      rw [usedByte_of_fields source snapshot p index memory domain endian]
      exact loaded
    have test : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) condition=some (.val (.word 0#64)) := by
      simpa [eval,evalHOLFinite] using condition_read source p index locals 0 actual
    have loopRun : evaluateHOLFiniteState source loop=(none,source) := by
      rw [loop,evaluateHOLFiniteState_while_total,test]
      simp
    rw [afterIndex,evaluateHOLFiniteState_seq_line780,loopRun] at normal
    simp only at normal
    have read:= (Input.return_normal source post (localVar "cap") value normal).1
    have capRead : eval source (localVar "cap")=some (.val (.word p.capacity)) := by
      simp [eval,localVar,evalHOLExact,toExact,locals.cap]
    exact ⟨p.capacity,Option.some.inj (read.symm.trans capRead),Or.inl rfl⟩
  | occupied index byte length inside nonzero loaded fits mapped tail ih =>
    have memory:=Input.LocalEffects.memory_of_erase snapshot source same
    have domain:=congrArg PanSemStateFiniteExact.memaddrs same
    have endian:=congrArg PanSemStateFiniteExact.be same
    have actual : usedByte source p index=some byte := by
      rw [usedByte_of_fields source snapshot p index memory domain endian]
      exact loaded
    have byteNonzero : byte.toNat≠0 := by intro zero; exact nonzero (UInt8.toNat.inj zero)
    have test : eval source condition=some (.val (.word 1#64)) := by
      simpa only [if_neg byteNonzero] using condition_read source p index locals byte actual
    by_cases zero : source.clock=0
    · have finiteTest : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) condition=some (.val (.word 1#64)) := by simpa only [eval,evalHOLFinite] using test
      rw [afterIndex,evaluateHOLFiniteState_seq_line780,loop,evaluateHOLFiniteState_while_total,finiteTest] at normal
      simp only [if_pos (by decide : (1#64 : BitVec 64)≠0#64),if_pos zero] at normal
      cases normal
    · have entryLocals : Locals (decClockHOLFinite source) p index :=
        ⟨locals.cap,locals.klen,locals.stride,locals.keys,locals.used,locals.key,locals.index⟩
      have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite source) loopBody
      have pure:=any_step_readonly source.code code (decClockHOLFinite source) rfl
      generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) loopBody=output at forward pure
      obtain ⟨answer,target⟩ := output
      have loopRun:=Input.while_active source target condition loopBody answer test zero computed forward
      change evaluateHOLFiniteState source loop=Input.whileResume target condition loopBody answer at loopRun
      rw [afterIndex,evaluateHOLFiniteState_seq_line780,loopRun] at normal
      cases answer with
      | none =>
        have resumed : evaluateHOLFiniteState target afterIndex=(some (.returned value),post) := by
          rw [afterIndex,evaluateHOLFiniteState_seq_line780]
          exact normal
        have nextLocals:=any_step_normal (decClockHOLFinite source) target p index entryLocals keyLength code computed
        have nextFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase snapshot := pure.trans same
        have targetCode:=Input.LocalEffects.code_of_erase source target pure
        have nextCode : target.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one) := by rw [targetCode]; exact code
        exact ih target post nextLocals nextFrame nextCode value resumed
      | some answer =>
        have controls:=any_step_no_control (decClockHOLFinite source)
        rw [computed] at controls
        cases answer with
        | «break» => exact (controls.1 rfl).elim
        | «continue» => exact (controls.2 rfl).elim
        | returned returned =>
          have valueEq : returned=value := by simpa only [Input.whileResume,Option.some.injEq,PanSemResultExact.returned.injEq] using congrArg Prod.fst normal
          have selected:=any_step_returned (decClockHOLFinite source) target p index entryLocals keyLength code returned computed
          exact ⟨index,valueEq.symm.trans selected,Or.inr ⟨inside,byte,nonzero,loaded⟩⟩
        | _ => cases normal

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.any_chain_selection
