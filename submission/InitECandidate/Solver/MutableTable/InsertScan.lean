import InitECandidate.Solver.MutableTable.InsertProgram

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem advanced_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters) (index : BitVec 64)
    (locals : Find.Locals source p index) :
    Find.Locals (bind (decClockHOLFinite source) "i" (Find.next p index)) p (Find.next p index) := by
  constructor
  · exact (bind_lookup_other _ "i" "cap" _ (by decide)).trans locals.cap
  · exact (bind_lookup_other _ "i" "klen" _ (by decide)).trans locals.klen
  · exact (bind_lookup_other _ "i" "stride" _ (by decide)).trans locals.stride
  · exact (bind_lookup_other _ "i" "keys" _ (by decide)).trans locals.keys
  · exact (bind_lookup_other _ "i" "used" _ (by decide)).trans locals.used
  · exact (bind_lookup_other _ "i" "key" _ (by decide)).trans locals.key
  · exact bind_lookup_same _ _ _

/-- The literal raw-insertion scan reaches its first empty slot, consumes
one clock per occupied slot, and preserves every local except its index. -/
theorem scan_prefix (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (indices : Nat→BitVec 64) (start length : Nat) (locals : Find.Locals source p (indices start))
    (advance : ∀ j<start+length,indices (j+1)=Find.next p (indices j))
    (occupied : ∀ j,start≤j→j<start+length→Find.usedByte source p (indices j)=some 1)
    (empty : Find.usedByte source p (indices (start+length))=some 0) (enough : length≤source.clock) :
    ∃ target,evaluateHOLFiniteState source loop=(none,target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-length} ∧
      Find.Locals target p (indices (start+length)) ∧
      ∀ name,ofString "i"≠name→target.locals.lookup name=source.locals.lookup name := by
  classical
  induction length generalizing source start with
  | zero=>
    have actual : Find.usedByte source p (indices start)=some 0:=by simpa using empty
    have test:=Find.condition_read source p (indices start) locals 0 actual
    refine ⟨source,?_,by simp,by simpa using locals,by intros;rfl⟩
    rw [loop,evaluateHOLFiniteState_while_total]
    simp only [eval,evalHOLFinite] at test ⊢
    rw [test]
    simp
  | succ length ih=>
    let entry:=decClockHOLFinite source
    let post:=bind entry "i" (Find.next p (indices start))
    have actual:=occupied start (Nat.le_refl _) (by omega)
    have test:=Find.condition_read source p (indices start) locals 1 actual
    have entryLocals : Find.Locals entry p (indices start):=
      ⟨locals.cap,locals.klen,locals.stride,locals.keys,locals.used,locals.key,locals.index⟩
    have stepped:=WitnessRadix.StateSteps.assign_execute entry "i" Find.nextIndex (indices start)
      (Find.next p (indices start)) entryLocals.index (Find.next_read entry p (indices start) entryLocals)
    have stepRun : evaluateHOLFiniteState entry increment=(none,post):=stepped
    have postLocals : Find.Locals post p (indices (start+1)) := by
      rw [advance start (by omega)]
      exact advanced_locals source p (indices start) locals
    have sum : start+1+length=start+(length+1):=by omega
    obtain ⟨target,recursive,frame,finalLocals,other⟩:=ih post (start+1) postLocals
      (by intro j inside;exact advance j (by omega))
      (by intro j lower upper;exact occupied j (by omega) (by omega))
      (by rw [sum];exact empty)
      (by change length≤source.clock-1;omega)
    have unfolded:=evaluateHOLFiniteState_while_total source Find.condition increment
    simp only [eval,evalHOLFinite] at test unfolded
    rw [test] at unfolded
    rw [if_neg (show (1:UInt8).toNat≠0 by decide)] at unfolded
    simp only at unfolded
    rw [if_pos (show (1#64)≠(0:BitVec 64) by decide),if_neg (show source.clock≠0 by omega),
      stepRun,WitnessRadix.StateSteps.fixed_clock entry post none (by exact Nat.le_refl _)] at unfolded
    refine ⟨target,unfolded.trans recursive,?_,by simpa only [sum] using finalLocals,?_⟩
    · have subtract : source.clock-1-length=source.clock-(length+1):=by omega
      simpa only [post,entry,WitnessRadix.QueryBranch.bind,setVarHOLFinite,decClockHOLFinite,emptyLocalsHOLFinite,subtract] using frame
    · intro name different
      rw [other name different]
      simp [post,entry,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,decClockHOLFinite]

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.scan_prefix
