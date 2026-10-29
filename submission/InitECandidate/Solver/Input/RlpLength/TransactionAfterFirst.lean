import InitECandidate.Solver.Input.RlpLength.TransactionProgram

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem bind_twice {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (first last : BitVec 64) :
    bind (bind source name first) name last=bind source name last := by
  have mapEq : (source.locals.update (ofString name,.val (.word first))).update (ofString name,.val (.word last))=
      source.locals.update (ofString name,.val (.word last)) := by
    apply HolFiniteMapExact.ext
    funext query
    by_cases same : ofString name=query <;> simp [HolFiniteMapExact.update,FUPDATE,same]
  exact congrArg (fun locals=>{source with locals:=locals}) mapEq

theorem tx_after_first_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first n : BitVec 64) (index sum : Nat)
    (small : n.toNat≤251655056)
    (fb : source.locals.lookup (ofString "fb")=some (.val (.word first)))
    (len : source.locals.lookup (ofString "n")=some (.val (.word n)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (tl : source.locals.lookup (ofString "tl")=some (.val (.word (BitVec.ofNat 64 sum))))
    (code : source.code.lookup (ofString "rlp_bytes_encoded_len")=some (BytesSize.formals,BytesSize.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 11≤source.clock) :
    ∃ encoded paid,n.toNat≤encoded ∧ encoded≤n.toNat+9 ∧ paid≤11 ∧
      evaluateHOLFiniteState source txAfterFirst=(none,txStep source paid index sum encoded) := by
  classical
  let entry:=bind source "el" n
  have fbEntry : entry.locals.lookup (ofString "fb")=some (.val (.word first)) :=
    (bind_lookup_other _ "el" "fb" _ (by decide)).trans fb
  have nEntry : entry.locals.lookup (ofString "n")=some (.val (.word n)) :=
    (bind_lookup_other _ "el" "n" _ (by decide)).trans len
  have elEntry : entry.locals.lookup (ofString "el")=some (.val (.word n)):=bind_lookup_same _ _ _
  have test:=wrap_read entry first n fbEntry nEntry
  have wrapResult : ∃ encoded paid,n.toNat≤encoded ∧ encoded≤n.toNat+9 ∧ paid≤11 ∧
      evaluateHOLFiniteState entry txWrap=(none,bind {entry with clock:=entry.clock-paid} "el" (BitVec.ofNat 64 encoded)) := by
    by_cases active : n=0#64 ∨ first.toNat<192
    · have args : evalListHOLFinite entry (h:=fun address=>Classical.propDecidable (entry.memaddrs address)) [localVar "fb",localVar "n"]=
          some [.val (.word first),.val (.word n)] := by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,fbEntry,nEntry]
      obtain ⟨encoded,paid,lower,upper,bound,number,called⟩:=BytesSize.assign_execute entry first n n "el" [localVar "fb",localVar "n"] small elEntry args code headerCode beCode enough
      refine ⟨encoded,paid+1,lower,upper,by omega,?_⟩
      have subtract : entry.clock-1-paid=entry.clock-(paid+1) := by omega
      rw [txWrap,evaluateHOLFiniteState_ite]
      change eval entry txWrapCondition=_ at test
      simp only [eval] at test
      rw [test]
      simp only [if_pos active]
      simpa [subtract] using called
    · refine ⟨n.toNat,0,by omega,by omega,by decide,?_⟩
      simp only [eval] at test
      rw [txWrap,evaluateHOLFiniteState_ite,test]
      simp only [if_neg active]
      have same : bind {entry with clock:=entry.clock-0} "el" (BitVec.ofNat 64 n.toNat)=entry := by
        simp only [Nat.sub_zero,BitVec.ofNat_toNat]
        exact bind_twice source "el" n n
      rw [same]
      simp
  obtain ⟨encoded,paid,lower,upper,bound,wrapped⟩:=wrapResult
  let addedEntry:=bind {entry with clock:=entry.clock-paid} "el" (BitVec.ofNat 64 encoded)
  have tlEntry : addedEntry.locals.lookup (ofString "tl")=some (.val (.word (BitVec.ofNat 64 sum))) :=
    (bind_lookup_other _ "el" "tl" _ (by decide)).trans ((bind_lookup_other _ "el" "tl" _ (by decide)).trans tl)
  have iEntry : addedEntry.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) :=
    (bind_lookup_other _ "el" "i" _ (by decide)).trans ((bind_lookup_other _ "el" "i" _ (by decide)).trans i)
  have elLocal : addedEntry.locals.lookup (ofString "el")=some (.val (.word (BitVec.ofNat 64 encoded))):=bind_lookup_same _ _ _
  have readSum : eval addedEntry txSumExpression=some (.val (.word (BitVec.ofNat 64 (sum+encoded)))) := by
    simp [eval,txSumExpression,localVar,evalHOLExact,evalListHOLExact,toExact,tlEntry,elLocal,valueIsWord,valueWord,wordOpHOL,wordOp,←BitVec.ofNat_add]
  have sumRun:=WitnessRadix.StateSteps.assign_execute addedEntry "tl" txSumExpression _ _ tlEntry readSum
  let added:=bind addedEntry "tl" (BitVec.ofNat 64 (sum+encoded))
  have iAdded : added.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) :=
    (bind_lookup_other _ "tl" "i" _ (by decide)).trans iEntry
  have readI : eval added incrementExpression=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,incrementExpression,localVar,evalHOLExact,evalListHOLExact,toExact,iAdded,valueIsWord,valueWord,wordOpHOL,wordOp,←BitVec.ofNat_add]
  have iRun:=WitnessRadix.StateSteps.assign_execute added "i" incrementExpression _ _ iAdded readI
  have addRun : evaluateHOLFiniteState addedEntry txAdd=(none,bind added "i" (BitVec.ofNat 64 (index+1))) := by
    rw [txAdd,WitnessRadix.StateSteps.next_sequence addedEntry added _ _ sumRun (Nat.le_refl _)]
    exact iRun
  have sequenceRun : evaluateHOLFiniteState entry (.seq txWrap txAdd)=(none,bind added "i" (BitVec.ofNat 64 (index+1))) := by
    rw [WitnessRadix.StateSteps.next_sequence entry addedEntry _ _ wrapped (by change source.clock-paid≤source.clock; omega)]
    exact addRun
  have nRead : eval source (localVar "n")=some (.val (.word n)) := by simp [eval,evalHOLExact,toExact,localVar,len]
  have declared:=ScalarScope.declare_execute source _ "el" (localVar "n") n (.seq txWrap txAdd) none nRead sequenceRun
  refine ⟨encoded,paid,lower,upper,bound,?_⟩
  change evaluateHOLFiniteState source (.dec (ofString "el") .one (localVar "n") (.seq txWrap txAdd))=_
  rw [declared]
  have restored : restore source "el" (bind added "i" (BitVec.ofNat 64 (index+1)))=txStep source paid index sum encoded := by
    rw [restore_bind_other source added "el" "i" _ (by decide)]
    change bind (restore source "el" (bind addedEntry "tl" (BitVec.ofNat 64 (sum+encoded)))) "i" _=_
    rw [restore_bind_other source addedEntry "el" "tl" _ (by decide)]
    have temporary : restore source "el" addedEntry={source with clock:=source.clock-paid} := by
      change restore source "el" (bind (bind {source with clock:=source.clock-paid} "el" n) "el" (BitVec.ofNat 64 encoded))=_
      rw [bind_twice]
      exact restore_bound {source with clock:=source.clock-paid} "el" (BitVec.ofNat 64 encoded)
    rw [temporary]
    rfl
  exact congrArg (fun target : PanSemStateFiniteExact 64 Guest.HostMemory=>(none,target)) restored

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.tx_after_first_execute
