import InitECandidate.Solver.Input.LocalWord
import InitECandidate.Solver.Input.VarList.Checks

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def priorState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (index : Nat) (current previous : BitVec 64) :=
  {source with memory:=if 0<index then WitnessRadix.StoreWord.put source.memory (lengthCell array (index-1)) (current-previous) else source.memory}
def pointerState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (current previous : BitVec 64) :=
  {priorState source plan.array index current previous with memory:=(WitnessRadix.StoreWord.put
    (priorState source plan.array index current previous).memory (row plan.array index) (plan.inputPointer+BitVec.ofNat 64 plan.start+current))}
def stepState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (current previous : BitVec 64) :=
  bind (bind (pointerState source input plan index current previous) "prev" current) "i" (BitVec.ofNat 64 (index+1))

/-- The actual conditional store finishes the preceding record's length;
index zero skips it. Both paths preserve every copied input byte. -/
theorem prior_store (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (small : index<plan.count) (current previous : BitVec 64)
    (heap : Blob.HeapInput source input plan.inputPointer) (domain : source.memaddrs=InitE.ordinaryDomain)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word plan.array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (o : source.locals.lookup (ofString "o")=some (.val (.word current)))
    (p : source.locals.lookup (ofString "prev")=some (.val (.word previous))) :
    evaluateHOLFiniteState source priorLengthStore=(none,priorState source plan.array index current previous) ∧
      Blob.HeapInput (priorState source plan.array index current previous) input plan.inputPointer := by
  classical
  have countSmall:=plan.count_small
  have test:=has_previous_read source index (by omega) i
  simp only [eval] at test
  by_cases positive : 0<index
  · simp only [if_pos positive] at test
    have address:=prior_address_read source plan.array index positive a i
    have value:=length_read source current previous o p
    have stored:=WitnessRadix.StoreWord.execute source priorLengthAddress priorLengthExpression (lengthCell plan.array (index-1)) (current-previous)
      address value (plan.length_mapped source domain (index-1) (by omega))
    have framed:=plan.length_store_input source heap (index-1) (by omega) (current-previous)
    refine ⟨?_,?_⟩
    · rw [priorLengthStore,evaluateHOLFiniteState_ite,test]
      simpa [priorState,positive] using stored
    · simpa only [priorState,if_pos positive] using framed
  · simp only [if_neg positive] at test
    refine ⟨?_,?_⟩
    · rw [priorLengthStore,evaluateHOLFiniteState_ite,test]
      simp [priorState,positive]
    · simpa only [priorState,if_neg positive] using heap

/-- The current record pointer is written to the real allocated array. -/
theorem pointer_store (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (small : index<plan.count) (current previous : BitVec 64)
    (heap : Blob.HeapInput (priorState source plan.array index current previous) input plan.inputPointer)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (a : source.locals.lookup (ofString "arr")=some (.val (.word plan.array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (o : source.locals.lookup (ofString "o")=some (.val (.word current)))
    (p : source.locals.lookup (ofString "p")=some (.val (.word (plan.inputPointer+BitVec.ofNat 64 plan.start)))) :
    evaluateHOLFiniteState (priorState source plan.array index current previous) rowPointerStore=(none,pointerState source input plan index current previous) ∧
      Blob.HeapInput (pointerState source input plan index current previous) input plan.inputPointer := by
  let entered:=priorState source plan.array index current previous
  have address:=row_address_read entered plan.array index a i
  have value:=pointer_read entered (plan.inputPointer+BitVec.ofNat 64 plan.start) current p o
  have stored:=WitnessRadix.StoreWord.execute entered rowPointerAddress rowPointerExpression (row plan.array index) _ address value (plan.row_mapped entered domain index small)
  exact ⟨stored,plan.row_store_input entered heap index small _⟩

/-- The actual two local assignments after both record stores, with no clock
payment or nonlocal-state change. -/
theorem step_updates (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (current previous : BitVec 64)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (o : source.locals.lookup (ofString "o")=some (.val (.word current)))
    (p : source.locals.lookup (ofString "prev")=some (.val (.word previous))) :
    evaluateHOLFiniteState (pointerState source input plan index current previous) (.seq savePrevious increment)=
      (none,stepState source input plan index current previous) := by
  classical
  let entered:=pointerState source input plan index current previous
  have value:=Request.local_word entered "o" current o
  have save : evaluateHOLFiniteState entered savePrevious=(none,bind entered "prev" current) :=
    WitnessRadix.StateSteps.assign_execute entered "prev" (localVar "o") previous current p value
  have savedI : (bind entered "prev" current).locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) :=
    (bind_lookup_other entered "prev" "i" current (by decide)).trans i
  have nextRead : eval (bind entered "prev" current) (.op .add [localVar "i",.const 1#64])=
      some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simpa only [Scalar.plus,BitVec.ofNat_add] using Scalar.plus_read (bind entered "prev" current) (localVar "i") (BitVec.ofNat 64 index) 1
      (Request.local_word _ "i" _ savedI)
  have next : evaluateHOLFiniteState (bind entered "prev" current) increment=(none,stepState source input plan index current previous) :=
    WitnessRadix.StateSteps.assign_execute (bind entered "prev" current) "i" (.op .add [localVar "i",.const 1#64]) (BitVec.ofNat 64 index) _ savedI nextRead
  rw [WitnessRadix.StateSteps.next_sequence entered (bind entered "prev" current) savePrevious increment save (Nat.le_refl _)]
  exact next

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.prior_store
#print axioms InitECandidate.Solver.Input.VarList.pointer_store
#print axioms InitECandidate.Solver.Input.VarList.step_updates
