import InitECandidate.Solver.Mpt.InsertEmptyFinish

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The complete original empty-root insertion returns its fresh leaf,
retains its exact nonlocal state, and spends at most three source ticks.
Allocation room and every intermediate normal call follow from the real run. -/
theorem empty_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word 0#64)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word 0#64)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    AllocatedBytes.Arena heap 64 ∧ value=.val (.word heap) ∧ target.clock=source.clock-3 ∧
      source.clock-target.clock≤3 ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase (finished source heap key length pointer size) := by
  obtain ⟨arena,inner,last,iterationPost,iterationInner,clock,frame,funded,bodyRun,leafRun,afterRun,stepClock,stepFrame,tailRun,returnRun⟩:=
    empty_leaf_created source target heap key length pointer size nodeCell keyCell lengthCell levelCell pointerCell sizeCell installed domain heapCell frontier aligned value normal
  have finishRun:=after_choice_execute source heap key length pointer size nodeCell levelCell
  have iterationEq : iterationInner=finished source heap key length pointer size:=congrArg Prod.snd (afterRun.symm.trans finishRun)
  rw [iterationEq] at stepClock stepFrame
  have currentNode : (firstDispatch source).locals.lookup (ofString "node")=some (.val (.word 0#64)):=by
    simpa [firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using nodeCell
  have suffixRun : evaluateHOLFiniteState (firstDispatch source) (.seq nodeChoice afterChoice)=(none,finished source heap key length pointer size):=by
    rw [evaluateHOLFiniteState_seq_line780,empty_choice (firstDispatch source) currentNode,leafRun]
    exact finishRun
  have firstGo : (decClockHOLFinite (setup source)).locals.lookup (ofString "go")=some (.val (.word 1#64)):=(setup_locals source).2.2
  have execution:=prefix_execution (decClockHOLFinite (setup source)) 1#64 firstGo
  rw [iteration_shape] at bodyRun
  have localAgreement (name : MlS) (avoid : ∀ action∈iterationActions,action.avoids name) :
      iterationPost.locals.lookup name=(finished source heap key length pointer size).locals.lookup name:=by
    have agreement:=execution.local_result name avoid (.seq nodeChoice afterChoice)
    rw [bodyRun] at agreement
    change iterationPost.locals.lookup name=(evaluateHOLFiniteState (firstDispatch source) (.seq nodeChoice afterChoice)).2.locals.lookup name at agreement
    rw [suffixRun] at agreement
    exact agreement
  have goZero : iterationPost.locals.lookup (ofString "go")=some (.val (.word 0#64)):=
    (localAgreement (ofString "go") (by simp [iterationActions,Input.CallPrefix.Action.avoids,ofString])).trans (finished_locals source heap key length pointer size).1
  have resultCell : iterationPost.locals.lookup (ofString "result")=some (.val (.word heap)):=
    (localAgreement (ofString "result") (by simp [iterationActions,Input.CallPrefix.Action.avoids,ofString])).trans (finished_locals source heap key length pointer size).2
  have testRead : eval iterationPost test=some (.val (.word 0#64)):=by
    simp [eval,test,localVar,evalHOLExact,toExact,goZero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have stopped : evaluateHOLFiniteState iterationPost (.while test loopBody)=(none,iterationPost):=by
    rw [evaluateHOLFiniteState_while_total]
    simp only [eval,evalHOLFinite] at testRead ⊢
    rw [testRead]
    simp
  have lastEq : last=iterationPost:=congrArg Prod.snd (tailRun.symm.trans stopped)
  rw [lastEq] at returnRun
  obtain ⟨read,innerEq⟩:=Input.return_normal iterationPost inner (localVar "result") value returnRun
  have resultRead : eval iterationPost (localVar "result")=some (.val (.word heap)):=by simp [eval,localVar,evalHOLExact,toExact,resultCell]
  have answer : value=.val (.word heap):=Option.some.inj (read.symm.trans resultRead)
  rw [innerEq] at clock frame
  have finalClock : target.clock=(finished source heap key length pointer size).clock:=clock.trans stepClock
  have exactClock : target.clock=source.clock-3:=finalClock.trans (finished_clock source heap key length pointer size)
  have fields : Input.LocalEffects.erase target=Input.LocalEffects.erase (finished source heap key length pointer size):=frame.trans stepFrame
  exact ⟨arena,answer,exactClock,by omega,fields⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.empty_normal
