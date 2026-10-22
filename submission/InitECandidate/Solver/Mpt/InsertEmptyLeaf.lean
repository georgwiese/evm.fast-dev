import InitECandidate.Solver.Mpt.InsertEmptyEntry
import InitECandidate.Solver.Mpt.LeafConstructorCall

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem first_dispatch_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : BitVec 64)
    (member : name∈["key","klen","level","vptr","vlen"])
    (cell : source.locals.lookup (ofString name)=some (.val (.word word))) :
    (firstDispatch source).locals.lookup (ofString name)=some (.val (.word word)) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl
  all_goals simpa [firstDispatch,dispatchEntry,prepared,setup,decClockHOLFinite,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString] using cell

def leafResult (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64):=
  setVarHOLFinite (ofString "r") (.val (.word heap))
    {PersistentAlloc.post {firstDispatch source with clock:=(firstDispatch source).clock-2} heap 64#64 with
      memory:=WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .leaf (NodeConstructor.leafWords key length pointer size)))}

/-- The true empty-root insertion derives its fresh initialized leaf from
the original assigned constructor, with the actual remaining executions.
Neither successful allocation nor a predicted leaf return is supplied. -/
theorem empty_leaf_created (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64)
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
    AllocatedBytes.Arena heap 64 ∧ ∃ inner last iterationPost iterationInner,
      target.clock=inner.clock ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase inner ∧ 1≤source.clock ∧
      evaluateHOLFiniteState (decClockHOLFinite (setup source)) loopBody=(none,iterationPost) ∧
      evaluateHOLFiniteState (firstDispatch source) leafCall=(none,leafResult source heap key length pointer size) ∧
      evaluateHOLFiniteState (leafResult source heap key length pointer size) afterChoice=(none,iterationInner) ∧
      iterationPost.clock=iterationInner.clock ∧ Input.LocalEffects.erase iterationPost=Input.LocalEffects.erase iterationInner ∧
      evaluateHOLFiniteState iterationPost (.while test loopBody)=(none,last) ∧
      evaluateHOLFiniteState last (.return (localVar "result"))=(some (.returned value),inner) := by
  obtain ⟨inner,last,iterationPost,leafPost,iterationInner,clock,frame,funded,bodyRun,leafRun,afterRun,stepClock,stepFrame,tailRun,returnRun⟩:=
    empty_leaf_entry source target nodeCell value normal
  have k:=first_dispatch_cell source "key" key (by simp) keyCell
  have n:=first_dispatch_cell source "klen" length (by simp) lengthCell
  have level:=first_dispatch_cell source "level" 0#64 (by simp) levelCell
  have p:=first_dispatch_cell source "vptr" pointer (by simp) pointerCell
  have sizeLocal:=first_dispatch_cell source "vlen" size (by simp) sizeCell
  have args : evalListHOLFinite (firstDispatch source) (h:=fun query=>Classical.propDecidable ((firstDispatch source).memaddrs query)) leafArguments=
      some [.val (.word key),.val (.word length),.val (.word pointer),.val (.word size)]:=by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,k,n,level,p,sizeLocal,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨arena,leafEq⟩:=NodeConstructor.leaf_assigned (firstDispatch source) leafPost heap key length pointer size (ofString "r") leafArguments
    args domain heapCell frontier aligned installed leafRun
  change leafPost=leafResult source heap key length pointer size at leafEq
  rw [leafEq] at leafRun afterRun
  exact ⟨arena,inner,last,iterationPost,iterationInner,clock,frame,funded,bodyRun,leafRun,afterRun,stepClock,stepFrame,tailRun,returnRun⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.first_dispatch_cell
#print axioms InitECandidate.Solver.Mpt.Insert.empty_leaf_created
