import InitECandidate.Solver.Mpt.LeafInsertCompareFrame
import InitECandidate.Solver.Mpt.TrieGraphPathErase
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem length_choice_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (size length : BitVec 64)
    (sizeCell : source.locals.lookup (ofString "el")=some (.val (.word size)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source lengthChoice=(some (.returned value),target)) :
    evaluateHOLFiniteState source compareScope=(some (.returned value),target) := by
  by_cases same : size=length
  · have read : eval source lengthTest=some (.val (.word 1#64)):=by
      simp [eval,lengthTest,evalHOLExact,toExact,localVar,sizeCell,lengthCell,same,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at read
    rw [dispatch_shapes.2.2.2.1,evaluateHOLFiniteState_ite,read] at normal
    exact normal
  · have read : eval source lengthTest=some (.val (.word 0#64)):=by
      simp [eval,lengthTest,evalHOLExact,toExact,localVar,sizeCell,lengthCell,same,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at read
    rw [dispatch_shapes.2.2.2.1,evaluateHOLFiniteState_ite,read] at normal
    have skipped : evaluateHOLFiniteState source .skip=(some (.returned value),target):=normal
    rw [evaluateHOLFiniteState_skip] at skipped
    cases skipped

/-- A genuine return through the original memeq scope has performed the
matching update. Read-only callee execution and actual caller restoration
retain the complete graph/path model at this real return. -/
theorem compare_scope_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node pointer size left oldLength right : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit lower upper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (member : graph.valid node) (active : node≠0#64) (leaf : wordAt source.memory node=1#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word left)))
    (oldLengthCell : source.locals.lookup (ofString "el")=some (.val (.word oldLength)))
    (rightCell : source.locals.lookup (ofString "rk")=some (.val (.word right)))
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source compareScope=(some (.returned value),target)) :
    value=.val (.word node) ∧ Input.LocalEffects.erase target=Input.LocalEffects.erase (post source node pointer size) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) compareArguments=
      some (MutableTable.MemeqByteRuntime.values left right oldLength.toNat):=by
    simp [compareArguments,MutableTable.MemeqByteRuntime.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leftCell,oldLengthCell,rightCell]
  obtain ⟨callee,called,aCell,bCell,nCell⟩:=MutableTable.MemeqByteRuntime.environment source.code.lookup left right oldLength.toNat
    (MutableTable.MemeqAny.original_code source.code installed)
  rw [dispatch_shapes.2.2.2.2.1] at normal
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source target "eq" .one (ofString "memeq") compareArguments _
    Memeq32.body compareGuard callee .one args called value normal
  let ready:=Input.CallNormal.continuationEntry source child "eq" returned
  have childFrame:=(MutableTable.MemeqAny.readonly source.code) (callEntryStateHOLFinite source callee) rfl
  rw [run] at childFrame
  have frame : Input.LocalEffects.erase ready=Input.LocalEffects.erase source:=childFrame
  have memory:=congrArg PanSemStateFiniteExact.memory frame
  have sameDomain:=congrArg PanSemStateFiniteExact.memaddrs frame
  change ready.memory=source.memory at memory
  change ready.memaddrs=source.memaddrs at sameDomain
  obtain ⟨base,same,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated⟩:=
    graph.after_erase source ready limit lower upper pathLower pathUpper property values regions disjoint paths pathRegions separated frame
  have current (name : MlS) (other : name≠ofString "eq") : ready.locals.lookup name=source.locals.lookup name:=by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have readyMember : base.valid node:=by rw [same]; exact member
  have readyLeaf : wordAt ready.memory node=1#64:=by rw [memory]; exact leaf
  obtain ⟨answer,innerEq,next,validEq,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    matching_path_normal ready inner node pointer size base limit lower upper pathLower pathUpper property baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated readyMember active readyLeaf
      ((current _ (by decide)).trans nodeCell) ((current _ (by decide)).trans pointerCell) ((current _ (by decide)).trans sizeCell) (sameDomain.trans domain)
      (by rw [sameDomain]; exact payload) extra value continued
  have postFrame : Input.LocalEffects.erase (post ready node pointer size)=Input.LocalEffects.erase (post source node pointer size):=by
    have lifted:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>Input.LocalEffects.erase (post state node pointer size)) frame
    exact lifted
  have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase (post source node pointer size):=by
    rw [endpoint,innerEq]
    exact postFrame
  refine ⟨answer,finalFrame,?_⟩
  rw [endpoint]
  exact ⟨next,validEq.trans same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.length_choice_return
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.compare_scope_path_normal
