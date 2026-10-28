import InitECandidate.Solver.Mpt.WitnessDecodeRootTrace

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real comparison prefix needs no premise about the empty-root global:
a missing or wrongly shaped value stops before the child call. A valid word
uses the same installed comparison and actual continuation as lookup_trace. -/
theorem lookup_trace_any (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db root : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤5 ∨ ∃ current inner,
      Input.LocalEffects.erase current=Input.LocalEffects.erase source ∧ current.clock≤source.clock ∧ source.clock-current.clock≤5 ∧
      current.locals.lookup (ofString "db")=some (.val (.word db)) ∧ current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      evaluateHOLFiniteState current lookupCall=(outcome,inner) ∧ post=restore source "is_empty" inner := by
  classical
  cases emptyRead : source.globals.lookup (ofString "empty_trie_root") with
  | none=>
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) compareArguments=none := by
      simp [compareArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rootCell,emptyRead]
    rw [shapes.1,evaluateHOLFiniteState_decCall_fixClockRewrite,args] at run
    have same : source.clock=post.clock := congrArg (fun output=>output.2.clock) run
    exact Or.inl (by omega)
  | some value=>
    cases value with
    | val word=>
      cases word with
      | word emptyRoot=>exact lookup_trace source post db root emptyRoot installed dbCell rootCell emptyRead outcome run
    | rStruct fields=>
      let values : List (ValueHOL 64):=[.val (.word root),.rStruct fields,.val (.word 32#64)]
      have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) compareArguments=some values := by
        simp [compareArguments,values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rootCell,emptyRead]
      have failed : lookupCodeHOLFinite source.code.lookup (ofString "memeq") values=none := by
        apply (lookupCodeHOLFinite_eq_none_iff source.code.lookup (ofString "memeq") values).mpr
        unfold lookupCodeHOLExact
        rw [MutableTable.MemeqAny.original_code source.code installed]
        simp [values,Memeq32.formals,shapeOfHOLExact,shapeEqHOL]
      rw [shapes.1,evaluateHOLFiniteState_decCall_fixClockRewrite,args] at run
      simp only [failed] at run
      have same : source.clock=post.clock := congrArg (fun output=>output.2.clock) run
      exact Or.inl (by omega)
    | nStruct label fields=>
      let values : List (ValueHOL 64):=[.val (.word root),.nStruct label fields,.val (.word 32#64)]
      have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) compareArguments=some values := by
        simp [compareArguments,values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,rootCell,emptyRead]
      have failed : lookupCodeHOLFinite source.code.lookup (ofString "memeq") values=none := by
        apply (lookupCodeHOLFinite_eq_none_iff source.code.lookup (ofString "memeq") values).mpr
        unfold lookupCodeHOLExact
        rw [MutableTable.MemeqAny.original_code source.code installed]
        simp [values,Memeq32.formals,shapeOfHOLExact,shapeEqHOL]
      rw [shapes.1,evaluateHOLFiniteState_decCall_fixClockRewrite,args] at run
      simp only [failed] at run
      have same : source.clock=post.clock := congrArg (fun output=>output.2.clock) run
      exact Or.inl (by omega)

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.lookup_trace_any
