import InitECandidate.Solver.Mpt.NodeRefLenBound
import InitECandidate.Solver.Mpt.NodeRefLenNormal
import InitECandidate.Solver.Input.CallPrefixScopedActual
import InitECandidate.Solver.Input.ClockCostScoped

namespace InitECandidate.Solver.Mpt.NodeRefLen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual serializer's scoped reference-length call supplies its
at-most33-byte result and retained caller state from the real callee run. -/
theorem scoped_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64))
    (installed : Input.OriginalCode.Installed source.code)
    (reached : Input.CallPrefix.Reaches source (.scoped name .one (ofString "node_ref_len") arguments) target) :
    ∃ result : BitVec 64,result.toNat≤33 ∧ target.locals.lookup name=some (.val (.word result)) ∧
      (∀ other,name≠other→target.locals.lookup other=source.locals.lookup other) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source ∧ source.clock-target.clock≤2 := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualBody callee actualShape returned childTarget args called funded run checked=>
    have bodyEq:=Input.LocalEffects.lookup_body source.code (ofString "node_ref_len") formals body .one (original_code source.code installed) actualValues actualBody callee actualShape called
    subst actualBody
    let entry:=callEntryStateHOLFinite source callee
    obtain ⟨result,answer,bound⟩:=normal_bound entry childTarget returned run
    have frame:=readonly source.code installed entry rfl
    rw [run] at frame
    have price:=body_cost source.code installed entry rfl
    rw [run] at price
    refine ⟨result,bound,?_,?_,frame,?_⟩
    · simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]
    · intro other different
      simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]
    · change source.clock-1-childTarget.clock≤1 at price
      change source.clock-childTarget.clock≤2
      omega

/-- The checked caller receives exactly the size computed from its real
child tag and cached RLP length, retaining the read-only caller frame. -/
theorem scoped_normal_exact {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64)) (child tag cached length : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word child)])
    (header : child≠0#64→source.memaddrs child ∧ source.memory child=.word tag)
    (cache : child≠0#64→tag≠0#64→source.memaddrs (child+8#64) ∧ source.memory (child+8#64)=.word cached)
    (size : child≠0#64→tag≠0#64→cached≠0#64→source.memaddrs (child+16#64) ∧ source.memory (child+16#64)=.word length)
    (reached : Input.CallPrefix.Reaches source (.scoped name .one (ofString "node_ref_len") arguments) target) :
    target.locals.lookup name=some (.val (.word (referenceWord child tag length))) ∧
      (child≠0#64→tag≠0#64→cached≠0#64) ∧
      (∀ other,name≠other→target.locals.lookup other=source.locals.lookup other) ∧
      Input.LocalEffects.erase target=Input.LocalEffects.erase source ∧ source.clock-target.clock≤2 := by
  obtain ⟨callee,called,childCell⟩:=environment source.code.lookup child (original_code source.code installed)
  obtain ⟨post,returned,run,endpoint⟩:=reached.scoped_known name .one (ofString "node_ref_len") arguments
    [.val (.word child)] body callee .one args called
  obtain ⟨answer,populated,_frame⟩:=body_normal_exact (callEntryStateHOLFinite source callee) post child tag cached length
    installed childCell header cache size returned run
  obtain ⟨_result,_bound,_lookup,locals,frame,price⟩:=scoped_normal name arguments installed reached
  refine ⟨?_,populated,locals,frame,price⟩
  rw [endpoint]
  simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]

theorem call_cost (code) (installed : Input.OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.call (Input.LocalEffects.callInfo destination) (ofString "node_ref_len") arguments) 2 :=
  Input.ClockCost.call_body code destination (ofString "node_ref_len") arguments formals body .one 1 (original_code code installed) (body_cost code installed)

theorem scoped_cost (code) (installed : Input.OriginalCode.Installed code)
    (name : MlS) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.decCall name .one (ofString "node_ref_len") arguments .skip) 2 :=
  Input.ClockCost.scoped_body code name .one (ofString "node_ref_len") arguments .skip formals body .one 1 0 (original_code code installed)
    (body_cost code installed) (Input.ClockCost.skip code)

end InitECandidate.Solver.Mpt.NodeRefLen

#print axioms InitECandidate.Solver.Mpt.NodeRefLen.scoped_normal
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.scoped_normal_exact
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.call_cost
#print axioms InitECandidate.Solver.Mpt.NodeRefLen.scoped_cost
