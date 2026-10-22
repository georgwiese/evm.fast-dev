import InitECandidate.Solver.Mpt.IndexedKeyBuffer
import InitECandidate.Solver.Input.RlpWrite.WordWriteCurrent
import InitECandidate.Solver.Input.OriginalRlpCodes

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original indexed loop's actual scoped encoder return supplies its
bounded key length, exact caller update and protected-memory frame. -/
theorem key_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (index : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (bindings : Input.Main.MptWorkspace.Bindings source)
    (i : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (reached : Input.CallPrefix.Reaches source (.scoped (ofString "klen") .one (ofString "rlp_encode_word") keyArguments) target) :
    ∃ encoded memory clock,1≤encoded ∧ encoded≤9 ∧ source.clock-clock≤19 ∧
      target=bind {source with memory:=memory,clock:=clock} "klen" (BitVec.ofNat 64 encoded) ∧
      (∀ query,(query.toNat<2713717624 ∨ 2713717640≤query.toNat)→memory query=source.memory query) := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualBody callee returnShape returned childTarget args called funded run checked=>
    have sameValues : actualValues=[.val (.word 2713717624#64),.val (.word index)]:=
      Option.some.inj (args.symm.trans (key_arguments source index bindings i))
    subst actualValues
    obtain ⟨expected,expectedCall,d,w⟩:=Input.RlpWrite.WordWrite.environment source.code.lookup 2713717624#64 index
      (Input.OriginalRlp.rlp_encode_word source.code installed)
    have same:=Option.some.inj (called.symm.trans expectedCall)
    have bodyEq:=congrArg Prod.fst same
    have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
    have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
    change actualBody=Input.RlpWrite.WordWrite.body at bodyEq
    change callee=expected at mapEq
    change returnShape=.one at shapeEq
    subst actualBody
    subst callee
    subst returnShape
    obtain ⟨encoded,lower,upper,valueEq,cost,frame,memory⟩:=Input.RlpWrite.WordWrite.body_normal
      (callEntryStateHOLFinite source expected) childTarget 2713717624#64 index d w
      (Input.OriginalRlp.rlp_be_len source.code installed) (Input.OriginalRlp.rlp_put_be source.code installed)
      (key_buffer_mapped source domain) returned run
    have restored:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
    have callerEq : {childTarget with locals:=source.locals}={source with memory:=childTarget.memory,clock:=childTarget.clock}:=restored
    refine ⟨encoded,childTarget.memory,childTarget.clock,lower,upper,?_,?_,?_⟩
    · change source.clock-1-childTarget.clock≤18 at cost
      omega
    · rw [valueEq,callerEq]
      rfl
    · intro query away
      apply memory query
      intro offset inside sameAddress
      have bounds:=key_backing_bounds offset inside
      rw [←sameAddress] at bounds
      omega

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.key_normal
