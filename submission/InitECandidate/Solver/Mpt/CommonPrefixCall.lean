import InitECandidate.Solver.Mpt.CommonPrefixNormal
import InitECandidate.Solver.Input.WordQuadEnvironment
import InitECandidate.Solver.Input.CallPrefixScopedActual

namespace InitECandidate.Solver.Mpt.CommonPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (a left b right : BitVec 64) : List (ValueHOL 64):=
  [.val (.word a),.val (.word left),.val (.word b),.val (.word right)]

theorem environment (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (a left b right : BitVec 64)
    (known : table (ofString "common_prefix_length")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite table (ofString "common_prefix_length") (values a left b right)=some (body,callee,.one) ∧
      callee.lookup (ofString "a")=some (.val (.word a)) ∧ callee.lookup (ofString "al")=some (.val (.word left)) ∧
      callee.lookup (ofString "b")=some (.val (.word b)) ∧ callee.lookup (ofString "bl")=some (.val (.word right)) :=
  Input.word_quad_environment table (ofString "common_prefix_length") (ofString "a") (ofString "al") (ofString "b") (ofString "bl") body .one
    a left b right (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) known

/-- The actual scoped comparison supplies its bounded scalar prefix and
exact pure caller state, without predicting byte equality or future success. -/
theorem scoped_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (arguments : List (ExpHOL 64)) (a left b right : BitVec 64)
    (small : min left.toNat right.toNat≤64) (installed : Input.OriginalCode.Installed source.code)
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values a left b right))
    (reached : Input.CallPrefix.Reaches source (.scoped name .one (ofString "common_prefix_length") arguments) target) :
    ∃ word : BitVec 64,word.toNat≤min left.toNat right.toNat ∧ source.clock-target.clock≤min left.toNat right.toNat+2 ∧
      target=setVarHOLFinite name (.val (.word word)) {source with clock:=target.clock} := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualBody callee actualShape returned childTarget args called funded run checked=>
    have sameValues : actualValues=values a left b right:=Option.some.inj (args.symm.trans argsRead)
    subst actualValues
    obtain ⟨expected,expectedCall,aLocal,leftLocal,bLocal,rightLocal⟩:=environment source.code.lookup a left b right (original_code source.code installed)
    have same:=Option.some.inj (called.symm.trans expectedCall)
    have bodyEq:=congrArg Prod.fst same
    have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
    have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
    change actualBody=body at bodyEq
    change callee=expected at mapEq
    change actualShape=.one at shapeEq
    subst actualBody
    subst callee
    subst actualShape
    obtain ⟨word,answer,bound,cost,frame⟩:=body_normal (callEntryStateHOLFinite source expected) childTarget left right small installed leftLocal rightLocal returned run
    have restored:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=childTarget.clock}) frame
    have callerEq : {childTarget with locals:=source.locals}={source with clock:=childTarget.clock}:=restored
    refine ⟨word,bound,?_,?_⟩
    · change source.clock-1-childTarget.clock≤min left.toNat right.toNat+1 at cost
      change source.clock-childTarget.clock≤min left.toNat right.toNat+2
      omega
    · rw [answer,callerEq]
      rfl

end InitECandidate.Solver.Mpt.CommonPrefix

#print axioms InitECandidate.Solver.Mpt.CommonPrefix.environment
#print axioms InitECandidate.Solver.Mpt.CommonPrefix.scoped_normal
