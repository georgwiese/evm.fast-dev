import InitECandidate.Solver.Input.FixedList.Environment

namespace InitECandidate.Solver.Input.FixedList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem caller_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length size limit : BitVec 64)
    (nonzero : size≠0#64)
    (divisionCode : source.code.lookup (ofString "udivmod")=some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (code : source.code.lookup (ofString "ssz_fixed_list_count")=some (formals,body,.one))
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (values length size limit))
    (enough : 67≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "ssz_fixed_list_count") expressions continuation)=(some (.returned value),post)) :
    ∃ next innerPost count paid,paid≤66 ∧
      next.locals=source.locals.update (ofString name,.val (.word count)) ∧ count.toNat≤limit.toNat ∧
      next.clock=source.clock-paid ∧ UDivMod.frozen next=UDivMod.frozen source ∧
      evaluateHOLFiniteState next continuation=(some (.returned value),innerPost) ∧ post=restore source name innerPost ∧ (size.toNat≤2^63→count.toNat=length.toNat/size.toNat ∧ length.toNat%size.toNat=0) := by
  classical
  obtain ⟨callee,called,n,s,l⟩:=environment source.code.lookup length size limit code
  obtain ⟨bodyPost,returned,bodyRun⟩:=CallNormal.callee_return source post (ofString name) .one (ofString "ssz_fixed_list_count") expressions
    (values length size limit) body continuation callee .one args called (by omega) value run
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨count,paid,bound,valueEq,countBound,clock,frame,arithmetic⟩:=normal_summary entry bodyPost length size limit n s l nonzero
    divisionCode failCode exceptionShape (by change 66≤source.clock-1; omega) returned bodyRun
  have shapePass : (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one)=true := by
    rw [valueEq]
    simp [shapeOfHOLExact,shapeEqHOL]
  have actual:=CallNormal.return_execute source bodyPost name .one (ofString "ssz_fixed_list_count") expressions (values length size limit)
    body continuation callee .one returned args called (by omega) bodyRun shapePass
  have normal:=actual.symm.trans run
  let next:=CallNormal.continuationEntry source bodyPost name returned
  have result : (evaluateHOLFiniteState next continuation).1=some (.returned value):=congrArg Prod.fst normal
  have postEq : post=restore source name (evaluateHOLFiniteState next continuation).2:=(congrArg Prod.snd normal).symm
  refine ⟨next,(evaluateHOLFiniteState next continuation).2,count,paid+1,by omega,?_,countBound,?_,?_,Prod.ext result rfl,postEq,arithmetic⟩
  · change source.locals.update (ofString name,returned)=source.locals.update (ofString name,.val (.word count))
    rw [valueEq]
  · change bodyPost.clock=source.clock-(paid+1)
    change bodyPost.clock=source.clock-1-paid at clock
    omega
  · change UDivMod.frozen bodyPost=UDivMod.frozen source
    exact frame

end InitECandidate.Solver.Input.FixedList

#print axioms InitECandidate.Solver.Input.FixedList.caller_normal
