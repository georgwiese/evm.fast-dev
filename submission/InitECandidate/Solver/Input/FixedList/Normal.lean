import InitECandidate.Solver.Input.FixedList.Tail

namespace InitECandidate.Solver.Input.FixedList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Real normal fixed-list decoding returns a word within its limit, pays at
most65 body clocks, and preserves all memory and control fields. -/
theorem normal_summary (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length size limit : BitVec 64)
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (s : source.locals.lookup (ofString "sz")=some (.val (.word size)))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit))) (nonzero : size≠0#64)
    (divisionCode : source.code.lookup (ofString "udivmod")=some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 66≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ count paid,paid≤65 ∧ value=.val (.word count) ∧ count.toNat≤limit.toNat ∧
      post.clock=source.clock-paid ∧ UDivMod.frozen post=UDivMod.frozen source ∧
      (size.toNat≤2^63→count.toNat=length.toNat/size.toNat ∧ length.toNat%size.toNat=0) := by
  classical
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (UDivMod.values length size) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,arguments,UDivMod.values,localVar,n,s]
  obtain ⟨next,q,r,paid,bound,localsEq,clock,frame,arithmetic,callRun⟩:=UDivMod.call_execute source length size nonzero (by omega) "qr" arguments tail args divisionCode
  rw [body_shape,callRun] at run
  have result : (evaluateHOLFiniteState next tail).1=some (.returned value) := congrArg Prod.fst run
  have postEq : post=restore source "qr" (evaluateHOLFiniteState next tail).2 := (congrArg Prod.snd run).symm
  have qr : next.locals.lookup (ofString "qr")=some (UDivMod.pairValue q r) := by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE]
  have lim : next.locals.lookup (ofString "lim")=some (.val (.word limit)) := by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,show (ofString "qr"==ofString "lim")=false from by decide] using l
  have codeEq:=congrArg PanSemStateFiniteExact.code frame
  change next.code=source.code at codeEq
  have shapeEq:=congrArg PanSemStateFiniteExact.eshapes frame
  change next.eshapes=source.eshapes at shapeEq
  obtain ⟨remainderZero,countBound,valueEq,tailPost⟩:=tail_normal next (evaluateHOLFiniteState next tail).2 q r limit qr lim
    (by rw [codeEq]; exact failCode) (by rw [shapeEq]; exact exceptionShape) (by omega) value (Prod.ext result rfl)
  refine ⟨q,paid+1,by omega,valueEq,countBound,?_,?_,?_⟩
  · rw [postEq,tailPost]
    change next.clock=source.clock-(paid+1)
    omega
  · rw [postEq,tailPost]
    exact frame
  · intro sizeSmall
    refine ⟨(arithmetic sizeSmall).1,?_⟩
    have remainder:=(arithmetic sizeSmall).2
    rw [remainderZero] at remainder
    exact remainder.symm

end InitECandidate.Solver.Input.FixedList

#print axioms InitECandidate.Solver.Input.FixedList.normal_summary
