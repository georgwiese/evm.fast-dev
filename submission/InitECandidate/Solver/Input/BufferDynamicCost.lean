import InitECandidate.Solver.Input.ScalarArgumentsLookup
import InitECandidate.Solver.Input.ZeroAnyCost
import InitECandidate.Solver.Input.CopyAnyCost
import InitECandidate.Solver.WitnessRadix.ZeroCost

namespace InitECandidate.Solver.Input.BufferDynamicCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A known current length suffices to price memzero; the destination may
fail to read, have the wrong type or point outside mapped memory. -/
theorem zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst size : ExpHOL 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (small : length+32<2^64)
    (sizeRead : eval source size=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") [dst,size])).2.clock≤ZeroAny.price length+1 := by
  have code:=Zero.original_code source.code installed
  cases dstRead : eval source dst with
  | none=>
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [dst,size]=none:=by
      simp only [eval] at dstRead sizeRead
      simp [evalListHOLFinite,evalListHOLExact,dstRead,sizeRead]
    rw [evaluateHOLFiniteState_call,args]; simp
  | some value=>
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [dst,size]=
        some [value,.val (.word (BitVec.ofNat 64 length))]:=by
      simp only [eval] at dstRead sizeRead
      simp [evalListHOLFinite,evalListHOLExact,dstRead,sizeRead]
    cases called : lookupCodeHOLFinite source.code.lookup (ofString "memzero") [value,.val (.word (BitVec.ofNat 64 length))] with
    | none=>rw [evaluateHOLFiniteState_call,args]; simp only; rw [called]; simp
    | some data=>
      obtain ⟨body,callee,shape⟩:=data
      obtain ⟨dstWord,sizeWord,dstEq,sizeEq⟩:=CallNormal.two_scalar_words source.code.lookup (ofString "memzero") (ofString "dst") (ofString "n")
        Zero.body body .one shape code value (.val (.word (BitVec.ofNat 64 length))) callee called
      rw [dstEq] at args
      exact ZeroAny.call_cost source [dst,size] dstWord length small args code

theorem copy_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src size : ExpHOL 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (small : length+32<2^64)
    (sizeRead : eval source size=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") [dst,src,size])).2.clock≤CopyAny.price length+1 := by
  have code:=CopyGeneral.original_code source.code installed
  cases dstRead : eval source dst with
  | none=>
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [dst,src,size]=none:=by
      simp only [eval] at dstRead
      simp [evalListHOLFinite,evalListHOLExact,dstRead]
    rw [evaluateHOLFiniteState_call,args]; simp
  | some dstValue=>
    cases srcRead : eval source src with
    | none=>
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [dst,src,size]=none:=by
        simp only [eval] at dstRead srcRead
        simp [evalListHOLFinite,evalListHOLExact,dstRead,srcRead]
      rw [evaluateHOLFiniteState_call,args]; simp
    | some srcValue=>
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [dst,src,size]=
          some [dstValue,srcValue,.val (.word (BitVec.ofNat 64 length))]:=by
        simp only [eval] at dstRead srcRead sizeRead
        simp [evalListHOLFinite,evalListHOLExact,dstRead,srcRead,sizeRead]
      cases called : lookupCodeHOLFinite source.code.lookup (ofString "memcpy") [dstValue,srcValue,.val (.word (BitVec.ofNat 64 length))] with
      | none=>rw [evaluateHOLFiniteState_call,args]; simp only; rw [called]; simp
      | some data=>
        obtain ⟨body,callee,shape⟩:=data
        obtain ⟨dstWord,srcWord,sizeWord,dstEq,srcEq,sizeEq⟩:=CallNormal.three_scalar_words source.code.lookup (ofString "memcpy")
          (ofString "dst") (ofString "src") (ofString "n") Copy32.body body .one shape code dstValue srcValue (.val (.word (BitVec.ofNat 64 length))) callee called
        rw [dstEq,srcEq] at args
        exact CopyAny.call_cost source [dst,src,size] dstWord srcWord length small args code

end InitECandidate.Solver.Input.BufferDynamicCost

#print axioms InitECandidate.Solver.Input.BufferDynamicCost.zero_cost
#print axioms InitECandidate.Solver.Input.BufferDynamicCost.copy_cost
