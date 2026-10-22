import InitECandidate.Solver.WitnessRadix.KeccakAnyCost

namespace InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch Input

/-- Current length pricing for arbitrary real caller expressions. Failed
pointer reads and wrong argument types stop before entering the hash body. -/
theorem dynamic_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer size out : ExpHOL 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (small : length+136<2^64)
    (sizeRead : eval source size=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") [pointer,size,out])).2.clock≤bodyPrice length+1 := by
  have code:=Keccak256.original_code source.code installed
  cases pointerRead : eval source pointer with
  | none=>
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [pointer,size,out]=none:=by
      simp only [eval] at pointerRead
      simp [evalListHOLFinite,evalListHOLExact,pointerRead]
    rw [evaluateHOLFiniteState_call,args]; simp
  | some pointerValue=>
    cases outRead : eval source out with
    | none=>
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [pointer,size,out]=none:=by
        simp only [eval] at pointerRead sizeRead outRead
        simp [evalListHOLFinite,evalListHOLExact,pointerRead,sizeRead,outRead]
      rw [evaluateHOLFiniteState_call,args]; simp
    | some outValue=>
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [pointer,size,out]=
          some [pointerValue,.val (.word (BitVec.ofNat 64 length)),outValue]:=by
        simp only [eval] at pointerRead sizeRead outRead
        simp [evalListHOLFinite,evalListHOLExact,pointerRead,sizeRead,outRead]
      cases called : lookupCodeHOLFinite source.code.lookup (ofString "keccak256") [pointerValue,.val (.word (BitVec.ofNat 64 length)),outValue] with
      | none=>rw [evaluateHOLFiniteState_call,args]; simp only; rw [called]; simp
      | some data=>
        obtain ⟨actual,callee,shape⟩:=data
        obtain ⟨pointerWord,sizeWord,outWord,pointerEq,sizeEq,outEq⟩:=CallNormal.three_scalar_words source.code.lookup (ofString "keccak256")
          (ofString "p") (ofString "n") (ofString "out") body actual .one shape code pointerValue (.val (.word (BitVec.ofNat 64 length))) outValue callee called
        rw [pointerEq,outEq] at args
        exact call_cost source [pointer,size,out] pointerWord outWord length small installed args

end InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.AnyCost.dynamic_call_cost
