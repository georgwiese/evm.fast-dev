import InitECandidate.Solver.CurrentKeccak.Cost
import InitECandidate.Solver.Input.ScalarArgumentsLookup

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input

/-- Current length pricing for arbitrary real caller expressions. Failed
pointer reads and wrong argument types stop before entering the hash body. -/
theorem dynamic_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer size out : ExpHOL 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (small : length+136<2^64)
    (sizeRead : eval source size=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") [pointer,size,out])).2.clock≤bodyPrice length+1 := by
  have code:=original_code source.code installed
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

/-- A length-sensitive caller allowance with a spatial ceiling, without
an initial length-smallness or successful pointer-read assumption. -/
theorem dynamic_call_bounded_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer size out : ExpHOL 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (sizeRead : eval source size=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") [pointer,size,out])).2.clock≤boundedBodyPrice length+1 := by
  have code:=original_code source.code installed
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
        exact call_bounded_cost source [pointer,size,out] pointerWord outWord length installed domain args

/-- Arbitrary actual pointer/output expressions retain the spatial bound;
failed reads and argument checks are covered by the sharper capped allowance. -/
theorem dynamic_call_domain_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer size out : ExpHOL 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (sizeRead : eval source size=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") [pointer,size,out])).2.clock≤domainBodyPrice+1 :=
  (dynamic_call_bounded_cost source pointer size out length installed domain sizeRead).trans
    (Nat.add_le_add_right (boundedBodyPrice_le_domain length) 1)

theorem dynamic_call_any_length_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer size out : ExpHOL 64) (length : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (sizeRead : eval source size=some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") [pointer,size,out])).2.clock≤bodyPrice length+1 :=
  (dynamic_call_bounded_cost source pointer size out length installed domain sizeRead).trans
    (Nat.add_le_add_right (boundedBodyPrice_le length) 1)

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.dynamic_call_cost

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.dynamic_call_domain_cost

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.dynamic_call_bounded_cost

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.dynamic_call_any_length_cost
