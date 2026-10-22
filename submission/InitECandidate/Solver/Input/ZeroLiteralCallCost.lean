import InitECandidate.Solver.Input.ZeroAnyCost

namespace InitECandidate.Solver.Input.ZeroAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A literal-size original zero call has a uniform cost even if its
destination expression fails or produces a nonscalar value. -/
theorem literal_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (destination : ExpHOL 64)
    (length : Nat) (small : length+32<2^64)
    (code : source.code.lookup (ofString "memzero")=some (Zero.formals,Zero.body,.one)) :
    source.clock-(evaluateHOLFiniteState source
      (.call (some (none,none)) (ofString "memzero") [destination,.const (BitVec.ofNat 64 length)])).2.clock≤price length+1 := by
  classical
  cases observed : eval source destination with
  | none=>
    simp only [eval] at observed
    rw [evaluateHOLFiniteState_call]
    simp [evalListHOLFinite,evalListHOLExact,observed]
  | some value=>
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query))
        [destination,.const (BitVec.ofNat 64 length)]=some [value,.val (.word (BitVec.ofNat 64 length))]:=by
      simp only [eval] at observed
      simp [evalListHOLFinite,evalListHOLExact,observed,evalHOLExact]
    cases value with
    | val payload=>
      cases payload with
      | word pointer=>exact call_cost source _ pointer length small args code
    | rStruct fields=>
      have failed : lookupCodeHOLFinite source.code.lookup (ofString "memzero")
          [.rStruct fields,.val (.word (BitVec.ofNat 64 length))]=none:=by
        apply (lookupCodeHOLFinite_eq_none_iff _ _ _).mpr
        simp [lookupCodeHOLExact,code,Zero.formals,shapeOfHOLExact,shapeEqHOL]
      rw [evaluateHOLFiniteState_call,args]
      simp [failed]
    | nStruct name fields=>
      have failed : lookupCodeHOLFinite source.code.lookup (ofString "memzero")
          [.nStruct name fields,.val (.word (BitVec.ofNat 64 length))]=none:=by
        apply (lookupCodeHOLFinite_eq_none_iff _ _ _).mpr
        simp [lookupCodeHOLExact,code,Zero.formals,shapeOfHOLExact,shapeEqHOL]
      rw [evaluateHOLFiniteState_call,args]
      simp [failed]

end InitECandidate.Solver.Input.ZeroAny

#print axioms InitECandidate.Solver.Input.ZeroAny.literal_call_cost
