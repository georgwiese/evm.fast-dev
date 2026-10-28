import InitECandidate.Solver.Input.CurrentHash.RequestListCost
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Input.CurrentHash.RequestList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def values (kind : Kind) (p out : BitVec 64) (n : Nat) : List (ValueHOL 64) :=
  [.val (.word (BitVec.ofNat 64 kind.tag)), .val (.word p), .val (.word (BitVec.ofNat 64 n)),
    .val (.word (BitVec.ofNat 64 kind.record.length)), .val (.word out)]

def rawLocals (kind : Kind) (p out : BitVec 64) (n : Nat) (key : MlS) : Option (ValueHOL 64) :=
  if key = ofString "out" then some (.val (.word out))
  else if key = ofString "sz" then some (.val (.word (BitVec.ofNat 64 kind.record.length)))
  else if key = ofString "n" then some (.val (.word (BitVec.ofNat 64 n)))
  else if key = ofString "p" then some (.val (.word p))
  else if key = ofString "kind" then some (.val (.word (BitVec.ofNat 64 kind.tag))) else none

theorem environment (code) (installed : OriginalCode.Installed code) (kind : Kind) (p out : BitVec 64) (n : Nat) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), lookupCodeHOLFinite code.lookup (ofString "htr_request_list") (values kind p out n) = some (body,callee,.one) ∧
      callee.lookup (ofString "kind") = some (.val (.word (BitVec.ofNat 64 kind.tag))) ∧
      callee.lookup (ofString "p") = some (.val (.word p)) ∧
      callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))) ∧
      callee.lookup (ofString "sz") = some (.val (.word (BitVec.ofNat 64 kind.record.length))) ∧
      callee.lookup (ofString "out") = some (.val (.word out)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values kind p out n).length ∧
      (formals.zip (values kind p out n)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact code.lookup (ofString "htr_request_list") (values kind p out n) = some (body,rawLocals kind p out n,.one) := by
    simp only [lookupCodeHOLExact,original_code code installed]
    rw [if_pos valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup code.lookup _ _ _ _ .one raw
  refine ⟨callee,called,?_,?_,?_,?_,?_⟩
  all_goals rw [locals]
  all_goals rfl

/-- The real five-word request-list ABI supplies its selected kind, fixed
record size and actual bounded count to the same observed callee execution. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p out : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (installed : OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind p out n))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_request_list") arguments) = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ price kind n+1 := by
  obtain ⟨callee,called,category,pointer,count,size,output⟩ := environment source.code installed kind p out n
  exact ClockCost.call_current_terminating source post destination (ofString "htr_request_list") arguments (values kind p out n) body callee .one
    (price kind n) args called (fun result target evaluated notTimeout =>
      body_cost (callEntryStateHOLFinite source callee) target kind p out n bounded
        ⟨installed,category,pointer,count,size,output⟩ result evaluated notTimeout) result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.RequestList

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.environment
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.call_cost
