import InitECandidate.Solver.Input.CurrentHash.ProgressiveCallCost
import InitECandidate.Solver.Input.CurrentHash.FixedHashCost
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

namespace InitECandidate.Solver.Input.CurrentHash.PListCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def arguments : List (ExpHOL 64) := [localVar "roots", localVar "n", localVar "out"]
def tail : ProgHOL 64 := .seq
  (.call (some (none, none)) (Code.name .mix_in_length) [localVar "out", localVar "len", localVar "out"]) (.return (.const 0#64))

theorem source_shape : Code.body .htr_plist_chunks = .seq (.call (some (none, none)) (ofString "merkleize_progressive") arguments) tail := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_plist_chunks, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, arguments, tail, Code.name, localVar]

theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots out : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source (Code.body .htr_plist_chunks) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ 88*n + 3168 := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (Progressive.values roots (BitVec.ofNat 64 n) out) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, arguments, localVar, pointer, count, output, Progressive.values, CallNormal.tripleValues]
  have tailCost : ClockCost.Bound source.code tail 47 :=
    ClockCost.sequence source.code _ _ 47 0 (FixedHashCost.mix_call source.code installed (some none) _) (ClockCost.returned source.code _)
  rw [source_shape] at actual
  have paid := ClockCost.sequence_terminating source post _ tail (88*n+3121) 47
    (fun result target evaluated notTimeout => ProgressiveCallCost.cost source target roots out n bounded installed (some none) arguments args result evaluated notTimeout)
    (by intro middle continued result target evaluated notTimeout
        have same := tailCost middle ((evaluation_fields source middle _ none continued).2.2.2)
        rw [evaluated] at same
        exact same) result actual notTimeout
  omega

def formals : List (MlS × ShapeHOL) := [(ofString "roots", .one), (ofString "n", .one), (ofString "len", .one), (ofString "out", .one)]
def values (roots len out : BitVec 64) (n : Nat) : List (ValueHOL 64) :=
  [.val (.word roots), .val (.word (BitVec.ofNat 64 n)), .val (.word len), .val (.word out)]
def rawLocals (roots len out : BitVec 64) (n : Nat) (name : MlS) : Option (ValueHOL 64) :=
  if name = ofString "out" then some (.val (.word out)) else if name = ofString "len" then some (.val (.word len))
  else if name = ofString "n" then some (.val (.word (BitVec.ofNat 64 n))) else if name = ofString "roots" then some (.val (.word roots)) else none

theorem environment (code) (installed : OriginalCode.Installed code) (roots len out : BitVec 64) (n : Nat) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), lookupCodeHOLFinite code.lookup (Code.name .htr_plist_chunks) (values roots len out n) =
      some (Code.body .htr_plist_chunks, callee, .one) ∧
      callee.lookup (ofString "roots") = some (.val (.word roots)) ∧ callee.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))) ∧
      callee.lookup (ofString "out") = some (.val (.word out)) := by
  have entry : code.lookup (Code.name .htr_plist_chunks) = some (formals, Code.body .htr_plist_chunks, .one) := by
    simpa only [Code.formals, Code.shape, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_htr_plist_chunks, formals, shapeToHOL, paramToHOL, List.map_cons, List.map_nil]
      using Code.installed code installed .htr_plist_chunks
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = (values roots len out n).length ∧
      (formals.zip (values roots len out n)).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true := by
    refine ⟨by decide, rfl, ?_⟩
    simp [formals, values, shapeEqHOL, shapeOfHOLExact]
  have raw : lookupCodeHOLExact code.lookup (Code.name .htr_plist_chunks) (values roots len out n) = some (Code.body .htr_plist_chunks, rawLocals roots len out n, .one) := by
    simp only [lookupCodeHOLExact, entry]
    rw [if_pos valid]
    rfl
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup code.lookup _ _ _ _ .one raw
  refine ⟨callee, called, ?_, ?_, ?_⟩
  · rw [locals]; simp [rawLocals, show ofString "roots" ≠ ofString "out" from by decide,
      show ofString "roots" ≠ ofString "len" from by decide, show ofString "roots" ≠ ofString "n" from by decide]
  · rw [locals]; simp [rawLocals, show ofString "n" ≠ ofString "out" from by decide, show ofString "n" ≠ ofString "len" from by decide]
  · rw [locals]; simp [rawLocals]

/-- Actual progressive-list caller, including the same observed traps/errors
and unrestricted length-mixing word. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots len out : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some (values roots len out n))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (Code.name .htr_plist_chunks) expressions) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ 88*n + 3169 := by
  obtain ⟨callee, called, pointer, count, output⟩ := environment source.code installed roots len out n
  exact ClockCost.call_current_terminating source post destination (Code.name .htr_plist_chunks) expressions (values roots len out n)
    (Code.body .htr_plist_chunks) callee .one (88*n+3168) args called
    (fun result target evaluated notTimeout => body_cost (callEntryStateHOLFinite source callee) target roots out n bounded installed pointer count output result evaluated notTimeout)
    result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.PListCost

#print axioms InitECandidate.Solver.Input.CurrentHash.PListCost.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.PListCost.body_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PListCost.environment
#print axioms InitECandidate.Solver.Input.CurrentHash.PListCost.call_cost
