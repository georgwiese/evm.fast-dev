import InitECandidate.Solver.Input.CurrentTable.FirstDiff.Cost
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.LocalEffectsScoped

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual scoped first-difference caller adds one call tick. No mapped
keys, actual future return or first-difference model is a pricing premise. -/
theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64)
    (length : Nat) (small : length < 2^64) (installed : OriginalCode.Installed source.code)
    (name : MlS) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun query => Classical.propDecidable (source.memaddrs query)) expressions =
      some [.val (.word a),.val (.word b),.val (.word (BitVec.ofNat 64 length))])
    (tail : ClockCost.Bound source.code continuation tailPrice) :
    source.clock - (evaluateHOLFiniteState source (.decCall name .one (ofString "htab_first_diff") expressions continuation)).2.clock ≤
      9*length + tailPrice + 1 := by
  obtain ⟨callee,called,aCell,bCell,lengthCell⟩ := word_triple_environment source.code.lookup
    (ofString "htab_first_diff") (ofString "a") (ofString "b") (ofString "key_len") body .one
    a b (BitVec.ofNat 64 length) (by decide) (by decide) (by decide) (original_code source.code installed)
  have price := body_cost (callEntryStateHOLFinite source callee) length small lengthCell
  exact ClockCost.scoped_current source name .one (ofString "htab_first_diff") expressions _
    body continuation callee .one (9*length) tailPrice args called price tail

theorem scoped_readonly (code) (installed : OriginalCode.Installed code)
    (name : MlS) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (tail : LocalEffects.Preserves code continuation) :
    LocalEffects.Preserves code (.decCall name .one (ofString "htab_first_diff") expressions continuation) :=
  LocalEffects.scoped_body code name .one (ofString "htab_first_diff") expressions continuation formals body .one
    (original_code code installed) (readonly code) tail

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scoped_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.scoped_readonly
