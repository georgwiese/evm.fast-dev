import InitECandidate.Solver.Input.CurrentHash.MerkleDenseCost
import InitECandidate.Solver.Input.CurrentHash.FixedMemoryCost
import InitECandidate.Solver.Input.CurrentHash.AllocatorCost

namespace InitECandidate.Solver.Input.CurrentHash.MerkleSuffixCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Select actual loop-and-suffix nodes; this traverses syntax only. -/
def loopSequences : ProgHOL 64 → List (ProgHOL 64)
  | .seq (.while test body) tail => .seq (.while test body) tail :: (loopSequences body ++ loopSequences tail)
  | .seq first second | .ite _ first second => loopSequences first ++ loopSequences second
  | .dec _ _ _ body | .decCall _ _ _ _ body | .while _ body => loopSequences body
  | _ => []

def denseContinuation : ProgHOL 64 := (loopSequences (Code.body .merkleize))[0]?.getD .skip
def afterDense : ProgHOL 64 := match denseContinuation with | .seq _ tail => tail | _ => .skip
def extensionContinuation : ProgHOL 64 := (loopSequences (Code.body .merkleize))[2]?.getD .skip
def afterExtension : ProgHOL 64 := match extensionContinuation with | .seq _ tail => tail | _ => .skip

set_option maxRecDepth 100000 in
theorem source_shape : denseContinuation = .seq MerkleDenseCost.loop afterDense ∧
    afterDense = .dec (ofString "d") .one (localVar "dn") extensionContinuation ∧
    extensionContinuation = .seq (MerklePairLoops.loop .extension) afterExtension ∧
    afterExtension = .seq
      (.call (some (none, none)) (ofString "memcpy") [localVar "out", localVar "buf", .const 32#64])
      (.seq (.call (some (none, none)) (ofString "heap_release") [localVar "mark"]) (.return (.const 0#64))) := by
  simp only [denseContinuation, afterDense, extensionContinuation, afterExtension, loopSequences,
    MerkleDenseCost.loop, MerklePairLoops.loop, MerklePairLoops.index, BuildProgram.loops,
    Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_merkleize, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.append_nil, List.nil_append, List.cons_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Option.map_none, localVar]
  exact ⟨True.intro, True.intro, True.intro, True.intro⟩

theorem output_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterExtension 43 := by
  rw [source_shape.2.2.2]
  exact ClockCost.sequence code _ _ 42 1 (FixedMemoryCost.copy code installed (some none) _ _ 32 (by decide))
    (ClockCost.sequence code _ _ 1 0 (AllocatorCost.release_call code installed (some none) _) (ClockCost.returned code _))

/-- Current extension/output/release work needs only its two actual depth
locals. Missing pointers, failed stores, failed release and timeout are included. -/
theorem after_dense_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (depth target : Nat)
    (small : target < 2^63) (inside : depth ≤ target) (installed : OriginalCode.Installed source.code)
    (dn : source.locals.lookup (ofString "dn") = some (.val (.word (BitVec.ofNat 64 depth))))
    (maximum : source.locals.lookup (ofString "target") = some (.val (.word (BitVec.ofNat 64 target)))) :
    source.clock - (evaluateHOLFiniteState source afterDense).2.clock ≤ 2 * (target - depth) + 43 := by
  let entry := bind source "d" (BitVec.ofNat 64 depth)
  have d : entry.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 depth))) := bind_lookup_same _ _ _
  have nextTarget : entry.locals.lookup (ofString "target") = some (.val (.word (BitVec.ofNat 64 target))) :=
    (bind_lookup_other source "d" "target" _ (by decide)).trans maximum
  have extensionCost := MerklePairLoops.cost .extension entry depth target small inside installed d nextTarget
  have read : eval source (localVar "dn") = some (.val (.word (BitVec.ofNat 64 depth))) := by
    simpa [eval, localVar, evalHOLExact, toExact] using dn
  rw [source_shape.2.1]
  apply ClockCost.declared_current source "d" (localVar "dn") (BitVec.ofNat 64 depth) extensionContinuation _ read
  rw [source_shape.2.2.1]
  exact ClockCost.sequence_current entry _ _ _ 43 extensionCost (output_cost source.code installed)

/-- The full actual dense/extension/output suffix is linear in capacity plus
actual depth extension. All helper/loop failures remain in scope. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cur capacity depth target : Nat)
    (positive : 1 ≤ cur) (inside : cur ≤ capacity) (capacitySmall : capacity < 2^63)
    (small : target < 2^63) (depths : depth ≤ target) (installed : OriginalCode.Installed source.code)
    (current : source.locals.lookup (ofString "cur") = some (.val (.word (BitVec.ofNat 64 cur))))
    (dn : source.locals.lookup (ofString "dn") = some (.val (.word (BitVec.ofNat 64 depth))))
    (maximum : source.locals.lookup (ofString "target") = some (.val (.word (BitVec.ofNat 64 target)))) :
    source.clock - (evaluateHOLFiniteState source denseContinuation).2.clock ≤ 3 * (cur - 1) + (2 * (target - depth) + 43) := by
  rw [source_shape.1]
  apply ClockCost.sequence_reached_current source MerkleDenseCost.loop afterDense (3 * (cur - 1)) _
    (MerkleDenseCost.cost source cur capacity positive inside capacitySmall installed current)
  intro middle normal
  have currentCode : OriginalCode.Installed middle.code := by
    rw [(evaluation_fields source middle MerkleDenseCost.loop none normal).2.2.2]
    exact installed
  have kept (name : String) (notCur : ofString name ≠ ofString "cur")
      (notHalf : ofString name ≠ ofString "half") (notJ : ofString name ≠ ofString "j") :
      middle.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    have safe : LocalPrefix (ofString name) MerkleDenseCost.loop := by
      rw [MerkleDenseCost.source_shape.1]
      exact .loop _ (MerkleDenseCost.other (ofString name) notCur notHalf notJ)
    have summary := safe.summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  exact after_dense_cost middle depth target small depths currentCode
    ((kept "dn" (by decide) (by decide) (by decide)).trans dn)
    ((kept "target" (by decide) (by decide) (by decide)).trans maximum)

end InitECandidate.Solver.Input.CurrentHash.MerkleSuffixCost

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleSuffixCost.source_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleSuffixCost.output_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleSuffixCost.after_dense_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleSuffixCost.cost
