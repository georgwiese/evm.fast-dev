import InitECandidate.Solver.Input.CurrentHash.PContainerSuffixCost
import InitECandidate.Solver.Input.CurrentHash.ProgressiveCallCost
import InitECandidate.Solver.Input.CurrentHash.StraightCost
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ClockCostScalarTerminating
import InitECandidate.Solver.Input.ClockCostTerminatingSequence

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.CurrentHash.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64) (n : Nat) : Prop where
  chunks : source.locals.lookup (ofString "ch") = some (.val (.word ch))
  count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))

theorem after_tmp_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (data : Params source ch n) (installed : OriginalCode.Installed source.code)
    (temporary : source.locals.lookup (ofString "tmp") = some (.val (.word tmp)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterTmp = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ 89*n+3165 := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) progressiveArguments =
      some (Progressive.values ch (BitVec.ofNat 64 n) tmp) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, progressiveArguments, localVar,
      data.chunks, data.count, temporary, Progressive.values, CallNormal.tripleValues]
  rw [body_shape.2.2.1] at actual
  have paid := ClockCost.sequence_terminating source post _ afterProgressive (88*n+3121) (n+44)
    (fun result target evaluated notTimeout => ProgressiveCallCost.cost source target ch tmp n bounded installed
      (some none) progressiveArguments args result evaluated notTimeout)
    (by intro middle normal result target evaluated notTimeout
        have kept (name : MlS) := CallNormal.ignored_lookup source middle name (ofString "merkleize_progressive") progressiveArguments normal
        have nextCode : OriginalCode.Installed middle.code := by
          rw [(evaluation_fields source middle _ none normal).2.2.2]
          exact installed
        have suffix := after_progressive_cost middle tmp n (by omega) nextCode
          ((kept _).trans temporary) ((kept _).trans data.count)
        rw [evaluated] at suffix
        exact suffix) result actual notTimeout
  omega

theorem after_mark_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (data : Params source ch n) (installed : OriginalCode.Installed source.code)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterMark = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ 89*n+3167 := by
  rw [body_shape.2.1] at actual
  have paid := ClockCost.scalar_scope_terminating source post "tmp" (ofString "alloc") [.const 64#64]
    PersistentAlloc.formals PersistentAlloc.body afterTmp .one 1 (89*n+3165)
    (PersistentAlloc.original_code source.code installed) (PersistentAlloc.body_price source.code installed)
    (by intro target tmp codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "tmp" (.val (.word tmp))
        have kept (name : String) (different : ofString "tmp" ≠ ofString name) :
            entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "tmp" name tmp different
        have next : Params entry ch n := ⟨(kept "ch" (by decide)).trans data.chunks, (kept "n" (by decide)).trans data.count⟩
        have tmpLocal : entry.locals.lookup (ofString "tmp") = some (.val (.word tmp)) := bind_lookup_same _ _ _
        have nextCode : OriginalCode.Installed entry.code := by
          change OriginalCode.Installed target.code
          rw [codeEq]
          exact installed
        exact after_tmp_cost entry final ch tmp n bounded next nextCode tmpLocal result evaluated notTimeout)
    result actual notTimeout
  omega

/-- Complete actual progressive-container body, including every non-timeout
failure. Its bit mask is charged by the same actual field count. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (data : Params source ch n) (installed : OriginalCode.Installed source.code)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source body = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ 89*n+3168 := by
  rw [body_shape.1] at actual
  have paid := ClockCost.scalar_scope_terminating source post "mark" (Code.name .heap_mark) []
    (Code.formals .heap_mark) (Code.body .heap_mark) afterMark (Code.shape .heap_mark) 0 (89*n+3167)
    (Code.installed source.code installed .heap_mark)
    (StraightCost.body source.code .heap_mark (StraightCost.basic_supported .heap_mark (by simp)))
    (by intro target mark codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "mark" (.val (.word mark))
        have kept (name : String) (different : ofString "mark" ≠ ofString name) :
            entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "mark" name mark different
        have next : Params entry ch n := ⟨(kept "ch" (by decide)).trans data.chunks, (kept "n" (by decide)).trans data.count⟩
        have nextCode : OriginalCode.Installed entry.code := by
          change OriginalCode.Installed target.code
          rw [codeEq]
          exact installed
        exact after_mark_cost entry final ch n bounded next nextCode result evaluated notTimeout)
    result actual notTimeout
  omega

/-- Actual three-word caller; neither output mapping nor successful hashing is
a premise, and the field count is retained from this same call. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch out : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (installed : OriginalCode.Installed source.code)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word ch), .val (.word (BitVec.ofNat 64 n)), .val (.word out)])
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htr_pcontainer") expressions) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ 89*n+3169 := by
  obtain ⟨callee, called, chunks, count, output⟩ := word_triple_environment source.code.lookup (ofString "htr_pcontainer")
    (ofString "ch") (ofString "n") (ofString "out") body .one ch (BitVec.ofNat 64 n) out
    (by decide) (by decide) (by decide) (original_code source.code installed)
  exact ClockCost.call_current_terminating source post destination (ofString "htr_pcontainer") expressions _ body callee .one
    (89*n+3168) args called
    (fun result target evaluated notTimeout => body_cost (callEntryStateHOLFinite source callee) target ch n bounded
      ⟨chunks, count⟩ installed result evaluated notTimeout) result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.PContainer

#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_tmp_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.body_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.call_cost
