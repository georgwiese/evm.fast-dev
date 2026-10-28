import InitECandidate.Solver.Input.ObserveDeclaration
import InitECandidate.Solver.Input.CurrentHash.ProgressiveLoopCost
import InitECandidate.Solver.Input.CurrentHash.ProgressiveFoldCost
import InitECandidate.Solver.Input.ClockCostScalarTerminating
import InitECandidate.Solver.Input.CurrentHash.StraightCost

namespace InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Progressive ProgressiveRound

set_option maxRecDepth 100000 in
theorem prefix_shape : body = .decCall (ofString "mark") .one (Code.name .heap_mark) [] afterMark ∧
    afterMark = .decCall (ofString "roots") .one (ofString "alloc") [.panop .mul [.const 24#64, .const 32#64]] afterRoots ∧
    afterRoots = .decCall (ofString "acc") .one (ofString "alloc") [.const 32#64] afterAcc ∧
    afterAcc = .dec (ofString "k") .one (.const 0#64) afterK ∧
    afterK = .dec (ofString "off") .one (.const 0#64) afterOff ∧
    afterOff = .dec (ofString "size") .one (.const 1#64) loopAndSuffix := by
  simp only [afterMark, afterRoots, afterAcc, afterK, afterOff, loopAndSuffix, body, Code.name,
    Guest.Software.guestFn_merkleize_progressive, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none]
  exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro⟩

theorem loop_suffix_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat)
    (bounded : n ≤ 134217728) (round : k ≤ 15) (data : Round source p roots n k)
    (installed : OriginalCode.Installed source.code) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source loopAndSuffix = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ currentAllowance n (offset k) k + 115 := by
  rw [fold_shape.2.2.1] at actual
  apply ClockCost.sequence_terminating source post loop afterLoop (currentAllowance n (offset k) k) 115
    (fun result target evaluated notTimeout => ProgressiveLoopCost.cost source target p roots n k bounded round data installed result evaluated notTimeout)
    (by intro middle continued result target evaluated notTimeout
        obtain ⟨position, inside, finalData⟩ := ProgressiveLoopCost.normal source middle p roots n k bounded round data continued
        have currentCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle loop none continued).2.2.2]; exact installed
        have paid := ProgressiveFoldCost.suffix_cost middle position inside currentCode finalData.round
        rw [evaluated] at paid
        exact Nat.le_trans paid (by omega)) result actual notTimeout

def initialized (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (bind (bind source "k" 0#64) "off" 0#64) "size" 1#64

theorem initialized_round (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n : Nat)
    (pointer : source.locals.lookup (ofString "p") = some (.val (.word p)))
    (root : source.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))) : Round (initialized source) p roots n 0 := by
  have kept (name : String) (notK : ofString "k" ≠ ofString name) (notOff : ofString "off" ≠ ofString name) (notSize : ofString "size" ≠ ofString name) :
      (initialized source).locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
    (bind_lookup_other _ "size" name _ notSize).trans ((bind_lookup_other _ "off" name _ notOff).trans (bind_lookup_other source "k" name _ notK))
  refine ⟨(kept "p" (by decide) (by decide) (by decide)).trans pointer,
    (kept "roots" (by decide) (by decide) (by decide)).trans root,
    (kept "n" (by decide) (by decide) (by decide)).trans count, ?_, bind_lookup_same _ _ _, ?_⟩
  · exact (bind_lookup_other _ "size" "off" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact (bind_lookup_other _ "size" "k" _ (by decide)).trans ((bind_lookup_other _ "off" "k" _ (by decide)).trans (bind_lookup_same _ _ _))

/-- The actual three constant declarations establish the initial geometric
state at no source tick cost, before the same observed loop/suffix run. -/
theorem initialized_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "p") = some (.val (.word p)))
    (root : source.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterAcc = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 88*n + 3115 := by
  rw [prefix_shape.2.2.2.1] at actual
  obtain ⟨firstPost, runFirst, endpointFirst⟩ := ScalarScope.declaration_observe source post "k" (.const 0#64) 0#64 afterK result rfl actual
  let firstState := bind source "k" 0#64
  rw [prefix_shape.2.2.2.2.1] at runFirst
  obtain ⟨secondPost, runSecond, endpointSecond⟩ := ScalarScope.declaration_observe firstState firstPost "off" (.const 0#64) 0#64 afterOff result rfl runFirst
  let secondState := bind firstState "off" 0#64
  rw [prefix_shape.2.2.2.2.2] at runSecond
  obtain ⟨thirdPost, runThird, endpointThird⟩ := ScalarScope.declaration_observe secondState secondPost "size" (.const 1#64) 1#64 loopAndSuffix result rfl runSecond
  have paid := loop_suffix_cost (initialized source) thirdPost p roots n 0 bounded (by decide) (initialized_round source p roots n pointer root count) installed result runThird notTimeout
  change source.clock - thirdPost.clock ≤ _ at paid
  rw [currentAllowance, offset] at paid
  rw [endpointFirst, endpointSecond, endpointThird]
  change source.clock - thirdPost.clock ≤ _
  omega

/-- Actual acc allocation. Only a checked scalar return resumes caller locals;
allocation failure paths are paid without assuming any allocator room. -/
theorem after_roots_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "p") = some (.val (.word p)))
    (root : source.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterRoots = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 88*n + 3117 := by
  rw [prefix_shape.2.2.1] at actual
  have paid := ClockCost.scalar_scope_terminating source post "acc" (ofString "alloc") [.const 32#64] PersistentAlloc.formals PersistentAlloc.body afterAcc .one 1 (88*n+3115)
    (PersistentAlloc.original_code source.code installed) (PersistentAlloc.body_price source.code installed)
    (by intro target acc codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "acc" (.val (.word acc))
        have kept (name : String) (different : ofString "acc" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "acc" name acc different
        have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact installed
        exact initialized_cost entry final p roots n bounded currentCode ((kept "p" (by decide)).trans pointer)
          ((kept "roots" (by decide)).trans root) ((kept "n" (by decide)).trans count) result evaluated notTimeout) result actual notTimeout
  omega

theorem after_mark_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "p") = some (.val (.word p)))
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterMark = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 88*n + 3119 := by
  rw [prefix_shape.2.1] at actual
  have paid := ClockCost.scalar_scope_terminating source post "roots" (ofString "alloc") [.panop .mul [.const 24#64, .const 32#64]] PersistentAlloc.formals PersistentAlloc.body afterRoots .one 1 (88*n+3117)
    (PersistentAlloc.original_code source.code installed) (PersistentAlloc.body_price source.code installed)
    (by intro target roots codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "roots" (.val (.word roots))
        have kept (name : String) (different : ofString "roots" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "roots" name roots different
        have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact installed
        exact after_roots_cost entry final p roots n bounded currentCode ((kept "p" (by decide)).trans pointer)
          (bind_lookup_same _ _ _) ((kept "n" (by decide)).trans count) result evaluated notTimeout) result actual notTimeout
  omega

/-- Whole current progressive hashing, including all allocations, actual capped
Merkle rounds, final SHA fold, clear/copy/release and failure paths. The same
observed non-timeout execution supplies continuation; no heap, workspace, mapped
arena, successful hashing or future funding is assumed. -/
theorem cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "p") = some (.val (.word p)))
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source body = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ 88*n + 3120 := by
  rw [prefix_shape.1] at actual
  have paid := ClockCost.scalar_scope_terminating source post "mark" (Code.name .heap_mark) [] (Code.formals .heap_mark) (Code.body .heap_mark) afterMark (Code.shape .heap_mark) 0 (88*n+3119)
    (Code.installed source.code installed .heap_mark) (StraightCost.body source.code .heap_mark (StraightCost.basic_supported .heap_mark (by simp)))
    (by intro target mark codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "mark" (.val (.word mark))
        have kept (name : String) (different : ofString "mark" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "mark" name mark different
        have currentCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact installed
        exact after_mark_cost entry final p n bounded currentCode ((kept "p" (by decide)).trans pointer) ((kept "n" (by decide)).trans count) result evaluated notTimeout)
    result actual notTimeout
  omega

end InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost.prefix_shape
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost.loop_suffix_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost.initialized_round
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost.initialized_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost.after_roots_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveBodyCost.cost
