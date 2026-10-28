import InitECandidate.Solver.Input.CurrentHash.RequestListLoop
import InitECandidate.Solver.Input.CurrentHash.PListCost
import InitECandidate.Solver.Input.CurrentHash.StraightCost
import InitECandidate.Solver.Input.ClockCostScalarTerminating
import InitECandidate.Solver.Input.ObserveDeclaration

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.CurrentHash.RequestList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def price (kind : Kind) (n : Nat) := (kind.record.price+90)*n+3173

theorem after_loop_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (roots out : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (installed : OriginalCode.Installed source.code)
    (root : source.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterLoop = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ 88*n+3170 := by
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) listArguments =
      some (PListCost.values roots (BitVec.ofNat 64 n) out n) := by
    simp [listArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,root,count,output,PListCost.values]
  unfold afterLoop at actual
  have paid := ClockCost.sequence_terminating source post _ FixedRecord.releaseSuffix (88*n+3169) 1
    (fun result target evaluated notTimeout => PListCost.call_cost source target roots (BitVec.ofNat 64 n) out n bounded installed
      (some none) listArguments args result evaluated notTimeout)
    (by intro middle normal result target evaluated notTimeout
        have suffix : ClockCost.Bound source.code FixedRecord.releaseSuffix 1 := ClockCost.sequence source.code _ _ 1 0
          (AllocatorCost.release_call source.code installed (some none) _) (ClockCost.returned source.code _)
        have paid := suffix middle ((evaluation_fields source middle _ none normal).2.2.2)
        rw [evaluated] at paid
        exact paid) result actual notTimeout
  omega

theorem loop_suffix_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (data : RoundState source kind p roots out n 0)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source loopAndSuffix = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ (kind.record.price+90)*n+3170 := by
  unfold loopAndSuffix at actual
  have paid := ClockCost.sequence_terminating source post loop afterLoop ((kind.record.price+2)*n) (88*n+3170)
    (by intro result target evaluated notTimeout
        simpa only [Nat.sub_zero] using loop_cost source target kind p roots out n 0 bounded (by omega) data result evaluated notTimeout)
    (by intro middle normal result target evaluated notTimeout
        have kept (name : String) (different : ofString name ≠ ofString "i") : middle.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
          have summary := (loop_local (ofString name) different).summary_full source
          unfold LocalSummary at summary
          rw [normal] at summary
          exact summary.1 rfl
        have nextCode : OriginalCode.Installed middle.code := by
          rw [(evaluation_fields source middle _ none normal).2.2.2]
          exact data.installed
        exact after_loop_cost middle target roots out n bounded nextCode
          ((kept "roots" (by decide)).trans data.root) ((kept "n" (by decide)).trans data.count)
          ((kept "out" (by decide)).trans data.output) result evaluated notTimeout) result actual notTimeout
  exact Nat.le_trans paid (by simp only [Nat.add_mul]; omega)

structure Params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p out : BitVec 64) (n : Nat) : Prop where
  installed : OriginalCode.Installed source.code
  category : source.locals.lookup (ofString "kind") = some (.val (.word (BitVec.ofNat 64 kind.tag)))
  pointer : source.locals.lookup (ofString "p") = some (.val (.word p))
  count : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 n)))
  size : source.locals.lookup (ofString "sz") = some (.val (.word (BitVec.ofNat 64 kind.record.length)))
  output : source.locals.lookup (ofString "out") = some (.val (.word out))

theorem after_roots_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (data : Params source kind p out n)
    (root : source.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterRoots = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ (kind.record.price+90)*n+3170 := by
  obtain ⟨inner,run,endpoint⟩ := ScalarScope.declaration_observe source post "i" (.const 0#64) 0#64 loopAndSuffix result rfl actual
  let entry := bind source "i" 0#64
  have kept (name : String) (different : ofString "i" ≠ ofString name) := bind_lookup_other source "i" name 0#64 different
  have ready : RoundState entry kind p roots out n 0 := ⟨data.installed,
    (kept "kind" (by decide)).trans data.category, (kept "p" (by decide)).trans data.pointer,
    (kept "n" (by decide)).trans data.count, (kept "sz" (by decide)).trans data.size,
    (kept "roots" (by decide)).trans root, (kept "out" (by decide)).trans data.output, bind_lookup_same _ _ _⟩
  have paid := loop_suffix_cost entry inner kind p roots out n bounded ready result run notTimeout
  rw [endpoint]
  exact paid

theorem after_mark_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p out : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (data : Params source kind p out n)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterMark = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ (kind.record.price+90)*n+3172 := by
  unfold afterMark at actual
  have paid := ClockCost.scalar_scope_terminating source post "roots" (ofString "alloc") allocationArguments
    PersistentAlloc.formals PersistentAlloc.body afterRoots .one 1 ((kind.record.price+90)*n+3170)
    (PersistentAlloc.original_code source.code data.installed) (PersistentAlloc.body_price source.code data.installed)
    (by intro target roots codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "roots" (.val (.word roots))
        have kept (name : String) (different : ofString "roots" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "roots" name roots different
        have nextCode : OriginalCode.Installed entry.code := by
          change OriginalCode.Installed target.code
          rw [codeEq]
          exact data.installed
        have next : Params entry kind p out n := ⟨nextCode, (kept "kind" (by decide)).trans data.category,
          (kept "p" (by decide)).trans data.pointer, (kept "n" (by decide)).trans data.count,
          (kept "sz" (by decide)).trans data.size, (kept "out" (by decide)).trans data.output⟩
        exact after_roots_cost entry final kind p roots out n bounded next (bind_lookup_same _ _ _) result evaluated notTimeout)
    result actual notTimeout
  omega

/-- Complete actual request-list body. The real selected record kind and
decoded count pay for dispatch, every iteration, progressive list and scopes. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p out : BitVec 64) (n : Nat)
    (bounded : n ≤ 134217728) (data : Params source kind p out n)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source body = (result,post))
    (notTimeout : result ≠ some .timeOut) : source.clock-post.clock ≤ price kind n := by
  rw [body_shape] at actual
  have paid := ClockCost.scalar_scope_terminating source post "mark" (Code.name .heap_mark) []
    (Code.formals .heap_mark) (Code.body .heap_mark) afterMark (Code.shape .heap_mark) 0 ((kind.record.price+90)*n+3172)
    (Code.installed source.code data.installed .heap_mark)
    (StraightCost.body source.code .heap_mark (StraightCost.basic_supported .heap_mark (by simp)))
    (by intro target mark codeEq result final evaluated notTimeout
        let entry := CallNormal.continuationEntry source target "mark" (.val (.word mark))
        have kept (name : String) (different : ofString "mark" ≠ ofString name) : entry.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
          bind_lookup_other {target with locals := source.locals} "mark" name mark different
        have nextCode : OriginalCode.Installed entry.code := by
          change OriginalCode.Installed target.code
          rw [codeEq]
          exact data.installed
        have next : Params entry kind p out n := ⟨nextCode, (kept "kind" (by decide)).trans data.category,
          (kept "p" (by decide)).trans data.pointer, (kept "n" (by decide)).trans data.count,
          (kept "sz" (by decide)).trans data.size, (kept "out" (by decide)).trans data.output⟩
        exact after_mark_cost entry final kind p out n bounded next result evaluated notTimeout)
    result actual notTimeout
  exact Nat.le_trans paid (by unfold price; omega)

end InitECandidate.Solver.Input.CurrentHash.RequestList

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.after_loop_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.loop_suffix_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.after_roots_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestList.body_cost
