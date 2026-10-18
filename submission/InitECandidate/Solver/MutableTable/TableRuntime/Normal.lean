import InitECandidate.Solver.MutableTable.TableRuntime.Budget
import InitECandidate.Solver.Input.NormalCallClock
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Exact original constructor price on an actual normal body return, with
no entry-clock allowance. Owned fresh-layout room remains an entry premise. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : capacity = 4 ∨ capacity % 8 = 0)
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source TableNew.body = (some (.returned value), target)) :
    price capacity ≤ source.clock ∧ value = .val (.word (BitVec.ofNat 64 start)) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (freshEnd kind start capacity))))
        memory := resultMemory source.memory source.be kind start capacity
        clock := source.clock - price capacity} := by
  let extra := price capacity
  let padded := {source with clock := source.clock + extra}
  have lifted := panPropsEvaluateAddClockEq TableNew.body source (some (.returned value)) target extra
    ⟨normal, by intro impossible; cases impossible⟩
  obtain ⟨checked, checkedRun, checkedFrame⟩ := execute padded kind start capacity valid domain capacityShape keyLocal capLocal heap allocCode zeroCode
    (by change price capacity ≤ source.clock + extra; omega)
  have valueEq := congrArg Prod.fst (lifted.symm.trans checkedRun)
  have returned : value = .val (.word (BitVec.ofNat 64 start)) := by simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using valueEq
  have checkedEq := congrArg Prod.snd (lifted.symm.trans checkedRun)
  change {target with clock := target.clock + extra} = checked at checkedEq
  have frame := (congrArg emptyLocalsHOLFinite checkedEq).trans (checkedFrame.trans (entered_frame padded kind start capacity))
  have stripped := strip_clock_padding source target {source with
    globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (freshEnd kind start capacity))))
    memory := resultMemory source.memory source.be kind start capacity} (price capacity) extra (by omega) frame
  exact ⟨stripped.1, returned, stripped.2⟩

/-- A real successful scoped constructor supplies its exact caller clock,
continuation entry and normal continuation run. Clock funding is derived. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (valid : Valid kind (fresh kind start capacity)) (domain : source.memaddrs = InitE.ordinaryDomain)
    (capacityShape : capacity = 4 ∨ capacity % 8 = 0)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind capacity))
    (code : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new") arguments continuation) = (some (.returned value), post)) :
    price capacity + 1 ≤ source.clock ∧ ∃ inner,
      evaluateHOLFiniteState (callState source name kind start capacity) continuation = (some (.returned value), inner) ∧
      post = restore source name inner := by
  have positive := Input.CallNormal.normal_clock source post (ofString name) .one (ofString "htab_new") arguments continuation value normal
  obtain ⟨callee, called, keyLocal, capLocal⟩ := environment source.code.lookup kind capacity code
  obtain ⟨calleePost, returned, calleeRun⟩ := Input.CallNormal.callee_return source post (ofString name) .one (ofString "htab_new") arguments (values kind capacity)
    TableNew.body continuation callee .one args called positive value normal
  obtain ⟨fits, _, _⟩ := body_normal (callEntryStateHOLFinite source callee) calleePost kind start capacity valid domain capacityShape keyLocal capLocal heap allocCode zeroCode returned calleeRun
  have funded : price capacity + 1 ≤ source.clock := by change price capacity ≤ source.clock - 1 at fits; omega
  have actual := call_execute source kind start capacity name arguments continuation valid domain capacityShape args code heap allocCode zeroCode funded
  have resultEq := congrArg Prod.fst (actual.symm.trans normal)
  have postEq := congrArg Prod.snd (actual.symm.trans normal)
  refine ⟨funded, (evaluateHOLFiniteState (callState source name kind start capacity) continuation).2, Prod.ext resultEq rfl, postEq.symm⟩

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.body_normal
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.call_normal
