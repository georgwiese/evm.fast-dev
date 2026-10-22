import InitECandidate.Solver.MutableTable.TableRuntime.CostProgram
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.WitnessRadix.ZeroCost

namespace InitECandidate.Solver.MutableTable.TableRuntime.Cost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem Locals.after_prefix (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (capacity : Nat) (names : List String)
    (locals : Locals source capacity names) (command : ProgHOL 64)
    (safe : ∀ key,Input.LocalPrefix key command) (normal : evaluateHOLFiniteState source command=(none,target)) : Locals target capacity names:=by
  apply locals.of_agreement source target capacity names
  intro key
  have info:=(safe key).summary source
  rewrite [normal] at info
  exact info.1 rfl

/-- Price actual constructor syntax at its current real scalar locals.
Allocator failures stop; only actual scalar returns install the next local.
No allocation room, table layout, mapped word or future success is supplied. -/
theorem program_cost (specs : List Action) (names : List String) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (capacity : Nat) (small : capacity+32<2^64) (valid : Valid names specs) (locals : Locals source capacity names)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (program specs)).2.clock≤price capacity specs:=by
  induction specs generalizing names source with
  | nil=>exact Input.ClockCost.returned source.code _ source rfl
  | cons action rest ih=>
    cases action with
    | allocation name amount=>
      have actual:=Input.ClockCost.scalar_scope_current source name (ofString "alloc") [amount] PersistentAlloc.formals PersistentAlloc.body (program rest) .one 1 (price capacity rest)
        (PersistentAlloc.original_code source.code installed) (PersistentAlloc.body_price source.code installed) (by
          intro target word codeEq
          let ready:=Input.CallNormal.continuationEntry source target name (.val (.word word))
          have saved : Locals {target with locals:=source.locals} capacity names:=locals
          have next:=saved.bind {target with locals:=source.locals} capacity names name word valid.1
          have readyInstalled : Input.OriginalCode.Installed ready.code:=by rewrite [show ready.code=source.code from codeEq]; exact installed
          exact ih (name::names) ready valid.2 next readyInstalled)
      change source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") [amount] (program rest))).2.clock≤2+price capacity rest
      omega
    | declaration name value=>
      apply Input.ClockCost.scalar_declaration_current source (ofString name) value (program rest) (price capacity rest)
      intro word
      exact ih (name::names) (QueryBranch.bind source name word) valid.2 (locals.bind source capacity names name word valid.1) installed
    | store address value=>
      change source.clock-(evaluateHOLFiniteState source (.seq (.store address value) (program rest))).2.clock≤price capacity rest
      have actual:=Input.ClockCost.sequence_reached_current source (.store address value) (program rest) 0 (price capacity rest)
        (Input.ClockCost.store source.code address value source rfl) (by
          intro middle normal
          have next:=locals.after_prefix source middle capacity names (.store address value) (fun _=>.store _ _) normal
          have codeEq:=(Input.evaluation_fields source middle (.store address value) none normal).2.2.2
          have middleInstalled : Input.OriginalCode.Installed middle.code:=by rewrite [codeEq]; exact installed
          exact ih names middle valid next middleInstalled)
      simpa only [Nat.zero_add] using actual
    | clear=>
      obtain ⟨dst,dstCell⟩:=locals.2 "used" valid.1
      have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "used",localVar "cap"]=some (Zero.values dst capacity):=by
        simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,dstCell,locals.1,Zero.values]
      have front:=Input.ZeroAny.call_cost source [localVar "used",localVar "cap"] dst capacity small args (Zero.original_code source.code installed)
      change source.clock-(evaluateHOLFiniteState source clear).2.clock≤Input.ZeroAny.price capacity+1 at front
      exact Input.ClockCost.sequence_reached_current source clear (program rest) (Input.ZeroAny.price capacity+1) (price capacity rest) front (by
        intro middle normal
        have next:=locals.after_prefix source middle capacity names clear (fun _=>.call none _ _ (by intro name impossible; cases impossible)) normal
        have codeEq:=(Input.evaluation_fields source middle clear none normal).2.2.2
        have middleInstalled : Input.OriginalCode.Installed middle.code:=by rewrite [codeEq]; exact installed
        exact ih names middle valid.2 next middleInstalled)

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (capacity : Nat)
    (small : capacity+32<2^64) (installed : Input.OriginalCode.Installed source.code)
    (capCell : source.locals.lookup (ofString "cap")=some (.val (.word (BitVec.ofNat 64 capacity)))) :
    source.clock-(evaluateHOLFiniteState source TableNew.body).2.clock≤Input.ZeroAny.price capacity+13:=by
  rewrite [body_shape,←actions_price capacity]
  exact program_cost actions [] source capacity small actions_valid ⟨capCell,by intro name impossible; cases impossible⟩ installed

end InitECandidate.Solver.MutableTable.TableRuntime.Cost

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.Cost.Locals.after_prefix
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.Cost.program_cost
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.Cost.body_cost
