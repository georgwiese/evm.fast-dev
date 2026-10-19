import InitECandidate.Solver.MutableTable.TableRuntime.NormalRoom
import InitECandidate.Solver.Input.AssignedCallNormal

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real assigned constructor call derives its reservation and exact
state, including the update of an existing scalar caller local. -/
theorem assigned_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (old : BitVec 64)
    (positive : 0 < capacity) (lower : 2701131776 ≤ start) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (keySmall : stride kind * capacity < 2 ^ 64) (wordSmall : 8 * capacity < 2 ^ 64) (capSmall : capacity + 32 < 2 ^ 64)
    (multiple : capacity % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some (values kind capacity))
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals,TableNew.body,.one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals,Input.Trap.body,.one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals,Zero.body,.one))
    (binding : source.locals.lookup (ofString name) = some (.val (.word old)))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "htab_new") arguments) = (none,post)) :
    price capacity + 1 ≤ source.clock ∧ Valid kind (fresh kind start capacity) ∧ post = callState source name kind start capacity := by
  obtain ⟨callee,called,keyLocal,capLocal⟩ := environment source.code.lookup kind capacity newCode
  obtain ⟨funded,target,returned,bodyRun⟩ := Input.CallNormal.assigned_callee_return source post (some (.local,ofString name)) (ofString "htab_new") arguments
    (values kind capacity) TableNew.body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  have valid := normal_layout entry target kind start capacity positive lower startBound startAligned keySmall wordSmall capSmall multiple domain
    keyLocal capLocal heap allocCode trapCode zeroCode returned bodyRun
  obtain ⟨bodyFunded,answer,frame⟩ := body_normal entry target kind start capacity valid domain (Or.inr multiple) keyLocal capLocal heap allocCode zeroCode returned bodyRun
  rw [answer] at bodyRun
  have checked : isValidValueHOLExact source.toExact .local (ofString name) (.val (.word (BitVec.ofNat 64 start))) = true := by
    simp [isValidValueHOLExact,lookupKvarHOLExact,toExact,binding,shapeOfHOLExact,shapeEqHOL]
  have actual := evaluateHOLFiniteState_call_return_set_kvar source .local (ofString name) none (ofString "htab_new") arguments (values kind capacity)
    TableNew.body callee .one (.val (.word (BitVec.ofNat 64 start))) target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL]) checked
  have postEq := congrArg Prod.snd (normal.symm.trans actual)
  change post = setVarHOLFinite (ofString name) (.val (.word (BitVec.ofNat 64 start))) {target with locals := source.locals} at postEq
  have updated := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have sub : source.clock - 1 - price capacity = source.clock - (price capacity + 1) := by omega
  have restored : {target with locals := source.locals} = {source with
      globals := source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (freshEnd kind start capacity))))
      memory := resultMemory source.memory source.be kind start capacity
      clock := source.clock - (price capacity + 1)} := by
    simpa only [emptyLocalsHOLFinite,entry,callEntryStateHOLFinite,sub] using updated
  change price capacity ≤ source.clock - 1 at bodyFunded
  refine ⟨by omega,valid,?_⟩
  rw [postEq]
  change bind {target with locals := source.locals} name (BitVec.ofNat 64 start) = _
  rw [restored]
  rfl

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.assigned_normal
