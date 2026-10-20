import InitECandidate.Solver.Input.MainBnLayout

namespace InitECandidate.Solver.Input.Main.BnInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

private theorem singleton_valid (action : InitializerAllocations.Action) (valid : InitializerAllocations.Valid action) :
    ∀ current,current ∈ [action] → InitializerAllocations.Valid current := by
  intro current member
  have same := List.mem_singleton.mp member
  subst current
  exact valid

theorem gamma_allocated_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    gammaAllocated {source with clock := clock} cursor = {gammaAllocated source cursor with clock := clock} := by
  unfold gammaAllocated
  rw [BnAccelInitialization.template_clock,InitializerAllocations.template_clock]

theorem gamma_written_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    gammaWritten {source with clock := clock} cursor = {gammaWritten source cursor with clock := clock} := by
  unfold gammaWritten
  rw [gamma_allocated_clock,InitializerQuads.written_clock]

theorem b2_allocated_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    b2Allocated {source with clock := clock} cursor = {b2Allocated source cursor with clock := clock} := by
  unfold b2Allocated
  rw [gamma_written_clock,InitializerAllocations.template_clock]

theorem gamma_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (gammaWritten source cursor) = InitializerAllocations.context source := by
  unfold gammaWritten gammaAllocated
  rw [InitializerQuads.written_context,InitializerAllocations.template_context,BnAccelInitialization.template_context]

theorem gamma_binding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (gammaAllocated source cursor).globals.lookup (ofString "bn_gamma") = some (.val (.word (BitVec.ofNat 64 (cursor + 416)))) := by
  simp only [gammaAllocated,InitializerAllocations.template_globals]
  simp [InitializerAllocations.globalTemplate,gammaAction,HolFiniteMapExact.update,FUPDATE,ofString]

theorem gamma_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (gammaWritten source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 800)))) := by
  simp only [gammaWritten,InitializerQuads.written_globals,gammaAllocated,InitializerAllocations.template_globals]
  simp [InitializerAllocations.globalTemplate,gammaAction,HolFiniteMapExact.update,FUPDATE,ofString,Nat.add_assoc]

/-- All actual accelerator setup, gamma allocation/table stores and B2
allocation execute and resume the literal arithmetic continuation. -/
theorem setup_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor)
    (room : cursor + 1216 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 6 ≤ source.clock) :
    evaluateHOLFiniteState source afterGuard = evaluateHOLFiniteState {b2Allocated source cursor with clock := source.clock - 6} afterB2Allocation := by
  have accelerator := BnAccelInitialization.call_execute source cursor installed scalars heap zero domain lower (by omega) aligned (by omega)
  let first := {BnAccelInitialization.template source cursor with clock := source.clock - 4}
  have firstContext : InitializerAllocations.context first = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock _ _).trans (BnAccelInitialization.template_context source cursor)
  have firstInstalled := InitializerAllocations.installed_of_context source first firstContext installed
  have firstScalars := BnAccelInitialization.template_scalars source cursor scalars
  have firstHeap := BnAccelInitialization.template_heap source cursor
  have allocation := InitializerAllocations.execute_prefix first (cursor + 416) [gammaAction] gammaStores firstInstalled firstScalars firstHeap
    (singleton_valid gammaAction gamma_valid) (by change cursor + 416 + (384 + 0) ≤ 33806089496; omega) (by omega) (by change 1 ≤ source.clock - 4; omega)
  have clock5 : source.clock - 4 - 1 = source.clock - 5 := by omega
  have allocated : evaluateHOLFiniteState first afterAccelerator = evaluateHOLFiniteState {gammaAllocated source cursor with clock := source.clock - 5} gammaStores := by
    simpa only [afterAccelerator,first,InitializerAllocations.template_clock,List.length_cons,List.length_nil,Nat.zero_add,clock5,gammaAllocated] using allocation
  let gammaReady := {gammaAllocated source cursor with clock := source.clock - 5}
  have number : (BitVec.ofNat 64 (cursor + 416)).toNat = cursor + 416 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have currentDomain := (InitializerAllocations.domain_of_context source first firstContext).trans domain
  have gammaDomain : gammaReady.memaddrs = InitE.ordinaryDomain := by
    exact (InitializerAllocations.domain_of_context first (InitializerAllocations.template first (cursor + 416) [gammaAction])
      (InitializerAllocations.template_context first (cursor + 416) [gammaAction])).trans currentDomain
  have stored := InitializerQuads.execute gammaReady "bn_gamma" (BitVec.ofNat 64 (cursor + 416)) 0 384 gamma afterGamma (gamma_binding source cursor) gammaDomain
    ⟨by rw [number]; omega,by rw [number]; omega⟩ (by rw [number]; omega) (by decide) (by rw [gamma_length])
  have storesRun : evaluateHOLFiniteState gammaReady gammaStores = evaluateHOLFiniteState {gammaWritten source cursor with clock := source.clock - 5} afterGamma := by
    have moved : InitializerQuads.written gammaReady (BitVec.ofNat 64 (cursor + 416)) 0 gamma =
        {gammaWritten source cursor with clock := source.clock - 5} :=
      InitializerQuads.written_clock (gammaAllocated source cursor) (BitVec.ofNat 64 (cursor + 416)) 0 gamma (source.clock - 5)
    exact stored.trans (congrArg (fun state => evaluateHOLFiniteState state afterGamma) moved)
  let writtenReady := {gammaWritten source cursor with clock := source.clock - 5}
  have writtenContext : InitializerAllocations.context writtenReady = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock (gammaWritten source cursor) (source.clock - 5)).trans (gamma_context source cursor)
  have writtenInstalled := InitializerAllocations.installed_of_context source writtenReady writtenContext installed
  have writtenGlobals : writtenReady.globals = (gammaAllocated source cursor).globals := by
    simp only [writtenReady,gammaWritten,InitializerQuads.written_globals]
  have writtenScalars : OriginalScalarGlobals.Scalars writtenReady.globals := by
    rw [writtenGlobals]
    exact InitializerAllocations.template_scalars (BnAccelInitialization.template source cursor) (cursor + 416) [gammaAction] (BnAccelInitialization.template_scalars source cursor scalars)
  have writtenHeap : writtenReady.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 800)))) := by
    rw [writtenGlobals]
    exact gamma_heap source cursor
  have secondAllocation := InitializerAllocations.execute_prefix writtenReady (cursor + 800) [b2Action] afterB2Allocation writtenInstalled writtenScalars writtenHeap
    (singleton_valid b2Action b2_valid) (by change cursor + 800 + (64 + 0) ≤ 33806089496; omega) (by omega) (by change 1 ≤ source.clock - 5; omega)
  have clock6 : source.clock - 5 - 1 = source.clock - 6 := by omega
  have secondRun : evaluateHOLFiniteState writtenReady afterGamma = evaluateHOLFiniteState {b2Allocated source cursor with clock := source.clock - 6} afterB2Allocation := by
    simpa only [afterGamma,writtenReady,InitializerAllocations.template_clock,List.length_cons,List.length_nil,Nat.zero_add,clock6,b2Allocated] using secondAllocation
  rw [afterGuard,StateSteps.next_sequence source first acceleratorCall _ accelerator (by change source.clock - 4 ≤ source.clock; omega),allocated,storesRun]
  exact secondRun

end InitECandidate.Solver.Input.Main.BnInitialization

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.gamma_allocated_clock
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.gamma_written_clock
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.b2_allocated_clock
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.gamma_context
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.gamma_binding
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.gamma_heap
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.setup_execute
