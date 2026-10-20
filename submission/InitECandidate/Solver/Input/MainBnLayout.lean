import InitECandidate.Solver.Input.MainBnProgram
import InitECandidate.Solver.Input.BnModmulCall
import InitECandidate.Solver.Input.InitializerMemoryFrame

namespace InitECandidate.Solver.Input.Main.BnInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def gammaAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  InitializerAllocations.template (BnAccelInitialization.template source cursor) (cursor + 416) [gammaAction]
def gammaWritten (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  InitializerQuads.written (gammaAllocated source cursor) (BitVec.ofNat 64 (cursor + 416)) 0 gamma
def b2Allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  InitializerAllocations.template (gammaWritten source cursor) (cursor + 800) [b2Action]

theorem b2_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (b2Allocated source cursor).globals :=
  InitializerAllocations.template_scalars _ _ _ (InitializerAllocations.template_scalars _ _ _ (BnAccelInitialization.template_scalars source cursor scalars))

theorem b2_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (b2Allocated source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 864)))) := by
  simp only [b2Allocated,InitializerAllocations.template_globals]
  simp [InitializerAllocations.globalTemplate,b2Action,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString,Nat.add_assoc]

theorem b2_binding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (b2Allocated source cursor).globals.lookup (ofString "bn_b2") = some (.val (.word (BitVec.ofNat 64 (cursor + 800)))) := by
  simp only [b2Allocated,InitializerAllocations.template_globals]
  simp [InitializerAllocations.globalTemplate,b2Action,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString]

theorem b2_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (b2Allocated source cursor) = InitializerAllocations.context source := by
  unfold b2Allocated gammaWritten gammaAllocated
  rw [InitializerAllocations.template_context,InitializerQuads.written_context,InitializerAllocations.template_context,BnAccelInitialization.template_context]

private theorem b2_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (gamma : key ≠ ofString "bn_gamma") (b2 : key ≠ ofString "bn_b2") :
    (b2Allocated source cursor).globals.lookup key = (BnAccelInitialization.template source cursor).globals.lookup key := by
  unfold b2Allocated gammaWritten gammaAllocated
  rw [InitializerAllocations.template_other _ _ _ key heap (by intro action member; simpa [b2Action,InitializerAllocations.constant] using (List.mem_singleton.mp member ▸ b2)),
    InitializerQuads.written_globals,
    InitializerAllocations.template_other _ _ _ key heap (by intro action member; simpa [gammaAction] using (List.mem_singleton.mp member ▸ gamma))]

private theorem endian_of_context (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : InitializerAllocations.context target = InitializerAllocations.context source) : target.be = source.be :=
  congrArg (fun state => state.be) same

theorem b2_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs = InitE.ordinaryDomain)
    (oracle : source.ffi.oracle = InitE.sourceOracle) (little : source.be = false)
    (lower : 2701131776 ≤ cursor) (room : cursor + 1216 ≤ 33806089496) (aligned : cursor % 8 = 0) :
    BnModmul.Environment (b2Allocated source cursor) (BitVec.ofNat 64 cursor) := by
  have context := b2_context source cursor
  have code := InitializerAllocations.code_of_context source (b2Allocated source cursor) context
  have currentDomain := (InitializerAllocations.domain_of_context source (b2Allocated source cursor) context).trans domain
  have currentOracle := (InitializerAllocations.oracle_of_context source (b2Allocated source cursor) context).trans oracle
  have endian := endian_of_context source (b2Allocated source cursor) context
  have number (offset : Nat) (inside : offset ≤ 1216) : (BitVec.ofNat 64 (cursor + offset)).toNat = cursor + offset := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have baseNumber : (BitVec.ofNat 64 cursor).toNat = cursor := by simpa using number 0 (by decide)
  have bindings := BnAccelInitialization.template_params_bindings source cursor
  refine ⟨?_,?_,?_,?_,?_,currentOracle,currentDomain,⟨by rw [baseNumber]; exact lower,by rw [baseNumber]; omega⟩,by rw [baseNumber]; exact aligned,endian.trans little,?_⟩
  · rw [code]; exact installed
  · rw [b2_other source cursor (ofString "bn_accel_params") (by decide) (by decide) (by decide)]; exact bindings.params
  · rw [b2_other source cursor (ofString "bn_accel_a") (by decide) (by decide) (by decide)]; exact bindings.a
  · rw [b2_other source cursor (ofString "bn_accel_b") (by decide) (by decide) (by decide)]
    simpa only [BitVec.ofNat_add] using bindings.b
  · rw [b2_other source cursor (ofString "bn_accel_d") (by decide) (by decide) (by decide)]
    simpa only [BitVec.ofNat_add] using bindings.d
  · intro index
    rw [b2Allocated,InitializerAllocations.template_memory]
    have previous := InitializerQuads.written_before (gammaAllocated source cursor) (BitVec.ofNat 64 (cursor + 416))
      (byteAddress (BitVec.ofNat 64 cursor) (96 + 8 * index.val)) 0 gamma
      (by rw [number 416 (by decide),gamma_length]; omega)
      (by rw [byteAddress_toNat _ _ (by rw [baseNumber]; omega),baseNumber,number 416 (by decide)]; omega)
    rw [gammaWritten,previous]
    rw [gammaAllocated,InitializerAllocations.template_memory]
    simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using BnAccelInitialization.template_modulus source cursor index

end InitECandidate.Solver.Input.Main.BnInitialization

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.b2_scalars
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.b2_heap
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.b2_binding
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.b2_context
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.b2_environment
