import InitECandidate.Solver.Input.MainBnPrefix

namespace InitECandidate.Solver.Input.Main.BnAccelInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (other : ∀ name ∈ symbols,key ≠ ofString name) :
    (template source cursor).globals.lookup key = source.globals.lookup key := by
  have h0 := other "bn_accel_params" (by simp [symbols])
  have h1 := other "bn_accel_a" (by simp [symbols])
  have h2 := other "bn_accel_b" (by simp [symbols])
  have h3 := other "bn_accel_zero" (by simp [symbols])
  have h4 := other "bn_accel_m" (by simp [symbols])
  have h5 := other "bn_accel_d" (by simp [symbols])
  have h6 := other "bn_accel_fp2_params" (by simp [symbols])
  have h7 := other "bn_accel_fp2_f1" (by simp [symbols])
  have h8 := other "bn_accel_fp2_f2" (by simp [symbols])
  have h9 := other "bn_accel_g1_params" (by simp [symbols])
  have h10 := other "bn_accel_g1_p1" (by simp [symbols])
  have h11 := other "bn_accel_g1_p2" (by simp [symbols])
  simp only [template,fp2,seeded,params,InitializerAliases.template_globals,InitializerAllocations.template_globals,InitializerQuads.written_globals]
  simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,paramsAliases,fp2Aliases,g1Aliases,paramsAction,fp2Action,g1Action,
    InitializerAliases.direct,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,Ne.symm heap,Ne.symm h0,Ne.symm h1,Ne.symm h2,Ne.symm h3,Ne.symm h4,Ne.symm h5,Ne.symm h6,Ne.symm h7,Ne.symm h8,Ne.symm h9,Ne.symm h10,Ne.symm h11]

end InitECandidate.Solver.Input.Main.BnAccelInitialization

namespace InitECandidate.Solver.Input.Main.BnInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (template source cursor) = InitializerAllocations.context source := by
  unfold template
  rw [InitializerAllocations.template_context,b2_context]

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (heap : key ≠ ofString "heap_ptr") (gamma : key ≠ ofString "bn_gamma") (b2 : key ≠ ofString "bn_b2") (expw : key ≠ ofString "bn_expw")
    (other : ∀ name ∈ BnAccelInitialization.symbols,key ≠ ofString name) :
    (template source cursor).globals.lookup key = source.globals.lookup key := by
  simp only [template,b2Allocated,gammaWritten,gammaAllocated,InitializerAllocations.template_globals,InitializerQuads.written_globals]
  have base := BnAccelInitialization.template_other source cursor key heap other
  simpa [InitializerAllocations.globalTemplate,gammaAction,b2Action,exponentAction,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,
    Ne.symm heap,Ne.symm gamma,Ne.symm b2,Ne.symm expw] using base

end InitECandidate.Solver.Input.Main.BnInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

private theorem globals_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.globals = source.globals := congrArg (fun state => state.globals) same

private theorem code_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.code = source.code := congrArg (fun state => state.code) same

theorem BnReached.heap (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : BnReached source mptMiddle middle) :
    middle.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713719944#64)) := by
  rw [globals_of_hash _ middle reached.control]
  exact BnInitialization.template_heap (secpState mptMiddle) 2713718728

theorem BnReached.scalars (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) :
    OriginalScalarGlobals.Scalars middle.globals := by
  rw [globals_of_hash _ middle reached.control]
  exact BnInitialization.template_scalars (secpState mptMiddle) 2713718728 (secp_scalars input source mptMiddle entry mpt)

theorem BnReached.code (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) : middle.code = source.code :=
  (code_of_hash _ middle reached.control).trans
    ((InitializerAllocations.code_of_context (secpState mptMiddle) (BnInitialization.template (secpState mptMiddle) 2713718728)
      (BnInitialization.template_context (secpState mptMiddle) 2713718728)).trans (secp_code source mptMiddle mpt))

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_other
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.template_other
#print axioms InitECandidate.Solver.Input.Main.BnReached.heap
#print axioms InitECandidate.Solver.Input.Main.BnReached.scalars
#print axioms InitECandidate.Solver.Input.Main.BnReached.code
