import InitECandidate.Solver.Input.MainEvmPrefix

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

private theorem globals_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.globals = source.globals := congrArg (fun state => state.globals) same
private theorem code_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.code = source.code := congrArg (fun state => state.code) same
private theorem domain_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.memaddrs = source.memaddrs := congrArg (fun state => state.memaddrs) same

theorem EvmReached.heap (source mptMiddle bnMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bn : BnReached source mptMiddle bnMiddle) (reached : EvmReached source bnMiddle middle) :
    middle.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713730840#64)) := by
  rw [globals_of_hash _ middle reached.control]
  exact EvmInitialization.template_heap (headerState bnMiddle) 2713730624 (header_heap source mptMiddle bnMiddle bn)

theorem EvmReached.scalars (input : Guest.InputBlob) (source mptMiddle bnMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (bn : BnReached source mptMiddle bnMiddle) (reached : EvmReached source bnMiddle middle) :
    OriginalScalarGlobals.Scalars middle.globals := by
  rw [globals_of_hash _ middle reached.control]
  exact EvmInitialization.template_scalars (headerState bnMiddle) 2713730624 (header_scalars input source mptMiddle bnMiddle entry mpt bn)

theorem EvmReached.code (source mptMiddle bnMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (mpt : MptReached source mptMiddle) (bn : BnReached source mptMiddle bnMiddle) (reached : EvmReached source bnMiddle middle) : middle.code = source.code :=
  (code_of_hash _ middle reached.control).trans
    ((InitializerAllocations.code_of_context (headerState bnMiddle) (EvmInitialization.template (headerState bnMiddle) 2713730624)
      (EvmInitialization.template_context (headerState bnMiddle) 2713730624)).trans
      ((InitializerAllocations.code_of_context bnMiddle (headerState bnMiddle) (header_context bnMiddle)).trans (bn.code source mptMiddle bnMiddle mpt)))

theorem EvmReached.domain (input : Guest.InputBlob) (source mptMiddle bnMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (bn : BnReached source mptMiddle bnMiddle) (reached : EvmReached source bnMiddle middle) :
    middle.memaddrs = InitE.ordinaryDomain :=
  (domain_of_hash _ middle reached.control).trans
    ((InitializerAllocations.domain_of_context (headerState bnMiddle) (EvmInitialization.template (headerState bnMiddle) 2713730624)
      (EvmInitialization.template_context (headerState bnMiddle) 2713730624)).trans (header_hash_environment input source mptMiddle bnMiddle entry mpt bn).domain)

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.EvmReached.heap
#print axioms InitECandidate.Solver.Input.Main.EvmReached.scalars
#print axioms InitECandidate.Solver.Input.Main.EvmReached.code
#print axioms InitECandidate.Solver.Input.Main.EvmReached.domain
