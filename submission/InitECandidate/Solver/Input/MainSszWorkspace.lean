import InitECandidate.Solver.Input.MainInputHeap

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

private def afterSszWrites := postSszNames ++ EvmInitialization.symbols ++ ForkInitialization.symbols
open scoped InitE.MetadataComputation InitE.NameComputation in
private theorem offsets_fresh : afterSszWrites.all (fun name => decide (ofString "ssz_offs" ≠ ofString name)) = true := by decide_cbv

private theorem different (name : String) (member : name ∈ afterSszWrites) : ofString "ssz_offs" ≠ ofString name :=
  of_decide_eq_true (List.all_eq_true.mp offsets_fresh name member)

private theorem globals_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.globals = source.globals := congrArg (fun state => state.globals) same

theorem ssz_offsets_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (sszState source).globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) := by
  change (SszInitialization.template (keccakState source) 2713715312).globals.lookup (ofString "ssz_offs") = _
  simp [SszInitialization.template,SszInitialization.allocated,InitializerWords.written,
    InitializerAllocations.template,InitializerAllocations.reserve,SszInitialization.actions,InitializerAllocations.constant,putGlobal,HolFiniteMapExact.update,FUPDATE,
    show ofString "heap_ptr" ≠ ofString "ssz_offs" from by decide,show ofString "zero_hashes" ≠ ofString "ssz_offs" from by decide]

/-- The decoder's actual initialized workspace pointer survives every real
later initializer; it is derived from retained startup provenance. -/
theorem StartupHistory.ssz_offsets (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory) (history : StartupHistory input current) :
    current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) := by
  obtain ⟨source,mptMiddle,bnMiddle,evmMiddle,_,mpt,bn,evm,fork⟩ := history
  have forkLookup := congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64) => globals.lookup (ofString "ssz_offs")) (globals_of_hash _ current fork.control)
  have forkOther := ForkInitialization.template_other evmMiddle 2713730840 (ofString "ssz_offs") (by decide)
    (by intro name member; exact different name (by simp [afterSszWrites,member]))
  have evmLookup := congrArg (fun globals : HolFiniteMapExact MlS (ValueHOL 64) => globals.lookup (ofString "ssz_offs")) (globals_of_hash _ evmMiddle evm.control)
  have evmOther := EvmInitialization.template_other (headerState bnMiddle) 2713730624 (ofString "ssz_offs") (by decide)
    (by intro name member; exact different name (by simp [afterSszWrites,member]))
  have headerOther := header_from_ssz source mptMiddle bnMiddle mpt bn (ofString "ssz_offs")
    (by intro name member; exact different name (by simp [afterSszWrites,member]))
  exact forkLookup.trans (forkOther.trans (evmLookup.trans (evmOther.trans (headerOther.trans (ssz_offsets_value source)))))

theorem InputCopied.ssz_offsets (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (copied : InputCopied input source current) :
    current.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) :=
  (copied.other_global input source current (ofString "ssz_offs") (by decide)).trans (copied.history.ssz_offsets input source)

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.ssz_offsets_value
#print axioms InitECandidate.Solver.Input.Main.StartupHistory.ssz_offsets
#print axioms InitECandidate.Solver.Input.Main.InputCopied.ssz_offsets
