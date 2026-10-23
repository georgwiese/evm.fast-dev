import InitECandidate.Solver.Mpt.FromWitnessProgram
import InitECandidate.Solver.Input.RootDecoderCost
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.Mpt.FromWitness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- All outcomes of the original245 wrapper have the existing complete
root-decoder allowance plus its real scoped and map-constructor calls. -/
theorem body_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db root : BitVec 64) (boundary : RootBoundary input source)
    (installed : Input.OriginalCode.Installed source.code) (scalars : Input.OriginalScalarGlobals.Scalars source.globals)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (hash : Keccak256.Environment source 2713714976#64 2713715176#64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤rootDecoderPrice input+4 := by
  obtain ⟨callee,called,entryDb,entryRoot⟩:=WitnessDecodeRoot.environment source.code.lookup db root (WitnessDecodeRoot.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have entryBoundary:=boundary.erase_frame input source entry rfl (entryDb.trans dbCell.symm)
  have entryScratch:=scratch.of_fields source entry 2713714688#64 2701135872#64 rfl rfl
  have entryHash:=hash.of_fields source entry 2713714976#64 2713715176#64 rfl rfl rfl (HeapGlobals.refl source)
  have price:=root_decoder_cost input entry root entryBoundary installed scalars entryRoot entryScratch entryHash
  have tailPrice : Input.ClockCost.Bound source.code tail 3:=
    Input.ClockCost.call_body source.code none (ofString "mpt_new") newArguments NewTrie.formals NewTrie.body .one 2
      (NewTrie.original_code source.code installed) (NewTrie.body_cost source.code installed)
  rw [body_shape]
  exact Input.ClockCost.scoped_current source (ofString "root") .one (ofString "decode_witness_to_mpt") decodeArguments _ WitnessDecodeRoot.body tail callee .one
    (rootDecoderPrice input) 3 (decode_arguments source db root dbCell rootCell) called price tailPrice

end InitECandidate.Solver.Mpt.FromWitness

#print axioms InitECandidate.Solver.Mpt.FromWitness.body_cost
