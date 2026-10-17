import InitECandidate.Solver.Input.SharedRead

namespace InitECandidate.Solver.Input.SharedRead
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (address : BitVec 64) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  {WitnessRadix.QueryBranch.bind source name (Guest.wordOfLeBytes (bytes source.ffi.ffiState address)) with ffi := nextFfi source.ffi address}

/-- Actual source word-width shared-memory load from the real source oracle;
only its destination local and successful FFI event change. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (expression : ExpHOL 64) (address old : BitVec 64)
    (addressRead : WitnessRadix.QueryBranch.eval source expression=some (.val (.word address)))
    (localPresent : source.locals.lookup (ofString name)=some (.val (.word old)))
    (oracleEq : source.ffi.oracle=InitE.sourceOracle) (mapped : source.shMemaddrs address)
    (present : ∀ offset<8,(source.ffi.ffiState (address+BitVec.ofNat 64 offset)).isSome=true) :
    evaluateHOLFiniteState source (.shMemLoad .opW .local (ofString name) expression)=(none,post source name address) := by
  classical
  have finiteRead : @evalHOLFinite 64 Guest.HostMemory _ source (fun current => Classical.propDecidable (source.memaddrs current)) expression=
      some (.val (.word address)) := addressRead
  have ffiRun := call_ffi source.ffi address oracleEq present
  have decoded : panWordOfBytesHOL false (0#64) ((bytes source.ffi.ffiState address).map byteToBits)=
      Guest.wordOfLeBytes (bytes source.ffi.ffiState address) :=
    WordCodec.pan_word_guest _ (by simp only [bytes_length]; exact Nat.le_refl 8)
  rw [evaluateHOLFiniteState_shMemLoad_source,finiteRead]
  simp [lookupKvarHOLFinite,localPresent,shMemLoadHOLFiniteExact,nbOpHOL,mapped,ffiRun,decoded,
    setKvarFfiHOLFinite,setKvarHOLFinite,post,WitnessRadix.QueryBranch.bind]

end InitECandidate.Solver.Input.SharedRead

#print axioms InitECandidate.Solver.Input.SharedRead.execute
