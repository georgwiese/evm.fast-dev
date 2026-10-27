import InitECandidate.Solver.Input.SharedReadNormal
import InitECandidate.Solver.Input.SharedReadExecution
import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.Input.SharedRead
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Derive an actual oracle reply from an observed continuing source word load.
Current address/local cells are operands; future readability is not a premise. -/
theorem reached_reply (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (expression : ExpHOL 64) (address old : BitVec 64)
    (addressRead : WitnessRadix.QueryBranch.eval source expression = some (.val (.word address)))
    (localPresent : source.locals.lookup (ofString name) = some (.val (.word old)))
    (normal : evaluateHOLFiniteState source (.shMemLoad .opW .local (ofString name) expression) =
      (none, target)) :
    source.shMemaddrs address ∧ ∃ host answer,
      source.ffi.oracle (.sharedMem .mappedRead) source.ffi.ffiState [0#8]
        (panWordToBytesHOL address false) = .ret host answer ∧
      target.locals.lookup (ofString name) =
        some (.val (.word (panWordOfBytesHOL false 0 answer))) := by
  classical
  have finiteRead : @evalHOLFinite 64 Guest.HostMemory _ source
      (fun current => Classical.propDecidable (source.memaddrs current)) expression =
      some (.val (.word address)) := addressRead
  rw [evaluateHOLFiniteState_shMemLoad_source, finiteRead] at normal
  simp only [lookupKvarHOLFinite, localPresent, nbOpHOL] at normal
  by_cases mapped : source.shMemaddrs address
  · cases called : callFFIHOL source.ffi (.sharedMem .mappedRead) [0#8]
        (panWordToBytesHOL address false) with
    | final event => simp [shMemLoadHOLFiniteExact, mapped, called] at normal
    | ret next answer =>
      obtain ⟨host, reply, hostEq⟩ := ffi_return_oracle source.ffi next address answer called
      have same : setKvarFfiHOLFinite .local (ofString name)
          (.val (.word (panWordOfBytesHOL false 0 answer))) source next = target := by
        simpa only [shMemLoadHOLFiniteExact, ↓reduceIte, mapped, called, Prod.mk.injEq, true_and]
          using normal
      refine ⟨mapped, host, answer, reply, ?_⟩
      rw [← same]
      simp [setKvarFfiHOLFinite, setKvarHOLFinite, setVarHOLFinite, FUPDATE]
  · simp [shMemLoadHOLFiniteExact, mapped] at normal

/-- Actual normal execution determines the exact scalar/FFI post-state. All
presence obligations are derived from that execution rather than supplied. -/
theorem normal_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (expression : ExpHOL 64) (address old : BitVec 64)
    (addressRead : WitnessRadix.QueryBranch.eval source expression = some (.val (.word address)))
    (localPresent : source.locals.lookup (ofString name) = some (.val (.word old)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (normal : evaluateHOLFiniteState source (.shMemLoad .opW .local (ofString name) expression) =
      (none, target)) : target = post source name address := by
  obtain ⟨mapped, host, answer, reply, cell⟩ :=
    reached_reply source target name expression address old addressRead localPresent normal
  rw [oracleEq] at reply
  have present := oracle_return_present source.ffi.ffiState host address answer reply
  have run := execute source name expression address old addressRead localPresent oracleEq mapped present
  exact congrArg Prod.snd (normal.symm.trans run)

end InitECandidate.Solver.Input.SharedRead

#print axioms InitECandidate.Solver.Input.SharedRead.reached_reply
#print axioms InitECandidate.Solver.Input.SharedRead.normal_post
