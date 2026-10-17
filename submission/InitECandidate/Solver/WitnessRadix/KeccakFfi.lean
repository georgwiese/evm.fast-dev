import InitECandidate.Solver.WitnessRadix.KeccakOracle
import InitECandidate.Solver.PanDeclarations
import InitECandidate.Solver.WitnessRadix.StateSteps

set_option maxRecDepth 10000

namespace InitECandidate.Solver.WitnessRadix.Keccak
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def nextFfi (source : HolFfiState Guest.HostMemory) (bytes : List (BitVec 8)) : HolFfiState Guest.HostMemory :=
  { source with ioEvents := source.ioEvents ++
    [{ name := .extCall (ofString "keccakf"), configuration := [], bytes := bytes.zip (answer bytes) }] }

theorem call_ffi (source : HolFfiState Guest.HostMemory) (bytes : List (BitVec 8))
    (oracleEq : source.oracle = InitE.sourceOracle) (length : bytes.length = 200) :
    callFFIHOL source (.extCall (ofString "keccakf")) [] bytes = .ret (nextFfi source bytes) (answer bytes) := by
  have reply : source.oracle (.extCall (ofString "keccakf")) source.ffiState [] bytes = .ret source.ffiState (answer bytes) := by
    rw [oracleEq]
    exact oracle source.ffiState bytes length
  have nonempty : (.extCall (ofString "keccakf") : HolFfiName) ≠ .extCall (MlString.implode []) := by decide
  simp [callFFIHOL, nonempty, reply, answer_length, length, nextFfi]

def extCode : ProgHOL 64 := .extCall (ofString "keccakf") (localVar "stp") (.const 0#64) (localVar "stp") (.const 200#64)
noncomputable def post (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (bytes : List (BitVec 8)) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  { source with
    memory := @panWriteBytearrayWord8HOL 64 _ pointer (answer bytes) source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
    ffi := nextFfi source.ffi bytes }

/-- The literal Keccak-f external call follows from real source-oracle and
successful array-read facts, with exact memory/FFI update and no body clock. -/
theorem ext_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (bytes : List (BitVec 8))
    (stpLocal : source.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (readArray : readBytearrayWordHOL (byteWidth := 8) pointer 200
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be) = some bytes) :
    evaluateHOLFiniteState source extCode = (none, post source pointer bytes) := by
  have length : bytes.length = 200 := readBytearrayWordHOL_length _ _ _ _ readArray
  have ffiRun := call_ffi source.ffi bytes oracleEq length
  have emptyRead : readBytearrayWordHOL (byteWidth := 8) pointer 0
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be) = some [] := rfl
  rw [extCode, evaluateHOLFiniteState_extCall_source]
  simp only [evalHOLFinite, evalHOLExact, localVar, toExact, stpLocal]
  simp only [show (0#64 : BitVec 64).toNat = 0 from rfl,
    show (200#64 : BitVec 64).toNat = 200 from rfl, emptyRead, readArray, ffiRun]
  change (none, ofExact (post source pointer bytes).toExact (post source pointer bytes).toExact_finiteSupport) = _
  rw [ofExact_toExact]

def f1600Body : ProgHOL 64 := match Guest.guestFn_keccak_f1600 with
  | .function fn => progToHOL fn.body | _ => .skip

theorem body_shape : f1600Body = .seq extCode (.return (.const 0#64)) := by
  simp only [f1600Body, Guest.guestFn_keccak_f1600, progToHOL, expToHOL, extCode, localVar]

theorem f1600_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (bytes : List (BitVec 8))
    (stpLocal : source.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (readArray : readBytearrayWordHOL (byteWidth := 8) pointer 200
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be) = some bytes) :
    evaluateHOLFiniteState source f1600Body =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite (post source pointer bytes)) := by
  rw [body_shape, StateSteps.next_sequence source (post source pointer bytes) _ _
    (ext_execute source pointer bytes stpLocal oracleEq readArray) (Nat.le_refl _)]
  exact BuildEntry.zero_return _

end InitECandidate.Solver.WitnessRadix.Keccak

#print axioms InitECandidate.Solver.WitnessRadix.Keccak.call_ffi
#print axioms InitECandidate.Solver.WitnessRadix.Keccak.ext_execute
#print axioms InitECandidate.Solver.WitnessRadix.Keccak.f1600_execute
