import InitECandidate.Solver.Input.WordCodec
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input.SharedRead
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def bytes (host : Guest.HostMemory) (address : BitVec 64) : List UInt8 :=
  (List.range 8).map (fun offset => (host (address+BitVec.ofNat 64 offset)).getD 0)

theorem mapM_read (host : Guest.HostMemory) (address : BitVec 64) (offsets : List Nat)
    (present : ∀ offset∈offsets,(host (address+BitVec.ofNat 64 offset)).isSome=true) :
    offsets.mapM (fun offset => host (address+BitVec.ofNat 64 offset))=
      some (offsets.map (fun offset => (host (address+BitVec.ofNat 64 offset)).getD 0)) := by
  induction offsets with
  | nil => rfl
  | cons offset rest ih =>
    have tailRead := ih (by intro next member; exact present next (List.mem_cons_of_mem _ member))
    have headPresent := present offset (by simp)
    cases read : host (address+BitVec.ofNat 64 offset) with
    | none => simp [read] at headPresent
    | some value => simp [List.mapM_cons,read,tailRead]

theorem bytes_length (host : Guest.HostMemory) (address : BitVec 64) : (bytes host address).length=8 := by simp [bytes]

theorem oracle (host : Guest.HostMemory) (address : BitVec 64)
    (present : ∀ offset<8,(host (address+BitVec.ofNat 64 offset)).isSome=true) :
    InitE.sourceOracle (.sharedMem .mappedRead) host [0#8] (panWordToBytesHOL address false)=
      .ret host ((bytes host address).map byteToBits) := by
  have read := mapM_read host address (List.range 8) (by intro offset member; exact present offset (List.mem_range.mp member))
  have length : (panWordToBytesHOL address false).length=8 := by simp [panWordToBytesHOL]
  have configZero : (bitsToByte (0#8)).toNat=0 := rfl
  simp [InitE.sourceOracle,Guest.guestOracle,Guest.sharedWidth,WordCodec.oracle_address,read,length,bytes,configZero]

def nextFfi (source : HolFfiState Guest.HostMemory) (address : BitVec 64) : HolFfiState Guest.HostMemory :=
  {source with ioEvents := (source.ioEvents++[
    {name := .sharedMem .mappedRead
     configuration := [0#8]
     bytes := (panWordToBytesHOL address false).zip ((bytes source.ffiState address).map byteToBits)}])}

theorem call_ffi (source : HolFfiState Guest.HostMemory) (address : BitVec 64)
    (oracleEq : source.oracle=InitE.sourceOracle)
    (present : ∀ offset<8,(source.ffiState (address+BitVec.ofNat 64 offset)).isSome=true) :
    callFFIHOL source (.sharedMem .mappedRead) [0#8] (panWordToBytesHOL address false)=
      .ret (nextFfi source address) ((bytes source.ffiState address).map byteToBits) := by
  have reply : source.oracle (.sharedMem .mappedRead) source.ffiState [0#8] (panWordToBytesHOL address false)=
      .ret source.ffiState ((bytes source.ffiState address).map byteToBits) := by
    rw [oracleEq]
    exact oracle source.ffiState address present
  have length : (panWordToBytesHOL address false).length=8 := by simp [panWordToBytesHOL]
  simp [callFFIHOL,reply,bytes_length,length,nextFfi]

end InitECandidate.Solver.Input.SharedRead

#print axioms InitECandidate.Solver.Input.SharedRead.mapM_read
#print axioms InitECandidate.Solver.Input.SharedRead.bytes_length
#print axioms InitECandidate.Solver.Input.SharedRead.oracle
#print axioms InitECandidate.Solver.Input.SharedRead.call_ffi
