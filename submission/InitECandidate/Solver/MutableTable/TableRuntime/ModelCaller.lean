import InitECandidate.Solver.MutableTable.TableRuntime.ModelEmpty
import InitECandidate.Solver.MutableTable.MemoryModelFields
import InitECandidate.Solver.MutableTable.MemoryModelEntry

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem caller_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (shape : capacity = 4 ∨ capacity % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false) :
    MemoryModel.Occupied (callState source name kind start capacity) kind (fresh kind start capacity) [] :=
  MemoryModel.Occupied.of_fields (enteredState source kind start capacity) (callState source name kind start capacity) kind _ []
    (entered_model source kind start capacity valid shape domain little) (entered_memory source kind start capacity) rfl rfl

/-- Actual original constructor result supplies the complete physical empty
entry data for all checked queries, insertion and no-growth setters. No table
header, used byte, occupied list or order-array result is assumed. Query and
code ownership are separate caller facts. -/
theorem caller_runtime_data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (shape : capacity = 4 ∨ capacity % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (query : BitVec 64) (bits : Nat) (small : bits < 64) (power : capacity = 2 ^ bits)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (hashCode : source.code.lookup (Flapjack.Basis.Pure.MlString.ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (Flapjack.Basis.Pure.MlString.ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one)) :
    Insert.GeneralData (callState source name kind start capacity) (cell (fresh kind start capacity) .header 0)
      (parameters kind (fresh kind start capacity) query) kind (cell (fresh kind start capacity) .values 0)
      (cell (fresh kind start capacity) .order 0) (cell (fresh kind start capacity) .position 0) 0#64 bits [] :=
  MemoryModel.runtime_data (callState source name kind start capacity) kind _ valid domain query [] valid.positive
    (caller_header source name kind start capacity valid) (caller_model source name kind start capacity valid shape domain little)
    bits small power queryFits queryMapped little hashCode copyCode

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.caller_model
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.caller_runtime_data
