import InitECandidate.Solver.MutableTable.TableRuntime.NormalFinish
import InitECandidate.Solver.MutableTable.TableRuntime.Normal

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Combined room for all six actual original constructor allocations.
The intermediate clear and header stores cannot alter its heap cursor.
This word-multiple case includes the real warm-up capacities 16 and 64. -/
theorem normal_room (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (lower : 2701131776 ≤ start) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (keySmall : stride kind * capacity < 2 ^ 64) (wordSmall : 8 * capacity < 2 ^ 64) (capSmall : capacity + 32 < 2 ^ 64)
    (multiple : capacity % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain)
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source TableNew.body = (some (.returned value), target)) :
    freshEnd kind start capacity ≤ 33806089496 := by
  obtain ⟨headerBound, memory, headerTarget, headerRun⟩ := normal_header source target kind start capacity startBound startAligned keyLocal capLocal heap code trapCode value normal
  let entered := {headerEntry source kind start with memory := memory}
  obtain ⟨usedBound, reached, inner, reachedRun, reachedLocals, reachedUsed, reachedHeap, codes, domainEq, endian⟩ :=
    normal_preclear entered headerTarget kind start capacity (header_entry_locals source kind start capacity capLocal memory)
      headerBound startAligned keySmall wordSmall (by omega) (TableNew.allocated_heap source "t" start (start + 72)) code trapCode value headerRun
  have alloc : reached.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one) := by rw [codes]; exact code
  have trap : reached.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one) := by rw [codes]; exact trapCode
  have zero : reached.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one) := by rw [codes]; exact zeroCode
  have mapped : reached.memaddrs = InitE.ordinaryDomain := domainEq.trans domain
  exact normal_finish reached inner kind start capacity reachedLocals reachedUsed lower startAligned usedBound wordSmall capSmall multiple mapped reachedHeap alloc trap zero value reachedRun

theorem normal_layout (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (positive : 0 < capacity) (lower : 2701131776 ≤ start) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (keySmall : stride kind * capacity < 2 ^ 64) (wordSmall : 8 * capacity < 2 ^ 64) (capSmall : capacity + 32 < 2 ^ 64)
    (multiple : capacity % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain)
    (keyLocal : source.locals.lookup (ofString "key_len") = some (.val (.word (BitVec.ofNat 64 (KeyHash.keySize kind)))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source TableNew.body = (some (.returned value), target)) :
    Valid kind (fresh kind start capacity) :=
  fresh_valid kind start capacity positive lower (normal_room source target kind start capacity lower startBound startAligned keySmall wordSmall capSmall multiple domain keyLocal capLocal heap code trapCode zeroCode value normal) startAligned

/-- A successful real scoped caller establishes its fresh layout. No final
reservation bound or prospective ownership predicate is an entry premise. -/
theorem normal_call_layout (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (start capacity : Nat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (positive : 0 < capacity) (lower : 2701131776 ≤ start) (startBound : start ≤ 33806089496) (startAligned : start % 8 = 0)
    (keySmall : stride kind * capacity < 2 ^ 64) (wordSmall : 8 * capacity < 2 ^ 64) (capSmall : capacity + 32 < 2 ^ 64)
    (multiple : capacity % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values kind capacity))
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (code : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new") arguments continuation) = (some (.returned value), post)) :
    Valid kind (fresh kind start capacity) := by
  have funded := Input.CallNormal.normal_clock source post (ofString name) .one (ofString "htab_new") arguments continuation value normal
  obtain ⟨callee, called, keyLocal, capLocal⟩ := environment source.code.lookup kind capacity newCode
  obtain ⟨target, returned, bodyRun⟩ := Input.CallNormal.callee_return source post (ofString name) .one (ofString "htab_new") arguments (values kind capacity) TableNew.body continuation callee .one args called funded value normal
  exact normal_layout (callEntryStateHOLFinite source callee) target kind start capacity positive lower startBound startAligned keySmall wordSmall capSmall multiple domain keyLocal capLocal heap code trapCode zeroCode returned bodyRun

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.normal_room
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.normal_layout
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.normal_call_layout
