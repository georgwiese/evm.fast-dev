import InitECandidate.Solver.MutableTable.QueryNoException
import InitECandidate.Solver.GasBudget.MemoryExtendNoEvmErr
import InitECandidate.Solver.Input.NoNamedExceptionLoop
import InitECandidate.Solver.GasBudget.WarmAddressMutation

namespace InitECandidate.Solver.MutableTable.SetNoEvmErr
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem copy_safe (code) : Input.NoException.Safe code WitnessRadix.Copy32.body := by
  simp only [WitnessRadix.Copy32.body, Guest.guestFn_memcpy, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoException.sequence
    | apply Input.NoException.declared
    | apply Input.NoException.conditional
    | apply Input.NoException.loop
    | exact Input.NoException.store code _ _
    | exact Input.NoException.store_byte code _ _
    | exact Input.NoException.assign code _ _
    | exact Input.NoException.returned code _
    | exact Input.NoException.skip code

theorem alloc_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : GasBudget.WarmKeys.Environment source) :
    Input.NoNamedException.Safe source.code (ofString "EvmErr") WitnessRadix.PersistentAlloc.body := by
  simp only [WitnessRadix.PersistentAlloc.body, Guest.guestFn_alloc, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoNamedException.sequence
    | apply Input.NoNamedException.declared
    | apply Input.NoNamedException.conditional
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.global_assign source.code _ _)
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.returned source.code _)
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.skip source.code)
    | exact Input.NoNamedException.call_body source.code _ (ofString "trap_with") _ Input.Trap.formals Input.Trap.body .one
        environment.trapCode (GasBudget.MemoryExtend.trap_no_evm_error source.code)

theorem insert_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : GasBudget.WarmKeys.Environment source) :
    Input.NoException.Safe source.code Insert.body := by
  simp only [Insert.body, Guest.guestFn_htab_insert_raw, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoException.sequence
    | apply Input.NoException.declared
    | apply Input.NoException.conditional
    | apply Input.NoException.loop
    | exact Input.NoException.store source.code _ _
    | exact Input.NoException.store_byte source.code _ _
    | exact Input.NoException.assign source.code _ _
    | exact Input.NoException.returned source.code _
    | exact Input.NoException.skip source.code
    | exact Input.NoException.call_body source.code (ofString "memcpy") _ WitnessRadix.CopyGeneral.formals WitnessRadix.Copy32.body .one
        environment.copyCode (copy_safe source.code)
    | apply Input.NoException.scoped_body source.code "h" .one (ofString "htab_hash") _ _ Hash.formals Hash.body .one
        environment.hashCode (QueryNoException.hash_safe source.code)

theorem grow_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : GasBudget.WarmKeys.Environment source) :
    Input.NoNamedException.Safe source.code (ofString "EvmErr") Grow.body := by
  simp only [Grow.body, Guest.guestFn_htab_grow, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoNamedException.sequence
    | apply Input.NoNamedException.declared
    | apply Input.NoNamedException.conditional
    | apply Input.NoNamedException.loop
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.store source.code _ _)
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.assign source.code _ _)
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.returned source.code _)
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.skip source.code)
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.call_body source.code (ofString "htab_insert_raw") _ TableCall.formals Insert.body .one
        environment.insertCode (insert_safe source environment))
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.call_body source.code (ofString "memzero") _ WitnessRadix.Zero.formals WitnessRadix.Zero.body .one
        environment.zeroCode (GasBudget.MemoryExtend.zero_no_exception source.code))
    | apply Input.NoNamedException.scoped_body source.code _ "nkeys" .one (ofString "alloc") _ _ WitnessRadix.PersistentAlloc.formals WitnessRadix.PersistentAlloc.body .one
        environment.allocCode (alloc_safe source environment)
    | apply Input.NoNamedException.scoped_body source.code _ "nvals" .one (ofString "alloc") _ _ WitnessRadix.PersistentAlloc.formals WitnessRadix.PersistentAlloc.body .one
        environment.allocCode (alloc_safe source environment)
    | apply Input.NoNamedException.scoped_body source.code _ "nused" .one (ofString "alloc") _ _ WitnessRadix.PersistentAlloc.formals WitnessRadix.PersistentAlloc.body .one
        environment.allocCode (alloc_safe source environment)
    | apply Input.NoNamedException.scoped_body source.code _ "norder" .one (ofString "alloc") _ _ WitnessRadix.PersistentAlloc.formals WitnessRadix.PersistentAlloc.body .one
        environment.allocCode (alloc_safe source environment)
    | apply Input.NoNamedException.scoped_body source.code _ "norder_pos" .one (ofString "alloc") _ _ WitnessRadix.PersistentAlloc.formals WitnessRadix.PersistentAlloc.body .one
        environment.allocCode (alloc_safe source environment)

theorem set_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : GasBudget.WarmKeys.Environment source) :
    Input.NoNamedException.Safe source.code (ofString "EvmErr") Set.body := by
  simp only [Set.body, Guest.guestFn_htab_set, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.NoNamedException.sequence
    | apply Input.NoNamedException.declared
    | apply Input.NoNamedException.conditional
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.store source.code _ _)
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.returned source.code _)
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.skip source.code)
    | exact Input.NoNamedException.call_body source.code _ (ofString "htab_grow") _ Grow.formals Grow.body .one environment.growCode (grow_safe source environment)
    | exact Input.NoNamedException.of_all source.code _ _ (Input.NoException.call_body source.code (ofString "htab_insert_raw") _ TableCall.formals Insert.body .one
        environment.insertCode (insert_safe source environment))
    | apply Input.NoNamedException.scoped_body source.code _ "i" .one (ofString "htab_find_slot") _ _ Find.formals Find.body .one
        environment.findCode (Input.NoNamedException.of_all source.code _ _ (QueryNoException.find_safe source.code environment.hashCode environment.memeqCode))

theorem warm_address_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : GasBudget.WarmKeys.Environment source) :
    Input.NoNamedException.Safe source.code (ofString "EvmErr") GasBudget.WarmAddressMutation.body := by
  rw [GasBudget.WarmAddressMutation.body_shape]
  exact Input.NoNamedException.sequence source.code _ _ _
    (Input.NoNamedException.call_body source.code _ (ofString "htab_set") _ TableCall.formals Set.body .one environment.setCode (set_safe source environment))
    (Input.NoNamedException.of_all source.code _ _ (Input.NoException.returned source.code _))

end InitECandidate.Solver.MutableTable.SetNoEvmErr

#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.copy_safe
#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.alloc_safe
#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.insert_safe
#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.grow_safe
#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.set_safe
#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.warm_address_safe
