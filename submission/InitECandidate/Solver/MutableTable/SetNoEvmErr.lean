import InitECandidate.Solver.MutableTable.SetNoOtherException

namespace InitECandidate.Solver.MutableTable.SetNoEvmErr
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

abbrev copy_safe := SetNoOtherException.copy_safe
abbrev insert_safe := SetNoOtherException.insert_safe

theorem alloc_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : GasBudget.WarmKeys.Environment source) :
    Input.NoNamedException.Safe source.code (ofString "EvmErr") WitnessRadix.PersistentAlloc.body :=
  SetNoOtherException.alloc_safe source environment (ofString "EvmErr") (by decide)

theorem grow_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : GasBudget.WarmKeys.Environment source) :
    Input.NoNamedException.Safe source.code (ofString "EvmErr") Grow.body :=
  SetNoOtherException.grow_safe source environment (ofString "EvmErr") (by decide)

theorem set_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : GasBudget.WarmKeys.Environment source) :
    Input.NoNamedException.Safe source.code (ofString "EvmErr") Set.body :=
  SetNoOtherException.set_safe source environment (ofString "EvmErr") (by decide)

theorem warm_address_safe (source : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : GasBudget.WarmKeys.Environment source) :
    Input.NoNamedException.Safe source.code (ofString "EvmErr") GasBudget.WarmAddressMutation.body :=
  SetNoOtherException.warm_address_safe source environment (ofString "EvmErr") (by decide)

end InitECandidate.Solver.MutableTable.SetNoEvmErr

#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.copy_safe
#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.insert_safe
#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.alloc_safe
#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.grow_safe
#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.set_safe
#print axioms InitECandidate.Solver.MutableTable.SetNoEvmErr.warm_address_safe
