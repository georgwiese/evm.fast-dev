import InitECandidate.Solver.Input.MainBnAccelProgram
import InitECandidate.Solver.Input.InitializerFields

namespace InitECandidate.Solver.Input.Main.BnAccelInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

structure ParamsGlobals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : Prop where
  params : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word (BitVec.ofNat 64 cursor)))
  a : source.globals.lookup (ofString "bn_accel_a") = some (.val (.word (BitVec.ofNat 64 cursor)))
  b : source.globals.lookup (ofString "bn_accel_b") = some (.val (.word (BitVec.ofNat 64 (cursor + 32))))
  zero : source.globals.lookup (ofString "bn_accel_zero") = some (.val (.word (BitVec.ofNat 64 (cursor + 64))))
  modulus : source.globals.lookup (ofString "bn_accel_m") = some (.val (.word (BitVec.ofNat 64 (cursor + 96))))
  d : source.globals.lookup (ofString "bn_accel_d") = some (.val (.word (BitVec.ofNat 64 (cursor + 128))))

theorem params_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : ParamsGlobals (params source cursor) cursor := by
  constructor
  all_goals
    simp only [params,InitializerAliases.template_globals,InitializerAllocations.template_globals]
    simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,paramsAliases,paramsAction,
      InitializerAliases.direct,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString,BitVec.ofNat_add]

theorem params_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (params source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 160)))) := by
  simp only [params,InitializerAliases.template_globals,InitializerAllocations.template_globals]
  simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,paramsAliases,paramsAction,
    InitializerAliases.direct,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString]

theorem fp2_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (fp2 source cursor).globals.lookup (ofString "bn_accel_fp2_params") = some (.val (.word (BitVec.ofNat 64 (cursor + 160)))) ∧
    (fp2 source cursor).globals.lookup (ofString "bn_accel_fp2_f1") = some (.val (.word (BitVec.ofNat 64 (cursor + 160)))) ∧
    (fp2 source cursor).globals.lookup (ofString "bn_accel_fp2_f2") = some (.val (.word (BitVec.ofNat 64 (cursor + 224)))) := by
  simp only [fp2,InitializerAliases.template_globals,InitializerAllocations.template_globals]
  simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,fp2Aliases,fp2Action,
    InitializerAliases.direct,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString,BitVec.ofNat_add,BitVec.add_assoc]

theorem fp2_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (fp2 source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 288)))) := by
  simp only [fp2,InitializerAliases.template_globals,InitializerAllocations.template_globals]
  simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,fp2Aliases,fp2Action,
    InitializerAliases.direct,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString,Nat.add_assoc]

theorem g1_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (template source cursor).globals.lookup (ofString "bn_accel_g1_params") = some (.val (.word (BitVec.ofNat 64 (cursor + 288)))) ∧
    (template source cursor).globals.lookup (ofString "bn_accel_g1_p1") = some (.val (.word (BitVec.ofNat 64 (cursor + 288)))) ∧
    (template source cursor).globals.lookup (ofString "bn_accel_g1_p2") = some (.val (.word (BitVec.ofNat 64 (cursor + 352)))) := by
  simp only [template,InitializerAliases.template_globals,InitializerAllocations.template_globals]
  simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,g1Aliases,g1Action,
    InitializerAliases.direct,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString,BitVec.ofNat_add,BitVec.add_assoc]

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 416)))) := by
  simp only [template,InitializerAliases.template_globals,InitializerAllocations.template_globals]
  simp [InitializerAliases.globalTemplate,InitializerAllocations.globalTemplate,g1Aliases,g1Action,
    InitializerAliases.direct,InitializerAliases.offset,InitializerAllocations.constant,HolFiniteMapExact.update,FUPDATE,ofString,Nat.add_assoc]

theorem params_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (params source cursor).globals :=
  InitializerAliases.template_scalars _ _ _ (InitializerAllocations.template_scalars source cursor [paramsAction] scalars)

theorem seeded_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (seeded source cursor).globals := params_scalars source cursor scalars

theorem fp2_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (fp2 source cursor).globals :=
  InitializerAliases.template_scalars _ _ _ (InitializerAllocations.template_scalars _ _ [fp2Action] (seeded_scalars source cursor scalars))

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (template source cursor).globals :=
  InitializerAliases.template_scalars _ _ _ (InitializerAllocations.template_scalars _ _ [g1Action] (fp2_scalars source cursor scalars))

theorem params_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    params {source with clock := clock} cursor = {params source cursor with clock := clock} := by
  unfold params
  rw [InitializerAllocations.template_clock,InitializerAliases.template_clock]

theorem seeded_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    seeded {source with clock := clock} cursor = {seeded source cursor with clock := clock} := by
  unfold seeded
  simp only [params_clock,InitializerQuads.written_clock]

theorem fp2_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    fp2 {source with clock := clock} cursor = {fp2 source cursor with clock := clock} := by
  unfold fp2
  rw [seeded_clock,InitializerAllocations.template_clock,InitializerAliases.template_clock]

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := by
  unfold template
  rw [fp2_clock,InitializerAllocations.template_clock,InitializerAliases.template_clock]

theorem params_clock_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : (params source cursor).clock = source.clock := by
  unfold params
  rw [InitializerAliases.template_clock_value,InitializerAllocations.template_clock_value]

theorem seeded_clock_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : (seeded source cursor).clock = source.clock := by
  unfold seeded
  rw [InitializerQuads.written_clock_value,InitializerQuads.written_clock_value,params_clock_value]

theorem fp2_clock_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : (fp2 source cursor).clock = source.clock := by
  unfold fp2
  rw [InitializerAliases.template_clock_value,InitializerAllocations.template_clock_value,seeded_clock_value]

theorem template_clock_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : (template source cursor).clock = source.clock := by
  unfold template
  rw [InitializerAliases.template_clock_value,InitializerAllocations.template_clock_value,fp2_clock_value]

theorem params_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (params source cursor) = InitializerAllocations.context source := by
  unfold params
  rw [InitializerAliases.template_context,InitializerAllocations.template_context]

theorem seeded_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (seeded source cursor) = InitializerAllocations.context source := by
  unfold seeded
  rw [InitializerQuads.written_context,InitializerQuads.written_context,params_context]

theorem fp2_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (fp2 source cursor) = InitializerAllocations.context source := by
  unfold fp2
  rw [InitializerAliases.template_context,InitializerAllocations.template_context,seeded_context]

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (template source cursor) = InitializerAllocations.context source := by
  unfold template
  rw [InitializerAliases.template_context,InitializerAllocations.template_context,fp2_context]

end InitECandidate.Solver.Input.Main.BnAccelInitialization

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.params_bindings

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.params_heap

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.fp2_bindings

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.fp2_heap

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.g1_bindings

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_heap

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.params_scalars

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.seeded_scalars

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.fp2_scalars

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_scalars

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.params_clock

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.seeded_clock

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.fp2_clock

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_clock

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.params_clock_value

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.seeded_clock_value

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.fp2_clock_value

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_clock_value

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.params_context

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.seeded_context

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.fp2_context

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_context
