import InitECandidate.Solver.Input.InitializerAliases
import InitECandidate.Solver.Input.InitializerQuads

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

namespace InitializerAliases

def globalTemplate (globals : HolFiniteMapExact MlS (ValueHOL 64)) (pointer : BitVec 64) : List Action → HolFiniteMapExact MlS (ValueHOL 64)
  | [] => globals
  | action :: rest => globalTemplate (globals.update (ofString action.name,.val (.word (pointer + BitVec.ofNat 64 action.offset)))) pointer rest

theorem template_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (actions : List Action) :
    (template source pointer actions).globals = globalTemplate source.globals pointer actions := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source pointer action)

theorem template_clock_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (actions : List Action) :
    (template source pointer actions).clock = source.clock := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source pointer action)

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (actions : List Action)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} pointer actions = {template source pointer actions with locals := locals} := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source pointer action)

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (actions : List Action) :
    (template source pointer actions).locals = source.locals := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source pointer action)

end InitializerAliases

namespace InitializerAllocations

def globalTemplate (globals : HolFiniteMapExact MlS (ValueHOL 64)) (cursor : Nat) : List Action → HolFiniteMapExact MlS (ValueHOL 64)
  | [] => globals
  | action :: rest => globalTemplate
      ((globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 (cursor + action.bytes))))).update (ofString action.name,.val (.word (BitVec.ofNat 64 cursor))))
      (cursor + action.bytes) rest

theorem template_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action) :
    (template source cursor actions).globals = globalTemplate source.globals cursor actions := by
  induction actions generalizing source cursor with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source action cursor) (cursor + action.bytes)

theorem template_clock_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action) :
    (template source cursor actions).clock = source.clock := by
  induction actions generalizing source cursor with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source action cursor) (cursor + action.bytes)

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor actions = {template source cursor actions with locals := locals} := by
  induction actions generalizing source cursor with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source action cursor) (cursor + action.bytes)

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (actions : List Action) :
    (template source cursor actions).locals = source.locals := by
  induction actions generalizing source cursor with
  | nil => rfl
  | cons action rest ih => exact ih (reserve source action cursor) (cursor + action.bytes)

theorem code_of_context (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : context target = context source) : target.code = source.code :=
  (context_code target).symm.trans ((congrArg (fun s => s.code) same).trans (context_code source))

theorem installed_of_context (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : context target = context source) (installed : OriginalCode.Installed source.code) : OriginalCode.Installed target.code := by
  rw [code_of_context source target same]
  exact installed

theorem domain_of_context (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : context target = context source) : target.memaddrs = source.memaddrs :=
  (context_domain target).symm.trans ((congrArg (fun s => s.memaddrs) same).trans (context_domain source))

theorem oracle_of_context (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : context target = context source) : target.ffi.oracle = source.ffi.oracle :=
  (context_oracle target).symm.trans ((congrArg (fun s => s.ffi.oracle) same).trans (context_oracle source))

end InitializerAllocations

namespace InitializerQuads

theorem written_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List Words) :
    (written source pointer offset words).globals = source.globals := rfl

theorem written_clock_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List Words) :
    (written source pointer offset words).clock = source.clock := rfl

theorem written_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List Words)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    written {source with locals := locals} pointer offset words = {written source pointer offset words with locals := locals} := rfl

theorem written_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset : Nat) (words : List Words) :
    (written source pointer offset words).locals = source.locals := rfl

end InitializerQuads
end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.InitializerAliases.template_globals
#print axioms InitECandidate.Solver.Input.InitializerAliases.template_clock_value
#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_globals
#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_clock_value
#print axioms InitECandidate.Solver.Input.InitializerQuads.written_globals
#print axioms InitECandidate.Solver.Input.InitializerQuads.written_clock_value

#print axioms InitECandidate.Solver.Input.InitializerAliases.template_locals
#print axioms InitECandidate.Solver.Input.InitializerAliases.template_locals_value

#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_locals
#print axioms InitECandidate.Solver.Input.InitializerAllocations.template_locals_value

#print axioms InitECandidate.Solver.Input.InitializerQuads.written_locals
#print axioms InitECandidate.Solver.Input.InitializerQuads.written_locals_value

#print axioms InitECandidate.Solver.Input.InitializerAllocations.code_of_context

#print axioms InitECandidate.Solver.Input.InitializerAllocations.installed_of_context

#print axioms InitECandidate.Solver.Input.InitializerAllocations.domain_of_context

#print axioms InitECandidate.Solver.Input.InitializerAllocations.oracle_of_context
