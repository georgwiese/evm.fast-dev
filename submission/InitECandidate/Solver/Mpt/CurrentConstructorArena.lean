import InitECandidate.Solver.Mpt.NodeConstructorGlobals
import InitECandidate.Solver.Mpt.CompactToNibblesGlobals
import InitECandidate.Solver.Input.CurrentStartup.ArenaEffects

namespace InitECandidate.Solver.Mpt
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input

theorem NodeConstructor.current_arena (kind : NodeConstructor.Kind)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arena : CurrentStartup.ArenaState source)
    (outcome : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source (NodeConstructor.body kind)=(outcome,post)) :
    CurrentStartup.ArenaState post :=
  arena.after_globals _ outcome actual (NodeConstructor.globals kind _ _ arena.code (by decide)) (NodeConstructor.globals kind _ _ arena.code (by decide))

theorem CompactToNibbles.current_arena (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) (outcome : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source CompactToNibbles.body=(outcome,post)) : CurrentStartup.ArenaState post :=
  arena.after_globals _ outcome actual (CompactToNibbles.globals _ _ arena.code (by decide)) (CompactToNibbles.globals _ _ arena.code (by decide))

end InitECandidate.Solver.Mpt

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.current_arena
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.current_arena
