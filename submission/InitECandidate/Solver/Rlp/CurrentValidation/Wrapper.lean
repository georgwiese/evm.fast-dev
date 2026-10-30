import InitECandidate.Solver.Rlp.ValidationCallFrame
import InitECandidate.Solver.Input.CurrentStartup.ArenaFrame

namespace InitECandidate.Solver.Rlp.CurrentValidate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

abbrev body := Validate.body
abbrev release := Validate.release
abbrev handler := Validate.handler
abbrev arguments := Validate.arguments
abbrev caught := Validate.caught
abbrev afterError := Validate.afterError
abbrev afterMark := Validate.afterMark

theorem body_shape : body=.decCall (ofString "mark") .one (ofString "scratch_mark") [] afterMark :=
  Validate.body_shape

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_validate_items")=some (Header.formals,body,.one) :=
  Validate.original_code code installed

theorem handler_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code handler 1 :=
  Validate.handler_price code installed

/-- Main's real initialized cursors now satisfy the mapped-stack validator
invariant. No room or successful future scratch allocation is assumed. -/
theorem startup_arena (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) :
    Validation.Arena source 2965299200#64 2952790016#64 :=
  ⟨arena.domain,arena.scratch,arena.frame,by decide,by decide,by decide,by decide⟩

theorem caught_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source caught).2.clock≤14*(2*length.toNat+1)+2 :=
  Validate.caught_cost source pointer length 2965299200#64 2952790016#64
    pointerCell lengthCell (startup_arena source arena) fits arena.code

/-- Complete unchanged public validator with the now reachable nested-list
push/pop paths. The input/stack rank decreases on every continuing iteration;
the saved mark and caught-error release remain part of the actual execution. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤14*(2*length.toNat+1)+4 :=
  Validate.body_cost source pointer length 2965299200#64 2952790016#64
    pointerCell lengthCell (startup_arena source arena) fits arena.code

/-- The real normal public return restores the startup arena and preserves
all memory outside its temporary scratch interval, including earlier inputs. -/
theorem body_normal_outside (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ Validation.Arena post 2965299200#64 2952790016#64 ∧
      Validation.Outside source post 2952790016 2965299200 :=
  Validate.body_normal_outside source post pointer length 2965299200#64 2952790016#64
    pointerCell lengthCell (startup_arena source arena) fits arena.code value normal

theorem ignored_normal_outside (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_validate_items") expressions)=(none,post)) :
    1≤source.clock ∧ post.locals=source.locals ∧ Validation.Arena post 2965299200#64 2952790016#64 ∧
      Validation.Outside source post 2952790016 2965299200 ∧ source.clock-post.clock≤14*(2*length.toNat+1)+5 :=
  Validate.ignored_normal_outside source post pointer length 2965299200#64 2952790016#64
    expressions args (startup_arena source arena) fits arena.code normal

end InitECandidate.Solver.Rlp.CurrentValidate

#print axioms InitECandidate.Solver.Rlp.CurrentValidate.original_code
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.startup_arena
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.caught_cost
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.body_cost

#print axioms InitECandidate.Solver.Rlp.CurrentValidate.body_normal_outside
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.ignored_normal_outside
