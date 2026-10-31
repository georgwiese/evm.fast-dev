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
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source caught).2.clock≤14*(2*length.toNat+1)+2 := by
  obtain ⟨cursor,limit,physical,lower,upper⟩:=arena.cursors
  exact Validate.caught_cost source pointer length cursor limit pointerCell lengthCell physical fits arena.code

/-- Complete unchanged validator at the actual live cursor. The saved mark
and error release restore that cursor, even during nested witness decoding. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤14*(2*length.toNat+1)+4 := by
  obtain ⟨cursor,limit,physical,lower,upper⟩:=arena.cursors
  exact Validate.body_cost source pointer length cursor limit pointerCell lengthCell physical fits arena.code

/-- A real normal public return restores its live arena and protects all
memory outside the containing current scratch region. -/
theorem body_normal_outside (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ LiveArena post ∧ Validation.Outside source post 2952790016 2965299200 := by
  obtain ⟨cursor,limit,physical,lower,upper⟩:=arena.cursors
  obtain ⟨answer,next,outside⟩:=Validate.body_normal_outside source post pointer length cursor limit pointerCell lengthCell physical fits arena.code value normal
  have codeEq := congrArg PanSemStateFiniteExact.code outside.runtime
  change post.code=source.code at codeEq
  exact ⟨answer,LiveArena.of_validation next lower upper (by rw [codeEq]; exact arena.code),outside.widen lower upper⟩

theorem ignored_normal_outside (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_validate_items") expressions)=(none,post)) :
    1≤source.clock ∧ post.locals=source.locals ∧ LiveArena post ∧ Validation.Outside source post 2952790016 2965299200 ∧
      source.clock-post.clock≤14*(2*length.toNat+1)+5 := by
  obtain ⟨cursor,limit,physical,lower,upper⟩:=arena.cursors
  obtain ⟨positive,locals,next,outside,price⟩:=Validate.ignored_normal_outside source post pointer length cursor limit expressions args physical fits arena.code normal
  have codeEq := congrArg PanSemStateFiniteExact.code outside.runtime
  change post.code=source.code at codeEq
  exact ⟨positive,locals,LiveArena.of_validation next lower upper (by rw [codeEq]; exact arena.code),outside.widen lower upper,price⟩

end InitECandidate.Solver.Rlp.CurrentValidate

#print axioms InitECandidate.Solver.Rlp.CurrentValidate.original_code
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.startup_arena
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.caught_cost
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.body_cost
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.body_normal_outside
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.ignored_normal_outside
