import InitECandidate.Solver.Headers.FieldFrame
import InitECandidate.Solver.Input.LiteralGuardNormal

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def Kind.flagError : Kind→BitVec 64 | .uint=>1#64 | .bytes=>6#64 | .raw=>8#64
def Kind.returnExpression : Kind→ExpHOL 64
  | .bytes=>.rfield 1 (localVar "it")
  | _=>.rstruct [.rfield 1 (localVar "it"),.rfield 2 (localVar "it")]
def Kind.returnValue (kind : Kind) (pointer payload : BitVec 64) : ValueHOL 64 :=
  match kind with | .bytes=>.val (.word pointer) | _=>.rStruct [.val (.word pointer),.val (.word payload)]
def Kind.checks : Kind→List (ProgHOL 64)
  | .uint=>[
      .ite (.cmp .notEqual (.rfield 2 (localVar "it")) (.const 0#64))
        (.ite (.cmp .equal (.loadByte (.rfield 1 (localVar "it"))) (.const 0#64)) (.raise (ofString "HdrErr") (.const 2#64)) .skip) .skip,
      .ite (.cmp .notEqual (localVar "maxb") (.const 0#64))
        (.ite (.cmp .lower (localVar "maxb") (.rfield 2 (localVar "it"))) (.raise (ofString "HdrErr") (.const 3#64)) .skip) .skip]
  | .bytes=>[.ite (.cmp .notEqual (.rfield 2 (localVar "it")) (localVar "width")) (.raise (ofString "HdrErr") (.const 7#64)) .skip]
  | .raw=>[]
def Kind.afterFlag (kind : Kind) : ProgHOL 64 := kind.checks.foldr .seq (.return kind.returnExpression)

theorem after_item_shape (kind : Kind) : kind.afterItem=.seq
    (.ite (.cmp .notEqual (.rfield 0 (localVar "it")) (.const 0#64)) (.raise (ofString "HdrErr") (.const kind.flagError)) .skip) kind.afterFlag := by
  cases kind <;> simp only [Kind.afterItem,Kind.body,Kind.declaration,Kind.flagError,Kind.afterFlag,Kind.checks,Kind.returnExpression,List.foldr_cons,List.foldr_nil,localVar,
    Guest.guestFn_hdr_uint_field,Guest.guestFn_hdr_bytes_field,Guest.guestFn_hdr_raw_field,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

theorem checks_pure (kind : Kind) : ∀ check∈kind.checks,Input.PureGuard check := by
  cases kind <;> simp only [Kind.checks,List.mem_cons,List.not_mem_nil,or_false]
  · intro check member
    rcases member with rfl|rfl
    all_goals exact .ite _ (.ite _ (.raise _ _) .skip) .skip
  · intro check same
    subst check
    exact .ite _ (.raise _ _) .skip
  · intro check impossible
    exact impossible.elim

private theorem checks_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (checks : List (ProgHOL 64))
    (pure : ∀ check∈checks,Input.PureGuard check) (expression : ExpHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (checks.foldr .seq (.return expression))=(some (.returned value),post)) :
    evaluateHOLFiniteState source (.return expression)=(some (.returned value),post) := by
  induction checks with
  | nil=>exact normal
  | cons check rest ih=>
    have tail := (pure check (by simp)).normal_continue source post (rest.foldr .seq (.return expression)) value normal
    exact ih (by intro check member; exact pure check (by simp [member])) tail

/-- A normal original field helper rejects list-kind items and returns
precisely the pointer/payload words of its actually decoded string item. -/
theorem after_item_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (pointer header payload flag : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source kind.afterItem=(some (.returned value),post)) :
    flag=0#64 ∧ value=kind.returnValue (pointer+header) payload := by
  have read : eval source (.cmp .notEqual (.rfield 0 (localVar "it")) (.const 0#64))=
      some (.val (.word (if flag≠0#64 then 1#64 else 0#64))) := by
    simp [eval,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [after_item_shape] at normal
  obtain ⟨zero,continued⟩ := Input.literal_guard_normal source post _ (ofString "HdrErr") kind.flagError (flag≠0#64) read kind.afterFlag value normal
  have returned := checks_normal source post kind.checks (checks_pure kind) kind.returnExpression value continued
  have expected : eval source kind.returnExpression=some (kind.returnValue (pointer+header) payload) := by
    cases kind <;> simp [Kind.returnExpression,Kind.returnValue,eval,evalHOLExact,evalListHOLExact,localVar,toExact,itemCell,Rlp.Item.result]
  have actual := (Input.return_normal source post kind.returnExpression value returned).1
  exact ⟨not_not.mp zero,Option.some.inj (actual.symm.trans expected)⟩

/-- The whole original helper derives its returned string slice from the
real item decoder, rather than accepting a supplied future header result. -/
theorem body_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (pointer length cursor limit : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) :
    ∃ header payload,Rlp.Item.Valid pointer length.toNat (Rlp.Item.result pointer header payload 0#64) ∧ value=kind.returnValue (pointer+header) payload := by
  rw [body_shape] at normal
  obtain ⟨funded,parsed,header,payload,flag,inner,valid,nextArena,above,domain,endian,code,heap,cost,continued,endpoint⟩ :=
    Rlp.Item.scoped_normal_above source post pointer length cursor limit "it" arguments kind.afterItem args arena fits installed value normal
  let ready := Input.CallNormal.continuationEntry source parsed "it" (Rlp.Item.result pointer header payload flag)
  have cell : ready.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag) := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨zero,valueEq⟩ := after_item_normal_value ready inner kind pointer header payload flag cell value continued
  subst flag
  exact ⟨header,payload,valid,valueEq⟩

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.after_item_shape
#print axioms InitECandidate.Solver.Headers.Field.checks_pure
#print axioms InitECandidate.Solver.Headers.Field.after_item_normal_value
#print axioms InitECandidate.Solver.Headers.Field.body_normal_value
