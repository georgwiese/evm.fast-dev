import InitECandidate.Solver.Headers.FieldResult

namespace InitECandidate.Solver.Headers.Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem check_passed (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (checks : List (ProgHOL 64))
    (pure : ∀ check∈checks,Input.PureGuard check) (expression : ExpHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (checks.foldr .seq (.return expression))=(some (.returned value),post)) :
    ∀ check∈checks,evaluateHOLFiniteState source check=(none,source) := by
  induction checks with
  | nil=>simp
  | cons check rest ih=>
    have current := pure check (by simp)
    have passed := current.normal_passed source post (rest.foldr .seq (.return expression)) value normal
    have tail := current.normal_continue source post (rest.foldr .seq (.return expression)) value normal
    have later := ih (by intro check member; exact pure check (by simp [member])) tail
    intro chosen member
    simp only [List.mem_cons] at member
    rcases member with rfl|member
    · exact passed
    · exact later chosen member

private theorem after_flag_run (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source kind.afterItem=(some (.returned value),post)) :
    evaluateHOLFiniteState source kind.afterFlag=(some (.returned value),post) := by
  rw [after_item_shape] at normal
  exact (Input.PureGuard.ite _ (.raise _ _) .skip).normal_continue source post kind.afterFlag value normal

/-- The original byte-field's real width check forces its decoded payload
length to equal the caller's current width operand on a normal return. -/
theorem bytes_width (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag width : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (widthCell : source.locals.lookup (ofString "width")=some (.val (.word width)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Kind.bytes.afterItem=(some (.returned value),post)) : payload=width := by
  have tail := after_flag_run source post .bytes value normal
  have read : eval source (.cmp .notEqual (.rfield 2 (localVar "it")) (localVar "width"))=
      some (.val (.word (if payload≠width then 1#64 else 0#64))) := by
    simp [eval,evalHOLExact,localVar,toExact,itemCell,widthCell,Rlp.Item.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  change evaluateHOLFiniteState source (.seq _ (.return _))=(some (.returned value),post) at tail
  have result := Input.literal_guard_normal source post _ (ofString "HdrErr") 7#64 (payload≠width) read _ value tail
  exact not_not.mp result.1

/-- The original uint-field's optional byte cap is derived from the actual
normal guard run, including its unrestricted zero-cap case. -/
theorem uint_max (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag maximum : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (maximumCell : source.locals.lookup (ofString "maxb")=some (.val (.word maximum)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Kind.uint.afterItem=(some (.returned value),post)) :
    maximum=0#64 ∨ payload.toNat≤maximum.toNat := by
  have tail := after_flag_run source post .uint value normal
  have passed := check_passed source post Kind.uint.checks (checks_pure .uint) Kind.uint.returnExpression value tail
  let capGuard : ProgHOL 64 := .ite (.cmp .notEqual (localVar "maxb") (.const 0#64))
    (.ite (.cmp .lower (localVar "maxb") (.rfield 2 (localVar "it"))) (.raise (ofString "HdrErr") (.const 3#64)) .skip) .skip
  have member : capGuard∈Kind.uint.checks := by
    change capGuard∈[_ , capGuard]
    simp
  have actual := passed capGuard member
  by_cases zero : maximum=0#64
  · exact Or.inl zero
  · refine Or.inr ?_
    by_contra outside
    have below : maximum<payload := by change maximum.toNat<payload.toNat; omega
    have branch : evaluateHOLFiniteState source capGuard=evaluateHOLFiniteState source (.raise (ofString "HdrErr") (.const 3#64)) := by
      simp [capGuard,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,itemCell,maximumCell,Rlp.Item.result,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero,below]
    rw [branch] at actual
    exact Input.raise_ne_none source (ofString "HdrErr") (.const 3#64) (congrArg Prod.fst actual)

end InitECandidate.Solver.Headers.Field

#print axioms InitECandidate.Solver.Headers.Field.bytes_width
#print axioms InitECandidate.Solver.Headers.Field.uint_max
