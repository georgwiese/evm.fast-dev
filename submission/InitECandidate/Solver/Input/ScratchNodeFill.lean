import InitECandidate.Solver.Input.ScratchStore
import InitECandidate.Solver.Arenas.MarkCost
import InitECandidate.Solver.Input.DropLeading

/- The early-stop results in this module require a cursor at or below
sourceBase. This explicit unmapped-arena premise does not hold at current
main startup; mapped scratch paths need their own execution proofs. -/

namespace InitECandidate.Solver.Input.ScratchNodeFill
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn__node_rlp_fill with | .function fn => progToHOL fn.body | _ => .skip
def rest : ProgHOL 64 := Payload.dropLeading 3 body
def tail : ProgHOL 64 := .decCall (ofString "fr") .one (ofString "scratch_alloc") [.const 48#64]
  (.seq (.store (Scalar.plus (localVar "fr") 0) (.const 0#64)) rest)

theorem body_shape : body = .decCall (ofString "mark") .one (ofString "scratch_mark") [] tail := by
  simp only [body, rest, tail, Payload.dropLeading, Guest.Software.guestFn__node_rlp_fill, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Scalar.plus, localVar]

set_option maxRecDepth 100000 in
theorem installed (code) (current : OriginalCode.Installed code) :
    code.lookup (ofString "_node_rlp_fill") = some ([(ofString "node", .one)], body, .one) := by
  have found := OriginalCode.indexed code current 258
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn__node_rlp_fill) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body,
    Guest.Software.guestFn__node_rlp_fill, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using found

set_option maxRecDepth 100000 in
theorem mark_installed (code) (current : OriginalCode.Installed code) :
    code.lookup (ofString "scratch_mark") = some ([], Arenas.markBody .down, .one) := by
  have found := OriginalCode.indexed code current 9
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_scratch_mark) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Arenas.markBody,
    Guest.Software.guestFn_scratch_mark, shapeToHOL, List.map_nil] using found

/-- The actual node encoder cannot pass its first ordinary scratch store.
Its later traversal loop is never entered under the real arena/domain facts. -/
theorem no_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer limit : BitVec 64) (value : ValueHOL 64)
    (pointerBound : pointer.toNat ≤ InitE.sourceBase) (ordered : limit ≤ pointer) (aligned : limit.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (current : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    evaluateHOLFiniteState source body ≠ (some (.returned value), post) := by
  intro actual
  rw [body_shape] at actual
  have positive := CallNormal.normal_clock source post (ofString "mark") .one (ofString "scratch_mark") [] tail value actual
  have marked := Arenas.mark_call source .down "mark" pointer tail (mark_installed source.code current) pointerGlobal positive
  simp only [Arenas.markName] at marked
  rw [marked] at actual
  let ready := bind {source with clock := source.clock - 1} "mark" pointer
  let output := evaluateHOLFiniteState ready tail
  have observed : output.1 = some (.returned value) := congrArg Prod.fst actual
  have run : evaluateHOLFiniteState ready tail = (some (.returned value), output.2) := Prod.ext observed rfl
  exact ScratchStore.allocated_no_return ready output.2 pointer limit 48 0 "fr" 0#64 rest value (by decide) (by decide)
    pointerBound ordered aligned domain current pointerGlobal limitGlobal run

/-- Every outcome, including allocation/trap failure and missing clocks,
spends at most three source ticks before this current scratch-store boundary. -/
theorem price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer limit : BitVec 64)
    (pointerBound : pointer.toNat ≤ InitE.sourceBase) (ordered : limit ≤ pointer) (aligned : limit.toNat % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain) (current : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 3 := by
  rw [body_shape]
  apply Arenas.mark_price_reached source .down "mark" pointer tail 2
    (mark_installed source.code current) pointerGlobal
  let ready := bind {source with clock := source.clock - 1} "mark" pointer
  change ready.clock - (evaluateHOLFiniteState ready tail).2.clock ≤ 2
  exact ScratchStore.allocated_price ready pointer limit 48 0 "fr" 0#64 rest (by decide) (by decide)
    pointerBound ordered aligned domain current pointerGlobal limitGlobal

end InitECandidate.Solver.Input.ScratchNodeFill

#print axioms InitECandidate.Solver.Input.ScratchNodeFill.body_shape
#print axioms InitECandidate.Solver.Input.ScratchNodeFill.installed
#print axioms InitECandidate.Solver.Input.ScratchNodeFill.mark_installed
#print axioms InitECandidate.Solver.Input.ScratchNodeFill.no_return
#print axioms InitECandidate.Solver.Input.ScratchNodeFill.price
