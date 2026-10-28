import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Entry
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.LocalEffectsScoped

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual current scoped caller adds one tick to the257-tick
traversal allowance. Invalid key reads and every stopped outcome are covered;
the original continuation keeps its separately supplied allowance. -/
theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table key base root : BitVec 64)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (image : Nodes source base valid bits left right) (present : root=0#64 ∨ valid root)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8=0)
    (keyCell : source.memory table=.word 32#64) (nodesCell : source.memory (table+40#64)=.word base)
    (rootCell : source.memory (table+56#64)=.word root)
    (installed : OriginalCode.Installed source.code) (name : MlS) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word table),.val (.word key)])
    (tail : ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall name .one (ofString "htab_find_leaf") expressions continuation)).2.clock≤257+tailPrice+1 := by
  obtain ⟨callee,called,tableCell,keyLocal⟩:=word_pair_environment source.code.lookup (ofString "htab_find_leaf") (ofString "t") (ofString "key") body .one table key (by decide) (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have next : Nodes entry base valid bits left right := image.of_frame rfl
  have price:=body_cost entry table base root valid bits left right next present domain arena aligned tableCell keyCell nodesCell rootCell
  exact ClockCost.scoped_current source name .one (ofString "htab_find_leaf") expressions _ body continuation callee .one 257 tailPrice args called price tail

/-- Original scoped find-leaf callers retain the entire physical state
when their continuation does, independent of any node/key validity premise. -/
theorem scoped_readonly (code) (installed : OriginalCode.Installed code) (name : MlS) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (tail : LocalEffects.Preserves code continuation) :
    LocalEffects.Preserves code (.decCall name .one (ofString "htab_find_leaf") expressions continuation) :=
  LocalEffects.scoped_body code name .one (ofString "htab_find_leaf") expressions continuation formals body .one
    (original_code code installed) (body_readonly code) tail

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scoped_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scoped_readonly
