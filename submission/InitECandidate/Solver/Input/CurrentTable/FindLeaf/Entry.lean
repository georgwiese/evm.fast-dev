import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Loop
import InitECandidate.Solver.Input.ScalarProgram
import InitECandidate.Solver.Input.LocalWord
import InitECandidate.Solver.WitnessRadix.AllocatedArena
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def tableAddress (offset : Nat) : ExpHOL 64 := Scalar.plus (localVar "t") offset
def bitsEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind source "keybits" 256#64
def nodesEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) := bind (bitsEntry source) "nodes" base
def rootEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base root : BitVec 64) := bind (nodesEntry source base) "n" root

def restoreEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (post : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "keybits" (restore (bitsEntry source) "nodes" (restore (nodesEntry source base) "n" post))

set_option maxRecDepth 100000 in
theorem body_shapes :
    body=.dec (ofString "keybits") .one (.panop .mul [.load .one (tableAddress 0),.const 8#64]) afterBits ∧
    afterBits=.dec (ofString "nodes") .one (.load .one (tableAddress 40)) afterNodes ∧
    afterNodes=.dec (ofString "n") .one (.load .one (tableAddress 56)) afterRoot ∧
    afterRoot=.seq loop (.return (localVar "n")) := by
  simp only [body,afterBits,afterNodes,afterRoot,loop,tableAddress,Scalar.plus,Guest.Software.guestFn_htab_find_leaf,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  trivial

theorem header_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table value : BitVec 64) (offset : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8=0)
    (inside : offset<88) (offsetAligned : offset%8=0)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (memory : source.memory (table+BitVec.ofNat 64 offset)=.word value) :
    eval source (.load .one (tableAddress offset))=some (.val (.word value)) :=
  Witness.load_word_read source _ _ _ (Scalar.plus_read source (localVar "t") table offset (Request.local_word source "t" table tableCell))
    (AllocatedBytes.word_mapped source table 88 offset domain arena inside aligned offsetAligned) memory

/-- The current three real table-header reads derive the bit marker,
node-array pointer and root; all declaration scopes are retained. -/
theorem setup_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table base root : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8=0)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.memory table=.word 32#64) (nodesCell : source.memory (table+40#64)=.word base)
    (rootCell : source.memory (table+56#64)=.word root) :
    evaluateHOLFiniteState source body=
      let output:=evaluateHOLFiniteState (rootEntry source base root) afterRoot
      (output.1,restoreEntry source base output.2) := by
  have keyRead:=header_read source table 32#64 0 domain arena aligned (by decide) (by decide) tableCell (by simpa only [BitVec.add_zero] using keyCell)
  have bitsRead : eval source (.panop .mul [.load .one (tableAddress 0),.const 8#64])=some (.val (.word 256#64)) := by
    simp only [eval] at keyRead
    simp only [eval]
    rw [evalHOLExact]
    simp only [evalListHOLExact,keyRead]
    rfl
  have firstTable : (bitsEntry source).locals.lookup (ofString "t")=some (.val (.word table)) :=
    (bind_lookup_other source "keybits" "t" 256#64 (by decide)).trans tableCell
  have nodesRead:=header_read (bitsEntry source) table base 40 domain arena aligned (by decide) (by decide) firstTable nodesCell
  have secondTable : (nodesEntry source base).locals.lookup (ofString "t")=some (.val (.word table)) :=
    (bind_lookup_other (bitsEntry source) "nodes" "t" base (by decide)).trans firstTable
  have rootRead:=header_read (nodesEntry source base) table root 56 domain arena aligned (by decide) (by decide) secondTable rootCell
  let output:=evaluateHOLFiniteState (rootEntry source base root) afterRoot
  have last : evaluateHOLFiniteState (nodesEntry source base) afterNodes=(output.1,restore (nodesEntry source base) "n" output.2) := by
    rw [body_shapes.2.2.1]
    exact ScalarScope.declare_execute (nodesEntry source base) output.2 "n" (.load .one (tableAddress 56)) root afterRoot output.1 rootRead rfl
  have middle : evaluateHOLFiniteState (bitsEntry source) afterBits=(output.1,restore (bitsEntry source) "nodes" (restore (nodesEntry source base) "n" output.2)) := by
    rw [body_shapes.2.1]
    exact ScalarScope.declare_execute (bitsEntry source) _ "nodes" (.load .one (tableAddress 40)) base afterNodes output.1 nodesRead last
  rw [body_shapes.1]
  exact ScalarScope.declare_execute source _ "keybits" (.panop .mul [.load .one (tableAddress 0),.const 8#64]) 256#64 afterBits output.1 bitsRead middle

theorem root_state (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base root : BitVec 64) : State source (rootEntry source base root) base root :=
  ⟨rfl,bind_lookup_same _ _ _,(bind_lookup_other (nodesEntry source base) "n" "nodes" root (by decide)).trans (bind_lookup_same _ _ _),
    (bind_lookup_other (nodesEntry source base) "n" "keybits" root (by decide)).trans
      ((bind_lookup_other (bitsEntry source) "nodes" "keybits" base (by decide)).trans (bind_lookup_same _ _ _))⟩

/-- The complete actual current find-leaf body is bounded by257source
clocks from its reached physical table and increasing-bit node image. No
successful key read, returned leaf or future lookup is assumed. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table base root : BitVec 64)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (image : Nodes source base valid bits left right) (present : root=0#64 ∨ valid root)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8=0)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.memory table=.word 32#64) (nodesCell : source.memory (table+40#64)=.word base)
    (rootCell : source.memory (table+56#64)=.word root) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤257 := by
  have state:=root_state source base root
  have price:=loop_cost image (source:=rootEntry source base root) ⟨root,state,present⟩
  have total:=ClockCost.sequence_current (rootEntry source base root) loop (.return (localVar "n")) 257 0 price (ClockCost.returned _ _)
  rw [←body_shapes.2.2.2] at total
  rw [setup_execute source table base root domain arena aligned tableCell keyCell nodesCell rootCell]
  exact total

/-- The current traversal changes no nonlocal field on any outcome,
including invalid table/key reads and short-clock loop timeouts. -/
theorem body_readonly (code) : LocalEffects.Preserves code body := by
  rw [body_shapes.1,body_shapes.2.1,body_shapes.2.2.1,body_shapes.2.2.2,shapes.1]
  exact LocalEffects.declared code _ _ _ _ (LocalEffects.declared code _ _ _ _ (LocalEffects.declared code _ _ _ _
    (LocalEffects.sequence code _ _ (LocalEffects.loop code _ _ (step_readonly code)) (LocalEffects.returned code _))))

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.body_shapes
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.setup_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.root_state
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.body_cost

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.body_readonly
