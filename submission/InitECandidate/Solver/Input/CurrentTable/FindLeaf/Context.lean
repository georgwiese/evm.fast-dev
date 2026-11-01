import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Entry
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Exit
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ClockCostTerminatingCall
import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Reached physical current traversal entry. The insertion proof must
supply its node image; key-byte mapping and future leaf success are absent. -/
structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table base root : BitVec 64)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64) (width : BitVec 64:=32#64) : Prop where
  image : Nodes source base valid bits left right (width*8#64).toNat
  present : root=0#64 ∨ valid root
  domain : source.memaddrs=InitE.ordinaryDomain
  arena : AllocatedBytes.Arena table 88
  aligned : table.toNat%8=0
  keyCell : source.memory table=.word width
  nodesCell : source.memory (table+40#64)=.word base
  rootCell : source.memory (table+56#64)=.word root

theorem Context.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {table base root : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {width : BitVec 64}
    (ready : Context source table base root valid bits left right width) (same : LocalEffects.erase target=LocalEffects.erase source) :
    Context target table base root valid bits left right width := by
  have memory:=LocalEffects.memory_of_erase source target same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs=source.memaddrs at domain
  exact ⟨ready.image.of_frame same,ready.present,domain.trans ready.domain,ready.arena,ready.aligned,
    by rw [memory]; exact ready.keyCell,by rw [memory]; exact ready.nodesCell,by rw [memory]; exact ready.rootCell⟩

/-- The actual scalar-width traversal uses its own word-valued marker. -/
theorem Context.width_price {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table base root width : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (ready : Context source table base root valid bits left right width)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤(width*8#64).toNat+1 :=
  body_width_cost source table base root width valid bits left right ready.image ready.present ready.domain ready.arena ready.aligned tableCell ready.keyCell ready.nodesCell ready.rootCell

theorem Context.price {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table base root : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (ready : Context source table base root valid bits left right)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤257 :=
  body_cost source table base root valid bits left right ready.image ready.present ready.domain ready.arena ready.aligned tableCell ready.keyCell ready.nodesCell ready.rootCell

/-- Any genuine returned value is zero or an actual leaf at the declared
marker in the same node image; physical memory/globals remain intact. -/
theorem Context.width_returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table base root : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {width : BitVec 64}
    (ready : Context source table base root valid bits left right width)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ leaf,value=.val (.word leaf) ∧ (leaf=0#64 ∨ valid leaf ∧ bits leaf=(width*8#64).toNat) ∧ LocalEffects.erase post=LocalEffects.erase source := by
  have original:=normal
  rw [setup_width_execute width source table base root ready.domain ready.arena ready.aligned tableCell ready.keyCell ready.nodesCell ready.rootCell] at normal
  let afterPost:=(evaluateHOLFiniteState (rootEntry source base root (width*8#64)) afterRoot).2
  have observed:=congrArg Prod.fst normal
  dsimp only at observed
  have afterRun : evaluateHOLFiniteState (rootEntry source base root (width*8#64)) afterRoot=(some (.returned value),afterPost) := Prod.ext observed rfl
  have initial : Invariant source base valid (rootEntry source base root (width*8#64)) (width*8#64) := ⟨root,root_state source base root (width*8#64),ready.present⟩
  rw [body_shapes.2.2.2] at afterRun
  obtain ⟨loopPost,loopRun,returnedRun⟩:=sequence_returned (rootEntry source base root (width*8#64)) afterPost loop (.return (localVar "n")) value
    (loop_never ready.image initial) afterRun
  obtain ⟨leaf,state,finished⟩:=loop_finished ready.image initial loopRun
  have expected : evaluateHOLFiniteState loopPost (.return (localVar "n"))=
      (some (.returned (.val (.word leaf))),emptyLocalsHOLFinite loopPost) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,state.nodeCell,shapeOfHOLExact]
  rw [expected] at returnedRun
  have answer : value=.val (.word leaf) := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst returnedRun).symm
  have frame:=body_readonly source.code source rfl
  rw [original] at frame
  exact ⟨leaf,answer,finished,frame⟩

theorem Context.returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table base root : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (ready : Context source table base root valid bits left right)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ leaf,value=.val (.word leaf) ∧ (leaf=0#64 ∨ valid leaf ∧ bits leaf=256) ∧ LocalEffects.erase post=LocalEffects.erase source :=
  ready.width_returned tableCell value normal

/-- A dynamic physical table header and numeric node range. Neither a
startup cursor nor increasing bit positions are part of this contract. -/
structure RangeContext (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table base root width : BitVec 64) (limit : Nat)
    (bits left right : BitVec 64 → BitVec 64) : Prop where
  image : RangeNodes source base (width * 8#64) limit bits left right
  inside : root.toNat < limit
  domain : source.memaddrs = InitE.ordinaryDomain
  arena : AllocatedBytes.Arena table 88
  aligned : table.toNat % 8 = 0
  keyCell : source.memory table = .word width
  nodesCell : source.memory (table + 40#64) = .word base
  rootCell : source.memory (table + 56#64) = .word root

theorem RangeContext.of_cells {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base root width : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (ready : RangeContext source table base root width limit bits left right)
    (domain : target.memaddrs = source.memaddrs)
    (header : ∀ offset, (offset = 0 ∨ offset = 40 ∨ offset = 56) →
      target.memory (table + BitVec.ofNat 64 offset) = source.memory (table + BitVec.ofNat 64 offset))
    (nodes : ∀ node, node ≠ 0#64 → node.toNat < limit → ∀ offset,
      (offset = 24 ∨ bits node ≠ width * 8#64 ∧ (offset = 8 ∨ offset = 16)) →
      target.memory (cell base node offset) = source.memory (cell base node offset)) :
    RangeContext target table base root width limit bits left right := by
  have keySame : target.memory table = source.memory table := by
    simpa only [BitVec.add_zero] using header 0 (Or.inl rfl)
  exact ⟨ready.image.of_cells domain nodes, ready.inside, domain.trans ready.domain, ready.arena, ready.aligned,
    keySame.trans ready.keyCell, (header 40 (Or.inr (Or.inl rfl))).trans ready.nodesCell,
    (header 56 (Or.inr (Or.inr rfl))).trans ready.rootCell⟩

theorem RangeContext.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base root width : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (ready : RangeContext source table base root width limit bits left right)
    (same : LocalEffects.erase target = LocalEffects.erase source) :
    RangeContext target table base root width limit bits left right := by
  have domain := congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs = source.memaddrs at domain
  exact ready.of_cells domain
    (by intro offset needed; exact congrFun (LocalEffects.memory_of_erase source target same) _)
    (by intro node nonzero inside offset needed; exact congrFun (LocalEffects.memory_of_erase source target same) _)

/-- Reuse an established ordered image when its live nodes exactly cover
the numeric range. Later dynamic producers may establish RangeNodes directly. -/
theorem Context.to_range {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base root width : BitVec 64} {limit : Nat}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (ready : Context source table base root valid bits left right width) (positive : 0 < limit)
    (bounded : ∀ node, valid node → node.toNat < limit)
    (complete : ∀ node, node ≠ 0#64 → node.toNat < limit → valid node) :
    RangeContext source table base root width limit (fun node => BitVec.ofNat 64 (bits node)) left right := by
  have internal : ∀ node, valid node → BitVec.ofNat 64 (bits node) ≠ width * 8#64 →
      bits node < (width * 8#64).toNat := by
    intro node member different
    have upper := ready.image.bitBound node member
    have unequal : bits node ≠ (width * 8#64).toNat := by
      intro equal
      apply different
      simp only [equal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    omega
  have image : RangeNodes source base (width * 8#64) limit (fun node => BitVec.ofNat 64 (bits node)) left right := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro node nonzero inside
      exact ready.image.bitMapped node (complete node nonzero inside)
    · intro node nonzero inside
      exact ready.image.bitCell node (complete node nonzero inside)
    · intro node nonzero inside different
      exact ready.image.leftMapped node (complete node nonzero inside) (internal node (complete node nonzero inside) different)
    · intro node nonzero inside different
      exact ready.image.rightMapped node (complete node nonzero inside) (internal node (complete node nonzero inside) different)
    · intro node nonzero inside different
      exact ready.image.leftCell node (complete node nonzero inside) (internal node (complete node nonzero inside) different)
    · intro node nonzero inside different
      exact ready.image.rightCell node (complete node nonzero inside) (internal node (complete node nonzero inside) different)
    · intro node nonzero inside different
      rcases ready.image.leftOrdered node (complete node nonzero inside) (internal node (complete node nonzero inside) different) with zero | child
      · simpa only [zero, BitVec.toNat_ofNat] using positive
      · exact bounded _ child.1
    · intro node nonzero inside different
      rcases ready.image.rightOrdered node (complete node nonzero inside) (internal node (complete node nonzero inside) different) with zero | child
      · simpa only [zero, BitVec.toNat_ofNat] using positive
      · exact bounded _ child.1
  have rootInside : root.toNat < limit := by
    rcases ready.present with zero | member
    · simpa only [zero, BitVec.toNat_ofNat] using positive
    · exact bounded root member
  exact ⟨image, rootInside, ready.domain, ready.arena, ready.aligned, ready.keyCell, ready.nodesCell, ready.rootCell⟩

theorem RangeContext.price {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base root width pointer : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (ready : RangeContext source table base root width limit bits left right)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (pointerCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (notTimeout : (evaluateHOLFiniteState source body).1 ≠ some .timeOut) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ limit :=
  range_body_cost source table base root width pointer limit bits left right ready.image ready.inside
    ready.domain ready.arena ready.aligned tableCell pointerCell ready.keyCell ready.nodesCell ready.rootCell notTimeout

theorem RangeContext.returned {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base root width pointer : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (ready : RangeContext source table base root width limit bits left right)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (pointerCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ leaf, value = .val (.word leaf) ∧ leaf.toNat < limit ∧
      (leaf = 0#64 ∨ bits leaf = width * 8#64) ∧ LocalEffects.erase post = LocalEffects.erase source := by
  have original := normal
  rw [setup_width_execute width source table base root ready.domain ready.arena ready.aligned tableCell ready.keyCell ready.nodesCell ready.rootCell] at normal
  let entry := rootEntry source base root (width * 8#64)
  let afterPost := (evaluateHOLFiniteState entry afterRoot).2
  have observed := congrArg Prod.fst normal
  have afterRun : evaluateHOLFiniteState entry afterRoot = (some (.returned value), afterPost) := Prod.ext observed rfl
  have entryKey : entry.locals.lookup (ofString "key") = some (.val (.word pointer)) :=
    (bind_lookup_other (nodesEntry source base (width * 8#64)) "n" "key" root (by decide)).trans
      ((bind_lookup_other (bitsEntry source (width * 8#64)) "nodes" "key" base (by decide)).trans
        ((bind_lookup_other source "keybits" "key" (width * 8#64) (by decide)).trans pointerCell))
  rw [body_shapes.2.2.2] at afterRun
  obtain ⟨loopPost, loopRun, returnedRun⟩ := sequence_returned entry afterPost loop (.return (localVar "n")) value
    (loop_never_any entry) afterRun
  obtain ⟨leaf, state, keyCell, inside, finished⟩ := range_loop_finished ready.image
    ⟨root, root_state source base root (width * 8#64), entryKey, ready.inside⟩ loopRun
  have expected : evaluateHOLFiniteState loopPost (.return (localVar "n")) =
      (some (.returned (.val (.word leaf))), emptyLocalsHOLFinite loopPost) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, localVar, state.nodeCell, shapeOfHOLExact]
  rw [expected] at returnedRun
  have answer : value = .val (.word leaf) := by
    simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using (congrArg Prod.fst returnedRun).symm
  have frame := body_readonly source.code source rfl
  rw [original] at frame
  exact ⟨leaf, answer, inside, finished, frame⟩

/-- The actual original ignored/assigned call inherits the same conditional
bound through its real argument evaluation, callee and returned result. -/
theorem RangeContext.call_price {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {table base root width pointer : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (ready : RangeContext source table base root width limit bits left right)
    (installed : OriginalCode.Installed source.code) (destination : Option (Option MlS))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word table), .val (.word pointer)])
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "htab_find_leaf") arguments) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ limit + 1 := by
  obtain ⟨callee, called, tableCell, pointerCell⟩ := word_pair_environment source.code.lookup
    (ofString "htab_find_leaf") (ofString "t") (ofString "key") body .one table pointer (by decide)
    (original_code source.code installed)
  have current : RangeContext (callEntryStateHOLFinite source callee) table base root width limit bits left right := ready.of_frame rfl
  exact ClockCost.call_current_terminating source post destination (ofString "htab_find_leaf") arguments _ body callee .one limit args called
    (by intro observed target evaluated noTimeout
        have observedNotTimeout : (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).1 ≠ some .timeOut := by
          rw [evaluated]
          exact noTimeout
        have price := current.price tableCell pointerCell observedNotTimeout
        rw [evaluated] at price
        exact price)
    result run notTimeout

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context.price
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context.returned

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context.width_price
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context.width_returned
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.RangeContext.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.RangeContext.price
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.RangeContext.call_price
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context.to_range
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.RangeContext.returned
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.RangeContext.of_cells
