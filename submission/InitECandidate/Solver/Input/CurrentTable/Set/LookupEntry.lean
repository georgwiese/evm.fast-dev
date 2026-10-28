import InitECandidate.Solver.Input.CurrentTable.Set.Program
import InitECandidate.Solver.Input.CurrentTable.Image
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Route
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Empty
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ScopedCallClassified

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def lengthEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind source "klen" 32#64
def strideEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (lengthEntry source) "stride" 32#64

def restoreLookup (source post : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "klen" (restore (lengthEntry source) "stride" post)

/-- The actual first two mapped table loads reach htab_find_leaf with the
real lexical klen/stride scopes, rather than an independent selected entry. -/
theorem lookup_setup {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table))) :
    evaluateHOLFiniteState source body =
      let output := evaluateHOLFiniteState (strideEntry source) afterStride
      (output.1,restoreLookup source output.2) := by
  have lengthRead := FindLeaf.header_read source table 32#64 0 image.domain image.geometry.table image.aligned
    (by decide) (by decide) tableCell (by simpa only [BitVec.add_zero] using image.keyLength)
  have firstTable := (bind_lookup_other source "klen" "t" 32#64 (by decide)).trans tableCell
  have strideRead := FindLeaf.header_read (lengthEntry source) table 32#64 8 image.domain image.geometry.table image.aligned
    (by decide) (by decide) firstTable image.stride
  let output := evaluateHOLFiniteState (strideEntry source) afterStride
  have tail : evaluateHOLFiniteState (lengthEntry source) afterLength =
      (output.1,restore (lengthEntry source) "stride" output.2) := by
    rw [entry_shapes.2.1]
    exact ScalarScope.declare_execute _ _ "stride" _ 32#64 afterStride output.1 strideRead rfl
  rw [entry_shapes.1]
  exact ScalarScope.declare_execute source _ "klen" _ 32#64 afterLength output.1 lengthRead tail

def Found (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (query : KeyBits.Key) (root leaf : BitVec 64) : Prop :=
  (root = 0#64 ∧ leaf = 0#64) ∨ valid leaf ∧ bits leaf = 256 ∧ Route bits left right query root leaf

/-- Actual htab_set entry and first lookup, on every outcome. The reached
continuation gets zero for an empty image or a real leaf and query route;
all physical table/key/value invariants are preserved through that call. -/
theorem lookup_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cap root pointer : BitVec 64) (next count : Nat) (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat)
    (left right : BitVec 64 → BitVec 64) (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key) (ValueOf : BitVec 64 → Prop)
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (view : FirstDiff.ByteView source pointer query) (installed : OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body = (outcome,post)) :
    (source.clock-post.clock ≤ 258 ∧ ∀ value,outcome ≠ some (.returned value)) ∨
      ∃ target leaf inner,Found valid bits left right query root leaf ∧ LocalEffects.erase target = LocalEffects.erase source ∧
        target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 258 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry (strideEntry source) target "leaf" (.val (.word leaf))) afterLeaf = (outcome,inner) ∧
        post = restoreLookup source (restore (strideEntry source) "leaf" inner) := by
  let selected := strideEntry source
  have kept (name : String) (notLength : ofString "klen" ≠ ofString name) (notStride : ofString "stride" ≠ ofString name) :
      selected.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
    (bind_lookup_other (lengthEntry source) "stride" name 32#64 notStride).trans (bind_lookup_other source "klen" name 32#64 notLength)
  have args : evalListHOLFinite selected (h:=fun address => Classical.propDecidable (selected.memaddrs address)) [localVar "t",localVar "key"] =
      some [.val (.word table),.val (.word pointer)] := by
    have t := (kept "t" (by decide) (by decide)).trans tableCell
    have key := (kept "key" (by decide) (by decide)).trans keyCell
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,t,key]
  obtain ⟨callee,called,calleeTable,calleeKey⟩ := word_pair_environment selected.code.lookup (ofString "htab_find_leaf")
    (ofString "t") (ofString "key") FindLeaf.body .one table pointer (by decide) (FindLeaf.original_code selected.code installed)
  let entry := callEntryStateHOLFinite selected callee
  have ready : Image entry table cap root next count valid bits left right keys ValueOf := image.of_frame rfl
  have context := ready.lookup_context
  have price := context.price calleeTable
  rw [lookup_setup image tableCell] at run
  change (let output := evaluateHOLFiniteState selected afterStride;(output.1,restoreLookup source output.2)) = (outcome,post) at run
  let output := evaluateHOLFiniteState selected afterStride
  have observed := congrArg Prod.fst run
  have endpoint := congrArg Prod.snd run
  change restoreLookup source output.2 = post at endpoint
  have selectedRun : evaluateHOLFiniteState selected afterStride = (outcome,output.2) := Prod.ext observed rfl
  rw [entry_shapes.2.2.1] at selectedRun
  rcases CallNormal.scoped_classified selected output.2 "leaf" .one (ofString "htab_find_leaf") [localVar "t",localVar "key"] _
    FindLeaf.body afterLeaf callee .one 257 args called price outcome selectedRun with stopped | reached
  · have clock : post.clock = output.2.clock := by rw [←endpoint]; rfl
    exact Or.inl ⟨by rw [clock]; exact stopped.1,stopped.2⟩
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,restored⟩ := reached
    have answer : ∃ leaf,value = .val (.word leaf) ∧ Found valid bits left right query root leaf ∧
        LocalEffects.erase target = LocalEffects.erase source := by
      by_cases zero : root = 0#64
      · have empty := FindLeaf.body_empty entry table (New.nodesPointer table cap) ready.domain ready.geometry.table ready.aligned calleeTable
          ready.keyLength ready.nodesCell (by simpa only [zero] using ready.rootCell)
        have returned := (congrArg Prod.fst bodyRun).symm.trans empty.1
        have valueEq : value = .val (.word 0#64) := by
          simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using returned
        have frame := FindLeaf.body_readonly entry.code entry rfl
        rw [bodyRun] at frame
        exact ⟨0#64,valueEq,Or.inl ⟨zero,rfl⟩,frame⟩
      · have member := ready.rootMember.resolve_left zero
        obtain ⟨leaf,valueEq,member,marked,route,frame⟩ := context.returned_route ready.routing member calleeTable calleeKey (view.of_frame rfl) value bodyRun
        exact ⟨leaf,valueEq,Or.inr ⟨member,marked,route⟩,frame⟩
    obtain ⟨leaf,valueEq,found,frame⟩ := answer
    rw [valueEq] at continued
    exact Or.inr ⟨target,leaf,inner,found,frame,forward,cost,continued,
      by rw [←endpoint]; change restoreLookup source output.2 = _; rw [restored]⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.lookup_setup
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.lookup_trace
