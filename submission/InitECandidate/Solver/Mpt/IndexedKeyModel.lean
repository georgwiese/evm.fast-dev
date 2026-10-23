import InitECandidate.Solver.Mpt.IndexedLoopModel
import InitECandidate.Solver.Mpt.IndexedKeyNormal
import InitECandidate.Solver.Mpt.TrieGraphPathBand
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual scoped key encoder changes only its fixed scratch bytes.
It retains the complete live map, graph and original input rows, while
deriving the current one-to-nine-byte key length from the real return. -/
theorem key_model (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (m array : BitVec 64)
    (count cutoff limit : Nat) (slices : Nat→BitVec 64×BitVec 64) (property : BitVec 64→BitVec 64→Prop)
    (model : LoopModel source m array count cutoff limit slices property)
    (reached : Input.CallPrefix.Reaches source (.scoped (ofString "klen") .one (ofString "rlp_encode_word") keyArguments) target) :
    ∃ (encoded : Nat) (next : LoopModel target m array count cutoff limit slices property),
      1≤encoded ∧ encoded≤9 ∧ target.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      next.index=model.index ∧ next.heap=model.heap ∧ source.clock-target.clock≤19 ∧
      (∀ query : BitVec 64,2713731432≤query.toNat→query.toNat<cutoff→target.memory query=source.memory query) := by
  obtain ⟨encoded,memory,clock,positive,small,price,targetEq,framed⟩:=key_normal model.index model.installed model.domain model.bindings model.indexCell reached
  subst target
  let current:=bind {source with memory:=memory,clock:=clock} "klen" (BitVec.ofNat 64 encoded)
  have band : ∀ query : BitVec 64,cutoff≤query.toNat→query.toNat<model.heap.toNat→current.memory query=source.memory query:=by
    intro query above _before
    exact framed query (Or.inr (by have lower:=model.cutoffLower; omega))
  obtain ⟨next,same,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=model.graph.after_path_band source current limit cutoff cutoff model.heap.toNat cutoff property
    model.values model.regions model.disjoint model.paths model.pathRegions model.separated model.cutoffAligned (Nat.le_refl _) (Nat.le_refl _) rfl rfl band
  have fields : model.graph.PathFields current.memory:=TrieWalk.Graph.PathFields.of_agreement model.graph current.memory (by
    intro query required
    have bounds:=model.graph.footprint_bounds cutoff model.heap.toNat model.regions query required
    exact band query bounds.1 bounds.2)
  have rootKept : current.memory m=source.memory m:=framed m (Or.inr (by have a:=model.headerAbove; have b:=model.cutoffLower; omega))
  have flagNumber : (m+8#64).toNat=m.toNat+8:=byteAddress_toNat m 8 (by have upper:=model.header.arena.upper; omega)
  have flagKept : current.memory (m+8#64)=source.memory (m+8#64):=framed (m+8#64) (Or.inr (by rw [flagNumber]; have a:=model.headerAbove; have b:=model.cutoffLower; omega))
  have nextHeader : SetTrie.Header current next m model.root 0#64:=⟨model.header.arena,model.header.aligned,rootKept.trans model.header.rootStored,flagKept.trans model.header.flagStored,
    by rw [same]; exact model.header.member,model.header.rootSafe.of_fields model.graph next m same fields,model.header.flagSafe.of_fields model.graph next (m+8#64) same fields⟩
  have rows:=model.rows.of_band source current array count cutoff limit slices property rfl (by intro query above _before; exact framed query (Or.inr (by omega)))
  let out : LoopModel current m array count cutoff limit slices property:={ model with
    indexCell:=(bind_lookup_other _ "klen" "i" _ (by decide)).trans model.indexCell
    countCell:=(bind_lookup_other _ "klen" "n" _ (by decide)).trans model.countCell
    mCell:=(bind_lookup_other _ "klen" "m" _ (by decide)).trans model.mCell
    arrayCell:=(bind_lookup_other _ "klen" "slice_arr" _ (by decide)).trans model.arrayCell
    bindings:=model.bindings.of_heap_globals source current (HeapGlobals.refl source)
    hash:=model.hash.of_fields source current 2713714976#64 2713715176#64 rfl rfl rfl (HeapGlobals.refl source)
    scratch:=model.scratch.of_fields source current 2713714688#64 2701135872#64 rfl rfl
    rows:=rows
    graph:=next
    values:=nextValues
    regions:=nextRegions
    disjoint:=nextDisjoint
    paths:=nextPaths
    pathRegions:=nextPathRegions
    separated:=nextSeparated
    header:=nextHeader }
  exact ⟨encoded,out,positive,small,bind_lookup_same _ _ _,rfl,rfl,price,by intro query above before; exact framed query (Or.inr (by omega))⟩

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.key_model
