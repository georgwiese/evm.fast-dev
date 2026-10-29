import InitECandidate.Solver.Mpt.SplitExtensionChoices

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_branch_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap branch segment prefixLength oldLength child key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat segment oldLength.toNat)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (queryBound : prefixLength.toNat≤length.toNat)
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (strict : prefixLength.toNat<oldLength.toNat) (floor : nodeLower≤heap.toNat)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (oldLengthCell : source.locals.lookup (ofString "sl")=some (.val (.word oldLength)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (branchMember : graph.valid branch) (branchActive : branch≠0#64) (tag : wordAt source.memory branch=3#64) (childMember : graph.valid child)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterBranch=(some (.returned value),target)) :
    value=.val (.word branch) ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      (∀ query : BitVec 64,query.toNat<branch.toNat → target.memory query=source.memory query) ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ wordAt target.memory branch=3#64 ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,
          (∀ node,graph.valid node → next.valid node) ∧ next.valid branch ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
          Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway segment oldLength.toNat address → TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) ∧ graph.CacheFrame target.memory := by
  have subtraction : (oldLength-prefixLength).toNat=oldLength.toNat-prefixLength.toNat:=BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have suffix:=buffer.window graph source.be pathLower heap.toNat segment prefixLength oldLength.toNat (oldLength-prefixLength).toNat (by omega) (by rw [subtraction])
  have positive : 0<(oldLength-prefixLength).toNat:=by rw [subtraction]; omega
  have read : eval source oldRemainder=some (.val (.word (oldLength-prefixLength))):=by
    simp [oldRemainder,eval,evalHOLExact,toExact,localVar,oldLengthCell,prefixCell,evalListHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [entry_shapes.2.2.2.2] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source target "sal" oldRemainder (oldLength-prefixLength) oldChoices value read normal
  let ready:=QueryBranch.bind source "sal" (oldLength-prefixLength)
  have current (name : String) (other : ofString "sal"≠ofString name) : ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    bind_lookup_other source "sal" name _ other
  have remainingCell : ready.locals.lookup (ofString "sal")=some (.val (.word (oldLength-prefixLength))):=bind_lookup_same source "sal" _
  obtain ⟨answer,domainEq,endianEq,codeEq,memory,finalHeap,finalHeapCell,finalArena,finalAligned,grows,finalTag,next,members,member,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,provenance,finalProtection,caches⟩:=
    choices_normal ready inner heap branch segment prefixLength (oldLength-prefixLength) child key length pointer size graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated suffix query queryBound
      ((current _ (by decide)).trans keyCell) ((current _ (by decide)).trans lengthCell) ((current _ (by decide)).trans pointerCell) ((current _ (by decide)).trans sizeCell)
      payload extra positive floor ((current _ (by decide)).trans branchCell) ((current _ (by decide)).trans segmentCell) ((current _ (by decide)).trans prefixCell)
      remainingCell ((current _ (by decide)).trans childCell) branchMember branchActive tag childMember domain heapCell frontier aligned installed value continued
  rw [endpoint]
  exact ⟨answer,domainEq,endianEq,codeEq,memory,finalHeap,finalHeapCell,finalArena,finalAligned,grows,finalTag,next,members,member,
    nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,provenance,
    (by
      intro address safe before oldAway queryAway
      exact finalProtection address safe before
        (oldAway.window segment prefixLength address oldLength.toNat _ (by omega) (by rw [subtraction])) queryAway),caches⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.after_branch_normal
