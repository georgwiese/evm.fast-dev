import InitECandidate.Solver.Mpt.InsertEmptyFields
import InitECandidate.Solver.Mpt.LeafRegistration

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real normal insertion into the empty root establishes a closed
physical leaf graph and its current value contract. No future traversal
or constructor success is assumed. -/
theorem empty_graph (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word 0#64)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word 0#64)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (fits : key.toNat+min length.toNat 64<2^64)
    (mapped : ∀ offset<min length.toNat 64,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word heap) ∧ source.clock-target.clock≤3 ∧
      ∃ graph : TrieWalk.Graph target.memory target.memaddrs,
        (∀ node,graph.valid node ↔ node=0#64 ∨ node=heap) ∧
        graph.valid heap ∧ graph.Regions heap.toNat (PersistentAlloc.rounded heap 64#64).toNat ∧ graph.Disjoint ∧
        Nonempty (TrieWalk.Values graph limit property) := by
  obtain ⟨arena,answer,cost,globals,nextArena,nextAligned,before,cells,oldMemory⟩:=
    empty_physical source target heap key length pointer size nodeCell keyCell lengthCell levelCell pointerCell sizeCell
      installed domain heapCell frontier aligned value normal
  obtain ⟨_,_,_,_,frame⟩:=empty_normal source target heap key length pointer size nodeCell keyCell lengthCell levelCell pointerCell sizeCell
    installed domain heapCell frontier aligned value normal
  have domainEq:=congrArg PanSemStateFiniteExact.memaddrs frame
  change target.memaddrs=source.memaddrs at domainEq
  have targetDomain : target.memaddrs=InitE.ordinaryDomain:=domainEq.trans domain
  have tag : target.memory heap=.word 1#64:=by
    simpa [FieldStores.Value.word] using cells ⟨0,.literal 1#64⟩ (by simp [NodeConstructor.fields])
  have storedKey : target.memory (heap+32#64)=.word key:=by
    simpa [FieldStores.Value.word,NodeConstructor.leafWords] using
      cells ⟨32,.saved "nib" key⟩ (by simp [NodeConstructor.fields,NodeConstructor.leafWords])
  have storedLength : target.memory (heap+40#64)=.word length:=by
    simpa [FieldStores.Value.word,NodeConstructor.leafWords] using
      cells ⟨40,.saved "nlen" length⟩ (by simp [NodeConstructor.fields,NodeConstructor.leafWords])
  have storedPointer : target.memory (heap+48#64)=.word pointer:=by
    simpa [FieldStores.Value.word,NodeConstructor.leafWords] using
      cells ⟨48,.saved "vptr" pointer⟩ (by simp [NodeConstructor.fields,NodeConstructor.leafWords])
  have storedSize : target.memory (heap+56#64)=.word size:=by
    simpa [FieldStores.Value.word,NodeConstructor.leafWords] using
      cells ⟨56,.saved "vlen" size⟩ (by simp [NodeConstructor.fields,NodeConstructor.leafWords])
  let base:=TrieWalk.Graph.empty target.memory target.memaddrs
  let data:=TrieWalk.Registration.leaf target base heap key length targetDomain arena aligned tag storedKey storedLength fits
    (by rw [domainEq]; exact mapped)
  let graph:=base.register heap data
  have leafTag : wordAt target.memory heap=1#64:=by simp [wordAt,tag,MemoryBytes.wordBits]
  have registeredRegions : graph.Regions heap.toNat (PersistentAlloc.rounded heap 64#64).toNat:=
    TrieWalk.Graph.Regions.register base heap data _ _ (TrieWalk.Graph.Regions.empty _ _ _ _) (Nat.le_refl _)
      (by rw [leafTag]; exact arena) aligned (by rw [leafTag]; exact before)
  have registeredDisjoint : graph.Disjoint:=
    TrieWalk.Graph.Disjoint.register base heap data (TrieWalk.Graph.Disjoint.empty _ _)
      (by intro old oldMember oldActive different; exact (oldActive oldMember).elim)
  let leafValue:=TrieWalk.ValueView.leaf target heap pointer size limit property targetDomain arena aligned storedPointer storedSize
    (by rw [domainEq]; exact payload) extra
  let registeredValues:=TrieWalk.Values.register base heap data limit (TrieWalk.Values.empty _ _ limit property)
    (fun _=>leafValue) (fun _ notLeaf _=>(notLeaf leafTag).elim)
  exact ⟨answer,cost,graph,(fun _=>Iff.rfl),Or.inr rfl,registeredRegions,registeredDisjoint,⟨registeredValues⟩⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.empty_graph
