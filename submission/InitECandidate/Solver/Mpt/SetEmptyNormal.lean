import InitECandidate.Solver.Mpt.SetEmptyAfterKeyNormal
import InitECandidate.Solver.Mpt.SetKeyEntry

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The complete real empty unsecured setter establishes a physical leaf
graph at its actual final state. The key allocation, leaf allocation, root
store, live heap and value registry all come from the original normal run. -/
theorem empty_unsecured_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m key heap pointer size : BitVec 64) (length : Nat) (small : length≤32)
    (installed : Input.OriginalCode.Installed source.code)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (mCell : source.locals.lookup (ofString "m")=some (.val (.word m)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word (BitVec.ofNat 64 length))))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (pointerActive : pointer≠0#64) (sizeActive : size≠0#64)
    (rootMapped : source.memaddrs m) (emptyRoot : source.memory m=.word 0#64) (older : m.toNat<heap.toNat)
    (securedMapped : source.memaddrs (m+8#64)) (unsecured : source.memory (m+8#64)=.word 0#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (inputArena : AllocatedBytes.Arena key length) (before : key.toNat+length≤heap.toNat)
    (limit : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    let leaf:=PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))
    let finalHeap:=PersistentAlloc.rounded leaf 64#64
    value=.val (.word 0#64) ∧ target.memory m=.word leaf ∧ source.clock-target.clock≤length/4+10 ∧
      target.globals=source.globals.update (ofString "heap_ptr",.val (.word finalHeap)) ∧
      AllocatedBytes.Arena leaf 64 ∧ AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ leaf.toNat+64≤finalHeap.toNat ∧
      ∃ graph : TrieWalk.Graph target.memory target.memaddrs,
        (∀ node,graph.valid node ↔ node=0#64 ∨ node=leaf) ∧ graph.valid leaf ∧
        graph.Regions leaf.toNat finalHeap.toNat ∧ graph.Disjoint ∧ Nonempty (TrieWalk.Values graph limit property) := by
  let amount:=BitVec.ofNat 64 (2*length)
  let leaf:=PersistentAlloc.rounded heap amount
  let finalHeap:=PersistentAlloc.rounded leaf 64#64
  have amountNumber : amount.toNat=2*length:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨current,inner,trace,endpoint,continued⟩:=key_trace source target value normal
  have ending:=trace.erase afterKey
  simp only [actions,Input.CallPrefix.program] at ending
  rw [body_shape] at normal
  rw [normal,continued] at ending
  obtain ⟨middle,first,last⟩:=trace.head
  have sameCurrent : current=middle:=by cases last; rfl
  subst current
  obtain ⟨keyArena,nk,saved,view,keyCost,frame,memory⟩:=NibbleKey.scoped_normal (ofString "nk") keyArguments m key heap length small installed domain little
    (key_arguments source m key length mCell keyCell lengthCell) securedMapped unsecured heapCell frontier aligned inputArena before first
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change middle.globals=source.globals.update (ofString "heap_ptr",.val (.word leaf)) at globals
  have runtime:=first.runtime
  have middleDomain : middle.memaddrs=source.memaddrs:=runtime.1
  have middleInstalled : Input.OriginalCode.Installed middle.code:=by rw [runtime.2.2.2.1]; exact installed
  have nextCell : middle.globals.lookup (ofString "heap_ptr")=some (.val (.word leaf)):=by
    rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]
  have growth:=PersistentAlloc.guards heap amount (by rw [amountNumber]; exact keyArena.upper)
  have leafGrows : heap.toNat+2*length≤leaf.toNat:=by
    have grows:=growth.2.2.1
    change heap.toNat+amount.toNat≤leaf.toNat at grows
    rwa [amountNumber] at grows
  have leafUpper : leaf.toNat≤33806089496:=growth.2.2.2.1
  have leafFrontier : AllocatedBytes.Arena leaf 0:=
    ⟨by have lower:=keyArena.lower; omega,by omega⟩
  have leafAligned : leaf.toNat%8=0:=growth.2.2.2.2
  have mBeforeLeaf : m.toNat<leaf.toNat:=by omega
  have keyFits : heap.toNat+min amount.toNat 64<2^64:=by
    have fits:=view.fits
    have bound:=Nat.min_le_left amount.toNat 64
    rw [amountNumber] at bound
    omega
  have keyMapped : ∀ offset<min amount.toNat 64,middle.memaddrs (panByteAlignHOL (width:=64) (byteAddress heap offset)):=by
    intro offset inside
    apply view.mapped
    have bound:=Nat.min_le_left amount.toNat 64
    rw [amountNumber] at bound
    omega
  obtain ⟨answer,stored,cost,finalGlobals,arena,finalArena,finalAligned,leafBefore,graph,valid,member,regions,disjoint,values⟩:=
    after_key_empty_normal middle inner m leaf heap amount pointer size middleInstalled (middleDomain.trans domain)
      ((saved _ (by decide)).trans mCell) (by rw [middleDomain]; exact rootMapped) ((memory m (Or.inl older)).trans emptyRoot)
      nk ((saved _ (by decide)).trans pointerCell) ((saved _ (by decide)).trans sizeCell) pointerActive sizeActive nextCell leafFrontier leafAligned mBeforeLeaf
      keyFits keyMapped limit property (by rw [middleDomain]; exact payload) extra value continued
  have finalMemory:=congrArg PanSemStateFiniteExact.memory ending
  change target.memory=inner.memory at finalMemory
  have finalDomain:=congrArg PanSemStateFiniteExact.memaddrs ending
  change target.memaddrs=inner.memaddrs at finalDomain
  have finalGlobalsEq:=congrArg PanSemStateFiniteExact.globals ending
  change target.globals=inner.globals at finalGlobalsEq
  refine ⟨answer,?_,?_,?_,arena,finalArena,finalAligned,leafBefore,?_⟩
  · rw [finalMemory]
    exact stored
  · have forward:=trace.forward
    have afterClock:=evaluateHOLFiniteState_clock_le middle afterKey
    rw [continued] at afterClock
    rw [endpoint]
    omega
  · rw [finalGlobalsEq,finalGlobals,globals]
    apply HolFiniteMapExact.ext
    funext name
    by_cases same : name=ofString "heap_ptr"
    · subst name
      simp [HolFiniteMapExact.update,FUPDATE,leaf,amount]
    · simp [HolFiniteMapExact.update,FUPDATE,same,Ne.symm same]
  · rw [finalMemory,finalDomain]
    exact ⟨graph,valid,member,regions,disjoint,values⟩

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.empty_unsecured_normal
