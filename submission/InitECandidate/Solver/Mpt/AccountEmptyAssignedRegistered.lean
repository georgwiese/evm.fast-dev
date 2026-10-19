import InitECandidate.Solver.Mpt.AccountEmptyAssigned

namespace InitECandidate.Solver.Mpt.AccountEmpty
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Real assigned constructor retains all current ownership and registers
its actual fresh result, including the local assignment used by get_account. -/
theorem assigned_registered {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root hash : BitVec 64)
    (cutoff : Nat) (objects : ι → MutableTable.TableFamily.Object) (accounts : List (BitVec 64))
    (family : MutableTable.TableFamily.Model source heap.toNat objects)
    (registry : AccountDecode.Registry source cutoff heap.toNat objects accounts)
    (property : ι → BitVec 64 → Prop) (tableValues : MutableTable.TableFamily.ValuesHave source objects property) (above : cutoff≤heap.toNat)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word root)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word hash)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (rootArena : AllocatedBytes.Arena root 32) (hashArena : AllocatedBytes.Arena hash 32)
    (installed : Input.OriginalCode.Installed source.code) (name : MlS) (expressions : List (ExpHOL 64))
    (expectedArgs : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "acct_empty") expressions)=(none,post)) :
    3≤source.clock ∧ heap.toNat+56≤33806089496 ∧ post=assignedTarget source heap root hash name ∧
      post.locals.lookup name=some (.val (.word heap)) ∧ post.clock=source.clock-3 ∧
      (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 ∧ Nonempty (AccountDecode.Image post heap) ∧
      Rlp.Slices.Window source post heap.toNat (heap.toNat+56) ∧ HeapGlobals source post ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) ∧ MutableTable.TableFamily.Model post (heap.toNat+56) objects ∧
      AccountDecode.Registry post cutoff (heap.toNat+56) objects (accounts++[heap]) ∧ MutableTable.TableFamily.ValuesHave post objects property ∧
      AccountDecode.Registry.Extension accounts (accounts++[heap]) heap.toNat ∧ AccountDecode.Registry.Known (accounts++[heap]) heap := by
  obtain ⟨funded,room,canonical,cell,clock,rounded,⟨image⟩,window,globals,heapAfter⟩ :=
    assigned_normal source post heap root hash rootGlobal hashGlobal heapGlobal heapLower heapBound heapAligned domain rootArena hashArena installed name expressions expectedArgs normal
  have nextWord : BitVec.ofNat 64 (heap.toNat+56)=PersistentAlloc.rounded heap 56#64 := by
    rw [←rounded]
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have nextHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (heap.toNat+56)))) := by rw [nextWord]; exact heapAfter
  have currentDomain : post.memaddrs=source.memaddrs := by rw [canonical]; rfl
  have currentEndian : post.be=source.be := by rw [canonical]; rfl
  obtain ⟨nextFamily,nextRegistry,nextValues,weakening,freshKnown⟩ := AccountDecode.Registry.after_fresh_account source post cutoff heap.toNat (heap.toNat+56) objects accounts
    family registry property tableValues heap image (Nat.le_refl _) above (Nat.le_refl _) room (by omega) nextHeap currentDomain currentEndian
    (fun query earlier=>window query (Or.inl earlier))
  exact ⟨funded,room,canonical,cell,clock,rounded,⟨image⟩,window,globals,heapAfter,nextFamily,nextRegistry,nextValues,weakening,freshKnown⟩

end InitECandidate.Solver.Mpt.AccountEmpty

#print axioms InitECandidate.Solver.Mpt.AccountEmpty.assigned_registered
