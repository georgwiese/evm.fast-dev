import InitECandidate.Solver.Mpt.AccountEmptyCallNormal
import InitECandidate.Solver.Mpt.AccountRegistryFresh

namespace InitECandidate.Solver.Mpt.AccountEmpty
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original empty-account creation retains every current table/value and
earlier account and registers exactly its actual fresh account. -/
theorem scoped_registered {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root hash : BitVec 64)
    (cutoff : Nat) (objects : ι → MutableTable.TableFamily.Object) (accounts : List (BitVec 64))
    (family : MutableTable.TableFamily.Model source heap.toNat objects)
    (registry : AccountDecode.Registry source cutoff heap.toNat objects accounts)
    (property : ι → BitVec 64 → Prop) (tableValues : MutableTable.TableFamily.ValuesHave source objects property) (above : cutoff≤heap.toNat)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word root)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word hash)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (rootArena : AllocatedBytes.Arena root 32) (hashArena : AllocatedBytes.Arena hash 32)
    (installed : Input.OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "acct_empty") expressions continuation)=(some (.returned returned),post)) :
    3≤source.clock ∧ heap.toNat+56≤33806089496 ∧ ∃ ready inner,
      ready.locals.lookup (ofString name)=some (.val (.word heap)) ∧ ready.clock=source.clock-3 ∧
      emptyLocalsHOLFinite ready=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
        memory:=AccountNew.finalMemory source.memory heap 0#64 zeroBalance root hash,clock:=source.clock-3} ∧
      (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 ∧ Nonempty (AccountDecode.Image ready heap) ∧
      Rlp.Slices.Window source ready heap.toNat (heap.toNat+56) ∧ HeapGlobals source ready ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) ∧
      MutableTable.TableFamily.Model ready (heap.toNat+56) objects ∧
      AccountDecode.Registry ready cutoff (heap.toNat+56) objects (accounts++[heap]) ∧ MutableTable.TableFamily.ValuesHave ready objects property ∧
      (∀ value : BitVec 64,AccountDecode.Registry.Known accounts value → AccountDecode.Registry.Known (accounts++[heap]) value) ∧ AccountDecode.Registry.Known (accounts++[heap]) heap ∧
      evaluateHOLFiniteState ready continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨funded,room,ready,inner,cell,clock,frame,rounded,⟨image⟩,window,globals,heapAfter,tailRun,restored⟩ :=
    scoped_normal source post heap root hash rootGlobal hashGlobal heapGlobal heapLower heapBound heapAligned domain rootArena hashArena installed
      name expressions continuation args returned normal
  have nextWord : BitVec.ofNat 64 (heap.toNat+56)=PersistentAlloc.rounded heap 56#64 := by
    rw [←rounded]
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have nextHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (heap.toNat+56)))) := by
    rw [nextWord]
    exact heapAfter
  have currentDomain := congrArg PanSemStateFiniteExact.memaddrs frame
  have currentEndian := congrArg PanSemStateFiniteExact.be frame
  change ready.memaddrs=source.memaddrs at currentDomain
  change ready.be=source.be at currentEndian
  obtain ⟨nextFamily,nextRegistry,nextValues,weakening,freshKnown⟩ := AccountDecode.Registry.after_fresh_account source ready cutoff heap.toNat (heap.toNat+56) objects accounts
    family registry property tableValues heap image (Nat.le_refl _) above (Nat.le_refl _) room (by omega) nextHeap currentDomain currentEndian
    (fun query earlier=>window query (Or.inl earlier))
  exact ⟨funded,room,ready,inner,cell,clock,frame,rounded,⟨image⟩,window,globals,heapAfter,nextFamily,nextRegistry,nextValues,weakening,freshKnown,tailRun,restored⟩

end InitECandidate.Solver.Mpt.AccountEmpty

#print axioms InitECandidate.Solver.Mpt.AccountEmpty.scoped_registered
