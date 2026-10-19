import InitECandidate.Solver.Mpt.AccountCopyCallNormal
import InitECandidate.Solver.Mpt.AccountRegistryFresh

namespace InitECandidate.Solver.Mpt.AccountCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real copy of a current registered account retains all live tables,
occupied values and old accounts, and registers the actual fresh copy. -/
theorem scoped_registered {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (account heap : BitVec 64)
    (cutoff : Nat) (objects : ι → MutableTable.TableFamily.Object) (accounts : List (BitVec 64))
    (family : MutableTable.TableFamily.Model source heap.toNat objects)
    (registry : AccountDecode.Registry source cutoff heap.toNat objects accounts)
    (property : ι → BitVec 64 → Prop) (tableValues : MutableTable.TableFamily.ValuesHave source objects property)
    (member : account∈accounts)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word account)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "acct_copy") expressions continuation)=(some (.returned returned),post)) :
    7≤source.clock ∧ heap.toNat+56≤33806089496 ∧ ∃ ready inner,
      ready.locals.lookup (ofString name)=some (.val (.word heap)) ∧ ready.clock=source.clock-7 ∧
      emptyLocalsHOLFinite ready=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
        memory:=CopyGeneral.resultMemory source.memory source.be account heap 56,clock:=source.clock-7} ∧
      (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 ∧ Nonempty (AccountDecode.Image ready heap) ∧
      Rlp.Slices.Window source ready heap.toNat (heap.toNat+56) ∧ HeapGlobals source ready ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) ∧
      MutableTable.TableFamily.Model ready (heap.toNat+56) objects ∧
      AccountDecode.Registry ready cutoff (heap.toNat+56) objects (accounts++[heap]) ∧ MutableTable.TableFamily.ValuesHave ready objects property ∧
      (∀ value : BitVec 64,AccountDecode.Registry.Known accounts value → AccountDecode.Registry.Known (accounts++[heap]) value) ∧ AccountDecode.Registry.Known (accounts++[heap]) heap ∧
      evaluateHOLFiniteState ready continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨sourceImage⟩ := registry.images account member
  have earlier := registry.before account member
  have above : cutoff≤heap.toNat := by have := registry.above account member; omega
  obtain ⟨funded,room,ready,inner,cell,clock,frame,rounded,⟨image⟩,window,globals,heapAfter,tailRun,restored⟩ :=
    scoped_normal source post account heap sourceImage earlier heapGlobal heapBound heapAligned installed name expressions continuation args returned normal
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

end InitECandidate.Solver.Mpt.AccountCopy

#print axioms InitECandidate.Solver.Mpt.AccountCopy.scoped_registered
