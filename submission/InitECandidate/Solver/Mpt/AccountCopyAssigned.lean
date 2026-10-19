import InitECandidate.Solver.Mpt.AccountCopyRegistered
import InitECandidate.Solver.Input.AssignedCallNormal

namespace InitECandidate.Solver.Mpt.AccountCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- The original mutators assign acct_copy to an existing caller local.
This real ABI path retains the fresh image, registry and all older words. -/
theorem assigned_registered {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (account heap : BitVec 64)
    (cutoff : Nat) (objects : ι → TableFamily.Object) (accounts : List (BitVec 64))
    (family : TableFamily.Model source heap.toNat objects) (registry : AccountDecode.Registry source cutoff heap.toNat objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (member : account ∈ accounts)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))) (heapBound : heap.toNat ≤ 33806089496) (heapAligned : heap.toNat % 8 = 0)
    (installed : Input.OriginalCode.Installed source.code) (name : String) (expressions : List (ExpHOL 64))
    (binding : source.locals.lookup (ofString name) = some (.val (.word account)))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word account)])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "acct_copy") expressions) = (none,post)) :
    7 ≤ source.clock ∧ heap.toNat + 56 ≤ 33806089496 ∧ post.clock = source.clock - 7 ∧
      post.locals = source.locals.update (ofString name,.val (.word heap)) ∧ post.code = source.code ∧
      post.memaddrs = source.memaddrs ∧ post.be = source.be ∧ HeapGlobals source post ∧
      Nonempty (AccountDecode.Image post heap) ∧ Rlp.Slices.Window source post heap.toNat (heap.toNat + 56) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (heap.toNat + 56)))) ∧
      TableFamily.Model post (heap.toNat + 56) objects ∧ AccountDecode.Registry post cutoff (heap.toNat + 56) objects (accounts ++ [heap]) ∧
      TableFamily.ValuesHave post objects property ∧ AccountDecode.Registry.Extension accounts (accounts ++ [heap]) heap.toNat ∧
      TableFamily.PersistentFrame cutoff heap.toNat objects objects source post := by
  obtain ⟨sourceImage⟩ := registry.images account member
  obtain ⟨callee,called,accountCell⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "acct_copy") "a" body account (original_code source.code installed)
  obtain ⟨positive,target,answer,bodyRun⟩ := Input.CallNormal.assigned_callee_return source post (some (.local,ofString name)) (ofString "acct_copy") expressions _ body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  let entryImage := AccountDecode.Image.of_agreement source entry account sourceImage rfl rfl rfl
  obtain ⟨funded,room,answerEq,clock,frame,rounded,⟨targetImage⟩,window,globals,heapAfter⟩ := body_normal entry target account heap accountCell entryImage (registry.before account member)
    heapGlobal heapBound heapAligned installed answer bodyRun
  rw [answerEq] at bodyRun
  have valid : isValidValueHOLExact source.toExact .local (ofString name) (.val (.word heap)) = true := by
    simp [isValidValueHOLExact,lookupKvarHOLExact,binding,shapeOfHOLExact,shapeEqHOL]
  have actual := evaluateHOLFiniteState_call_return_set_kvar source .local (ofString name) none (ofString "acct_copy") expressions _ body callee .one (.val (.word heap)) target
    args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL]) valid
  have postEq := congrArg Prod.snd (normal.symm.trans actual)
  change post = setVarHOLFinite (ofString name) (.val (.word heap)) {target with locals := source.locals} at postEq
  have codes : post.code = source.code := by
    have current := congrArg PanSemStateFiniteExact.code frame
    change target.code = source.code at current
    rw [postEq]
    exact current
  have domain : post.memaddrs = source.memaddrs := by
    have current := congrArg PanSemStateFiniteExact.memaddrs frame
    change target.memaddrs = source.memaddrs at current
    rw [postEq]
    exact current
  have endian : post.be = source.be := by
    have current := congrArg PanSemStateFiniteExact.be frame
    change target.be = source.be at current
    rw [postEq]
    exact current
  have postImage : AccountDecode.Image post heap := AccountDecode.Image.of_agreement target post heap targetImage (by rw [postEq]; rfl) (by rw [postEq]; rfl) (by rw [postEq]; rfl)
  have postWindow : Rlp.Slices.Window source post heap.toNat (heap.toNat + 56) := by
    intro query away
    rw [postEq]
    exact window query away
  have nextWord : BitVec.ofNat 64 (heap.toNat + 56) = PersistentAlloc.rounded heap 56#64 := by
    rw [← rounded]
    simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have nextHeap : post.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (heap.toNat + 56)))) := by rw [postEq,nextWord]; exact heapAfter
  have above : cutoff ≤ heap.toNat := by have := registry.above account member; have := registry.before account member; omega
  obtain ⟨nextFamily,nextRegistry,nextValues,extension,known⟩ := AccountDecode.Registry.after_fresh_account source post cutoff heap.toNat (heap.toNat + 56) objects accounts family registry property values
    heap postImage (Nat.le_refl _) above (Nat.le_refl _) room (by omega) nextHeap domain endian (fun query earlier => postWindow query (Or.inl earlier))
  change 6 ≤ source.clock - 1 at funded
  change target.clock = source.clock - 1 - 6 at clock
  refine ⟨by omega,room,by rw [postEq]; change target.clock = _; omega,by rw [postEq]; rfl,codes,domain,endian,?_,⟨postImage⟩,postWindow,nextHeap,nextFamily,nextRegistry,nextValues,extension,?_⟩
  · rw [postEq]
    exact globals
  · exact ⟨fun query lower earlier outside => ⟨outside,postWindow query (Or.inl earlier)⟩⟩

end InitECandidate.Solver.Mpt.AccountCopy

#print axioms InitECandidate.Solver.Mpt.AccountCopy.assigned_registered
