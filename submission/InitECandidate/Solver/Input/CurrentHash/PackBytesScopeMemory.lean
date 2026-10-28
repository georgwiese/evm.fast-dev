import InitECandidate.Solver.Input.CurrentHash.PackBytesMemory
import InitECandidate.Solver.Input.CurrentHash.PackBytes
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Input.CurrentHash.PackBytesScopeMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Invert the same normal scoped packing invocation. Its actual allocation
supplies room, tuple, heap and memory facts to its real continuation. -/
theorem image (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor query : BitVec 64) (n : Nat)
    (small : n+64<2^64) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (heapLower : 2701131776≤cursor.toNat) (heapBound : cursor.toNat≤2952790016) (aligned : cursor.toNat%8=0)
    (inputArena : AllocatedBytes.Arena p n) (below : query.toNat<cursor.toNat)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (PackBytes.values p n))
    (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source (.decCall (ofString name) PackBytes.returnShape (ofString "pack_bytes") arguments continuation)=(some (.returned value),post)) :
    ∃ target inner,
      PackBytesMemory.Returned source target cursor query n (PackBytesReturn.tuple cursor n) ∧
      target.code=source.code ∧ target.memaddrs=source.memaddrs ∧
      (∀ cursor : Cursor, target.globals.lookup (key cursor)=source.globals.lookup (key cursor)) ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (PackBytesReturn.tuple cursor n)) continuation=(some (.returned value),inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointer,length⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code installed)
  obtain ⟨funded,target,returned,inner,bodyRun,checked,remaining,endpoint⟩ := CallNormal.scoped_normal source post name PackBytes.returnShape
    (ofString "pack_bytes") arguments (PackBytes.values p n) PackBytes.body continuation callee PackBytes.returnShape args called value actual
  have calleeImage := PackBytesMemory.body_image (callEntryStateHOLFinite source callee) target p cursor query n small installed domain pointer length heap
    heapLower heapBound aligned inputArena below returned bodyRun
  have image : PackBytesMemory.Returned source target cursor query n returned :=
    ⟨calleeImage.tuple,calleeImage.room,calleeImage.heap,calleeImage.grows,calleeImage.nextBound,calleeImage.nextAligned,calleeImage.protectedWord⟩
  have tuple := image.tuple
  subst returned
  have fields := evaluation_fields (callEntryStateHOLFinite source callee) target _ _ bodyRun
  refine ⟨target,inner,image,fields.2.2.2,fields.1,?_,remaining,endpoint⟩
  intro cursor
  have frame := PackBytes.preserves cursor source.code installed (callEntryStateHOLFinite source callee) rfl
  change GlobalEffects.erase (key cursor) (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) PackBytes.body).2 = _ at frame
  rw [bodyRun] at frame
  exact congrArg Prod.snd frame

end InitECandidate.Solver.Input.CurrentHash.PackBytesScopeMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.PackBytesScopeMemory.image
