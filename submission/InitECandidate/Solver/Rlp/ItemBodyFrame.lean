import InitECandidate.Solver.Rlp.ItemNormalFrame
import InitECandidate.Solver.Rlp.DecodeGlobals

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (answer : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned answer),post)) :
    ∃ header payload flag,answer=result pointer header payload flag ∧ Valid pointer length.toNat (result pointer header payload flag) ∧
      Validation.Arena post cursor limit ∧ Validation.Above source post cursor.toNat ∧ post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code ∧
      post.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧ source.clock-post.clock≤60*length.toNat+41 := by
  obtain ⟨valid,nextArena,above,price⟩ := body_normal_above source post pointer length cursor limit pointerCell lengthCell arena fits installed answer normal
  obtain ⟨header,payload,flag,answerEq,head,positive,bounded,binary,listHead⟩ := valid
  have fields := Input.evaluation_fields source post body (some (.returned answer)) normal
  have heapFrame := globals (ofString "heap_ptr") source.code installed (by decide) source rfl
  rw [normal] at heapFrame
  have heapEq := congrArg Prod.snd heapFrame
  exact ⟨header,payload,flag,answerEq,⟨header,payload,flag,rfl,head,positive,bounded,binary,listHead⟩,
    nextArena,above,fields.1,fields.2.1,fields.2.2.2,heapEq,price⟩

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.body_frame
