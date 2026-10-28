import InitECandidate.Solver.Input.CurrentStartup.DecodedWitnessFields
import InitECandidate.Solver.Input.VarList.RecordsFrame

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessArrays
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- One real decoded witness array, with its physical SI pointer/count,
validated record lengths, input slice and actual allocation boundary. -/
structure Image (input : Guest.InputBlob) (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si array : BitVec 64) (start length boundary offset itemLimit countLimit : Nat) : Prop where
  siArena : AllocatedBytes.Arena si 96
  siAligned : si.toNat%8=0
  siLower : 2701134640≤si.toNat
  siBefore : si.toNat+96≤boundary
  inputLower : 2701134640≤pointer.toNat
  inside : start+length≤input.length%2^64
  before : array.toNat+16*VarList.decodedCount input start length≤boundary
  records : VarList.Records state input pointer array start length
  lengths : ∀ index<VarList.decodedCount input start length,
    (VarList.recordLength input start length (VarList.decodedCount input start length) index).toNat≤itemLimit
  countBound : VarList.decodedCount input start length≤countLimit
  pointerCell : state.memory (si+BitVec.ofNat 64 offset)=.word (VarList.decodedArray array length)
  countCell : state.memory (si+BitVec.ofNat 64 (offset+8))=.word (BitVec.ofNat 64 (VarList.decodedCount input start length))

/-- The same physical image survives any actual earlier-memory frame.
Empty decoded arrays require no readable zero pointer. -/
theorem Image.of_interval {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array : BitVec 64} {start length boundary offset itemLimit countLimit : Nat}
    (data : Image input source pointer si array start length boundary offset itemLimit countLimit)
    (offsetBound : offset+8<96)
    (memory : ∀ query : BitVec 64,2701134640≤query.toNat → query.toNat<boundary → post.memory query=source.memory query) :
    Image input post pointer si array start length boundary offset itemLimit countLimit := by
  have records : VarList.Records post input pointer array start length := by
    rcases data.records with empty|⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,complete,valid⟩
    · exact Or.inl empty
    · refine Or.inr ⟨plan,pointerEq,arrayEq,startEq,lengthEq,countEq,?_,valid⟩
      intro index inside
      have rowNumber:=plan.row_nat index inside
      have lengthNumber:=plan.length_nat index inside
      have afterInput:=plan.arrayAfter
      have count : plan.count=VarList.decodedCount input start length := by
        have ne : length≠0 := by have positive:=plan.positive; have header:=plan.header; omega
        simp only [VarList.decodedCount,if_neg ne]
        exact countEq
      have before : plan.array.toNat+16*plan.count≤boundary := by rw [arrayEq,count]; exact data.before
      have rowFrame : post.memory (VarList.row plan.array index)=source.memory (VarList.row plan.array index) := by
        apply memory
        · rw [rowNumber]; rw [pointerEq] at afterInput; have h:=data.inputLower; omega
        · rw [rowNumber]; omega
      have lengthFrame : post.memory (VarList.lengthCell plan.array index)=source.memory (VarList.lengthCell plan.array index) := by
        apply memory
        · rw [lengthNumber]; rw [pointerEq] at afterInput; have h:=data.inputLower; omega
        · rw [lengthNumber]; omega
      change _ ∧ _
      rw [rowFrame,lengthFrame]
      exact complete index inside
  have siFrame (extra : Nat) (small : extra<96) : post.memory (si+BitVec.ofNat 64 extra)=source.memory (si+BitVec.ofNat 64 extra) := by
    have number : (si+BitVec.ofNat 64 extra).toNat=si.toNat+extra := byteAddress_toNat si extra (by have h:=data.siArena.upper; omega)
    apply memory
    · rw [number]; have h:=data.siLower; omega
    · rw [number]; have h:=data.siBefore; omega
  exact ⟨data.siArena,data.siAligned,data.siLower,data.siBefore,data.inputLower,data.inside,data.before,records,data.lengths,data.countBound,
    (siFrame offset (by omega)).trans data.pointerCell,(siFrame (offset+8) offsetBound).trans data.countCell⟩

end InitECandidate.Solver.Input.CurrentStartup.WitnessArrays

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessArrays.Image.of_interval
