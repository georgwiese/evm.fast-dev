import InitECandidate.Solver.Input.HeapScalar

namespace InitECandidate.Solver.Input.Scalar
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

def flatAddress (base : ExpHOL 64) : List Nat→ExpHOL 64
  | []=>base
  | offsets=>.op .add (base::offsets.map (fun offset=>.const (BitVec.ofNat 64 offset)))

theorem const_list {F : Type} (source : PanSemStateFiniteExact 64 F) (offsets : List Nat) :
    @evalListHOLExact 64 F _ source.toExact (fun address=>Classical.propDecidable (source.memaddrs address))
      (offsets.map (fun offset=>ExpHOL.const (BitVec.ofNat 64 offset)))=
      some (offsets.map (fun offset=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 offset)))) := by
  classical
  induction offsets with
  | nil=>rfl
  | cons offset rest ih=>simp [evalListHOLExact,evalHOLExact,ih]

theorem sum_words (offsets : List Nat) :
    (offsets.map (BitVec.ofNat 64)).foldr (fun left right=>left+right) 0=BitVec.ofNat 64 offsets.sum := by
  induction offsets with
  | nil=>rfl
  | cons offset rest ih=>simp only [List.map_cons,List.foldr_cons,List.sum_cons,ih,BitVec.ofNat_add]

theorem flat_read {F : Type} (source : PanSemStateFiniteExact 64 F) (base : ExpHOL 64) (pointer : BitVec 64)
    (offsets : List Nat) (baseRead : eval source base=some (.val (.word pointer))) :
    eval source (flatAddress base offsets)=some (.val (.word (pointer+BitVec.ofNat 64 offsets.sum))) := by
  classical
  cases offsets with
  | nil=>simpa [flatAddress] using baseRead
  | cons offset rest=>
    have constants:=const_list source (offset::rest)
    have allWords : ((offset::rest).map (fun offset=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 offset)))).all valueIsWord=true := by
      simp [valueIsWord]
    have words : ((offset::rest).map (fun offset=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 offset)))).map valueWord=
        (offset::rest).map (BitVec.ofNat 64) := by simp [valueWord]
    simp only [eval] at baseRead
    have listRead : @evalListHOLExact 64 F _ source.toExact (fun address=>Classical.propDecidable (source.memaddrs address))
        (base::(offset::rest).map (fun offset=>ExpHOL.const (BitVec.ofNat 64 offset)))=
        some (ValueHOL.val (HolWordLab.word pointer)::(offset::rest).map (fun offset=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 offset)))) := by
      rw [evalListHOLExact,baseRead,constants]
    simp only [eval] at baseRead ⊢
    simp only [flatAddress]
    rw [evalHOLExact,listRead]
    have fullAll : (ValueHOL.val (HolWordLab.word pointer)::(offset::rest).map (fun offset=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 offset)))).all valueIsWord=true := by
      simp only [List.all_cons,valueIsWord,allWords,Bool.and_self]
    have fullWords : (ValueHOL.val (HolWordLab.word pointer)::(offset::rest).map (fun offset=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 offset)))).map valueWord=
        pointer::(offset::rest).map (BitVec.ofNat 64) := by
      rw [List.map_cons,words]
      rfl
    simp only [fullAll,fullWords,↓reduceIte,wordOpHOL,wordOp,List.foldr_cons,sum_words,Option.map_some]

end InitECandidate.Solver.Input.Scalar

#print axioms InitECandidate.Solver.Input.Scalar.const_list
#print axioms InitECandidate.Solver.Input.Scalar.sum_words
#print axioms InitECandidate.Solver.Input.Scalar.flat_read
