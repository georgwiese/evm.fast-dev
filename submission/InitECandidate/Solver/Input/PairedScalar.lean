import InitECandidate.Solver.Input.HeapFlatScalar

namespace InitECandidate.Solver.Input.Scalar
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

def pairedAddress (base offset : ExpHOL 64) (extras : List Nat) : ExpHOL 64 :=
  .op .add (base::offset::extras.map (fun n=>.const (BitVec.ofNat 64 n)))
def paired32 (base offset : ExpHOL 64) : ExpHOL 64 := .op .or [
  .loadByte (pairedAddress base offset []),shift (.loadByte (pairedAddress base offset [1])) 8,
  shift (.loadByte (pairedAddress base offset [2])) 16,shift (.loadByte (pairedAddress base offset [3])) 24]

theorem paired_read {F : Type} (source : PanSemStateFiniteExact 64 F) (base offset : ExpHOL 64) (pointer amount : BitVec 64)
    (extras : List Nat) (baseRead : eval source base=some (.val (.word pointer)))
    (offsetRead : eval source offset=some (.val (.word amount))) :
    eval source (pairedAddress base offset extras)=some (.val (.word (pointer+amount+BitVec.ofNat 64 extras.sum))) := by
  classical
  have constants:=const_list source extras
  simp only [eval] at baseRead offsetRead ⊢
  have reads : @evalListHOLExact 64 F _ source.toExact (fun address=>Classical.propDecidable (source.memaddrs address))
      (base::offset::extras.map (fun n=>ExpHOL.const (BitVec.ofNat 64 n)))=
      some (.val (.word pointer)::.val (.word amount)::extras.map (fun n=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 n)))) := by
    rw [evalListHOLExact,baseRead,evalListHOLExact,offsetRead,constants]
  have allWords : (extras.map (fun n=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 n)))).all valueIsWord=true := by simp [valueIsWord]
  have words : (extras.map (fun n=>ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 n)))).map valueWord=extras.map (BitVec.ofNat 64) := by simp [valueWord]
  rw [pairedAddress,evalHOLExact,reads]
  simp only [List.all_cons,valueIsWord,allWords,Bool.and_self,↓reduceIte,List.map_cons,valueWord,words,
    wordOpHOL,wordOp,List.foldr_cons,sum_words,Option.map_some,BitVec.add_assoc]

theorem paired_append {F : Type} (source : PanSemStateFiniteExact 64 F) (base offset : ExpHOL 64) (pointer amount : BitVec 64)
    (byte : Nat) (baseRead : eval source base=some (.val (.word pointer)))
    (offsetRead : eval source offset=some (.val (.word amount))) :
    eval source (pairedAddress base offset [byte])=eval source (plus (pairedAddress base offset []) byte) := by
  have first:=paired_read source base offset pointer amount [byte] baseRead offsetRead
  have start : eval source (pairedAddress base offset [])=some (.val (.word (pointer+amount))) := by
    simpa using paired_read source base offset pointer amount [] baseRead offsetRead
  have second:=plus_read source (pairedAddress base offset []) (pointer+amount) byte start
  simpa using first.trans second.symm

theorem paired32_equiv {F : Type} (source : PanSemStateFiniteExact 64 F) (base offset : ExpHOL 64) (pointer amount : BitVec 64)
    (baseRead : eval source base=some (.val (.word pointer))) (offsetRead : eval source offset=some (.val (.word amount))) :
    eval source (paired32 base offset)=eval source (le32 (pairedAddress base offset [])) := by
  apply op_congr
  exact .cons rfl
    (.cons (shift_congr source _ _ 8 (byte_congr source _ _ (paired_append source base offset pointer amount 1 baseRead offsetRead)))
      (.cons (shift_congr source _ _ 16 (byte_congr source _ _ (paired_append source base offset pointer amount 2 baseRead offsetRead)))
        (.cons (shift_congr source _ _ 24 (byte_congr source _ _ (paired_append source base offset pointer amount 3 baseRead offsetRead))) .nil)))

theorem paired_heap_le32 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (inputPointer pointer amount : BitVec 64) (base offset : ExpHOL 64) (start : Nat)
    (heap : Blob.HeapInput source input inputPointer) (inside : start+4≤input.length%2^64)
    (baseRead : eval source base=some (.val (.word pointer))) (offsetRead : eval source offset=some (.val (.word amount)))
    (field : pointer+amount=inputPointer+BitVec.ofNat 64 start) :
    eval source (paired32 base offset)=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input start)))) := by
  have addressRead : eval source (pairedAddress base offset [])=some (.val (.word (inputPointer+BitVec.ofNat 64 start))) := by
    simpa [field] using paired_read source base offset pointer amount [] baseRead offsetRead
  exact (paired32_equiv source base offset pointer amount baseRead offsetRead).trans
    (heap_le32 source input inputPointer start _ heap inside addressRead)

end InitECandidate.Solver.Input.Scalar

#print axioms InitECandidate.Solver.Input.Scalar.paired_read
#print axioms InitECandidate.Solver.Input.Scalar.paired_append
#print axioms InitECandidate.Solver.Input.Scalar.paired32_equiv
#print axioms InitECandidate.Solver.Input.Scalar.paired_heap_le32
