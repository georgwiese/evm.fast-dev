import InitECandidate.Solver.Mpt.AccountNewProgram
import InitECandidate.Solver.Mpt.AccountObjectGeometry
import InitECandidate.Solver.Input.RlpWrite.U256Store
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.AccountNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Input.RlpWrite

def finalMemory (memory : WordWrites.Memory) (out nonce : BitVec 64) (balance : U256Value.Words) (root hash : BitVec 64) : WordWrites.Memory :=
  StoreWord.put (StoreWord.put (WordWrites.write (StoreWord.put memory (out+0#64) nonce)
    (U256Value.wordWrites (out+8#64) balance)) (out+40#64) root) (out+48#64) hash

def tailTarget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out nonce : BitVec 64)
    (balance : U256Value.Words) (root hash : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  emptyLocalsHOLFinite {source with memory:=finalMemory source.memory out nonce balance root hash}

theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64)
    (cell : source.locals.lookup (ofString "a")=some (.val (.word out))) (offset : Nat) :
    eval source (address offset)=some (.val (.word (out+BitVec.ofNat 64 offset))) := by
  simp [eval,address,localVar,evalHOLExact,evalListHOLExact,toExact,cell,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- All seven actual account words are written in the literal original
suffix. Tuple stores retain their real four-limb semantics and no helper
clock is spent by these stores and the return. -/
theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out nonce : BitVec 64)
    (balance : U256Value.Words) (root hash : BitVec 64)
    (outCell : source.locals.lookup (ofString "a")=some (.val (.word out)))
    (nonceCell : source.locals.lookup (ofString "nonce")=some (.val (.word nonce)))
    (balanceCell : source.locals.lookup (ofString "balance")=some (U256Value.tuple balance))
    (hashCell : source.locals.lookup (ofString "code_hash")=some (.val (.word hash)))
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word root)))
    (output : AccountDecode.Output out) (domain : source.memaddrs=InitE.ordinaryDomain)
    (rootArena : AllocatedBytes.Arena root 32) (hashArena : AllocatedBytes.Arena hash 32) :
    evaluateHOLFiniteState source tail=(some (.returned (.val (.word out))),tailTarget source out nonce balance root hash) ∧
      Nonempty (AccountDecode.Image (tailTarget source out nonce balance root hash) out) ∧
      Rlp.Slices.Window source (tailTarget source out nonce balance root hash) out.toNat (out.toNat+56) := by
  let first := {source with memory:=StoreWord.put source.memory (out+0#64) nonce}
  let second := {first with memory:=WordWrites.write first.memory (U256Value.wordWrites (out+8#64) balance)}
  let third := {second with memory:=StoreWord.put second.memory (out+40#64) root}
  let fourth := {third with memory:=StoreWord.put third.memory (out+48#64) hash}
  have mapped (offset : Nat) (inside : offset+8≤56) (aligned : offset%8=0) : source.memaddrs (out+BitVec.ofNat 64 offset) := by
    rw [domain]
    exact output.word_mapped out offset inside aligned
  have nonceRead : eval source (localVar "nonce")=some (.val (.word nonce)) := by
    simp [eval,localVar,evalHOLExact,toExact,nonceCell]
  have nonceRun := StoreWord.execute source (address 0) (localVar "nonce") (out+0#64) nonce (address_read source out outCell 0) nonceRead (mapped 0 (by decide) (by decide))
  have balanceRead : eval first (localVar "balance")=some (U256Value.tuple balance) := by
    simp [eval,localVar,evalHOLExact,toExact,first,balanceCell]
  have balanceMapped (index : Fin 4) : first.memaddrs (out+8#64+BitVec.ofNat 64 (8*index.val)) := by
    have inside : 8+8*index.val+8≤56 := by have := index.isLt; omega
    have actual := mapped (8+8*index.val) inside (by omega)
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using actual
  have balanceRun := U256Value.store_execute first (address 8) (localVar "balance") (out+8#64) balance
    (address_read first out outCell 8) balanceRead balanceMapped
  have rootRead : eval second (.var .global (ofString "empty_trie_root"))=some (.val (.word root)) := by
    simp [eval,evalHOLExact,toExact,second,first,rootGlobal]
  have rootRun := StoreWord.execute second (address 40) (.var .global (ofString "empty_trie_root")) (out+40#64) root
    (address_read second out outCell 40) rootRead (mapped 40 (by decide) (by decide))
  have hashRead : eval third (localVar "code_hash")=some (.val (.word hash)) := by
    simp [eval,localVar,evalHOLExact,toExact,third,second,first,hashCell]
  have hashRun := StoreWord.execute third (address 48) (localVar "code_hash") (out+48#64) hash
    (address_read third out outCell 48) hashRead (mapped 48 (by decide) (by decide))
  have returnRun : evaluateHOLFiniteState fourth (.return (localVar "a"))=
      (some (.returned (.val (.word out))),tailTarget source out nonce balance root hash) := by
    simp [evaluateHOLFiniteState_return,localVar,evalHOLExact,toExact,fourth,third,second,first,outCell,
      shapeOfHOLExact,sizeOfShapeWithContextHOL,tailTarget,finalMemory]
  refine ⟨?_,?_,?_⟩
  · rw [tail,StateSteps.next_sequence source first _ _ nonceRun (Nat.le_refl _),
      afterNonce,StateSteps.next_sequence first second _ _ balanceRun (Nat.le_refl _),
      afterBalance,rootStore,StateSteps.next_sequence second third _ _ rootRun (Nat.le_refl _),
      afterRoot,hashStore,StateSteps.next_sequence third fourth _ _ hashRun (Nat.le_refl _)]
    exact returnRun
  · refine ⟨⟨output,domain,root,hash,?_,?_,rootArena,hashArena⟩⟩
    · change finalMemory source.memory out nonce balance root hash (out+40#64)=.word root
      have different : out+40#64≠out+48#64 := by
        intro equal
        have numbers := congrArg BitVec.toNat equal
        rw [output.slot_number out 40 (by decide),output.slot_number out 48 (by decide)] at numbers
        omega
      simp only [finalMemory,StoreWord.put,if_neg different,↓reduceIte]
    · change finalMemory source.memory out nonce balance root hash (out+48#64)=.word hash
      simp only [finalMemory,StoreWord.put,↓reduceIte]
  · intro query outside
    have nonceAway := output.outside_slot out query 0 (by decide) outside
    have rootAway := output.outside_slot out query 40 (by decide) outside
    have hashAway := output.outside_slot out query 48 (by decide) outside
    have balanceAway : query∉(U256Value.wordWrites (out+8#64) balance).map Prod.fst := by
      simp only [U256Value.wordWrites,List.map_cons,List.map_nil,Prod.fst,List.mem_cons,List.not_mem_nil,not_or,not_false_eq_true,and_true]
      refine ⟨?_,?_,?_,?_⟩
      · exact output.outside_slot out query 8 (by decide) outside
      · simpa [BitVec.add_assoc] using output.outside_slot out query 16 (by decide) outside
      · simpa [BitVec.add_assoc] using output.outside_slot out query 24 (by decide) outside
      · simpa [BitVec.add_assoc] using output.outside_slot out query 32 (by decide) outside
    have balanceAgree : WordWrites.write (StoreWord.put source.memory (out+0#64) nonce) (U256Value.wordWrites (out+8#64) balance) query=source.memory query := by
      rw [WordWrites.write_away _ _ query balanceAway]
      exact if_neg nonceAway
    change finalMemory source.memory out nonce balance root hash query=source.memory query
    simp only [finalMemory,StoreWord.put,if_neg rootAway,if_neg hashAway]
    exact balanceAgree

end InitECandidate.Solver.Mpt.AccountNew

#print axioms InitECandidate.Solver.Mpt.AccountNew.address_read
#print axioms InitECandidate.Solver.Mpt.AccountNew.tail_execute
