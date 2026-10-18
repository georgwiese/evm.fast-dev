import InitECandidate.Solver.GasBudget.RootMessageFirstStores
import InitECandidate.Solver.Input.NormalScalarStore

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable

/-- Actual initialized root message immediately after its original MSG_GAS
store. The canonical call state fixes its pointer, heap cursor and clock;
only the explicitly executed message memory stores differ. -/
structure Prepared (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) (gas : BitVec 64) : Prop where
  region : MemoryRegion.Valid ⟨start, 176⟩
  funded : 10 ≤ source.clock
  frame : target = {MsgNew.callState source "m" start with memory := target.memory}
  gas : target.memory (BitVec.ofNat 64 start + 40#64) = .word gas
  recipient : CopiesRecipient source target start
  outside : ∀ query : BitVec 64, query.toNat < start ∨ start + 176 ≤ query.toNat → target.memory query = source.memory query

/-- Actual message constructor, first four field stores and MSG_GAS, with
allocation room, message geometry and exact10clock payment derived. -/
theorem allocation_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64) (start : Nat)
    (blockEnv txEnv : HolWordLab 64) (sender gas : BitVec 64)
    (lower : 2701131776 ≤ start) (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (blockGlobal : source.globals.lookup (ofString "be") = some (.val blockEnv))
    (txLocal : source.locals.lookup (ofString "te") = some (.val txEnv))
    (senderLocal : source.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (gasLocal : source.locals.lookup (ofString "mgas") = some (.val (.word gas)))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Input.Trap.formals, Input.Trap.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (msgCode : source.code.lookup (ofString "msg_new") = some (MsgNew.formals, MsgNew.body, .one))
    (normal : evaluateHOLFiniteState source initialSite = (some (.returned value), post)) :
    ∃ stored inner : PanSemStateFiniteExact 64 Guest.HostMemory,
      Prepared source stored start gas ∧ evaluateHOLFiniteState stored RootCaller.afterMsgGas = (some (.returned value), inner) ∧ post = restore source "m" inner := by
  rw [initial_shape] at normal
  obtain ⟨region, funded, inner, afterNew, restored⟩ := MsgNew.call_normal source post start "m" beforeGas lower bounded aligned domain heap allocCode trapCode zeroCode msgCode value normal
  let constructed := MsgNew.callState source "m" start
  have constructedMessage : constructed.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))) := bind_lookup_same _ _ _
  have constructedBlock : constructed.globals.lookup (ofString "be") = some (.val blockEnv) := blockGlobal
  have constructedTx : constructed.locals.lookup (ofString "te") = some (.val txEnv) := (bind_lookup_other _ "m" "te" _ (by decide)).trans txLocal
  have constructedSender : constructed.locals.lookup (ofString "sender") = some (.val (.word sender)) := (bind_lookup_other _ "m" "sender" _ (by decide)).trans senderLocal
  obtain ⟨ready, gasSiteRun, readyFrame, readyRecipient, readyOutside⟩ := first_stores_normal constructed inner value start blockEnv txEnv (.word sender) region constructedMessage constructedBlock constructedTx constructedSender afterNew
  have readyMessage : ready.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))) := by rw [readyFrame]; exact constructedMessage
  have readyGas : ready.locals.lookup (ofString "mgas") = some (.val (.word gas)) := by
    rw [readyFrame]
    exact (bind_lookup_other _ "m" "mgas" _ (by decide)).trans gasLocal
  rw [RootCaller.actual_msg_gas] at gasSiteRun
  have safe : Input.LocalPrefix (ofString "m") RootCaller.msgGasStore := .store _ _
  obtain ⟨stored, storeRun, restRun, _⟩ := safe.normal_continue ready inner RootCaller.afterMsgGas value gasSiteRun
  obtain ⟨pointer, pointerLocal, mapped, storedEq, gasCell⟩ := Input.scalar_store_normal ready stored "m" "mgas" 40#64 gas readyGas storeRun
  have pointerEq : pointer = BitVec.ofNat 64 start := by
    simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using pointerLocal.symm.trans readyMessage
  subst pointer
  have storedFrame := Input.store_none_frame ready stored _ _ storeRun
  have frame : stored = {constructed with memory := stored.memory} :=
    storedFrame.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := stored.memory}) readyFrame)
  have outside (query : BitVec 64) (away : query.toNat < start ∨ start + 176 ≤ query.toNat) : stored.memory query = source.memory query := by
    have different : query ≠ BitVec.ofNat 64 start + 40#64 := by
      intro same
      have number := congrArg BitVec.toNat same
      rw [MessageField.field_number start 40 region (by decide)] at number
      omega
    have unchanged : stored.memory query = ready.memory query := by rw [storedEq]; simp only [StoreWord.put, if_neg different]
    exact unchanged.trans ((readyOutside query away).trans (MsgNew.memory_away source "m" start region query away))
  have copies : CopiesRecipient source stored start := by
    intro tx recipient read
    have constructedRead : TxRecipient constructed start tx recipient := read.of_frame
      (bind_lookup_other _ "m" "tx" _ (by decide)) rfl (fun query before => MsgNew.memory_away source "m" start region query (Or.inl before))
    have copied := readyRecipient tx recipient constructedRead
    rw [storedEq]
    simpa only [WitnessRadix.StoreWord.put, BitVec.add_right_inj,
      show (24#64 : BitVec 64) ≠ 40#64 from by decide, ↓reduceIte] using copied
  exact ⟨stored, inner, ⟨region, funded, frame, gasCell, copies, outside⟩, restRun, restored⟩

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.allocation_normal
