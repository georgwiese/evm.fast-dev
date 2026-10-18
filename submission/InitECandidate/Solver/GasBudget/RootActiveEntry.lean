import InitECandidate.Solver.GasBudget.MessageCallNormalOpen
import InitECandidate.Solver.GasBudget.FrameNewPersistentEntry

namespace InitECandidate.Solver.GasBudget.RootMessage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable

/-- Actual owned data and bindings at the original msg_new declaration.
These are caller-reachability obligations, not helper executions or a clock
allowance. The validator/split supplies the gas cap on the corresponding path. -/
structure NoncreateSetup (source : PanSemStateFiniteExact 64 Guest.HostMemory) where
  start : Nat
  txStart : Nat
  addressesStart : Nat
  addressCount : Nat
  keysStart : Nat
  keyCount : Nat
  precompileStart : Nat
  blockEnv : HolWordLab 64
  txEnv : HolWordLab 64
  sender : BitVec 64
  recipient : BitVec 64
  data : BitVec 64
  length : BitVec 64
  gas : BitVec 64
  reservoir : BitVec 64
  intrinsicRegular : Nat
  pointers : Nat → BitVec 64
  environment : WarmKeys.Environment source
  lower : 2701131776 ≤ start
  bounded : start ≤ 33806089496
  aligned : start % 8 = 0
  record : Recipient.TxData source.memory txStart start recipient data length
  precompileValid : MemoryRegion.Valid ⟨precompileStart, 360⟩
  array : PointerArray source.memory 20 addressesStart addressCount start pointers
  positive : 0 < addressCount
  keyRegion : MemoryRegion.Valid (WarmKeys.inputRegion keysStart keyCount)
  heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start)))
  precompiles : source.globals.lookup (ofString "precompile_addrs") = some (.val (.word (BitVec.ofNat 64 precompileStart)))
  blockGlobal : source.globals.lookup (ofString "be") = some (.val blockEnv)
  txEnvLocal : source.locals.lookup (ofString "te") = some (.val txEnv)
  txLocal : source.locals.lookup (ofString "tx") = some (.val (.word (BitVec.ofNat 64 txStart)))
  gasLocal : source.locals.lookup (ofString "mgas") = some (.val (.word gas))
  reservoirLocal : source.locals.lookup (ofString "reservoir") = some (.val (.word reservoir))
  senderLocal : source.locals.lookup (ofString "sender") = some (.val (.word sender))
  addressesLocal : source.locals.lookup (ofString "al_addrs") = some (.val (.word (BitVec.ofNat 64 addressesStart)))
  countLocal : source.locals.lookup (ofString "nal") = some (.val (.word (BitVec.ofNat 64 (addressCount - 1))))
  keysLocal : source.locals.lookup (ofString "al_keys") = some (.val (.word (BitVec.ofNat 64 keysStart)))
  keyCountLocal : source.locals.lookup (ofString "nkeys") = some (.val (.word (BitVec.ofNat 64 keyCount)))
  senderFits : sender.toNat + 20 < 2 ^ 64
  senderMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress sender offset))
  nonzero : recipient ≠ 0#64
  recipientFits : recipient.toNat + 20 < 2 ^ 64
  recipientMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress recipient offset))
  newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one)
  msgCode : source.code.lookup (ofString "msg_new") = some (MsgNew.formals, MsgNew.body, .one)
  cap : gas.toNat + intrinsicRegular ≤ 16777216

structure FrameCode (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  prefixCode : FrameNew.Code source
  memoryCode : source.code.lookup (ofString "frame_mem_alloc") = some (Arenas.formals, Arenas.body .up, .one)
  jumpCode : source.code.lookup (ofString "compute_jumpdests") = some (JumpDest.formals, JumpDest.body, .one)
  logCode : source.code.lookup (ofString "lst_new_scratch") = some (ScratchList.formals, ScratchList.body, .one)
  tableCode : source.code.lookup (ofString "htab_new_scratch") = some (ScratchTable.formals, ScratchTable.body, .one)
  countCode : source.code.lookup (ofString "htab_count") = some (TableCount.formals, TableCount.body, .one)
  newCode : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one)
  openCode : source.code.lookup (ofString "frame_open") = some (FrameOpen.formals, FrameOpen.body, .one)
  messageCode : source.code.lookup (ofString "process_message") = some ([(ofString "msg", .one)], ProcessMessage.body, .one)
  callCode : source.code.lookup (ofString "process_message_call") = some (MessageCall.formals, MessageCall.body, .one)

/-- Original incoming arena and parent bindings. Room and these cursor
facts still need reachability from startup/earlier frame releases. -/
structure ArenaEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start : Nat) where
  scratch : BitVec 64
  lower : BitVec 64
  empty : BitVec 64
  parent : BitVec 64
  continuation : BitVec 64
  scratchGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  lowerGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word lower))
  emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty))
  evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent))
  continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation))
  scratchAligned : scratch.toNat % 8 = 0
  lowerAligned : lower.toNat % 8 = 0
  lowerBound : 2701131776 ≤ lower.toNat
  scratchBound : scratch.toNat ≤ 33806089496
  room : lower.toNat + 2768 ≤ scratch.toNat
  persistent : scratch.toNat ≤ start

theorem FrameCode.of_code {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (frame : FrameCode source) (codes : target.code = source.code) : FrameCode target := by
  exact ⟨⟨by rw [codes]; exact frame.prefixCode.scratchMark,
    by rw [codes]; exact frame.prefixCode.memoryMark,
    by rw [codes]; exact frame.prefixCode.scratch,
    by rw [codes]; exact frame.prefixCode.zero⟩,
    by rw [codes]; exact frame.memoryCode,
    by rw [codes]; exact frame.jumpCode,
    by rw [codes]; exact frame.logCode,
    by rw [codes]; exact frame.tableCode,
    by rw [codes]; exact frame.countCode,
    by rw [codes]; exact frame.newCode,
    by rw [codes]; exact frame.openCode,
    by rw [codes]; exact frame.messageCode,
    by rw [codes]; exact frame.callCode⟩

theorem empty_activation_price : (0#64 : BitVec 64).toNat + Zero.price (JumpDest.bitmapBytes (0#64 : BitVec 64).toNat) + 52 = 53 := by decide

end InitECandidate.Solver.GasBudget.RootMessage

#print axioms InitECandidate.Solver.GasBudget.RootMessage.empty_activation_price
#print axioms InitECandidate.Solver.GasBudget.RootMessage.FrameCode.of_code
