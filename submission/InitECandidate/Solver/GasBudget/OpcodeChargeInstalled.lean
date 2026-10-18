import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.GasBudget.OpcodeChargeSites

namespace InitECandidate.Solver.GasBudget.OpcodeChargeSites
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000

-- Literal original declaration data, not a replacement implementation.
def Kind.original : Kind → Decl (BitVec 64)
  | .op_add => Guest.guestFn_op_add
  | .op_mul => Guest.guestFn_op_mul
  | .op_sub => Guest.guestFn_op_sub
  | .op_div => Guest.guestFn_op_div
  | .op_sdiv => Guest.guestFn_op_sdiv
  | .op_mod => Guest.guestFn_op_mod
  | .op_smod => Guest.guestFn_op_smod
  | .op_addmod => Guest.guestFn_op_addmod
  | .op_mulmod => Guest.guestFn_op_mulmod
  | .op_signextend => Guest.guestFn_op_signextend
  | .op_lt => Guest.guestFn_op_lt
  | .op_gt => Guest.guestFn_op_gt
  | .op_slt => Guest.guestFn_op_slt
  | .op_sgt => Guest.guestFn_op_sgt
  | .op_eq => Guest.guestFn_op_eq
  | .op_iszero => Guest.guestFn_op_iszero
  | .op_and => Guest.guestFn_op_and
  | .op_or => Guest.guestFn_op_or
  | .op_xor => Guest.guestFn_op_xor
  | .op_not => Guest.guestFn_op_not
  | .op_byte => Guest.guestFn_op_byte
  | .op_shl => Guest.guestFn_op_shl
  | .op_shr => Guest.guestFn_op_shr
  | .op_sar => Guest.guestFn_op_sar
  | .op_clz => Guest.guestFn_op_clz
  | .op_jump => Guest.guestFn_op_jump
  | .op_jumpi => Guest.guestFn_op_jumpi
  | .op_pc => Guest.guestFn_op_pc
  | .op_gas => Guest.guestFn_op_gas
  | .op_jumpdest => Guest.guestFn_op_jumpdest
  | .op_msize => Guest.guestFn_op_msize
  | .op_pop => Guest.guestFn_op_pop
  | .op_dup => Guest.guestFn_op_dup
  | .op_swap => Guest.guestFn_op_swap
  | .op_dupn => Guest.guestFn_op_dupn
  | .op_swapn => Guest.guestFn_op_swapn
  | .op_exchange => Guest.guestFn_op_exchange
  | .op_tload => Guest.guestFn_op_tload
  | .op_address => Guest.guestFn_op_address
  | .op_origin => Guest.guestFn_op_origin
  | .op_caller => Guest.guestFn_op_caller
  | .op_callvalue => Guest.guestFn_op_callvalue
  | .op_calldataload => Guest.guestFn_op_calldataload
  | .op_calldatasize => Guest.guestFn_op_calldatasize
  | .op_codesize => Guest.guestFn_op_codesize
  | .op_gasprice => Guest.guestFn_op_gasprice
  | .op_returndatasize => Guest.guestFn_op_returndatasize
  | .op_selfbalance => Guest.guestFn_op_selfbalance
  | .op_basefee => Guest.guestFn_op_basefee
  | .op_blobhash => Guest.guestFn_op_blobhash
  | .op_blobbasefee => Guest.guestFn_op_blobbasefee
  | .op_blockhash => Guest.guestFn_op_blockhash
  | .op_coinbase => Guest.guestFn_op_coinbase
  | .op_timestamp => Guest.guestFn_op_timestamp
  | .op_number => Guest.guestFn_op_number
  | .op_gaslimit => Guest.guestFn_op_gaslimit
  | .op_chainid => Guest.guestFn_op_chainid
  | .op_prevrandao => Guest.guestFn_op_prevrandao
  | .op_slotnum => Guest.guestFn_op_slotnum

def Kind.label : Kind → String
  | .op_add => "op_add"
  | .op_mul => "op_mul"
  | .op_sub => "op_sub"
  | .op_div => "op_div"
  | .op_sdiv => "op_sdiv"
  | .op_mod => "op_mod"
  | .op_smod => "op_smod"
  | .op_addmod => "op_addmod"
  | .op_mulmod => "op_mulmod"
  | .op_signextend => "op_signextend"
  | .op_lt => "op_lt"
  | .op_gt => "op_gt"
  | .op_slt => "op_slt"
  | .op_sgt => "op_sgt"
  | .op_eq => "op_eq"
  | .op_iszero => "op_iszero"
  | .op_and => "op_and"
  | .op_or => "op_or"
  | .op_xor => "op_xor"
  | .op_not => "op_not"
  | .op_byte => "op_byte"
  | .op_shl => "op_shl"
  | .op_shr => "op_shr"
  | .op_sar => "op_sar"
  | .op_clz => "op_clz"
  | .op_jump => "op_jump"
  | .op_jumpi => "op_jumpi"
  | .op_pc => "op_pc"
  | .op_gas => "op_gas"
  | .op_jumpdest => "op_jumpdest"
  | .op_msize => "op_msize"
  | .op_pop => "op_pop"
  | .op_dup => "op_dup"
  | .op_swap => "op_swap"
  | .op_dupn => "op_dupn"
  | .op_swapn => "op_swapn"
  | .op_exchange => "op_exchange"
  | .op_tload => "op_tload"
  | .op_address => "op_address"
  | .op_origin => "op_origin"
  | .op_caller => "op_caller"
  | .op_callvalue => "op_callvalue"
  | .op_calldataload => "op_calldataload"
  | .op_calldatasize => "op_calldatasize"
  | .op_codesize => "op_codesize"
  | .op_gasprice => "op_gasprice"
  | .op_returndatasize => "op_returndatasize"
  | .op_selfbalance => "op_selfbalance"
  | .op_basefee => "op_basefee"
  | .op_blobhash => "op_blobhash"
  | .op_blobbasefee => "op_blobbasefee"
  | .op_blockhash => "op_blockhash"
  | .op_coinbase => "op_coinbase"
  | .op_timestamp => "op_timestamp"
  | .op_number => "op_number"
  | .op_gaslimit => "op_gaslimit"
  | .op_chainid => "op_chainid"
  | .op_prevrandao => "op_prevrandao"
  | .op_slotnum => "op_slotnum"

def Kind.name (kind : Kind) : MlS := ofString kind.label
def Kind.signature (kind : Kind) : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=
  match kind.original with
  | .function fn => (fn.params.map paramToHOL, progToHOL fn.body, shapeToHOL fn.returnShape)
  | _ => ([], .skip, .one)

def Kind.index : Kind → Nat
  | .op_add => 433
  | .op_mul => 434
  | .op_sub => 435
  | .op_div => 436
  | .op_sdiv => 437
  | .op_mod => 438
  | .op_smod => 439
  | .op_addmod => 440
  | .op_mulmod => 441
  | .op_signextend => 443
  | .op_lt => 444
  | .op_gt => 445
  | .op_slt => 446
  | .op_sgt => 447
  | .op_eq => 448
  | .op_iszero => 449
  | .op_and => 450
  | .op_or => 451
  | .op_xor => 452
  | .op_not => 453
  | .op_byte => 454
  | .op_shl => 455
  | .op_shr => 456
  | .op_sar => 457
  | .op_clz => 458
  | .op_jump => 461
  | .op_jumpi => 462
  | .op_pc => 463
  | .op_gas => 464
  | .op_jumpdest => 465
  | .op_msize => 469
  | .op_pop => 471
  | .op_dup => 473
  | .op_swap => 475
  | .op_dupn => 478
  | .op_swapn => 479
  | .op_exchange => 480
  | .op_tload => 487
  | .op_address => 489
  | .op_origin => 491
  | .op_caller => 492
  | .op_callvalue => 493
  | .op_calldataload => 494
  | .op_calldatasize => 495
  | .op_codesize => 498
  | .op_gasprice => 500
  | .op_returndatasize => 504
  | .op_selfbalance => 507
  | .op_basefee => 509
  | .op_blobhash => 510
  | .op_blobbasefee => 511
  | .op_blockhash => 512
  | .op_coinbase => 513
  | .op_timestamp => 514
  | .op_number => 515
  | .op_gaslimit => 516
  | .op_chainid => 517
  | .op_prevrandao => 518
  | .op_slotnum => 519

theorem signature_body (kind : Kind) : kind.signature.2.1 = kind.body := by cases kind <;> rfl

theorem signature_return (kind : Kind) : kind.signature.2.2 = .one := by
  cases kind <;> simp only [Kind.signature, Kind.original, shapeToHOL, Guest.guestFn_op_add, Guest.guestFn_op_mul, Guest.guestFn_op_sub, Guest.guestFn_op_div, Guest.guestFn_op_sdiv, Guest.guestFn_op_mod, Guest.guestFn_op_smod, Guest.guestFn_op_addmod, Guest.guestFn_op_mulmod, Guest.guestFn_op_signextend, Guest.guestFn_op_lt, Guest.guestFn_op_gt, Guest.guestFn_op_slt, Guest.guestFn_op_sgt, Guest.guestFn_op_eq, Guest.guestFn_op_iszero, Guest.guestFn_op_and, Guest.guestFn_op_or, Guest.guestFn_op_xor, Guest.guestFn_op_not, Guest.guestFn_op_byte, Guest.guestFn_op_shl, Guest.guestFn_op_shr, Guest.guestFn_op_sar, Guest.guestFn_op_clz, Guest.guestFn_op_jump, Guest.guestFn_op_jumpi, Guest.guestFn_op_pc, Guest.guestFn_op_gas, Guest.guestFn_op_jumpdest, Guest.guestFn_op_msize, Guest.guestFn_op_pop, Guest.guestFn_op_dup, Guest.guestFn_op_swap, Guest.guestFn_op_dupn, Guest.guestFn_op_swapn, Guest.guestFn_op_exchange, Guest.guestFn_op_tload, Guest.guestFn_op_address, Guest.guestFn_op_origin, Guest.guestFn_op_caller, Guest.guestFn_op_callvalue, Guest.guestFn_op_calldataload, Guest.guestFn_op_calldatasize, Guest.guestFn_op_codesize, Guest.guestFn_op_gasprice, Guest.guestFn_op_returndatasize, Guest.guestFn_op_selfbalance, Guest.guestFn_op_basefee, Guest.guestFn_op_blobhash, Guest.guestFn_op_blobbasefee, Guest.guestFn_op_blockhash, Guest.guestFn_op_coinbase, Guest.guestFn_op_timestamp, Guest.guestFn_op_number, Guest.guestFn_op_gaslimit, Guest.guestFn_op_chainid, Guest.guestFn_op_prevrandao, Guest.guestFn_op_slotnum]

theorem original_index (kind : Kind) :
    (functionsHOL Input.OriginalCode.program)[kind.index]? = some (kind.name, kind.signature) := by
  cases kind <;> rfl

theorem installed (code) (environment : Input.OriginalCode.Installed code) (kind : Kind) :
    code.lookup kind.name = some (kind.signature.1, kind.body, .one) := by
  have original := Input.OriginalCode.indexed code environment kind.index (kind.name, kind.signature) (original_index kind)
  have pair : kind.signature = (kind.signature.1, kind.body, .one) := by
    rw [← signature_body kind, ← signature_return kind]
  rw [pair] at original
  exact original

end InitECandidate.Solver.GasBudget.OpcodeChargeSites

#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.signature_body
#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.signature_return
#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.original_index
#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.installed
