import InitECandidate.Solver.GasBudget.OpcodeChargePrefix

namespace InitECandidate.Solver.GasBudget.OpcodeChargeSites
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

-- Generated proof data from unchanged original opcode prefixes.
-- body_shape checks every case against the original Guest AST.
inductive Kind where
  | op_add
  | op_mul
  | op_sub
  | op_div
  | op_sdiv
  | op_mod
  | op_smod
  | op_addmod
  | op_mulmod
  | op_signextend
  | op_lt
  | op_gt
  | op_slt
  | op_sgt
  | op_eq
  | op_iszero
  | op_and
  | op_or
  | op_xor
  | op_not
  | op_byte
  | op_shl
  | op_shr
  | op_sar
  | op_clz
  | op_jump
  | op_jumpi
  | op_pc
  | op_gas
  | op_jumpdest
  | op_msize
  | op_pop
  | op_dup
  | op_swap
  | op_dupn
  | op_swapn
  | op_exchange
  | op_tload
  | op_address
  | op_origin
  | op_caller
  | op_callvalue
  | op_calldataload
  | op_calldatasize
  | op_codesize
  | op_gasprice
  | op_returndatasize
  | op_selfbalance
  | op_basefee
  | op_blobhash
  | op_blobbasefee
  | op_blockhash
  | op_coinbase
  | op_timestamp
  | op_number
  | op_gaslimit
  | op_chainid
  | op_prevrandao
  | op_slotnum

def Kind.body : Kind → ProgHOL 64
  | .op_add => match Guest.guestFn_op_add with | .function fn => progToHOL fn.body | _ => .skip
  | .op_mul => match Guest.guestFn_op_mul with | .function fn => progToHOL fn.body | _ => .skip
  | .op_sub => match Guest.guestFn_op_sub with | .function fn => progToHOL fn.body | _ => .skip
  | .op_div => match Guest.guestFn_op_div with | .function fn => progToHOL fn.body | _ => .skip
  | .op_sdiv => match Guest.guestFn_op_sdiv with | .function fn => progToHOL fn.body | _ => .skip
  | .op_mod => match Guest.guestFn_op_mod with | .function fn => progToHOL fn.body | _ => .skip
  | .op_smod => match Guest.guestFn_op_smod with | .function fn => progToHOL fn.body | _ => .skip
  | .op_addmod => match Guest.guestFn_op_addmod with | .function fn => progToHOL fn.body | _ => .skip
  | .op_mulmod => match Guest.guestFn_op_mulmod with | .function fn => progToHOL fn.body | _ => .skip
  | .op_signextend => match Guest.guestFn_op_signextend with | .function fn => progToHOL fn.body | _ => .skip
  | .op_lt => match Guest.guestFn_op_lt with | .function fn => progToHOL fn.body | _ => .skip
  | .op_gt => match Guest.guestFn_op_gt with | .function fn => progToHOL fn.body | _ => .skip
  | .op_slt => match Guest.guestFn_op_slt with | .function fn => progToHOL fn.body | _ => .skip
  | .op_sgt => match Guest.guestFn_op_sgt with | .function fn => progToHOL fn.body | _ => .skip
  | .op_eq => match Guest.guestFn_op_eq with | .function fn => progToHOL fn.body | _ => .skip
  | .op_iszero => match Guest.guestFn_op_iszero with | .function fn => progToHOL fn.body | _ => .skip
  | .op_and => match Guest.guestFn_op_and with | .function fn => progToHOL fn.body | _ => .skip
  | .op_or => match Guest.guestFn_op_or with | .function fn => progToHOL fn.body | _ => .skip
  | .op_xor => match Guest.guestFn_op_xor with | .function fn => progToHOL fn.body | _ => .skip
  | .op_not => match Guest.guestFn_op_not with | .function fn => progToHOL fn.body | _ => .skip
  | .op_byte => match Guest.guestFn_op_byte with | .function fn => progToHOL fn.body | _ => .skip
  | .op_shl => match Guest.guestFn_op_shl with | .function fn => progToHOL fn.body | _ => .skip
  | .op_shr => match Guest.guestFn_op_shr with | .function fn => progToHOL fn.body | _ => .skip
  | .op_sar => match Guest.guestFn_op_sar with | .function fn => progToHOL fn.body | _ => .skip
  | .op_clz => match Guest.guestFn_op_clz with | .function fn => progToHOL fn.body | _ => .skip
  | .op_jump => match Guest.guestFn_op_jump with | .function fn => progToHOL fn.body | _ => .skip
  | .op_jumpi => match Guest.guestFn_op_jumpi with | .function fn => progToHOL fn.body | _ => .skip
  | .op_pc => match Guest.guestFn_op_pc with | .function fn => progToHOL fn.body | _ => .skip
  | .op_gas => match Guest.guestFn_op_gas with | .function fn => progToHOL fn.body | _ => .skip
  | .op_jumpdest => match Guest.guestFn_op_jumpdest with | .function fn => progToHOL fn.body | _ => .skip
  | .op_msize => match Guest.guestFn_op_msize with | .function fn => progToHOL fn.body | _ => .skip
  | .op_pop => match Guest.guestFn_op_pop with | .function fn => progToHOL fn.body | _ => .skip
  | .op_dup => match Guest.guestFn_op_dup with | .function fn => progToHOL fn.body | _ => .skip
  | .op_swap => match Guest.guestFn_op_swap with | .function fn => progToHOL fn.body | _ => .skip
  | .op_dupn => match Guest.guestFn_op_dupn with | .function fn => progToHOL fn.body | _ => .skip
  | .op_swapn => match Guest.guestFn_op_swapn with | .function fn => progToHOL fn.body | _ => .skip
  | .op_exchange => match Guest.guestFn_op_exchange with | .function fn => progToHOL fn.body | _ => .skip
  | .op_tload => match Guest.guestFn_op_tload with | .function fn => progToHOL fn.body | _ => .skip
  | .op_address => match Guest.guestFn_op_address with | .function fn => progToHOL fn.body | _ => .skip
  | .op_origin => match Guest.guestFn_op_origin with | .function fn => progToHOL fn.body | _ => .skip
  | .op_caller => match Guest.guestFn_op_caller with | .function fn => progToHOL fn.body | _ => .skip
  | .op_callvalue => match Guest.guestFn_op_callvalue with | .function fn => progToHOL fn.body | _ => .skip
  | .op_calldataload => match Guest.guestFn_op_calldataload with | .function fn => progToHOL fn.body | _ => .skip
  | .op_calldatasize => match Guest.guestFn_op_calldatasize with | .function fn => progToHOL fn.body | _ => .skip
  | .op_codesize => match Guest.guestFn_op_codesize with | .function fn => progToHOL fn.body | _ => .skip
  | .op_gasprice => match Guest.guestFn_op_gasprice with | .function fn => progToHOL fn.body | _ => .skip
  | .op_returndatasize => match Guest.guestFn_op_returndatasize with | .function fn => progToHOL fn.body | _ => .skip
  | .op_selfbalance => match Guest.guestFn_op_selfbalance with | .function fn => progToHOL fn.body | _ => .skip
  | .op_basefee => match Guest.guestFn_op_basefee with | .function fn => progToHOL fn.body | _ => .skip
  | .op_blobhash => match Guest.guestFn_op_blobhash with | .function fn => progToHOL fn.body | _ => .skip
  | .op_blobbasefee => match Guest.guestFn_op_blobbasefee with | .function fn => progToHOL fn.body | _ => .skip
  | .op_blockhash => match Guest.guestFn_op_blockhash with | .function fn => progToHOL fn.body | _ => .skip
  | .op_coinbase => match Guest.guestFn_op_coinbase with | .function fn => progToHOL fn.body | _ => .skip
  | .op_timestamp => match Guest.guestFn_op_timestamp with | .function fn => progToHOL fn.body | _ => .skip
  | .op_number => match Guest.guestFn_op_number with | .function fn => progToHOL fn.body | _ => .skip
  | .op_gaslimit => match Guest.guestFn_op_gaslimit with | .function fn => progToHOL fn.body | _ => .skip
  | .op_chainid => match Guest.guestFn_op_chainid with | .function fn => progToHOL fn.body | _ => .skip
  | .op_prevrandao => match Guest.guestFn_op_prevrandao with | .function fn => progToHOL fn.body | _ => .skip
  | .op_slotnum => match Guest.guestFn_op_slotnum with | .function fn => progToHOL fn.body | _ => .skip

def Kind.names : Kind → List String
  | .op_add => ["x", "y"]
  | .op_mul => ["x", "y"]
  | .op_sub => ["x", "y"]
  | .op_div => ["x", "y"]
  | .op_sdiv => ["x", "y"]
  | .op_mod => ["x", "y"]
  | .op_smod => ["x", "y"]
  | .op_addmod => ["x", "y", "z"]
  | .op_mulmod => ["x", "y", "z"]
  | .op_signextend => ["b", "x"]
  | .op_lt => ["x", "y"]
  | .op_gt => ["x", "y"]
  | .op_slt => ["x", "y"]
  | .op_sgt => ["x", "y"]
  | .op_eq => ["x", "y"]
  | .op_iszero => ["x"]
  | .op_and => ["x", "y"]
  | .op_or => ["x", "y"]
  | .op_xor => ["x", "y"]
  | .op_not => ["x"]
  | .op_byte => ["i", "x"]
  | .op_shl => ["sh", "x"]
  | .op_shr => ["sh", "x"]
  | .op_sar => ["sh", "x"]
  | .op_clz => ["x"]
  | .op_jump => ["dest"]
  | .op_jumpi => ["dest", "cond"]
  | .op_pc => []
  | .op_gas => []
  | .op_jumpdest => []
  | .op_msize => []
  | .op_pop => ["x"]
  | .op_dup => []
  | .op_swap => []
  | .op_dupn => []
  | .op_swapn => []
  | .op_exchange => []
  | .op_tload => ["kv"]
  | .op_address => []
  | .op_origin => []
  | .op_caller => []
  | .op_callvalue => []
  | .op_calldataload => ["start"]
  | .op_calldatasize => []
  | .op_codesize => []
  | .op_gasprice => []
  | .op_returndatasize => []
  | .op_selfbalance => []
  | .op_basefee => []
  | .op_blobhash => ["iv"]
  | .op_blobbasefee => []
  | .op_blockhash => ["bn"]
  | .op_coinbase => []
  | .op_timestamp => []
  | .op_number => []
  | .op_gaslimit => []
  | .op_chainid => []
  | .op_prevrandao => []
  | .op_slotnum => []

def Kind.fee : Kind → Nat
  | .op_add => 3
  | .op_mul => 5
  | .op_sub => 3
  | .op_div => 5
  | .op_sdiv => 5
  | .op_mod => 5
  | .op_smod => 5
  | .op_addmod => 8
  | .op_mulmod => 8
  | .op_signextend => 5
  | .op_lt => 3
  | .op_gt => 3
  | .op_slt => 3
  | .op_sgt => 3
  | .op_eq => 3
  | .op_iszero => 3
  | .op_and => 3
  | .op_or => 3
  | .op_xor => 3
  | .op_not => 3
  | .op_byte => 3
  | .op_shl => 3
  | .op_shr => 3
  | .op_sar => 3
  | .op_clz => 5
  | .op_jump => 8
  | .op_jumpi => 10
  | .op_pc => 2
  | .op_gas => 2
  | .op_jumpdest => 1
  | .op_msize => 2
  | .op_pop => 2
  | .op_dup => 3
  | .op_swap => 3
  | .op_dupn => 3
  | .op_swapn => 3
  | .op_exchange => 3
  | .op_tload => 100
  | .op_address => 2
  | .op_origin => 2
  | .op_caller => 2
  | .op_callvalue => 2
  | .op_calldataload => 3
  | .op_calldatasize => 2
  | .op_codesize => 2
  | .op_gasprice => 2
  | .op_returndatasize => 2
  | .op_selfbalance => 5
  | .op_basefee => 2
  | .op_blobhash => 3
  | .op_blobbasefee => 2
  | .op_blockhash => 20
  | .op_coinbase => 2
  | .op_timestamp => 2
  | .op_number => 2
  | .op_gaslimit => 2
  | .op_chainid => 2
  | .op_prevrandao => 2
  | .op_slotnum => 2

def stripPops : Nat → ProgHOL 64 → ProgHOL 64
  | 0, program => program
  | count + 1, .decCall _ _ _ _ rest => stripPops count rest
  | _ + 1, _ => .skip

def Kind.suffix (kind : Kind) : ProgHOL 64 :=
  match stripPops kind.names.length kind.body with | .seq _ rest => rest | _ => .skip

theorem body_shape (kind : Kind) : kind.body = OpcodeChargePrefix.program kind.names (BitVec.ofNat 64 kind.fee) kind.suffix := by
  cases kind <;> simp only [Kind.body, Kind.names, Kind.fee, Kind.suffix, stripPops, OpcodeChargePrefix.program, StackPop.pops, StackPop.shape, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Guest.guestFn_op_add, Guest.guestFn_op_mul, Guest.guestFn_op_sub, Guest.guestFn_op_div, Guest.guestFn_op_sdiv, Guest.guestFn_op_mod, Guest.guestFn_op_smod, Guest.guestFn_op_addmod, Guest.guestFn_op_mulmod, Guest.guestFn_op_signextend, Guest.guestFn_op_lt, Guest.guestFn_op_gt, Guest.guestFn_op_slt, Guest.guestFn_op_sgt, Guest.guestFn_op_eq, Guest.guestFn_op_iszero, Guest.guestFn_op_and, Guest.guestFn_op_or, Guest.guestFn_op_xor, Guest.guestFn_op_not, Guest.guestFn_op_byte, Guest.guestFn_op_shl, Guest.guestFn_op_shr, Guest.guestFn_op_sar, Guest.guestFn_op_clz, Guest.guestFn_op_jump, Guest.guestFn_op_jumpi, Guest.guestFn_op_pc, Guest.guestFn_op_gas, Guest.guestFn_op_jumpdest, Guest.guestFn_op_msize, Guest.guestFn_op_pop, Guest.guestFn_op_dup, Guest.guestFn_op_swap, Guest.guestFn_op_dupn, Guest.guestFn_op_swapn, Guest.guestFn_op_exchange, Guest.guestFn_op_tload, Guest.guestFn_op_address, Guest.guestFn_op_origin, Guest.guestFn_op_caller, Guest.guestFn_op_callvalue, Guest.guestFn_op_calldataload, Guest.guestFn_op_calldatasize, Guest.guestFn_op_codesize, Guest.guestFn_op_gasprice, Guest.guestFn_op_returndatasize, Guest.guestFn_op_selfbalance, Guest.guestFn_op_basefee, Guest.guestFn_op_blobhash, Guest.guestFn_op_blobbasefee, Guest.guestFn_op_blockhash, Guest.guestFn_op_coinbase, Guest.guestFn_op_timestamp, Guest.guestFn_op_number, Guest.guestFn_op_gaslimit, Guest.guestFn_op_chainid, Guest.guestFn_op_prevrandao, Guest.guestFn_op_slotnum] <;> rfl

theorem fee_positive (kind : Kind) : 0 < (BitVec.ofNat 64 kind.fee).toNat := by
  cases kind <;> decide

/-- Actual normal execution of any of these59 original helpers reaches its
real suffix after a positive charge. This is a prefix contract, not a claim
about suffix gas preservation, covered exceptional paths or whole runtime. -/
theorem normal (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (stackCode : source.code.lookup (ofString "stack_pop") = some ([], StackPop.body, StackPop.shape))
    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source kind.body = (some (.returned value), post)) :
    ∃ ready inner, kind.names.length + 1 ≤ source.clock ∧ ready.clock = source.clock - (kind.names.length + 1) ∧
      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - (kind.names.length + 1)} ∧
      evaluateHOLFiniteState ready kind.suffix = (some (.returned value), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner ∧
      regularBudget ready.memory frame = regularBudget source.memory frame ∧
      (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + kind.fee ∧
      (wordAt source.memory (frame + 184#64)).toNat < (wordAt ready.memory (frame + 184#64)).toNat ∧
      (wordAt ready.memory (frame + 16#64)).toNat + kind.names.length = (wordAt source.memory (frame + 16#64)).toNat ∧
      (∀ address, address ≠ frame + 16#64 → address ≠ frame + 64#64 → address ≠ frame + 184#64 →
        ready.memory address = source.memory address) := by
  rw [body_shape] at run
  obtain ⟨ready, inner, fits, clock, frameEq, continuationRun, postEq, budget, credit, depth, outside⟩ :=
    OpcodeChargePrefix.normal kind.names source post frame (BitVec.ofNat 64 kind.fee) kind.suffix stackCode chargeCode ev cap value run
  have feeSmall : kind.fee < 2 ^ 64 := by cases kind <;> decide
  have positive := fee_positive kind
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt feeSmall] at credit positive
  exact ⟨ready, inner, fits, clock, frameEq, continuationRun, postEq, budget, credit, by omega, depth, outside⟩

end InitECandidate.Solver.GasBudget.OpcodeChargeSites

#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.body_shape
#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.fee_positive
#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.normal
