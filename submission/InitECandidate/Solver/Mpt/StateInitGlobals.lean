import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.GlobalEffectsAtoms
import InitECandidate.Solver.Input.GlobalByteEffects
import InitECandidate.Solver.Input.GlobalEffectsLoop
import InitECandidate.Solver.Input.GlobalEffectsCaught
import InitECandidate.Solver.Input.GlobalEffectsGlobalCall

namespace InitECandidate.Solver.Mpt.StateInitGlobals
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

namespace Code
inductive Routine where
  | trap_with
  | alloc
  | key_to_nibbles
  | mpt_fail
  | compact_to_nibbles
  | memzero
  | node_new_branch
  | node_new_leaf
  | rlp_fail
  | rlp_read_length
  | rlp_item_header
  | scratch_alloc
  | _rlp_validate_items_body
  | scratch_mark
  | scratch_release
  | rlp_validate_items
  | rlp_item_total
  | rlp_list_count
  | rlp_item
  | rlp_decode_fully
  | rlp_item_total_unchecked
  | rlp_list_to_slices
  | _decode_step
  | node_new_hashed
  | htab_find_leaf
  | memeq
  | htab_get
  | nodedb_lookup
  | _resolve_step
  | node_new_ext
  | _decode_witness_node_body
  | _decode_witness_node_mpt
  | _decode_witness_node
  | memcpy
  | decode_witness_to_mpt
  | htab_new
  | state_init

def declaration : Routine → Decl (BitVec 64)
  | .trap_with => Guest.Software.guestFn_trap_with
  | .alloc => Guest.Software.guestFn_alloc
  | .key_to_nibbles => Guest.Software.guestFn_key_to_nibbles
  | .mpt_fail => Guest.Software.guestFn_mpt_fail
  | .compact_to_nibbles => Guest.Software.guestFn_compact_to_nibbles
  | .memzero => Guest.Software.guestFn_memzero
  | .node_new_branch => Guest.Software.guestFn_node_new_branch
  | .node_new_leaf => Guest.Software.guestFn_node_new_leaf
  | .rlp_fail => Guest.Software.guestFn_rlp_fail
  | .rlp_read_length => Guest.Software.guestFn_rlp_read_length
  | .rlp_item_header => Guest.Software.guestFn_rlp_item_header
  | .scratch_alloc => Guest.Software.guestFn_scratch_alloc
  | ._rlp_validate_items_body => Guest.Software.guestFn__rlp_validate_items_body
  | .scratch_mark => Guest.Software.guestFn_scratch_mark
  | .scratch_release => Guest.Software.guestFn_scratch_release
  | .rlp_validate_items => Guest.Software.guestFn_rlp_validate_items
  | .rlp_item_total => Guest.Software.guestFn_rlp_item_total
  | .rlp_list_count => Guest.Software.guestFn_rlp_list_count
  | .rlp_item => Guest.Software.guestFn_rlp_item
  | .rlp_decode_fully => Guest.Software.guestFn_rlp_decode_fully
  | .rlp_item_total_unchecked => Guest.Software.guestFn_rlp_item_total_unchecked
  | .rlp_list_to_slices => Guest.Software.guestFn_rlp_list_to_slices
  | ._decode_step => Guest.Software.guestFn__decode_step
  | .node_new_hashed => Guest.Software.guestFn_node_new_hashed
  | .htab_find_leaf => Guest.Software.guestFn_htab_find_leaf
  | .memeq => Guest.Software.guestFn_memeq
  | .htab_get => Guest.Software.guestFn_htab_get
  | .nodedb_lookup => Guest.Software.guestFn_nodedb_lookup
  | ._resolve_step => Guest.Software.guestFn__resolve_step
  | .node_new_ext => Guest.Software.guestFn_node_new_ext
  | ._decode_witness_node_body => Guest.Software.guestFn__decode_witness_node_body
  | ._decode_witness_node_mpt => Guest.Software.guestFn__decode_witness_node_mpt
  | ._decode_witness_node => Guest.Software.guestFn__decode_witness_node
  | .memcpy => Guest.Software.guestFn_memcpy
  | .decode_witness_to_mpt => Guest.Software.guestFn_decode_witness_to_mpt
  | .htab_new => Guest.Software.guestFn_htab_new
  | .state_init => Guest.Software.guestFn_state_init

def entry (routine : Routine) := GasBudget.OriginalCodeEnvironment.originalEntry (declaration routine)
def name : Routine → MlS
  | .trap_with => ofString "trap_with"
  | .alloc => ofString "alloc"
  | .key_to_nibbles => ofString "key_to_nibbles"
  | .mpt_fail => ofString "mpt_fail"
  | .compact_to_nibbles => ofString "compact_to_nibbles"
  | .memzero => ofString "memzero"
  | .node_new_branch => ofString "node_new_branch"
  | .node_new_leaf => ofString "node_new_leaf"
  | .rlp_fail => ofString "rlp_fail"
  | .rlp_read_length => ofString "rlp_read_length"
  | .rlp_item_header => ofString "rlp_item_header"
  | .scratch_alloc => ofString "scratch_alloc"
  | ._rlp_validate_items_body => ofString "_rlp_validate_items_body"
  | .scratch_mark => ofString "scratch_mark"
  | .scratch_release => ofString "scratch_release"
  | .rlp_validate_items => ofString "rlp_validate_items"
  | .rlp_item_total => ofString "rlp_item_total"
  | .rlp_list_count => ofString "rlp_list_count"
  | .rlp_item => ofString "rlp_item"
  | .rlp_decode_fully => ofString "rlp_decode_fully"
  | .rlp_item_total_unchecked => ofString "rlp_item_total_unchecked"
  | .rlp_list_to_slices => ofString "rlp_list_to_slices"
  | ._decode_step => ofString "_decode_step"
  | .node_new_hashed => ofString "node_new_hashed"
  | .htab_find_leaf => ofString "htab_find_leaf"
  | .memeq => ofString "memeq"
  | .htab_get => ofString "htab_get"
  | .nodedb_lookup => ofString "nodedb_lookup"
  | ._resolve_step => ofString "_resolve_step"
  | .node_new_ext => ofString "node_new_ext"
  | ._decode_witness_node_body => ofString "_decode_witness_node_body"
  | ._decode_witness_node_mpt => ofString "_decode_witness_node_mpt"
  | ._decode_witness_node => ofString "_decode_witness_node"
  | .memcpy => ofString "memcpy"
  | .decode_witness_to_mpt => ofString "decode_witness_to_mpt"
  | .htab_new => ofString "htab_new"
  | .state_init => ofString "state_init"

def formals (routine : Routine) := (entry routine).2.1
def body (routine : Routine) := (entry routine).2.2.1
def shape (routine : Routine) := (entry routine).2.2.2

set_option maxRecDepth 100000 in
theorem installed (code) (installed : OriginalCode.Installed code) (routine : Routine) :
    code.lookup (name routine)=some (formals routine,body routine,shape routine) := by
  cases routine with
  | trap_with => exact OriginalCode.indexed code installed 0 (entry .trap_with) (by rfl)
  | alloc => exact OriginalCode.indexed code installed 2 (entry .alloc) (by rfl)
  | key_to_nibbles => exact OriginalCode.indexed code installed 222 (entry .key_to_nibbles) (by rfl)
  | mpt_fail => exact OriginalCode.indexed code installed 220 (entry .mpt_fail) (by rfl)
  | compact_to_nibbles => exact OriginalCode.indexed code installed 223 (entry .compact_to_nibbles) (by rfl)
  | memzero => exact OriginalCode.indexed code installed 12 (entry .memzero) (by rfl)
  | node_new_branch => exact OriginalCode.indexed code installed 232 (entry .node_new_branch) (by rfl)
  | node_new_leaf => exact OriginalCode.indexed code installed 230 (entry .node_new_leaf) (by rfl)
  | rlp_fail => exact OriginalCode.indexed code installed 93 (entry .rlp_fail) (by rfl)
  | rlp_read_length => exact OriginalCode.indexed code installed 94 (entry .rlp_read_length) (by rfl)
  | rlp_item_header => exact OriginalCode.indexed code installed 97 (entry .rlp_item_header) (by rfl)
  | scratch_alloc => exact OriginalCode.indexed code installed 8 (entry .scratch_alloc) (by rfl)
  | _rlp_validate_items_body => exact OriginalCode.indexed code installed 98 (entry ._rlp_validate_items_body) (by rfl)
  | scratch_mark => exact OriginalCode.indexed code installed 9 (entry .scratch_mark) (by rfl)
  | scratch_release => exact OriginalCode.indexed code installed 10 (entry .scratch_release) (by rfl)
  | rlp_validate_items => exact OriginalCode.indexed code installed 99 (entry .rlp_validate_items) (by rfl)
  | rlp_item_total => exact OriginalCode.indexed code installed 100 (entry .rlp_item_total) (by rfl)
  | rlp_list_count => exact OriginalCode.indexed code installed 101 (entry .rlp_list_count) (by rfl)
  | rlp_item => exact OriginalCode.indexed code installed 95 (entry .rlp_item) (by rfl)
  | rlp_decode_fully => exact OriginalCode.indexed code installed 96 (entry .rlp_decode_fully) (by rfl)
  | rlp_item_total_unchecked => exact OriginalCode.indexed code installed 102 (entry .rlp_item_total_unchecked) (by rfl)
  | rlp_list_to_slices => exact OriginalCode.indexed code installed 103 (entry .rlp_list_to_slices) (by rfl)
  | _decode_step => exact OriginalCode.indexed code installed 235 (entry ._decode_step) (by rfl)
  | node_new_hashed => exact OriginalCode.indexed code installed 229 (entry .node_new_hashed) (by rfl)
  | htab_find_leaf => exact OriginalCode.indexed code installed 119 (entry .htab_find_leaf) (by rfl)
  | memeq => exact OriginalCode.indexed code installed 13 (entry .memeq) (by rfl)
  | htab_get => exact OriginalCode.indexed code installed 120 (entry .htab_get) (by rfl)
  | nodedb_lookup => exact OriginalCode.indexed code installed 228 (entry .nodedb_lookup) (by rfl)
  | _resolve_step => exact OriginalCode.indexed code installed 234 (entry ._resolve_step) (by rfl)
  | node_new_ext => exact OriginalCode.indexed code installed 231 (entry .node_new_ext) (by rfl)
  | _decode_witness_node_body => exact OriginalCode.indexed code installed 236 (entry ._decode_witness_node_body) (by rfl)
  | _decode_witness_node_mpt => exact OriginalCode.indexed code installed 237 (entry ._decode_witness_node_mpt) (by rfl)
  | _decode_witness_node => exact OriginalCode.indexed code installed 238 (entry ._decode_witness_node) (by rfl)
  | memcpy => exact OriginalCode.indexed code installed 11 (entry .memcpy) (by rfl)
  | decode_witness_to_mpt => exact OriginalCode.indexed code installed 239 (entry .decode_witness_to_mpt) (by rfl)
  | htab_new => exact OriginalCode.indexed code installed 116 (entry .htab_new) (by rfl)
  | state_init => exact OriginalCode.indexed code installed 320 (entry .state_init) (by rfl)
end Code

/-- Actual global destinations in this fixed call graph, including handlers. -/
def changed : List MlS := [ofString "bs", ofString "heap_ptr", ofString "journal", ofString "journal_cap", ofString "journal_n", ofString "scratch_ptr", ofString "sk_buf", ofString "ts", ofString "ws"]

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_trap_with (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .trap_with) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_trap_with,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.sequence key code _ _
  (GlobalEffects.shared_store key code _ _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.shared_store key code _ _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.shared_store key code _ _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.external key code _ _ _ _ _)
  (GlobalEffects.raised key code _ _)))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_alloc (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .alloc) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_alloc,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with) (Code.installed code installed .trap_with) (preserves_trap_with key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with) (Code.installed code installed .trap_with) (preserves_trap_with key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.global_other key code _ _ (by intro equal; apply safe; rw [equal]; decide))
  (GlobalEffects.returned key code _))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_key_to_nibbles (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .key_to_nibbles) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_key_to_nibbles,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.assign key code _ _))))))))))))))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.assign key code _ _)))))
  (GlobalEffects.returned key code _))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_mpt_fail (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .mpt_fail) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_mpt_fail,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.sequence key code _ _
  (GlobalEffects.raised key code _ _)
  (GlobalEffects.returned key code _))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_compact_to_nibbles (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .compact_to_nibbles) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_compact_to_nibbles,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.assign key code _ _))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some none) (Code.name .key_to_nibbles) _ (Code.formals .key_to_nibbles) (Code.body .key_to_nibbles) (Code.shape .key_to_nibbles) (Code.installed code installed .key_to_nibbles) (preserves_key_to_nibbles key code installed safe))
  (GlobalEffects.returned key code _))))))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_memzero (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .memzero) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_memzero,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.assign key code _ _))))))
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.assign key code _ _))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.assign key code _ _))))))))))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.assign key code _ _)))
  (GlobalEffects.returned key code _)))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_node_new_branch (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .node_new_branch) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_node_new_branch,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some none) (Code.name .memzero) _ (Code.formals .memzero) (Code.body .memzero) (Code.shape .memzero) (Code.installed code installed .memzero) (preserves_memzero key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.returned key code _))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_node_new_leaf (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .node_new_leaf) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_node_new_leaf,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.returned key code _))))))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_rlp_fail (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .rlp_fail) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_fail,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.sequence key code _ _
  (GlobalEffects.raised key code _ _)
  (GlobalEffects.returned key code _))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_rlp_read_length (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .rlp_read_length) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_read_length,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _)))
  (GlobalEffects.returned key code _)))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_rlp_item_header (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .rlp_item_header) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_item_header,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_read_length) _ _ (Code.formals .rlp_read_length) (Code.body .rlp_read_length) (Code.shape .rlp_read_length)
  (Code.installed code installed .rlp_read_length) (preserves_rlp_read_length key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _))))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _)))
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_read_length) _ _ (Code.formals .rlp_read_length) (Code.body .rlp_read_length) (Code.shape .rlp_read_length)
  (Code.installed code installed .rlp_read_length) (preserves_rlp_read_length key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _))))))))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_scratch_alloc (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .scratch_alloc) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_scratch_alloc,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with) (Code.installed code installed .trap_with) (preserves_trap_with key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .trap_with) _ (Code.formals .trap_with) (Code.body .trap_with) (Code.shape .trap_with) (Code.installed code installed .trap_with) (preserves_trap_with key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.global_other key code _ _ (by intro equal; apply safe; rw [equal]; decide))
  (GlobalEffects.returned key code _))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves__rlp_validate_items_body (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body ._rlp_validate_items_body) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn__rlp_validate_items_body,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _))))
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_item_header) _ _ (Code.formals .rlp_item_header) (Code.body .rlp_item_header) (Code.shape .rlp_item_header)
  (Code.installed code installed .rlp_item_header) (preserves_rlp_item_header key code installed safe)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .scratch_alloc) _ _ (Code.formals .scratch_alloc) (Code.body .scratch_alloc) (Code.shape .scratch_alloc)
  (Code.installed code installed .scratch_alloc) (preserves_scratch_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _)))))))
  (GlobalEffects.assign key code _ _)))))))
  (GlobalEffects.returned key code _))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_scratch_mark (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .scratch_mark) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_scratch_mark,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.returned key code _)

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_scratch_release (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .scratch_release) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_scratch_release,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.sequence key code _ _
  (GlobalEffects.global_other key code _ _ (by intro equal; apply safe; rw [equal]; decide))
  (GlobalEffects.returned key code _))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_rlp_validate_items (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .rlp_validate_items) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_validate_items,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .scratch_mark) _ _ (Code.formals .scratch_mark) (Code.body .scratch_mark) (Code.shape .scratch_mark)
  (Code.installed code installed .scratch_mark) (preserves_scratch_mark key code installed safe)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.caught_destination key code none (Code.name ._rlp_validate_items_body) _ (Code.formals ._rlp_validate_items_body) (Code.body ._rlp_validate_items_body) (Code.shape ._rlp_validate_items_body) _ _ _
  (Code.installed code installed ._rlp_validate_items_body) (preserves__rlp_validate_items_body key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some none) (Code.name .scratch_release) _ (Code.formals .scratch_release) (Code.body .scratch_release) (Code.shape .scratch_release) (Code.installed code installed .scratch_release) (preserves_scratch_release key code installed safe))
  (GlobalEffects.raised key code _ _)))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some none) (Code.name .scratch_release) _ (Code.formals .scratch_release) (Code.body .scratch_release) (Code.shape .scratch_release) (Code.installed code installed .scratch_release) (preserves_scratch_release key code installed safe))
  (GlobalEffects.returned key code _)))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_rlp_item_total (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .rlp_item_total) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_item_total,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_item_header) _ _ (Code.formals .rlp_item_header) (Code.body .rlp_item_header) (Code.shape .rlp_item_header)
  (Code.installed code installed .rlp_item_header) (preserves_rlp_item_header key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_validate_items) _ (Code.formals .rlp_validate_items) (Code.body .rlp_validate_items) (Code.shape .rlp_validate_items) (Code.installed code installed .rlp_validate_items) (preserves_rlp_validate_items key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _)))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_rlp_list_count (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .rlp_list_count) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_list_count,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_item_total) _ _ (Code.formals .rlp_item_total) (Code.body .rlp_item_total) (Code.shape .rlp_item_total)
  (Code.installed code installed .rlp_item_total) (preserves_rlp_item_total key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _))))
  (GlobalEffects.returned key code _))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_rlp_item (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .rlp_item) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_item,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_read_length) _ _ (Code.formals .rlp_read_length) (Code.body .rlp_read_length) (Code.shape .rlp_read_length)
  (Code.installed code installed .rlp_read_length) (preserves_rlp_read_length key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _))))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_list_count) _ (Code.formals .rlp_list_count) (Code.body .rlp_list_count) (Code.shape .rlp_list_count) (Code.installed code installed .rlp_list_count) (preserves_rlp_list_count key code installed safe))
  (GlobalEffects.returned key code _))))
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_read_length) _ _ (Code.formals .rlp_read_length) (Code.body .rlp_read_length) (Code.shape .rlp_read_length)
  (Code.installed code installed .rlp_read_length) (preserves_rlp_read_length key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_list_count) _ (Code.formals .rlp_list_count) (Code.body .rlp_list_count) (Code.shape .rlp_list_count) (Code.installed code installed .rlp_list_count) (preserves_rlp_list_count key code installed safe))
  (GlobalEffects.returned key code _)))))))))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_rlp_decode_fully (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .rlp_decode_fully) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_decode_fully,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_item) _ _ (Code.formals .rlp_item) (Code.body .rlp_item) (Code.shape .rlp_item)
  (Code.installed code installed .rlp_item) (preserves_rlp_item key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .rlp_fail) _ (Code.formals .rlp_fail) (Code.body .rlp_fail) (Code.shape .rlp_fail) (Code.installed code installed .rlp_fail) (preserves_rlp_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _)))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_rlp_item_total_unchecked (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .rlp_item_total_unchecked) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_item_total_unchecked,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_read_length) _ _ (Code.formals .rlp_read_length) (Code.body .rlp_read_length) (Code.shape .rlp_read_length)
  (Code.installed code installed .rlp_read_length) (preserves_rlp_read_length key code installed safe)
  (GlobalEffects.returned key code _)))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_read_length) _ _ (Code.formals .rlp_read_length) (Code.body .rlp_read_length) (Code.shape .rlp_read_length)
  (Code.installed code installed .rlp_read_length) (preserves_rlp_read_length key code installed safe)
  (GlobalEffects.returned key code _))))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_rlp_list_to_slices (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .rlp_list_to_slices) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_list_to_slices,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_list_count) _ _ (Code.formals .rlp_list_count) (Code.body .rlp_list_count) (Code.shape .rlp_list_count)
  (Code.installed code installed .rlp_list_count) (preserves_rlp_list_count key code installed safe)
  (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_item_total_unchecked) _ _ (Code.formals .rlp_item_total_unchecked) (Code.body .rlp_item_total_unchecked) (Code.shape .rlp_item_total_unchecked)
  (Code.installed code installed .rlp_item_total_unchecked) (preserves_rlp_item_total_unchecked key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _))))))
  (GlobalEffects.returned key code _))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves__decode_step (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body ._decode_step) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.caught_destination key code (some _) (Code.name .rlp_decode_fully) _ (Code.formals .rlp_decode_fully) (Code.body .rlp_decode_fully) (Code.shape .rlp_decode_fully) _ _ _
  (Code.installed code installed .rlp_decode_fully) (preserves_rlp_decode_fully key code installed safe)
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe)))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe)))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_list_to_slices) _ _ (Code.formals .rlp_list_to_slices) (Code.body .rlp_list_to_slices) (Code.shape .rlp_list_to_slices)
  (Code.installed code installed .rlp_list_to_slices) (preserves_rlp_list_to_slices key code installed safe)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_item) _ _ (Code.formals .rlp_item) (Code.body .rlp_item) (Code.shape .rlp_item)
  (Code.installed code installed .rlp_item) (preserves_rlp_item key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .compact_to_nibbles) _ _ (Code.formals .compact_to_nibbles) (Code.body .compact_to_nibbles) (Code.shape .compact_to_nibbles)
  (Code.installed code installed .compact_to_nibbles) (preserves_compact_to_nibbles key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_item) _ _ (Code.formals .rlp_item) (Code.body .rlp_item) (Code.shape .rlp_item)
  (Code.installed code installed .rlp_item) (preserves_rlp_item key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .node_new_leaf) _ _ (Code.formals .node_new_leaf) (Code.body .node_new_leaf) (Code.shape .node_new_leaf)
  (Code.installed code installed .node_new_leaf) (preserves_node_new_leaf key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.returned key code _))))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .scratch_alloc) _ _ (Code.formals .scratch_alloc) (Code.body .scratch_alloc) (Code.shape .scratch_alloc)
  (Code.installed code installed .scratch_alloc) (preserves_scratch_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.returned key code _)))))))))))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .node_new_branch) _ _ (Code.formals .node_new_branch) (Code.body .node_new_branch) (Code.shape .node_new_branch)
  (Code.installed code installed .node_new_branch) (preserves_node_new_branch key code installed safe)
  (GlobalEffects.scoped_body key code _ _ (Code.name .scratch_alloc) _ _ (Code.formals .scratch_alloc) (Code.body .scratch_alloc) (Code.shape .scratch_alloc)
  (Code.installed code installed .scratch_alloc) (preserves_scratch_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.returned key code _))))))))))))))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_node_new_hashed (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .node_new_hashed) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_node_new_hashed,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.returned key code _))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_htab_find_leaf (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .htab_find_leaf) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_htab_find_leaf,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.stopped key code).1
  (GlobalEffects.skip key code))
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _)))))
  (GlobalEffects.returned key code _)))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_memeq (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .memeq) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _)))))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _)))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _)))))))))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.assign key code _ _))))))
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.assign key code _ _)))))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.assign key code _ _))))))))))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.assign key code _ _)))
  (GlobalEffects.returned key code _)))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_htab_get (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .htab_get) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_htab_get,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .htab_find_leaf) _ _ (Code.formals .htab_find_leaf) (Code.body .htab_find_leaf) (Code.shape .htab_find_leaf)
  (Code.installed code installed .htab_find_leaf) (preserves_htab_find_leaf key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .memeq) _ _ (Code.formals .memeq) (Code.body .memeq) (Code.shape .memeq)
  (Code.installed code installed .memeq) (preserves_memeq key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _))))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_nodedb_lookup (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .nodedb_lookup) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_nodedb_lookup,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .htab_get) _ _ (Code.formals .htab_get) (Code.body .htab_get) (Code.shape .htab_get)
  (Code.installed code installed .htab_get) (preserves_htab_get key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _)))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves__resolve_step (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body ._resolve_step) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn__resolve_step,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.caught_destination key code (some _) (Code.name .rlp_item) _ (Code.formals .rlp_item) (Code.body .rlp_item) (Code.shape .rlp_item) _ _ _
  (Code.installed code installed .rlp_item) (preserves_rlp_item key code installed safe)
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe)))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .nodedb_lookup) _ _ (Code.formals .nodedb_lookup) (Code.body .nodedb_lookup) (Code.shape .nodedb_lookup)
  (Code.installed code installed .nodedb_lookup) (preserves_nodedb_lookup key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .node_new_hashed) _ _ (Code.formals .node_new_hashed) (Code.body .node_new_hashed) (Code.shape .node_new_hashed)
  (Code.installed code installed .node_new_hashed) (preserves_node_new_hashed key code installed safe)
  (GlobalEffects.returned key code _))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _)))))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _)))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_node_new_ext (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .node_new_ext) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_node_new_ext,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.returned key code _)))))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves__decode_witness_node_body (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body ._decode_witness_node_body) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name ._decode_step) _ _ (Code.formals ._decode_step) (Code.body ._decode_step) (Code.shape ._decode_step)
  (Code.installed code installed ._decode_step) (preserves__decode_step key code installed safe)
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _))
  (GlobalEffects.assign key code _ _))))))
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name ._resolve_step) _ _ (Code.formals ._resolve_step) (Code.body ._resolve_step) (Code.shape ._resolve_step)
  (Code.installed code installed ._resolve_step) (preserves__resolve_step key code installed safe)
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _)))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _)))))))
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.skip key code))
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .node_new_ext) _ _ (Code.formals .node_new_ext) (Code.body .node_new_ext) (Code.shape .node_new_ext)
  (Code.installed code installed .node_new_ext) (preserves_node_new_ext key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _))))))))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _)))
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .rlp_item) _ _ (Code.formals .rlp_item) (Code.body .rlp_item) (Code.shape .rlp_item)
  (Code.installed code installed .rlp_item) (preserves_rlp_item key code installed safe)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.skip key code))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.assign key code _ _))))))))))))))))))))))
  (GlobalEffects.returned key code _)))))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves__decode_witness_node_mpt (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body ._decode_witness_node_mpt) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn__decode_witness_node_mpt,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.caught_destination key code (some _) (Code.name ._decode_witness_node_body) _ (Code.formals ._decode_witness_node_body) (Code.body ._decode_witness_node_body) (Code.shape ._decode_witness_node_body) _ _ _
  (Code.installed code installed ._decode_witness_node_body) (preserves__decode_witness_node_body key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some none) (Code.name .scratch_release) _ (Code.formals .scratch_release) (Code.body .scratch_release) (Code.shape .scratch_release) (Code.installed code installed .scratch_release) (preserves_scratch_release key code installed safe))
  (GlobalEffects.raised key code _ _)))
  (GlobalEffects.returned key code _))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves__decode_witness_node (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body ._decode_witness_node) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn__decode_witness_node,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .scratch_mark) _ _ (Code.formals .scratch_mark) (Code.body .scratch_mark) (Code.shape .scratch_mark)
  (Code.installed code installed .scratch_mark) (preserves_scratch_mark key code installed safe)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.caught_destination key code (some _) (Code.name ._decode_witness_node_mpt) _ (Code.formals ._decode_witness_node_mpt) (Code.body ._decode_witness_node_mpt) (Code.shape ._decode_witness_node_mpt) _ _ _
  (Code.installed code installed ._decode_witness_node_mpt) (preserves__decode_witness_node_mpt key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some none) (Code.name .scratch_release) _ (Code.formals .scratch_release) (Code.body .scratch_release) (Code.shape .scratch_release) (Code.installed code installed .scratch_release) (preserves_scratch_release key code installed safe))
  (GlobalEffects.raised key code _ _)))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some none) (Code.name .scratch_release) _ (Code.formals .scratch_release) (Code.body .scratch_release) (Code.shape .scratch_release) (Code.installed code installed .scratch_release) (preserves_scratch_release key code installed safe))
  (GlobalEffects.returned key code _))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_memcpy (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .memcpy) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_memcpy,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.assign key code _ _))))))
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.assign key code _ _))))
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.assign key code _ _))))))))))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.loop key code _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.byte_store key code _ _)
  (GlobalEffects.assign key code _ _)))
  (GlobalEffects.returned key code _)))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_decode_witness_to_mpt (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .decode_witness_to_mpt) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_decode_witness_to_mpt,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .memeq) _ _ (Code.formals .memeq) (Code.body .memeq) (Code.shape .memeq)
  (Code.installed code installed .memeq) (preserves_memeq key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.returned key code _)
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name .nodedb_lookup) _ _ (Code.formals .nodedb_lookup) (Code.body .nodedb_lookup) (Code.shape .nodedb_lookup)
  (Code.installed code installed .nodedb_lookup) (preserves_nodedb_lookup key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.call_body key code (some none) (Code.name .mpt_fail) _ (Code.formals .mpt_fail) (Code.body .mpt_fail) (Code.shape .mpt_fail) (Code.installed code installed .mpt_fail) (preserves_mpt_fail key code installed safe))
  (GlobalEffects.skip key code))
  (GlobalEffects.scoped_body key code _ _ (Code.name ._decode_witness_node) _ _ (Code.formals ._decode_witness_node) (Code.body ._decode_witness_node) (Code.shape ._decode_witness_node)
  (Code.installed code installed ._decode_witness_node) (preserves__decode_witness_node key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some none) (Code.name .memcpy) _ (Code.formals .memcpy) (Code.body .memcpy) (Code.shape .memcpy) (Code.installed code installed .memcpy) (preserves_memcpy key code installed safe))
  (GlobalEffects.store key code _ _)))
  (GlobalEffects.skip key code))
  (GlobalEffects.returned key code _)))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_htab_new (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .htab_new) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_htab_new,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.declared key code _ _ _ _
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.conditional key code _ _ _
  (GlobalEffects.assign key code _ _)
  (GlobalEffects.skip key code))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.scoped_body key code _ _ (Code.name .alloc) _ _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc)
  (Code.installed code installed .alloc) (preserves_alloc key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.returned key code _)))))))))))))))))))

-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_state_init (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .state_init) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_state_init,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact (GlobalEffects.sequence key code _ _
  (GlobalEffects.global_call_body key code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc) (by intro equal; apply safe; rw [equal]; decide) (Code.installed code installed .alloc) (preserves_alloc key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.scoped_body key code _ _ (Code.name .decode_witness_to_mpt) _ _ (Code.formals .decode_witness_to_mpt) (Code.body .decode_witness_to_mpt) (Code.shape .decode_witness_to_mpt)
  (Code.installed code installed .decode_witness_to_mpt) (preserves_decode_witness_to_mpt key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.scoped_body key code _ _ (Code.name .htab_new) _ _ (Code.formals .htab_new) (Code.body .htab_new) (Code.shape .htab_new)
  (Code.installed code installed .htab_new) (preserves_htab_new key code installed safe)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.global_call_body key code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc) (by intro equal; apply safe; rw [equal]; decide) (Code.installed code installed .alloc) (preserves_alloc key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some (some _)) (Code.name .htab_new) _ (Code.formals .htab_new) (Code.body .htab_new) (Code.shape .htab_new) (Code.installed code installed .htab_new) (preserves_htab_new key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some (some _)) (Code.name .htab_new) _ (Code.formals .htab_new) (Code.body .htab_new) (Code.shape .htab_new) (Code.installed code installed .htab_new) (preserves_htab_new key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some (some _)) (Code.name .htab_new) _ (Code.formals .htab_new) (Code.body .htab_new) (Code.shape .htab_new) (Code.installed code installed .htab_new) (preserves_htab_new key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some (some _)) (Code.name .htab_new) _ (Code.formals .htab_new) (Code.body .htab_new) (Code.shape .htab_new) (Code.installed code installed .htab_new) (preserves_htab_new key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some (some _)) (Code.name .htab_new) _ (Code.formals .htab_new) (Code.body .htab_new) (Code.shape .htab_new) (Code.installed code installed .htab_new) (preserves_htab_new key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some (some _)) (Code.name .htab_new) _ (Code.formals .htab_new) (Code.body .htab_new) (Code.shape .htab_new) (Code.installed code installed .htab_new) (preserves_htab_new key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.call_body key code (some (some _)) (Code.name .htab_new) _ (Code.formals .htab_new) (Code.body .htab_new) (Code.shape .htab_new) (Code.installed code installed .htab_new) (preserves_htab_new key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.store key code _ _)
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.global_call_body key code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc) (by intro equal; apply safe; rw [equal]; decide) (Code.installed code installed .alloc) (preserves_alloc key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.global_other key code _ _ (by intro equal; apply safe; rw [equal]; decide))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.global_call_body key code _ (Code.name .alloc) _ (Code.formals .alloc) (Code.body .alloc) (Code.shape .alloc) (by intro equal; apply safe; rw [equal]; decide) (Code.installed code installed .alloc) (preserves_alloc key code installed safe))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.global_other key code _ _ (by intro equal; apply safe; rw [equal]; decide))
  (GlobalEffects.sequence key code _ _
  (GlobalEffects.global_other key code _ _ (by intro equal; apply safe; rw [equal]; decide))
  (GlobalEffects.returned key code _))))))))))))))))))))))))))))))))

end InitECandidate.Solver.Mpt.StateInitGlobals

#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.Code.installed
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_trap_with
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_alloc
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_key_to_nibbles
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_mpt_fail
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_compact_to_nibbles
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_memzero
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_node_new_branch
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_node_new_leaf
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_rlp_fail
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_rlp_read_length
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_rlp_item_header
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_scratch_alloc
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves__rlp_validate_items_body
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_scratch_mark
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_scratch_release
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_rlp_validate_items
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_rlp_item_total
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_rlp_list_count
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_rlp_item
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_rlp_decode_fully
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_rlp_item_total_unchecked
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_rlp_list_to_slices
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves__decode_step
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_node_new_hashed
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_htab_find_leaf
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_memeq
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_htab_get
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_nodedb_lookup
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves__resolve_step
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_node_new_ext
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves__decode_witness_node_body
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves__decode_witness_node_mpt
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves__decode_witness_node
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_memcpy
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_decode_witness_to_mpt
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_htab_new
#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_state_init
