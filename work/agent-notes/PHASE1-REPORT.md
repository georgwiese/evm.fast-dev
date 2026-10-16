# Phase 1: baseline step counts

Measured on 2026-10-16. The current guest passes all 33,614 EEST records.
These are Spike measurements, not a certified evaluator bound. Phase 2 has
checked cost lemmas but no finite certificate; claim.json remains infinity.

## Artifact and reproducibility

Installed the pinned Flapjack compiler, Spike submodule, cross-binutils and
public EEST fixtures after the user authorized installing missing dependencies.
Fixture release: execution-specs `tests-zkevm@v21.0.1`. Flapjack revision:
`034bb5a1ed0b757082768d5406206bd2f8e31b7c`. Commands, failed attempts and
resource measurements are in PROGRESS.md and its logs directory.

The rebuilt ELF **does not match BASELINE.json**. Current artifacts:

| Artifact | SHA-256 |
|---|---|
| guest/build/guest.elf | af59ed6b844728699f84d400c4195e3765e1829465ae1fb6b6149fa869a1215e |
| Guest/guest.pp.pnk (matches fresh CPP output) | 414d70d031f9e367ad9e5c70bc6dbd523238a3c542fba59a09aed866f3e5f860 |
| Guest/Ast.lean | 21925d793b4159c30406a4d48a7402d4a2cdc23e0189201342aa89778d4534ed |
| Current ROM, 950,344 bytes | 22a1dd0963f12a3492e647b2626101fad2312dfcff813978b8ff1aca9897d7cc |

The ROM reconstructed from submission Prefix/Bytes/Suffix literals is byte-for-byte
identical to `objcopy -O binary guest/build/guest.elf`. This was a file comparison,
not a Lean artifact-equality proof. The source and AST hashes also differ from
BASELINE.json, so historical counts are comparisons, not exact reproductions.

## Full EEST results

| Population | Records | Minimum | Maximum | Mean Spike instructions |
|---|---:|---:|---:|---:|
| All records | 33,614 | 48,245 | 12,288,467,579 | 8,980,605.947 |
| Declared gas ≤ 200M | 32,444 | 48,245 | 4,654,270,509 | 8,478,606.534 |

33,605 PASS(full), nine PASS(malformed), no failures. Historical minimum 48,236,
maximum 12,288,467,569 and rounded mean 8,980,596 are respectively nine, ten and
approximately ten instructions lower. The corpus maximum has declared gas
334,862,111 and is outside the challenge's gas premise. The covered maximum is
`29895_test_valid_gas_g2msm_fork_Amsterdam-discount_table_6_of_8-blockchain_test_from_state_test-precom`.

The highest observed ratio among covered cases is **5,168.308 instructions per
payload gasUsed**, from BN254 pairing case
`28355_test_pairing_test_fork_Amsterdam-blockchain_test_from_state_test-d5-g0__b0`:
770,000,402 instructions, gasUsed 148,985, declared limit 14,012,015, input 6,093
bytes. This ratio includes startup and all block work. gasUsed is the input
payload's claim, not an independently instrumented EVM consumption counter.
The declared limit is parsed with the fixed Guest.GasLimit reader's offsets and
zero-extension semantics. Passing fixture checks do not prove a universal bound.

Full joined per-fixture data: `work/baseline-steps/steps-and-gas.json`.
Compact tracked summary: `work/agent-notes/eest-summary.json`.
Run: 14 workers, 10m39.17s wall; maximum child RSS 148,216 KiB; sampled process
group RSS sum 644,268 KiB (shared pages may be counted repeatedly); at least
26,038,372 KiB host memory available; disk at most 44% during that run.

## Spike and the formal clock

`evaluateTargetHOL` is noncomputable. Its classical decisions and predicate-valued
memory domains prevent direct Lean #eval. No executable mirror/agreement proof
was built, so there is no measured formal-clock count here.

Source inspection of TargetSem/Evaluate.lean and InitE/MachineInitialization.lean:
ordinary dispatch performs one native `next` and consumes one clock unit after
state/code/frame checks; FFI, cache and terminal dispatch each consume one unit.
Crypto computation inside the oracle has no additional evaluator clock cost.
Spike counts retired instructions in the concrete runtime stubs and trap handler.
For example, a crypto CSR/return stub plus its two-instruction dispatch slot is
four Spike instructions versus one formal foreign-call transition. PTRS2 and
PTRS5 ABI wrappers use respectively 11 and 17 instructions including the slot.
The terminal handler and cache stub also need separate corrections. Thus there
is no single constant to subtract from every corpus count. A formal comparison
must prove state/ABI agreement and count each dispatch kind; it cannot simply
assert that Spike and evaluator clocks agree.

Current bootstrap disassembly copies 4,617 words. Its 52 static instructions
include a five-instruction loop, giving 52 + 5*(4617−1) = **23,132** executed
RV instructions. A Spike breakpoint at native entry 0x80001190 measured exactly
23,132. The existing BootstrapTrace theorem's 23,120 is an *ASM-operation*
count; encodings can contain multiple RV instructions. Its evaluator theorem
currently hides the native count existentially. Historical documentation's
23,127 hardware count is stale for these bytes.

Normal batched execution of empty malformed input gives 48,245; single-step
breakpoint mode gives 48,244. Repeated runs agree: the fine loop polls the halt
flag immediately after its store, whereas the normal batch retires the following
WFI (Spike execute.cc counts it). All results in the tables use normal batching.

## Whole-guest synthetic blocks and malformed inputs

These use the exact current guest ELF. Exits were zero and output bytes were
saved, but arbitrary synthetic blocks have no EEST conformance assertion.

| Input, all declared gas zero | Input bytes / entries | Instructions |
|---|---:|---:|
| malformed empty | 0 bytes | 48,245 |
| malformed zeros | 1,048,576 bytes | 1,227,907 |
| malformed zeros | 16,777,216 bytes | 18,922,627 |
| malformed zeros at arena limit | 134,217,712 bytes | 151,043,185 |
| advertised length too large | 134,217,713 bytes | 47,137 |
| structured payload with withdrawals, no headers | 4,096 withdrawals | 31,501,167 |
| duplicate 64 KiB witness codes, one header | 256 entries | 110,913,261 |
| duplicate 64 KiB witness codes, one header | 2,047 entries / 134,161,654 bytes | 885,793,643 |
| distinct 32-byte witness codes, one header | 65,536 entries | 89,329,386 |
| distinct 32-byte witness codes, one header | 1,048,576 entries / 37,750,010 bytes | 1,426,789,894 |

Bulk malformed copying has measured slope 9/8 instructions per byte. Oversized
transport is clipped to the host-visible arena while retaining the original
length word, avoiding writes outside the arena by the Spike loader. The formal
input type is unbounded; any proof must justify this observational reduction.

The first structured cases have no headers: failure byte 3 rejects them before
witness ingestion or withdrawal execution. They measure decoding/payload hashing.
The later cases use a public passing fixture's RLP header (provenance saved).
All have failure byte **4**, after nodedb_build for state and code, at the empty
transaction check. They establish that witness hashing/table construction runs
at zero user gas. They do not execute the EVM. Distinct code hashes are ordinary
hash outputs, not deliberately colliding table keys.

## Library and opcode diagnostics

`work/agent-notes/microbench.pnk` includes unchanged guest functions with a new
main. This separate executable is not the challenge program. Counts include
loop/operand setup; incremental costs subtract an identical zero-iteration run.

| Work | Incremental instructions |
|---|---:|
| 64 KiB all-JUMPDEST bitmap, ten rebuilds | 11,184,130 (17.066/byte/rebuild) |
| 64 KiB aligned memcpy, ten copies | 348,890 (0.53236/byte/copy) |
| 64 KiB unaligned memcpy, ten copies | 2,949,800 (4.50104/byte/copy) |
| 1,024 colliding 52-byte keys via htab_set | 56,598,966 |
| 4,096 colliding 52-byte keys via htab_set | 895,378,232 |

The keys vary two equal 64-bit chunks: htab_hash XOR-folds them, so all hashes
collide at every capacity. Measured cost approaches **53.4 N²** including growth.
This is a library construction; full-block reachability/gas accounting is unproved.
A bitmap rebuild costs about 1,118,413 instructions. Attributing only a warm
CALL's 100 gas would yield 11,184 instructions/gas, but that excludes operand,
call setup and other transaction charges, so it is not a measured block ratio.

Direct opcode calls, maximum over three operand patterns, incremental instructions
per gas actually charged by those opcode functions: ADD 185.67, MUL 241.4,
DIV 1,288.4, MOD 1,288.8, ADDMOD 883, MULMOD 1,493.75, EXP 158.75. The diagnostic
includes operand setup and excludes dispatcher/operand-opcode gas. These are
samples, not maxima over all U256 operands. In the corpus, software pairing and
multiscalar multiplication dominate the expensive cases; accelerators' internal
host runtime is outside both the native instruction count and formal clock.

## Candidate envelope and uncertainty

A deliberately loose **proof-planning target**, not a proven bound, is

    K_design(G, B) = 10,000,000·G + 10,000,000·B + 1,000,000,000,000

where G is declared gas and B is the visible input length, capped only after
proving the oversized-input rejection case. At G=200,000,000 and B=134,217,712
this is **3,343,177,120,000,000**, below 9,007,199,254,740,985. The coefficients
are slack allocated for proof engineering, not regression estimates or measured
worst-case constants. Confidence that this is a universal bound is **low**;
confidence in the reported execution measurements is high. Do not put this K
in claim.json without the missing proof. A quadratic or multivariate potential
may be necessary before reducing bounded domains to a linear envelope.

Key unresolved charging obligations:

- Collision chains, table growth, deletion and rollback require adversarial
  bounds. Expected constant-time hashing is inapplicable.
- Every frame rebuilds jump destinations. SSZ and CREATE both enforce the
  65,536-byte code limit, but repeated sequential calls remain possible. The
  63/64 rule bounds nested forwarding, not total calls or rescans by itself.
- Memory expansion has quadratic gas, while copy alignment changes instruction
  cost. Gas pools, refunds and failed execution paths need precise invariants.
- System calls have independent 30M gas budgets. Witness, input, output,
  withdrawals and initialization need non-user-gas terms.
- ALLOC-AUDIT/JOURNAL-BOUND contain older memory-layout and trap assumptions.
  The current challenge excludes outcomes 1, 6 and 7; traps 4 and 5 remain
  covered. Read the actual definitions rather than importing the old envelope.

Tracked measurements: synthetic-measurements.json, witness-measurements.json,
microbench-measurements.json, opcode-measurements.json. Raw outputs and generated
input files remain under work/baseline-steps. No full audit or verifier was run.
