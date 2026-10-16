# Phase 1: baseline step counts

Status: setup underway; no new guest execution measurements yet.

The repository reports 33,614 records, minimum 48,236, maximum 12,288,467,569
and rounded mean 8,980,596 Spike instructions for its zero-RAM run. These are
historical claims, not reproduced measurements. The referenced results file
and ELF were not present in this checkout.

## Measurement distinctions

`tools/spike/spike_run.cc` measures the difference in `minstret` around the
whole run, including runtime stubs and the host trap handler. `handler.s` uses
WFI to stop instruction batches at halt. The formal evaluator dispatches FFI
and cache operations through hooks. A direct count conversion must account for
each stub's expansion and the halt handler; it cannot use the corpus maximum
as a certified K. Accelerator host computation is not charged as RV steps.

BootstrapTrace proves 23,120 *ASM* operations, but each may encode multiple
RV instructions. Its evaluator theorem hides the target count existentially.
The documented 23,127 hardware steps are not yet independently reproduced.

## Static candidates for expensive work

- `compute_jumpdests` scans contract code on every frame creation, including
  a warm call. Code bytes scanned need charging to call count and code size.
- `htab_hash` folds 64-bit chunks with XOR before its final avalanche.
  Equal folds collide at every table capacity. Probing, insertion, growth,
  deletion and rollback therefore require adversarial rather than average bounds.
- `input_blob` copies eight bytes per loop before schema validation; the length
  check uses INPUT_MAX_BYTES. Invalid lengths trap with covered code 8.
- Witness processing, withdrawals, system calls, output and startup need costs
  independent of user transaction gas. System transactions receive 30M gas.
- Memory growth/copy, U256 arithmetic, precompile implementations and call
  access-set merging still need measurements and a path-by-path audit.

No measured worst steps/gas ratio or defensible numeric coefficients a,b,c
are available yet. A linear envelope can absorb bounded quadratic costs only
after bounding their domains; a fitted average is not such a bound.

## Current-source checks

The converted corpus has exactly 33,614 records (fresh conversion).
Current CPP output matches Guest/guest.pp.pnk: SHA-256
`414d70d031f9e367ad9e5c70bc6dbd523238a3c542fba59a09aed866f3e5f860`.
Current Guest/Ast.lean SHA-256:
`21925d793b4159c30406a4d48a7402d4a2cdc23e0189201342aa89778d4534ed`.
Both differ from BASELINE.json. Reconstructing the exact literal byte lists
(Prefix000..001, Bytes000..220, Suffix000..010) gives 950,344 bytes, SHA-256
`22a1dd0963f12a3492e647b2626101fad2312dfcff813978b8ff1aca9897d7cc`.
No Lean artifact-equality proof was run for this reconstruction.

Binutils disassembly of the current literals gives data endpoints 0xa0020000
and 0xa0029048: 4,617 copy iterations. The 208-byte startup has 52 RV64
instructions, including a five-instruction copy loop. Static execution count
is therefore 52 + 5*(4617-1) = 23,132, not the historical 23,127. The current
Guest/Bookkeeping.lean agrees with the literals; the documentation is stale.
The data pointer delta accounts for five more bootstrap instructions.
A Spike breakpoint measurement is planned to check this static count.

The witness decoder explicitly limits each code blob to 65,536 bytes
(types.h MAX_BYTES_PER_CODE; ssz.pnk decode_bytes_list). This bounds the code
scan even for arbitrary pre-state witnesses; relying only on CREATE's size
limit would have missed that separate obligation. Oversized synthetic code
inputs test early rejection, not huge executable contracts.

## Fresh measurements (current artifact, 2026-10-16)

Built guest ELF SHA-256:
`af59ed6b844728699f84d400c4195e3765e1829465ae1fb6b6149fa869a1215e`.
`objcopy -O binary` output is byte-identical to the reconstructed submitted ROM.
ELF build: 21.87 s; maximum child RSS 901,228 KiB. The historical ELF hash does
not match, so the new corpus result will be a current-revision measurement.

A breakpoint at native entry 0x80001190 measures **23,132** retired bootstrap
instructions, agreeing with the disassembly calculation. Empty malformed input
then halts at 48,245 instructions with normal batching, 48,244 with single-step
breakpoint mode. Repeated runs reproduce the one-count difference: fine mode
stops immediately when the handler stores the halt flag; normal batches execute
the following WFI. Spike execute.cc increments instret for that WFI. All corpus
and synthetic counts below use normal batching. This is a harness-boundary
difference, not nondeterminism or a guest-speed change.

Whole-guest synthetic inputs (all process exits zero; outputs recorded, no
conformance claim for arbitrary synthetic blocks):

| Input | Input bytes / count | Spike instructions |
|---|---:|---:|
| malformed empty | 0 | 48,245 |
| malformed zeros | 1,024 | 49,411 |
| malformed zeros | 1,048,576 | 1,227,907 |
| malformed zeros | 16,777,216 | 18,922,627 |
| malformed zeros at arena limit | 134,217,712 | 151,043,185 |
| advertised length one byte too large | 134,217,713 | 47,137 |
| structured SSZ, zero gas, 1 withdrawal | 1 withdrawal | 145,308 |
| structured SSZ, zero gas, 256 withdrawals | 256 withdrawals | 2,100,011 |
| structured SSZ, zero gas, 4,096 withdrawals | 4,096 withdrawals | 31,501,167 |

Zero-filled malformed inputs have declared gas zero. Bulk copying after the
small-input boundary has measured slope 9/8 = 1.125 instructions/byte. This
does not cover other decoders. Withdrawal cases include payload hashing but
may reject before executing withdrawals; do not infer execution cost from them.
Oversized input transport is clipped to the host's visible arena while retaining
the original length word. This matches the fixed host's address clipping; it
avoids a Spike loader fault outside the arena. The guest reports trap marker
and code in the saved output; its formal outcome has not been kernel-evaluated.

## Library diagnostics (separate executable)

`microbench.pnk` includes unchanged guest library functions with a diagnostic
main. This is not the challenge program and does not prove full-block reachability.
Measured steps include its own startup and driver. Incremental costs subtract
the zero-iteration case with identical size.

| Work | Measured incremental Spike cost |
|---|---:|
| 64 KiB all-JUMPDEST bitmap, 10 rebuilds | 11,184,130 (17.066/byte per rebuild) |
| 64 KiB aligned memcpy, 10 copies | 348,890 (0.53236/byte per copy) |
| 64 KiB unaligned memcpy, 10 copies | 2,949,800 (4.50104/byte per copy) |
| 1,024 colliding 52-byte keys via htab_set | 56,598,966 |
| 4,096 colliding 52-byte keys via htab_set | 895,378,232 |

Hash-table cost approaches about **53.4 N² instructions** in this measured
range, including growth. Keys vary two equal 64-bit chunks, so the XOR fold
and final hash are identical for all keys, not merely for the initial capacity.
A generous 100-gas-per-insertion attribution would give about 2,186 instructions
per gas at N=4096, but this is a diagnostic quotient: no EVM gas was actually
charged by the harness, and a full transaction has additional costs.
The repeated-call bitmap cost alone is about 11,184 instructions per 100 gas
for a 64 KiB callee, ignoring additional CALL setup and operand gas.

Raw records: work/baseline-steps/synthetic-run/results.json and
work/baseline-steps/microbench-run/results.json. Full corpus run is ongoing.
