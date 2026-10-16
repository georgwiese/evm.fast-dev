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
