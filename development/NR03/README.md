# NR-03 remote development compiler

This directory is a scratch-ready copy of the NR-03 proof candidate for bounded
Linux compiler feedback. It is **not** authoritative Lean verification, a
Comparator result, a final proof review, or a solved-status claim. The
canonical NR-03 target and its statement-stage boundary are unchanged.

Formalization: **George Stepaniants**, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA, with
AI-agent assistance. The underlying mathematical counterexample is attributed
to Sidney Holden; the retained Colbrook material remains historical partial
background. No email is included.

## Exact inputs

`NLA/NR03/Definitions.lean` and `Challenge.lean` are copied byte-for-byte from
NR-03 candidate commit `e788494836d075c2ff9e75729634c0fdf812a29a`. `Solution.lean`
is the author optimization proposal `decide +kernel` plus the structural core
reduction, SHA-256
`4224164dd803b1d0418694acee1318517da39b47b16fd110955af42e7f779f28`.
`SOURCE_INPUTS.json` binds every committed input and the workflow. The source
boundary remains the full real Boolean-vector target; no certificate data are
trusted and no target quantifier is weakened.

The ten dependency revisions are retained in `lake-manifest.json`: LeanCert,
Mathlib, Plausible, LeanSearchClient, importGraph, ProofWidgets, Aesop, Qq,
Batteries and Cli. The toolchain is Lean 4.33.1. The `formalization.yaml` and
`comparator.json` files are retained as metadata context only; this workflow
does not execute Comparator or promote any status.

## Remote-only bounded run

The dedicated workflow is `.github/workflows/lean-nr03-development.yml` and is
restricted to `codex/lean-nr03-nonnegative-rank`. On Ubuntu 24.04 it installs the
pinned toolchain, runs `lake env true`, obtains the Mathlib development cache,
checks all ten dependency revisions, compiles the directly imported LeanCert
verification module, then attempts the two project modules in order:

1. `NLA.NR03.Definitions`
2. `Solution`

Every direct Lean process uses `-M4096 -j1` and a GNU `timeout` of 120 seconds.
The driver records a dependency graph, command arguments, elapsed time, raw
stdout/stderr, return codes, source copies, before/after SHA-256 inventories,
and a final `result.json`, including when a setup or module step fails. A
failed dependency skips only descendants; independent modules are still
attempted. No aggregate `lake build` is run.

This package must run on Linux GitHub Actions only. Do not run Lean, Lake,
cache setup, or dependency compilation locally. The artifact is development
feedback only. A green run does not establish Comparator matching, permitted
axioms, statement correspondence, independent final review, or Lean-verified
status; those are separate gates.

## Reproduction inputs

The eventual remote branch should preserve the package under
`development/NR03` and the workflow under `.github/workflows`. The first step
is always `--record-inputs`; the second is `--compile`. The live canonical
NR-03 job is independent of this package and must not be canceled or restarted
because of observation.
