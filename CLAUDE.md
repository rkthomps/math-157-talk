# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Purpose

This is a Lean 4 project containing lecture examples for a Math 157 talk on Lean. The examples demonstrate:
- Software verification (proving correctness of programs)
- Metaprogramming in Lean 4

The talk covers: verified foundations, proof automation, and the `grind` tactic. See `plan.md` for the lecture outline.

## Common Commands

```bash
# Build the project
lake build

# Run the executable
lake exec examples

# Check/elaborate a single file (useful during development)
lake build Examples.InsertionSort
```

Lean's language server (via VS Code or the Lean 4 extension) is the primary way to interact with proofs interactively — hover over terms to see types, click into goals, etc.

## Architecture

- **`lakefile.toml`** — defines two targets: the `Examples` library and the `examples` executable (`Main.lean`)
- **`Examples.lean`** — library root; import new modules here to include them in the build
- **`Examples/InsertionSort.lean`** — main content: insertion sort implementation, a `is_sorted`/`is_permutation` specification, and partially-complete correctness proofs (several `sorry`s remain)
- **`Main.lean`** — thin executable entry point; imports `Examples`
- **Toolchain**: Lean `v4.29.1` (pinned in `lean-toolchain`); no external Lake packages

## Proof Status

`Examples/InsertionSort.lean` has intentional `sorry`s in:
- `insert_preserves_sortedness` (Case 2: `x > y` branch)
- `insertion_sort_correct` (both the `is_sorted` and `is_permutation` goals in the cons case)

These are likely left incomplete as live demo material for the lecture.
