# mean Copilot Instructions

## Build, test, and lint commands

- Install the Lean toolchain with `elan`, then run `lake build` to type-check the full formalization.
- For the smallest useful targeted check, run a single Lean file with `lake env lean Mean/Basic.lean` or `lake env lean Mean/Step.lean`.
- There is no separate lint or runtime test suite in this repository; proof checking happens through Lean compilation.

## High-level architecture

- This repository is a single Lean library, `Mean`, with the root module `Mean.lean` importing the four substantive modules in dependency order: `Basic`, `Nest`, `Subst`, and `Step`.
- `Mean/Basic.lean` defines the core object language and metatheory scaffolding: the `Ty`, `Expr`, `Program`, and `Computation` types; typing relations; local-reference predicates; boundedness and valid-reference predicates; and the `Program.Prefix` machinery used to reason about program extension without changing existing labels.
- `Mean/Nest.lean` adds the global graph structure that is not obvious from `Basic.lean` alone: free variables can flow through referenced functions, `Program.Nests`/`NestsEq` encode nesting, `Program.Succ` and `Program.PathWithout` encode CFG-style reachability, and `Program.Dominates` connects the nesting story back to dominance.
- `Mean/Subst.lean` is the bridge from static structure to evaluation. Substitution is map-based (`VarMap`, `FunMap`) and can extend the program with fresh function labels when a substituted variable is free inside reachable nested functions. Most preservation lemmas here are phrased in terms of `Program.Prefix` because substitution may grow the program while keeping old entries unchanged.
- `Mean/Step.lean` defines the small-step semantics over `Computation` and proves progress, preservation, and soundness on top of the substitution machinery.
- The module split mirrors the paper structure: basic syntax and typing, then nesting/dominance, then substitution, then operational semantics.
- This repo is the Lean formalization of the `λ_G` core that underpins the broader C++ MimIR implementation in `../mimir`. When terminology or intent is unclear, align with the concepts documented there, especially “SSA without dominance”, free-variable nesting, and the long-term goal of a Lean reimplementation of MimIR.

## Key conventions

- Program labels are plain `Nat` indices into three synchronized vectors: `fn`, `ty`, and `ret`. Many proofs rely on that representation, so preserve index-based reasoning instead of introducing alternative label abstractions.
- Expressions and programs do not enforce reference validity structurally. Use typing assumptions or the explicit predicates `Expr.ValidRefs` and `Program.ValidRefs` whenever a proof needs bounds facts.
- Distinguish **local references** from **free variables**. `Expr.Local` is purely syntactic, while `Expr.Free` in `Nest.lean` traverses through referenced function bodies; do not treat them as interchangeable.
- Substitution is not simple tree replacement. It may clone reachable nested functions, assign fresh labels, and return a larger program. Reuse `Expr.subst`, `Computation.subst`, `VarMap`, `FunMap`, and the existing prefix-preservation lemmas instead of inventing ad hoc substitution helpers.
- The codebase leans heavily on Lean automation: `simp`, `grind`, `grind_pattern`, `solve_by_elim`, `omega`, `lia`, and `fun_induction` are part of the normal proof style. New lemmas are more useful when they are phrased so this automation can consume them, and when appropriate they should be registered with the same attributes as nearby lemmas.
- Keep the established notation and naming from the paper and the code: `Nests`/`NestsEq` for strict/non-strict nesting, Unicode notations such as `⊢`, `⇒`, `⇒*`, `≻`, `≽`, and `⟶`, and theorem names that closely track the formal statement they prove.
