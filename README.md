# Mean

[![Build](https://img.shields.io/github/actions/workflow/status/mimir/mean/build.yml?style=flat-square&logo=github&label=Build&branch=master)](https://github.com/mimir/mean/actions/workflows/build.yml?query=branch%3Amaster)

This repository contains the Lean formalisation of $\lambda_G$, the graph-based $\lambda$-calculus from the paper *“SSA without Dominance for Higher-Order Programs”*.
It proves the paper's lemmas and theorems — in particular the correspondence between nesting and dominance, and basic soundness (progress and preservation).

## Vision: MimIR in Lean

The formalisation in this repository is the first step towards a much larger goal: a full **reimplementation of [MimIR](https://github.com/mimir/mimir) in [Lean](https://lean-lang.org)**.

MimIR is a pure, graph-based, higher-order intermediate representation rooted in the Calculus of Constructions.
Its structural foundation — free-variable nesting instead of CFG dominance — is exactly the theory that $\lambda_G$ formalises here.
Today MimIR is written in C++, where its type checker, normalizers, and transformations are trusted but unverified.

Reimplementing MimIR in Lean lets the *specification* and the *implementation* live in the same language:

- **One source of truth.**
  The metatheory in this repository (typing, substitution, nesting/dominance, progress, and preservation) becomes the ground on which the implementation is built, rather than a separate paper artefact that can drift from the code.
- **Verified core.**
  Type checking, β-reduction/normalization, and the core rewrites can be proved correct against the semantics — turning today's trusted C++ kernel into a machine-checked one.
- **Executable formalisation.**
  Lean is both a proof assistant and a programming language, so the same definitions that we reason about can be compiled and run, closing the gap between "the model" and "the compiler".
- **Extensibility with guarantees.**
  MimIR's plugin/axiom architecture (domain-specific types, normalizers, and phases) can be given typed interfaces and correctness obligations, so extensions inherit soundness by construction.

The path from here to there is incremental.
`mean` currently covers the graph-based λ-calculus core; future work grows it towards MimIR's full feature set — dependent types, parametric and higher-kinded polymorphism, the sea-of-nodes representation with hash-consing and on-the-fly normalization, and eventually plugins and lowering.
The documentation and module structure below will evolve alongside that effort.

## Checking the proofs

The Lean version manager `elan` needs to be installed.
The project can then be built and checked with

```sh
lake build
```

## Project structure

This section maps the paper's definitions and results to their location in the code.

- The basic language definition and type system is contained in [`Mean/Basic.lean`](Mean/Basic.lean).
  The types `Expr` and `Program` correspond to expressions and programs in the paper; a `Computation` is a pair consisting of a program and an expression and is used in the small-step reduction relation.
  Labels are simply natural numbers here.
  For both expressions and programs, a predicate `ValidRefs` is defined that states that all labels that appear in expressions actually exist in the program.
  These are implied by typing assumptions.
  Local variables and functions are also defined here under the name `Local`.

- Free variables (`Expr.Free`) and the nesting relation are defined in [`Mean/Nest.lean`](Mean/Nest.lean).
  The strict nesting relation ($\succ$) is called `Nests`, while the non-strict version ($\succeq$) is called `NestsEq`.
  This file also defines control-flow successors and dominance.
  The theorems `Expr.free_in_fn_of_succ` and `Expr.free_in_fn_of_pathWithout` correspond to Lemma 1 and Lemma 2 in the paper.
  Theorem 1 is proved as `Program.dominates_of_nestsEq`.

- Substitution is defined in [`Mean/Subst.lean`](Mean/Subst.lean).
  Here, `Expr.subst` is the recursive definition of substitution and `Computation.subst` is a version that substitutes a single variable with a value, used in the substitution lemma and the small-step semantics.
  The substitution lemma (Lemma 3) is proved by `Computation.subst_types_and_wf`.

- The small-step reduction is defined in [`Mean/Step.lean`](Mean/Step.lean).
  Progress (Theorem 2) is called `Computation.progress`, preservation (Theorem 3) is called `Computation.preservation`.
  A combined soundness theorem (`Computation.soundness`) is also included.

## Differences to the paper

There are some differences between the paper and the formalisation, some of which are explained here.
Also note the documentation comments on relevant definitions, which provide more explanations.

- The version of the language defined here does not include let-expressions.
  These are considered syntactic sugar and could be desugared into the formalised language either by
  - substituting their right-hand side for every use (this is how MimIR implements it and uses expression DAGs and hash-consing in order not to duplicate expressions), or
  - by defining a new function for each let-expression (just like in the $\lambda$-calculus):

    ```
    let x = e1; e2    =>    (λx.e2) e1
    ```

- Instead of the branch function `br`, we define conditional expressions.
- Some theorems have fewer assumptions than their statements in the original submission for the paper, as the stronger assumptions turned out to be unnecessary.
  These superfluous assumptions have also been dropped in later revisions of the paper.
  In particular:
  - The reachability assumption has been removed from Theorem 1.
  - The typing assumption for the program has been removed from Theorem 2.
    It is sufficient for the expression to be well-typed.
  - The well-formedness condition for expressions WF-E has been removed.
    Lemma 3 and Theorems 2 and 3 no longer make use of this construct.
