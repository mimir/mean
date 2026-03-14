# lambda-graph

This repository contains the Lean formalisation of $\lambda_G$, the graph-based
$\lambda$-calculus defined in the paper “SSA without Dominance for Higher-Order
Programs”. It contains proofs of the lemmas and theorems in the paper, in
particular the relationship between nesting and dominance and basic soundness
results.

## Checking the proofs

The Lean version manager `elan` needs to be installed. The project can then be
built and checked with

```sh
lake build
```

## Project structure

This section describes where definitions and results from the paper can be found
in the repository.

-   The basic language definition and type system is contained in
    [`LambdaGraph/Basic.lean`]. The types `Expr` and `Program` correspond to
    expressions and programs in the paper; a `Computation` is a pair of a
    program and an expression and is used in the small-step reduction relation.
    Labels are simply natural numbers here. For both expressions and programs, a
    predicate `ValidRefs` is defined which states that all labels that appear in
    expressions actually exist in the program. These assumptions are generally
    left implicit in the paper, but are needed for a number of theorems. They
    are implied by typing assumptions. Local variables and functions are also
    defined here under the name `Local`.

-   Free variables and the nesting relation are defined in
    [`LambdaGraph/Nest.lean`]. The strict nesting relation ($\succ$) is called
    `Nests`, while the non-strict version ($\succeq$) is called `NestsEq`. This
    file also defines control-flow successors and dominance. The theorems
    `Program.free_in_fn_of_succ` and `Program.free_in_fn_of_pathWithout`
    correspond closely to Lemma 1 and Lemma 2 in the paper. Theorem 1 is proved
    as `Program.dominates_of_nestsEq`.

-   Substitution is defined in [`LambdaGraph/Subst.lean`]. Here, `Expr.subst` is
    the recursive definition of substitution and `Computation.subst` is a
    version that substitutes a single variable for a value, used in the
    substitution lemma and the small-step semantics. The substitution lemma
    (Lemma 3) is proved in two parts, `Computation.subst_types` and
    `Computation.subst_wf`.

-   The small-step reduction is defined in [`LambdaGraph/Step.lean`]. Progress
    (Theorem 2) is called `progress`, preservation (Theorem 3) is proved in two
    parts (`Computation.preservation_types` and `Computation.preservation_wf`).

[`LambdaGraph/Basic.lean`]: LambdaGraph/Basic.lean
[`LambdaGraph/Nest.lean`]: LambdaGraph/Nest.lean
[`LambdaGraph/Subst.lean`]: LambdaGraph/Subst.lean
[`LambdaGraph/Step.lean`]: LambdaGraph/Step.lean

## Differences to the paper

There are some differences between the paper and the formalisation, some of
which are explained here. Also note the documentation comments on relevant
definitions, which provide more explanations.

-   The version of the language defined here does not include let-expressions.
    These are considered syntactic sugar and could be desugared into the
    formalised language either by substituting their right-hand side for every
    use, or by defining a new function for each let-expression (just like in the
    $\lambda$-calculus).

-   Some theorems have weaker assumptions than their statements in the original
    submission for the paper, as the stronger assumptions turned out to be
    unnecessary. In particular, there is no well-formedness condition for
    expressions corresponding to WF-E. These superfluous assumptions have also
    been dropped in later revisions of the paper.
