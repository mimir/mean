# lambda-graph

This repository contains the Lean formalisation of $\lambda_G$, the graph-based
$\lambda$-calculus defined in the paper “SSA without Dominance for Higher-Order
Programs”. It contains proofs of the lemmas and theorems in the paper, in
particular the relationship between nesting and dominance and basic soundness
results. This formalisation was produced for Johannes Griebler's master's
thesis; the version submitted as part of that thesis is tagged `thesis`.

## Checking the proofs

The Lean version manager `elan` needs to be installed. The project can then be
built and checked with

```sh
lake build
```

## Project structure

This section describes where definitions and results from the paper can be found
in the repository.

- The basic language definition and type system is contained in
  [`LambdaGraph/Basic.lean`]. The types `Expr` and `Program` correspond to
  expressions and programs in the paper; a `Computation` is a pair consisting of
  a program and an expression and is used in the small-step reduction relation.
  Labels are simply natural numbers here. For both expressions and programs, a
  predicate `ValidRefs` is defined that states that all labels that appear in
  expressions actually exist in the program. These are implied by typing
  assumptions. Local variables and functions are also defined here under the
  name `Local`.

- Free variables (`Expr.Free`) and the nesting relation are defined in
  [`LambdaGraph/Nest.lean`]. The strict nesting relation ($\succ$) is called
  `Nests`, while the non-strict version ($\succeq$) is called `NestsEq`. This
  file also defines control-flow successors and dominance. The theorems
  `Expr.free_in_fn_of_succ` and `Expr.free_in_fn_of_pathWithout` correspond to
  Lemma 1 and Lemma 2 in the paper. Theorem 1 is proved as
  `Program.dominates_of_nestsEq`.

- Substitution is defined in [`LambdaGraph/Subst.lean`]. Here, `Expr.subst` is
  the recursive definition of substitution and `Computation.subst` is a
  version that substitutes a single variable with a value, used in the
  substitution lemma and the small-step semantics. The substitution lemma
  (Lemma 3) is proved by `Computation.subst_types_and_wf`.

- The small-step reduction is defined in [`LambdaGraph/Step.lean`]. Progress
  (Theorem 2) is called `Computation.progress`, preservation (Theorem 3) is
  called `Computation.preservation`. A combined soundness theorem
  (`Computation.soundness`) is also included.

- Verified algorithms and `Decidable` instances are contained in
  [`LambdaGraph/Algorithms.lean`]. This covers type checking, free variable
  computation, the nesting relation, and well-formedness checking.

- The file [`LambdaGraph/SubstMaps.lean`] contains definitions and theorems
  needed for substitution. This includes the definitions of variable and
  function maps (`VarMap` and `FunMap`) with some basic theorems, as well as the
  ingredients required for the termination proof of substitution.

- A simple implementation of finite sets is contained in
  [`LambdaGraph/Finset.lean`]. Finite sets are used in some proofs, primarily
  for the termination argument for substitution.

- The file [`LambdaGraph/Syntax.lean`] defines syntax extensions to conveniently
  represent $\lambda_G$ expressions, types, and programs in Lean.

- Finally, [`Examples.lean`] contains some simple examples showcasing the Lean
  syntax for $\lambda_G$ and the verified decision procedures.

[`LambdaGraph/Basic.lean`]: LambdaGraph/Basic.lean
[`LambdaGraph/Nest.lean`]: LambdaGraph/Nest.lean
[`LambdaGraph/Subst.lean`]: LambdaGraph/Subst.lean
[`LambdaGraph/Step.lean`]: LambdaGraph/Step.lean
[`LambdaGraph/Algorithms.lean`]: LambdaGraph/Algorithms.lean
[`LambdaGraph/SubstMaps.lean`]: LambdaGraph/SubstMaps.lean
[`LambdaGraph/Finset.lean`]: LambdaGraph/Finset.lean
[`LambdaGraph/Syntax.lean`]: LambdaGraph/Syntax.lean
[`Examples.lean`]: Examples.lean

## Differences to the paper

There are some differences between the paper and the formalisation, some of
which are explained here. Also note the documentation comments on relevant
definitions, which provide more explanations.

- The version of the language defined here does not include let-expressions.
  These are considered syntactic sugar and could be desugared into the
  formalised language either by
  - substituting their right-hand side for every use
    (this is how MimIR implements it and uses expression DAGs and
    hash-consing in order not to duplicate expressions), or
  - by defining a new function for each let-expression (just like in the
    $\lambda$-calculus):

    ```
    let x = e1; e2    =>    (λx.e2) e1
    ```

- Instead of the branch function `br`, we define conditional expressions.
