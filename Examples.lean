module

import LambdaGraph
meta import LambdaGraph

def factorial : Program := prog
  λ [int, int → ⊥] → ⊥. [1] (var[0].0, 1)
  λ [int, int] → ⊥. if var[1].0 ≤ 1 then [3] () else [2] ()
  λ [] → ⊥. [1] (var[1].0 - 1, var[1].1 * var[1].0)
  λ [] → ⊥. var[0].1 var[1].1
  λ int → ⊥. [4] var[4]

example : ⊢ factorial := by decide
example : factorial ⊢ expr([0] (5, [4])) : ty(⊥) := by decide

-- The following examples involving free variables need to use native_decide
-- instead of decide because we use Std.HashSet operations in the decision
-- procedure, which the kernel cannot reduce. This could be avoided by using a
-- different data structure.

example : expr([0] (5, [4])).Closed factorial := by native_decide
example : expr([1] (var[0].0, 1)).Free factorial 0 := by native_decide

def factorial' : Program := prog
  λ [int, int → ⊥] → ⊥. [1] (var[0].0, 1)
  λ [int, int] → ⊥. if var[1].0 ≤ 1 then [3] () else [2] ()
  λ [] → ⊥. [1] (var[1].0 - 1, var[1].1 * var[1].0)
  λ [] → ⊥. var[0].1 var[1].1
  λ int → ⊥. [4] var[4]
  λ [int, int] → ⊥. if var[5].0 ≤ 1 then [6] () else [7] ()
  λ [] → ⊥. (5, [4]).1 var[5].1
  λ [] → ⊥. [5] (var[5].0 - 1, var[5].1 * var[5].0)

def comp : Computation := ⟨factorial, expr([1] (var[0].0, 1))⟩
def comp' : Computation := ⟨factorial', expr([5] ((5, [4]).0, 1))⟩

-- This example requires native_decide, both because it uses the free variable
-- algorithm and because substitution is defined using well-founded recursion.
example : comp.subst 0 expr((5, [4])) = comp' := by native_decide
