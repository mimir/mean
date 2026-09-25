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

example : 0 ≻[factorial] 1 := by native_decide
example : factorial.WF := by native_decide

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

-- The following example is from Section 3.1.3 of the thesis.

def illformed : Program := prog
  λ int → int. [1] var[0] + [2] ()
  λ int → int. var[0] + [2] ()
  λ [] → int. var[0] + var[1]

def ex : Expr := expr([1] var[0] + [2] ())

def vm : VarMap 3 := .mk _ 0 expr(0)

def fm : FunMap 3 := .mk _

example : ⊢ illformed := by decide

example : illformed ⊢ ex : ty(int) := by decide

example : ¬illformed.WF := by native_decide

def wellformed : Program := illformed.setBody 0 expr(42)

example : wellformed.WF := by native_decide

def illformed' : Program := prog
  λ int → int. [1] var[0] + [2] ()
  λ int → int. var[0] + [2] ()
  λ [] → int. var[0] + var[1]
  λ int → int. 0 + [4] ()
  λ [] → int. 0 + var[3]

def wellformed' : Program := illformed'.setBody 0 expr(42)

def illformedResult : SubstResult illformed ex vm fm := ex.subst illformed vm fm

def wellformedResult : SubstResult wellformed ex vm fm := ex.subst wellformed vm fm

example : illformedResult.expr = expr([3] 0 + [4] ()) := by native_decide

example : illformedResult.program = illformed' := by native_decide

example : illformedResult.expr.Free illformed' 3 := by native_decide

example : wellformedResult.expr = expr([3] 0 + [4] ()) := by native_decide

example : wellformedResult.program = wellformed' := by native_decide

example : wellformedResult.expr.Free wellformed' 3 := by native_decide
