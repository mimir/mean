/--
An expression.

An expression is part of a program containing labelled lambda terms that may
refer to other lambdas and their variables by label. The expression language
does not contain a construct for unnamed lambdas.
-/
inductive Expr where
  | var (n : Nat)
  | fn (n : Nat)
  | app (f e : Expr)
  | bool (b : Bool)
  | cond (c et ef : Expr)

/-- The type of an `Expr`. -/
inductive Ty where
  | bot
  | bool
  | cn (t : Ty)

/--
A collection of labelled lambda terms.

A program is represented as an array of function bodies and an array of the
types of their corresponding variables.
-/
structure Program where
  size : Nat
  /-- Maps each label to the corresponding function body. -/
  fn : Vector Expr size
  /-- Maps each label to the type of the corresponding function's argument. -/
  ty : Vector Ty size

/-- Extends a program by a new function with a given body and argument type. -/
abbrev Program.push (p : Program) (b : Expr) (t : Ty) : Program :=
  ⟨_, p.fn.push b, p.ty.push t⟩

/-- Sets a function body in a program to a new expression. -/
abbrev Program.setBody (p : Program) (i : Nat) (b : Expr)
    (hi : i < p.size := by get_elem_tactic) : Program :=
  { p with fn := p.fn.set i b }

/-- A computation consists of a program and an expression to be evaluated. -/
@[pp_using_anonymous_constructor]
structure Computation extends Program where
  /-- The expression to be evaluated. -/
  expr : Expr

/-- A fully reduced expression. -/
inductive Expr.Value : Expr → Prop where
  | fn n : Value (.fn n)
  | bool b : Value (.bool b)

/--
The typing relation on expressions.

The relation is parameterised by the program, which contains the typing
information for all variables and functions. Variables and functions are only
well-typed if their labels are in bounds.
-/
inductive Expr.Types (p : Program) : Expr → Ty → Prop where
  | var (n : Nat) (_ : n < p.size) : Types p (var n) p.ty[n]
  | fn (n : Nat) (_ : n < p.size) : Types p (fn n) p.ty[n].cn
  | app (f e : Expr) (t : Ty) :
    Types p f t.cn → Types p e t → Types p (f.app e) .bot
  | bool (b : Bool) : Types p (bool b) .bool
  | cond (c et ef : Expr) (t : Ty) :
    Types p c .bool → Types p et t → Types p ef t → Types p (c.cond et ef) t

notation:60 p:61 " ⊢ " e:61 " : " t:61 => Expr.Types p e t

/--
The typing predicate for programs.

A program is well-typed if all function bodies are well-typed.
-/
def Program.Types (p : Program) : Prop := ∀ {n}, (_ : n < p.size) → p ⊢ p.fn[n] : .bot

notation:60 "⊢ " p:61 => Program.Types p

/--
The typing relation on computations.

A computation is well-typed if the program is well-typed and the expression is
well-typed in that program.
-/
structure Computation.Types (p : Computation) (t : Ty) : Prop where
  program_types : ⊢ p.toProgram
  expr_types : p.toProgram ⊢ p.expr : t

notation:60 "⊢ " p:61 " : " t:61 => Computation.Types p t

theorem value_types_cn {p : Program} {v : Expr} {t : Ty} (h : p ⊢ v : t.cn) :
    v.Value → ∃ n, v = .fn n
  | .fn n => by simp
  | .bool b => nomatch h

theorem value_types_bool {p : Program} {v : Expr} (h : p ⊢ v : .bool) :
    v.Value → ∃ b, v = .bool b
  | .fn n => nomatch h
  | .bool b => by simp

inductive Expr.ValidRefs (p : Program) : Expr → Prop where
  | var (n : Nat) : n < p.size → (Expr.var n).ValidRefs p
  | fn (n : Nat) : n < p.size → (Expr.fn n).ValidRefs p
  | app (f e : Expr) : f.ValidRefs p → e.ValidRefs p → (f.app e).ValidRefs p
  | bool (b : Bool) : (Expr.bool b).ValidRefs p
  | cond (c et ef : Expr) : c.ValidRefs p → et.ValidRefs p → ef.ValidRefs p →
    (c.cond et ef).ValidRefs p

theorem Expr.Types.validRefs {p : Program} {e : Expr} {t : Ty} (ht : p ⊢ e : t)
    : e.ValidRefs p := by
  induction ht with constructor <;> assumption

def Program.ValidRefs (p : Program) : Prop :=
  ∀ {i} (_ : i < p.size), p.fn[i].ValidRefs p

theorem Program.Types.validRefs {p : Program} (ht : ⊢ p) : p.ValidRefs :=
  fun hi => (ht hi).validRefs
