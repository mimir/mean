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

/--
A recursive call of a function with its own argument.

This is used during substitution as a temporary placeholder body.
-/
abbrev Expr.recurse (n : Nat) : Expr := (fn n).app (var n)

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

/-- A kind of reference, either a variable or a function. -/
inductive RefKind where
  | var
  | fn

/-- A reference (variable or function) occuring as a subexpression. -/
inductive Expr.Local (n : Nat) : RefKind → Expr → Prop where
  | var : (var n).Local n .var
  | fn : (fn n).Local n .fn
  | appL (r : RefKind) (f e : Expr) : f.Local n r → (f.app e).Local n r
  | appR (r : RefKind) (f e : Expr) : e.Local n r → (f.app e).Local n r
  | condC (r : RefKind) (c et ef : Expr) : c.Local n r → (c.cond et ef).Local n r
  | condT (r : RefKind) (c et ef : Expr) : et.Local n r → (c.cond et ef).Local n r
  | condF (r : RefKind) (c et ef : Expr) : ef.Local n r → (c.cond et ef).Local n r

/-- A local variable in an expression. -/
@[grind unfold]
def Expr.LocalVar (e : Expr) (n : Nat) : Prop := e.Local n .var

/-- A local function reference in an expression. -/
@[grind unfold]
def Expr.LocalFn (e : Expr) (n : Nat) : Prop := e.Local n .fn

/-- All references in an expression are in bounds of a given program. -/
def Expr.ValidRefs (e : Expr) (p : Program) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃r : RefKind⦄, e.Local n r → n < p.size

theorem Expr.Types.validRefs {p : Program} {e : Expr} {t : Ty} (ht : p ⊢ e : t)
    : e.ValidRefs p := by
  intro n r hl
  induction ht with cases hl <;> solve_by_elim

def Program.ValidRefs (p : Program) : Prop :=
  ∀ ⦃i⦄ (_ : i < p.size), p.fn[i].ValidRefs p

theorem Program.Types.validRefs {p : Program} (ht : ⊢ p) : p.ValidRefs :=
  fun _ hi => (ht hi).validRefs

@[grind →]
theorem Expr.lt_size_of_local {p : Program} {e : Expr} {n : Nat} {r : RefKind}
    (he : e.ValidRefs p) (h : e.Local n r) : n < p.size := he h

theorem Program.validRefs_fn {p : Program} {n : Nat} (hn : n < p.size)
    (hp : p.ValidRefs) : p.fn[n].ValidRefs p := hp hn

grind_pattern Program.validRefs_fn =>
  p.ValidRefs, n < p.size, p.fn[n]

@[simp, grind =]
theorem Expr.local_var_iff {m n : Nat} {r : RefKind} :
    (var m).Local n r ↔ r = .var ∧ m = n := by
  constructor
  · intro h
    have .var := h
    simp
  · intro ⟨hr, rfl⟩
    subst hr
    constructor

@[simp, grind =]
theorem Expr.local_fn_iff {m n : Nat} {r : RefKind} :
    (fn m).Local n r ↔ r = .fn ∧ m = n := by
  constructor
  · intro h
    have .fn := h
    simp
  · intro ⟨hr, rfl⟩
    subst hr
    constructor

@[simp, grind =]
theorem Expr.local_app_iff {f e : Expr} {n : Nat} {r : RefKind} :
    (f.app e).Local n r ↔ f.Local n r ∨ e.Local n r := by
  constructor
  · intro h
    cases h <;> solve_by_elim [Or.inl, Or.inr]
  · rintro (hf | he) <;> solve_by_elim [Local.appL, Local.appR]

@[simp, grind .]
theorem Expr.not_local_bool {b : Bool} {n : Nat} {r : RefKind} :
    ¬(bool b).Local n r := nofun

@[simp, grind =]
theorem Expr.local_cond_iff {c et ef : Expr} {n : Nat} {r : RefKind} :
    (c.cond et ef).Local n r ↔ c.Local n r ∨ et.Local n r ∨ ef.Local n r := by
  constructor
  · intro h
    cases h <;> solve_by_elim [Or.inl, Or.inr]
  · rintro (hc | het | hef) <;>
      solve_by_elim [Local.condC, Local.condT, Local.condF]

@[simp, grind =]
theorem Expr.validRefs_var_iff {p : Program} {n : Nat} :
    (var n).ValidRefs p ↔ n < p.size := by
  constructor <;> intro h
  · solve_by_elim
  · intro m r hl
    have .var := hl
    exact h

@[simp, grind =]
theorem Expr.validRefs_fn_iff {p : Program} {n : Nat} :
    (fn n).ValidRefs p ↔ n < p.size := by
  constructor <;> intro h
  · solve_by_elim
  · intro m r hl
    have .fn := hl
    exact h

@[simp, grind =]
theorem Expr.validRefs_app_iff {p : Program} {f e : Expr} :
    (f.app e).ValidRefs p ↔ f.ValidRefs p ∧ e.ValidRefs p := by
  constructor
  · intro h
    and_intros
    · intro m r hl
      apply_rules [Local.appL]
    · intro m r hl
      apply_rules [Local.appR]
  · intro ⟨hf, he⟩ m r hl
    cases hl <;> solve_by_elim

@[simp, grind .]
theorem Expr.validRefs_bool {p : Program} {b : Bool} :
    (bool b).ValidRefs p := by
  intro n r hl
  cases hl

@[simp, grind =]
theorem Expr.validRefs_cond_iff {p : Program} {c et ef : Expr} :
    (c.cond et ef).ValidRefs p ↔ c.ValidRefs p ∧ et.ValidRefs p ∧ ef.ValidRefs p := by
  constructor
  · intro h
    and_intros
    · intro m r hl
      apply_rules [Local.condC]
    · intro m r hl
      apply_rules [Local.condT]
    · intro m r hl
      apply_rules [Local.condF]
  · intro ⟨hc, het, hef⟩ m r hl
    cases hl <;> solve_by_elim

theorem Expr.validRefs_of_size_ge {p₁ p₂ : Program} {e : Expr}
    (heq : p₁.size ≤ p₂.size) (h : e.ValidRefs p₁) : e.ValidRefs p₂ :=
  fun _ _ hl => Nat.lt_of_lt_of_le (h hl) heq

theorem Expr.types_in_push_of_types {p : Program} {e b : Expr} {t t' : Ty}
    (h : p ⊢ e : t) : p.push b t' ⊢ e : t := by
  induction h with try solve_by_elim
  | var n hn =>
    have hn' : n < (p.push b t').size := by lia
    have : p.ty[n] = (p.push b t').ty[n] := by
      simp [Program.push, hn]
    rw [this]
    constructor
  | fn n hn =>
    have hn' : n < (p.push b t').size := by lia
    have : p.ty[n] = (p.push b t').ty[n] := by
      simp [Program.push, hn]
    rw [this]
    constructor

theorem Expr.types_in_setBody_of_types {p : Program} {e b : Expr} {t : Ty}
    {i : Nat} (hi : i < p.size) (h : p ⊢ e : t) : p.setBody i b ⊢ e : t := by
  induction h with constructor <;> assumption

theorem Program.types_push {p : Program} {b : Expr} {t' : Ty} (hp : ⊢ p)
    (hf : p.push b t' ⊢ b : .bot) : ⊢ p.push b t' := by
  intro i hi
  by_cases i = p.size
  · simp [*]
  · replace hi : i < p.size := by lia
    apply Expr.types_in_push_of_types
    simp [push, *]
    exact hp hi

theorem Expr.validRefs_in_push {p : Program} {e b : Expr} {t : Ty}
    (h : e.ValidRefs p) : e.ValidRefs (p.push b t) :=
  validRefs_of_size_ge (by simp) h

theorem Program.validRefs_push {p : Program} {b : Expr} {t : Ty}
    (h : p.ValidRefs) (hb : b.ValidRefs (p.push b t)) :
    (p.push b t).ValidRefs := by
  intro i hi n r hl
  by_cases i = p.size
  · simp only [Vector.getElem_push_eq, *] at hl
    simpa using Nat.lt_of_succ_le (hb hl)
  · replace hi : i < p.size := by lia
    simp only [Vector.getElem_push_lt, hi] at hl
    exact Nat.lt_add_right 1 (h hi hl)

theorem Program.validRefs_setBody {p : Program} {i : Nat} {b : Expr}
    (hi : i < p.size) (h : p.ValidRefs) (hb : b.ValidRefs p) :
    (p.setBody i b).ValidRefs := by
  intro j hj
  by_cases i = j
  · simp only [Vector.getElem_set_self, *]
    exact Expr.validRefs_of_size_ge (by simp) hb
  · simp only [ne_eq, not_false_eq_true, Vector.getElem_set_ne, *]
    apply Expr.validRefs_of_size_ge (by simp) (h hj)
