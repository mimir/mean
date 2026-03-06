/-- The type of an expression. -/
inductive Ty where
  | bot
  | unit
  | bool
  | int
  | fn (t₁ t₂ : Ty)
  | prod (t₁ t₂ : Ty)

class Denote (α : Type) (β : outParam Type) where
  denote : α → β

notation "⟦" x "⟧" => Denote.denote x

inductive Op where
  | add
  | sub
  | mul

instance : Denote Op (Int → Int → Int) where
  denote
    | .add => (· + ·)
    | .sub => (· - ·)
    | .mul => (· * ·)

inductive Cmp where
  | eq
  | ne
  | le
  | lt

instance : Denote Cmp (Int → Int → Bool) where
  denote
    | .eq => (· = ·)
    | .ne => (· ≠ ·)
    | .le => (· ≤ ·)
    | .lt => (· < ·)

inductive Logic where
  | and
  | or
  | xor

instance : Denote Logic (Bool → Bool → Bool) where
  denote
    | .and => (· && ·)
    | .or => (· || ·)
    | .xor => (· ^^ ·)

inductive Const where
  | unit
  | bool (b : Bool)
  | int (x : Int)
  | op (f : Op)
  | cmp (f : Cmp)
  | logic (f : Logic)

def Const.ty : Const → Ty
  | unit => .unit
  | bool _ => .bool
  | int _ => .int
  | op _ => .fn (.prod .int .int) .int
  | cmp _ => .fn (.prod .int .int) .bool
  | logic _ => .fn (.prod .bool .bool) .bool

inductive BinKind where
  | app
  | pair

/--
An expression.

An expression is part of a program containing labelled lambda terms that may
refer to other lambdas and their variables by label. The expression language
does not contain a construct for unnamed lambdas.
-/
inductive Expr where
  | var (n : Nat)
  | fn (n : Nat)
  | const (c : Const)
  | bin (k : BinKind) (e₁ e₂ : Expr)
  | cond (c et ef : Expr)
  | proj (e : Expr) (i : Fin 2)

abbrev Expr.unit : Expr := .const .unit

abbrev Expr.app (f e : Expr) : Expr := f.bin .app e

abbrev Expr.pair (e₁ e₂ : Expr) : Expr := e₁.bin .pair e₂

@[coe]
def Expr.ofBool (b : Bool) : Expr := .const (.bool b)

@[coe]
def Expr.ofInt (x : Int) : Expr := .const (.int x)

@[coe]
def Expr.ofOp (f : Op) : Expr := .const (.op f)

@[coe]
def Expr.ofCmp (f : Cmp) : Expr := .const (.cmp f)

@[coe]
def Expr.ofLogic (f : Logic) : Expr := .const (.logic f)

instance : Coe Bool Expr := ⟨Expr.ofBool⟩

instance : Coe Int Expr := ⟨Expr.ofInt⟩

instance : Coe Op Expr := ⟨Expr.ofOp⟩

instance : Coe Cmp Expr := ⟨Expr.ofCmp⟩

instance : Coe Logic Expr := ⟨Expr.ofLogic⟩

/--
A recursive call of a function with its own argument.

This is used during substitution as a temporary placeholder body.
-/
abbrev Expr.recurse (n : Nat) : Expr := (fn n).app (var n)

/--
A collection of labelled lambda terms.

A program is represented as an array of function bodies and arrays of their
corresponding argument and return types.
-/
structure Program where
  size : Nat
  /-- Maps each label to the corresponding function body. -/
  fn : Vector Expr size
  /-- Maps each label to the corresponding function's argument type. -/
  ty : Vector Ty size
  /-- Maps each label to the corresponding function's return type. -/
  ret : Vector Ty size

/-- Extends a program by a new function with a given body and argument type. -/
abbrev Program.push (p : Program) (b : Expr) (t₁ t₂ : Ty) : Program :=
  ⟨_, p.fn.push b, p.ty.push t₁, p.ret.push t₂⟩

/-- Sets a function body in a program to a new expression. -/
abbrev Program.setBody (p : Program) (i : Nat) (b : Expr)
    (hi : i < p.size := by get_elem_tactic) : Program :=
  { p with fn := p.fn.set i b }

/-- Extending a program at the end keeps the old program as a prefix. -/
structure Program.Prefix (p p' : Program) where
  size_le : p.size ≤ p'.size
  fn_eq : ∀ {m} (_ : m < p.size), p'.fn[m] = p.fn[m]
  ty_eq : ∀ {m} (_ : m < p.size), p'.ty[m] = p.ty[m]
  ret_eq : ∀ {m} (_ : m < p.size), p'.ret[m] = p.ret[m]

attribute [grind →] Program.Prefix.size_le

grind_pattern Program.Prefix.fn_eq => p.Prefix p', m < p.size, p.fn[m]
grind_pattern Program.Prefix.fn_eq => p.Prefix p', m < p.size, p'.fn[m]

grind_pattern Program.Prefix.ty_eq => p.Prefix p', m < p.size, p.ty[m]
grind_pattern Program.Prefix.ty_eq => p.Prefix p', m < p.size, p'.ty[m]

grind_pattern Program.Prefix.ret_eq => p.Prefix p', m < p.size, p.ret[m]
grind_pattern Program.Prefix.ret_eq => p.Prefix p', m < p.size, p'.ret[m]

/-- A computation consists of a program and an expression to be evaluated. -/
@[pp_using_anonymous_constructor]
structure Computation extends Program where
  /-- The expression to be evaluated. -/
  expr : Expr

/-- A fully reduced expression. -/
inductive Expr.Value : Expr → Prop where
  | fn n : Value (.fn n)
  | const c : Value (.const c)
  | pair v₁ v₂ : Value v₁ → Value v₂ → Value (v₁.pair v₂)

/--
The typing relation on expressions.

The relation is parameterised by the program, which contains the typing
information for all variables and functions. Variables and functions are only
well-typed if their labels are in bounds.
-/
inductive Expr.Types (p : Program) : Expr → Ty → Prop where
  | var (n : Nat) (_ : n < p.size) : Types p (var n) p.ty[n]
  | fn (n : Nat) (_ : n < p.size) : Types p (fn n) (p.ty[n].fn p.ret[n])
  | const (c : Const) : Types p (.const c) c.ty
  | app (f e : Expr) (t₁ t₂ : Ty) :
    Types p f (t₁.fn t₂) → Types p e t₁ → Types p (f.app e) t₂
  | pair (e₁ e₂ : Expr) (t₁ t₂ : Ty) :
    Types p e₁ t₁ → Types p e₂ t₂ → Types p (e₁.pair e₂) (.prod t₁ t₂)
  | cond (c et ef : Expr) (t : Ty) :
    Types p c .bool → Types p et t → Types p ef t → Types p (c.cond et ef) t
  | proj0 (e : Expr) (t₁ t₂ : Ty) :
    Types p e (.prod t₁ t₂) → Types p (e.proj 0) t₁
  | proj1 (e : Expr) (t₁ t₂ : Ty) :
    Types p e (.prod t₁ t₂) → Types p (e.proj 1) t₂

notation:60 p:61 " ⊢ " e:61 " : " t:61 => Expr.Types p e t

/--
The typing predicate for programs.

A program is well-typed if all function bodies are well-typed.
-/
def Program.Types (p : Program) : Prop :=
  ∀ ⦃n⦄ (_ : n < p.size), p ⊢ p.fn[n] : p.ret[n]

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

/-- A kind of reference, either a variable or a function. -/
inductive RefKind where
  | var
  | fn

/-- A reference (variable or function) occuring as a subexpression. -/
inductive Expr.Local (n : Nat) : RefKind → Expr → Prop where
  | var : (var n).Local n .var
  | fn : (fn n).Local n .fn
  | binL (r : RefKind) (k : BinKind) (e₁ e₂ : Expr) :
    e₁.Local n r → (e₁.bin k e₂).Local n r
  | binR (r : RefKind) (k : BinKind) (e₁ e₂ : Expr) :
    e₂.Local n r → (e₁.bin k e₂).Local n r
  | condC (r : RefKind) (c et ef : Expr) :
    c.Local n r → (c.cond et ef).Local n r
  | condT (r : RefKind) (c et ef : Expr) :
    et.Local n r → (c.cond et ef).Local n r
  | condF (r : RefKind) (c et ef : Expr) :
    ef.Local n r → (c.cond et ef).Local n r
  | proj (r : RefKind) (e : Expr) (i : Fin 2) :
    e.Local n r → (e.proj i).Local n r

/-- A local variable in an expression. -/
abbrev Expr.LocalVar (e : Expr) (n : Nat) : Prop := e.Local n .var

/-- A local function reference in an expression. -/
abbrev Expr.LocalFn (e : Expr) (n : Nat) : Prop := e.Local n .fn

/-- All references in an expression are less than `n`. -/
def Expr.Bounded (e : Expr) (n : Nat) : Prop :=
  ∀ ⦃m : Nat⦄ ⦃r : RefKind⦄, e.Local m r → m < n

/-- All references in an expression are in bounds of a given program. -/
abbrev Expr.ValidRefs (e : Expr) (p : Program) : Prop := e.Bounded p.size

@[grind →]
theorem Expr.Types.validRefs {p : Program} {e : Expr} {t : Ty} (ht : p ⊢ e : t)
    : e.ValidRefs p := by
  intro n r hl
  induction ht with cases hl <;> solve_by_elim

def Program.ValidRefs (p : Program) : Prop :=
  ∀ ⦃i⦄ (_ : i < p.size), p.fn[i].ValidRefs p

@[grind →]
theorem Program.Types.validRefs {p : Program} (ht : ⊢ p) : p.ValidRefs :=
  fun _ hi => (ht hi).validRefs

theorem Expr.value_types_fn {p : Program} {v : Expr} {t₁ t₂ : Ty}
    (h : p ⊢ v : t₁.fn t₂) : v.Value → (∃ n, v = .fn n) ∨
      (∃ f : Op, v = f) ∨ (∃ f : Cmp, v = f) ∨ (∃ f : Logic, v = f)
  | .fn n => Or.inl ⟨n, rfl⟩
  | .const (.op f) => Or.inr (Or.inl ⟨f, rfl⟩)
  | .const (.cmp f) => Or.inr (Or.inr (Or.inl ⟨f, rfl⟩))
  | .const (.logic f) => Or.inr (Or.inr (Or.inr ⟨f, rfl⟩))

theorem Expr.value_types_bool {p : Program} {v : Expr} (h : p ⊢ v : .bool) :
    v.Value → ∃ b : Bool, v = b
  | .const (.bool b) => ⟨b, rfl⟩

theorem Expr.value_types_int {p : Program} {v : Expr} (h : p ⊢ v : .int) :
    v.Value → ∃ x : Int, v = x
  | .const (.int x) => ⟨x, rfl⟩

theorem Expr.value_types_prod {p : Program} {v : Expr} {t₁ t₂ : Ty}
    (h : p ⊢ v : t₁.prod t₂) : v.Value →
      ∃ v₁ v₂, v = .pair v₁ v₂ ∧ v₁.Value ∧ v₂.Value
  | .pair v₁ v₂ hv₁ hv₂ => ⟨v₁, v₂, rfl, hv₁, hv₂⟩

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

@[simp, grind .]
theorem Expr.not_local_const {c : Const} {n : Nat} {r : RefKind} :
    ¬(const c).Local n r := nofun

@[simp, grind =]
theorem Expr.local_bin_iff {k : BinKind} {e₁ e₂ : Expr} {n : Nat} {r : RefKind} :
    (e₁.bin k e₂).Local n r ↔ e₁.Local n r ∨ e₂.Local n r := by
  constructor
  · intro h
    cases h <;> solve_by_elim [Or.inl, Or.inr]
  · rintro (h₁ | h₂) <;> solve_by_elim [Local.binL, Local.binR]

@[simp, grind =]
theorem Expr.local_cond_iff {c et ef : Expr} {n : Nat} {r : RefKind} :
    (c.cond et ef).Local n r ↔ c.Local n r ∨ et.Local n r ∨ ef.Local n r := by
  constructor
  · intro h
    cases h <;> solve_by_elim [Or.inl, Or.inr]
  · rintro (hc | het | hef) <;>
      solve_by_elim [Local.condC, Local.condT, Local.condF]

@[simp, grind =]
theorem Expr.local_proj_iff {e : Expr} {i : Fin 2} {n : Nat} {r : RefKind} :
    (e.proj i).Local n r ↔ e.Local n r := by
  constructor
  · intro h
    let .proj _ _ _ h := h
    exact h
  · exact .proj _ _ _

@[simp, grind =]
theorem Expr.bounded_var_iff {n m : Nat} :
    (var m).Bounded n ↔ m < n := by
  constructor <;> intro h
  · solve_by_elim
  · intro m r hl
    have .var := hl
    exact h

@[simp, grind =]
theorem Expr.bounded_fn_iff {n m : Nat} :
    (fn m).Bounded n ↔ m < n := by
  constructor <;> intro h
  · solve_by_elim
  · intro m r hl
    have .fn := hl
    exact h

@[simp, grind .]
theorem Expr.bounded_const {n : Nat} {c : Const} :
    (const c).Bounded n := by
  intro n r hl
  cases hl

@[simp, grind =]
theorem Expr.bounded_bin_iff {n : Nat} {k : BinKind} {e₁ e₂ : Expr} :
    (e₁.bin k e₂).Bounded n ↔ e₁.Bounded n ∧ e₂.Bounded n := by
  constructor
  · intro h
    and_intros
    · intro m r hl
      apply_rules [Local.binL]
    · intro m r hl
      apply_rules [Local.binR]
  · intro ⟨h₁, h₂⟩ m r hl
    cases hl <;> solve_by_elim

@[simp, grind =]
theorem Expr.bounded_cond_iff {n : Nat} {c et ef : Expr} :
    (c.cond et ef).Bounded n ↔ c.Bounded n ∧ et.Bounded n ∧ ef.Bounded n := by
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

@[simp, grind =]
theorem Expr.bounded_proj_iff {n : Nat} {e : Expr} {i : Fin 2} :
    (e.proj i).Bounded n ↔ e.Bounded n := by
  constructor
  · intro h m r hl
    exact h (.proj _ _ _ hl)
  · intro h m r hl
    have .proj _ _ _ hl := hl
    exact h hl

@[grind .]
theorem Expr.bounded_of_ge {n₁ n₂ : Nat} {e : Expr}
    (hle : n₁ ≤ n₂) (h : e.Bounded n₁) : e.Bounded n₂ :=
  fun _ _ hl => Nat.lt_of_lt_of_le (h hl) hle

@[grind →]
theorem Program.prefix_trans {p p' p'' : Program} (h : p.Prefix p')
    (h' : p'.Prefix p'') : p.Prefix p'' := by
  constructor <;> grind

theorem Program.prefix_push {p : Program} {b : Expr} {t₁ t₂ : Ty} :
    p.Prefix (p.push b t₁ t₂) := by
  constructor <;> simp_all

grind_pattern Program.prefix_push => p.push b t₁ t₂

theorem Expr.types_in_prefix_iff {p p' : Program} {e : Expr} {t : Ty}
    (he : e.ValidRefs p) (h : p.Prefix p') : p' ⊢ e : t ↔ p ⊢ e : t := by
  constructor <;> intro ht <;> induction ht with grind [intro Types]

grind_pattern Expr.types_in_prefix_iff => p.Prefix p', p ⊢ e : t
grind_pattern Expr.types_in_prefix_iff => p.Prefix p', p' ⊢ e : t

theorem Expr.types_in_push_of_types {p : Program} {e b : Expr} {t t₁ t₂ : Ty}
    (h : p ⊢ e : t) : p.push b t₁ t₂ ⊢ e : t :=
  (types_in_prefix_iff h.validRefs Program.prefix_push).mpr h

theorem Expr.types_in_setBody_of_types {p : Program} {e b : Expr} {t : Ty}
    {i : Nat} (hi : i < p.size) (h : p ⊢ e : t) : p.setBody i b ⊢ e : t := by
  induction h with constructor <;> assumption

theorem Program.types_push {p : Program} {b : Expr} {t₁ t₂ : Ty} (hp : ⊢ p)
    (hf : p.push b t₁ t₂ ⊢ b : t₂) : ⊢ p.push b t₁ t₂ := by
  intro i hi
  by_cases i = p.size
  · simp [*]
  · replace hi : i < p.size := by lia
    apply Expr.types_in_push_of_types
    simp [push, *]
    exact hp hi

theorem Expr.validRefs_in_push {p : Program} {e b : Expr} {t₁ t₂ : Ty}
    (h : e.ValidRefs p) : e.ValidRefs (p.push b t₁ t₂) :=
  bounded_of_ge (by simp) h

theorem Program.validRefs_push {p : Program} {b : Expr} {t₁ t₂ : Ty}
    (h : p.ValidRefs) (hb : b.ValidRefs (p.push b t₁ t₂)) :
    (p.push b t₁ t₂).ValidRefs := by
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
  · simp [*]
  · simp only [ne_eq, not_false_eq_true, Vector.getElem_set_ne, *]
    apply Expr.bounded_of_ge (by simp) (h hj)
