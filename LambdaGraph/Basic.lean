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

/-- A computation consists of a program and an expression to be evaluated. -/
@[pp_using_anonymous_constructor]
structure Computation extends Program where
  /-- The expression to be evaluated. -/
  expr : Expr

/--
The free-variable relation.

A variable occurs free in an expression if the expression itself contains the
variable, or if it contains a reference to a function in which the variable
occurs free.
-/
inductive Expr.Free (p : Program) (n : Nat) : Expr → Prop where
  | var : Free p n (.var n)
  | fn (m : Nat) (_ : m < p.size) : n ≠ m → Free p n p.fn[m] → Free p n (.fn m)
  | appL (f e : Expr) : Free p n f → Free p n (.app f e)
  | appR (f e : Expr) : Free p n e → Free p n (.app f e)
  | condC (c et ef : Expr) : Free p n c → Free p n (.cond c et ef)
  | condT (c et ef : Expr) : Free p n et → Free p n (.cond c et ef)
  | condF (c et ef : Expr) : Free p n ef → Free p n (.cond c et ef)

/--
The nesting relation between functions in a program.

During substitution, all functions nested in the function corresponding to the
substitution variable must be rewritten.
-/
inductive Nests (p : Program) (n : Nat) : Nat → Prop where
  | free (m : Nat) (_ : m < p.size) : n ≠ m → p.fn[m].Free p n → Nests p n m
  | step (m k : Nat) (_ : k < p.size) :
    m ≠ k → p.fn[k].Free p m → Nests p n m → Nests p n k

/-- An expression is closed if it has no free variables. -/
def Expr.Closed (p : Program) (e : Expr) : Prop := ∀ n, ¬e.Free p n

/--
Free variables of a computation.

A variable occurs free in a computation if it occurs free in the computation's
expression.
-/
def Computation.Free (p : Computation) (n : Nat) := p.expr.Free p.toProgram n

/-- A computation is closed if its expression is closed in its program. -/
def Computation.Closed (p : Computation) : Prop := ∀ n, ¬p.Free n

/--
A mapping from old labels to new labels assigned for substitution.

There is also a mapping that maps the newly assigned labels back to their
original labels.
-/
structure LabelMap (p : Program) where
  fwd : Vector Nat p.size
  inv : Array (Fin p.size)

open Classical in -- TODO: Remove this by implementing Decidable.
/-- Returns a label map to use for substitution of the variable `n`. -/
noncomputable def Program.labelMap (p : Program) (n : Nat) :
    LabelMap p :=
  let (fwd, inv) := aux 0 (Vector.ofFn Fin.val) #[]
  ⟨fwd, inv⟩
where
  aux i map inv :=
    if h : i < p.size then
      if Nests p n i then
        aux (i + 1) (map.set i (p.size + inv.size)) (inv.push ⟨i, h⟩)
      else
        aux (i + 1) map inv
    else
      (map, inv)

/--
Substitutes a value for a variable in an expression.

The expression may include references to functions nested inside the function
corresponding to the substitution variable. For these functions, new versions
need to be added to the program, with their bodies substituted in the same way.
This function does not perform this change to the program, but takes a label map
mapping function labels to the labels assigned to their substituted versions.
-/
noncomputable def Expr.subst {p : Program} (e : Expr) (map : LabelMap p)
    (n : Nat) (v : Expr) : Expr :=
  match e with
  | var m => if n = m then v else var (map.fwd[m]?.getD m)
  | fn m => fn (map.fwd[m]?.getD m)
  | app f e => (f.subst map n v).app (e.subst map n v)
  | bool b => bool b
  | cond c et ef => (c.subst map n v).cond (et.subst map n v) (ef.subst map n v)

/--
Substitutes a value for a variable in a program.

This creates a new version of each function that depends on `n`, as specified by
the passed label map.
-/
noncomputable def Program.subst (p : Program) (map : LabelMap p) (n : Nat) (v : Expr) :
    Program :=
  let fnExt : Vector Expr map.inv.size :=
    ⟨map.inv.map (p.fn[·].subst map n v), by simp⟩
  let tyExt : Vector Ty map.inv.size :=
    ⟨map.inv.map (p.ty[·]), by simp⟩
  { size := _, fn := p.fn ++ fnExt, ty := p.ty ++ tyExt }

/--
Substitutes a value for a variable in a computation.

This computes the map for translating old labels into new ones and applies the
substitution to the program and the expression.
-/
noncomputable def Computation.subst (p : Computation) (n : Nat) (v : Expr) : Computation :=
  let map := p.labelMap n
  ⟨p.toProgram.subst map n v, p.expr.subst map n v⟩

/-- A fully reduced expression. -/
inductive Expr.Value : Expr → Prop where
  | fn n : Value (.fn n)
  | bool b : Value (.bool b)

/-- The small-step reduction relation. -/
inductive Step : Computation → Computation → Prop where
  | app (p : Program) (n : Nat) (e : Expr) (_ : n < p.size) :
    e.Value → Step ⟨p, .app (.fn n) e⟩ (Computation.subst ⟨p, p.fn[n]⟩ n e)
  | appL (p p' : Program) (f f' e : Expr) :
    Step ⟨p, f⟩ ⟨p', f'⟩ → Step ⟨p, f.app e⟩ ⟨p', f'.app e⟩
  | appR (p p' : Program) (f e e' : Expr) :
    f.Value → Step ⟨p, e⟩ ⟨p', e'⟩ → Step ⟨p, f.app e⟩ ⟨p', f.app e'⟩
  | condT (p : Program) (et ef : Expr) :
    Step ⟨p, (.cond (.bool true) et ef)⟩ ⟨p, et⟩
  | condF (p : Program) (et ef : Expr) :
    Step ⟨p, (.cond (.bool false) et ef)⟩ ⟨p, ef⟩
  | condC (p p' : Program) (c c' et ef : Expr) :
    Step ⟨p, c⟩ ⟨p', c'⟩ → Step ⟨p, c.cond et ef⟩ ⟨p', c'.cond et ef⟩

notation:40 p:41 " ⇒ " p':41 => Step p p'

/-- The reflexive-transitive closure of the reduction relation. -/
inductive Steps : Computation → Computation → Prop where
  | refl (p : Computation) : Steps p p
  | step (p p' p'' : Computation) : Step p p' → Steps p' p'' → Steps p p''

notation:40 p:41 " ⇒* " p':41 => Steps p p'

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
