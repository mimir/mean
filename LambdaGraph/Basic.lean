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

An environment is represented as an array of function bodies and an array of the
types of their corresponding variables.
-/
structure Env where
  size : Nat
  /-- Maps each label to the corresponding function body. -/
  fn : Vector Expr size
  /-- Maps each label to the type of the corresponding function's argument. -/
  ty : Vector Ty size

/-- A program consists of an environment and an expression to be evaluated. -/
structure Program extends Env where
  /-- The expression to be evaluated. -/
  expr : Expr

/--
The free-variable relation.

A variable occurs free in an expression if the expression itself contains the
variable, or if it contains a reference to a function in which the variable
occurs free.
-/
inductive Free (p : Env) (n : Nat) : Expr → Prop where
  | var : Free p n (.var n)
  | fn (m : Nat) (_ : m < p.size) : n ≠ m → Free p n p.fn[m] → Free p n (.fn m)
  | appL (f e : Expr) : Free p n f → Free p n (.app f e)
  | appR (f e : Expr) : Free p n e → Free p n (.app f e)
  | condC (c et ef : Expr) : Free p n c → Free p n (.cond c et ef)
  | condT (c et ef : Expr) : Free p n et → Free p n (.cond c et ef)
  | condF (c et ef : Expr) : Free p n ef → Free p n (.cond c et ef)

/--
A dependency of a function on a variable.

During substitution, all functions that depend on the substitution variable must
be rewritten.
-/
inductive Depends (p : Env) : Nat → Nat → Prop where
  | free (m n : Nat) (_ : m < p.size) : n ≠ m → Free p n p.fn[m] → Depends p m n
  | step (m n k : Nat) (_ : m < p.size) :
    n ≠ m → Free p n p.fn[m] → Depends p n k → Depends p m k

/-- An expression is closed if it has no free variables. -/
def Expr.Closed (p : Env) (e : Expr) : Prop := ∀ n, ¬Free p n e

/-- A program is closed if its expression is closed in its environment. -/
def Program.Closed (p : Program) : Prop := p.expr.Closed p.toEnv

open Classical in -- TODO: Remove this by implementing Decidable.
/--
Assigns labels for new versions of the functions with free occurrences of `n`.

Returns an array mapping each function label to the label of the new version of
that function (or itself if there is none), as well as an array mapping each of
the added labels back to the label of its original function.
-/
noncomputable def Env.labelMap (p : Env) (n : Nat) :
    Vector Nat p.size × Array (Fin p.size) :=
  aux 0 p.size (Vector.ofFn Fin.val) #[]
where
  aux i k map inv :=
    if h : i < p.size then
      if Depends p i n then
        aux (i + 1) (k + 1) (map.set i k) (inv.push ⟨i, h⟩)
      else
        aux (i + 1) k map inv
    else
      (map, inv)

/--
Substitutes a value for a variable in an expression.

The expression may include references to functions that include the variable to
be substituted as a free variable. For these functions, new versions need to be
added to the environment, with their free occurrences substituted as well. This
function does not perform this change to the environment, but receives an array
mapping function labels to the labels of their substituted versions.
-/
noncomputable def Expr.subst (e : Expr) (map : Array Nat) (n : Fin map.size)
    (v : Expr) : Expr :=
  match e with
  | var m => if n = m then v else var (map.getD m m)
  | fn m => fn (map.getD m m)
  | app f e => (f.subst map n v).app (e.subst map n v)
  | bool b => bool b
  | cond c et ef => (c.subst map n v).cond (et.subst map n v) (ef.subst map n v)

/--
Substitutes a value for a variable in a program.

Creates a new version of each function with `n` as a free variable and performs
substitution of the program expression.
-/
noncomputable def Program.subst (p : Program) (n : Fin p.size) (v : Expr) :
    Program :=
  let lmap := p.labelMap n
  let map := lmap.1.toArray
  let inv := lmap.2
  have h : p.size = map.size := by simp [map]
  let fnExt : Vector Expr inv.size :=
    ⟨inv.map (p.fn[·].subst map (h ▸ n) v), by simp⟩
  let tyExt : Vector Ty inv.size :=
    ⟨inv.map (p.ty[·]), by simp⟩
  {
    size := _
    fn := p.fn ++ fnExt
    ty := p.ty ++ tyExt
    expr := p.expr.subst map (h ▸ n) v
  }

/-- A fully reduced expression. -/
inductive Expr.Value : Expr → Prop where
  | fn n : Value (.fn n)
  | bool b : Value (.bool b)

/-- The small-step reduction relation. -/
inductive Step : Program → Program → Prop where
  | app (p : Env) (n : Nat) (e : Expr) (h : n < p.size) :
    e.Value → Step ⟨p, .app (.fn n) e⟩ (Program.subst ⟨p, p.fn[n]⟩ ⟨n, h⟩ e)
  | appL (p p' : Env) (f f' e : Expr) :
    Step ⟨p, f⟩ ⟨p', f'⟩ → Step ⟨p, f.app e⟩ ⟨p', f'.app e⟩
  | appR (p p' : Env) (f e e' : Expr) :
    f.Value → Step ⟨p, e⟩ ⟨p', e'⟩ → Step ⟨p, f.app e⟩ ⟨p', f.app e'⟩
  | condT (p : Env) (et ef : Expr) :
    Step ⟨p, (.cond (.bool true) et ef)⟩ ⟨p, et⟩
  | condF (p : Env) (et ef : Expr) :
    Step ⟨p, (.cond (.bool false) et ef)⟩ ⟨p, ef⟩
  | condC (p p' : Env) (c c' et ef : Expr) :
    Step ⟨p, c⟩ ⟨p', c'⟩ → Step ⟨p, c.cond et ef⟩ ⟨p', c'.cond et ef⟩

notation:40 p:41 " ⇒ " p':41 => Step p p'

/-- The reflexive-transitive closure of the reduction relation. -/
inductive Steps : Program → Program → Prop where
  | refl (p : Program) : Steps p p
  | step (p p' p'' : Program) : Step p p' → Steps p' p'' → Steps p p''

notation:40 p:41 " ⇒* " p':41 => Steps p p'

/--
The typing relation on expressions.

The expression is parameterised by the environment, which contains the typing
information for all variables and functions. Variables and functions are only
well-typed if their labels are in bounds.
-/
inductive Expr.Types (p : Env) : Expr → Ty → Prop where
  | var (n : Nat) (_ : n < p.size) : Types p (var n) p.ty[n]
  | fn (n : Nat) (_ : n < p.size) : Types p (fn n) p.ty[n].cn
  | app (f e : Expr) (t : Ty) :
    Types p f t.cn → Types p e t → Types p (f.app e) .bot
  | bool (b : Bool) : Types p (bool b) .bool
  | cond (c et ef : Expr) (t : Ty) :
    Types p c .bool → Types p et t → Types p ef t → Types p (c.cond et ef) t

notation:60 p:61 " ⊢ " e:61 " : " t:61 => Expr.Types p e t

/--
The typing relation on programs.

A program is well-typed if the environment is well-typed and the expression is
well-typed in that context.
-/
structure Program.Types (p : Program) (t : Ty) : Prop where
  ctx_types : ∀ n (_ : n < p.size), p.toEnv ⊢ p.fn[n] : .bot
  expr_types : p.toEnv ⊢ p.expr : t

notation:60 "⊢ " p:61 " : " t:61 => Program.Types p t
