/--
An expression with labels of type `L`.

An expression is part of a program containing labelled lambda terms that may
refer to other lambdas and their variables by label. The expression language
does not contain a construct for unnamed lambdas. Closures are needed during
reduction to bind lambda references to the environment from which they came;
they are not considered part of the surface syntax.
-/
inductive Expr (L : Type) where
  | var (l : L)
  | fn (l : L)
  | app (f e : Expr L)
  | clos (l : L) (σ : L → Option (Expr L))
  | bool (b : Bool)
  | cond (c et ef : Expr L)

/-- The type of an `Expr`. -/
inductive Ty where
  | bot
  | bool
  | cn (t : Ty)

/--
A collection of labelled lambda terms.

A program is represented with functions mapping each label to the body of the
lambda associated with that label and to the type of its variable.
-/
structure Program (L : Type) : Type where
  /-- Maps each label to the corresponding function body. -/
  fn : L → Expr L
  /-- Maps each label to the type of the corresponding function's argument. -/
  ty : L → Ty

/-- A partial function from labels to expressions. -/
def Env (L : Type) : Type := L → Option (Expr L)

/-- Updates an environment with a new value for a given label. -/
def Env.update {L : Type} [DecidableEq L] (σ : Env L) (l : L) (v : Expr L) :=
  fun l' => if l = l' then some v else σ l'

notation "[" l " ↦ " e "]" σ:max => Env.update σ l e

/--
Applies substitutions from an environment to an expression.

Each labelled variable in the expression is replaced with its value in the
environment (if present) and each lambda reference is instantiated to a closure
with the environment.
-/
def Expr.subst {L : Type} [DecidableEq L] (e : Expr L) (σ : Env L) : Expr L :=
  match e with
  | var l => (σ l).getD (var l)
  | fn l => clos l σ
  | app f e => (f.subst σ).app (e.subst σ)
  | clos l σ' => clos l σ'
  | bool b => bool b
  | cond c et ef => (c.subst σ).cond (et.subst σ) (ef.subst σ)

/-- A fully reduced expression. -/
inductive Expr.Value {L : Type} : Expr L → Prop where
  | clos l σ : Value (.clos l σ)
  | bool b : Value (.bool b)

/--
The small-step reduction relation.

The relation is parameterised by the program. Beta reduction of closure
application applies substitutions to the lambda's body using the closure's
stored environment.
-/
inductive Step {L : Type} [DecidableEq L] (p : Program L) :
    Expr L → Expr L → Prop where
  | app (l : L) (σ : Env L) (e : Expr L) :
    Expr.Value e → Step p (.app (.clos l σ) e) ((p.fn l).subst ([l ↦ e] σ))
  | appL (f f' e : Expr L) : Step p f f' → Step p (f.app e) (f'.app e)
  | appR (f e e' : Expr L) : f.Value → Step p e e' → Step p (f.app e) (f.app e')
  | condT (et ef : Expr L) : Step p (.cond (.bool true) et ef) et
  | condF (et ef : Expr L) : Step p (.cond (.bool false) et ef) ef
  | condC (c c' et ef : Expr L) :
    Step p c c' → Step p (c.cond et ef) (c'.cond et ef)

/-- The reflexive-transitive closure of the reduction relation. -/
inductive Steps {L : Type} [DecidableEq L] (p : Program L) :
    Expr L → Expr L → Prop where
  | refl (e : Expr L) : Steps p e e
  | step (e e' e'' : Expr L) : Step p e e' → Steps p e' e'' → Steps p e e''

/--
The typing relation.

The relation is parameterised by the program and a context represented as a list
of the labels of all variables in scope (the corresponding types are already
contained in the program). A variable must be in the context to be well-typed. A
function reference is well-typed if its body is well-typed in the context
extended with its bound variable, or if its label is already in the context
(since this requires checking the body anyway). A closure is only well-typed if
its environment contains all the variables it depends on.
-/
inductive Types {L : Type} (p : Program L) : List L → Expr L → Ty → Prop where
  | var (Γ : List L) (l : L) : l ∈ Γ → Types p Γ (.var l) (p.ty l)
  | fnRec (Γ : List L) (l : L) : l ∈ Γ → Types p Γ (.fn l) (p.ty l).cn
  | fnNew (Γ : List L) (l : L) :
    l ∉ Γ → Types p (l :: Γ) (p.fn l) .bot → Types p Γ (.fn l) (p.ty l).cn
  | app (Γ : List L) (f e : Expr L) (t : Ty) :
    Types p Γ f t.cn → Types p Γ e t → Types p Γ (f.app e) .bot
  -- FIXME: A closure should only be well-typed if its environment contains all
  -- the variables it depends on.
  | clos (Γ : List L) (l : L) (σ : Env L) : Types p Γ (.clos l σ) (p.ty l).cn
  | bool (Γ : List L) (b : Bool) : Types p Γ (.bool b) .bool
  | cond (Γ : List L) (c et ef : Expr L) (t : Ty) :
    Types p Γ c .bool → Types p Γ et t → Types p Γ ef t
      → Types p Γ (c.cond et ef) t

notation:60 p:61 " / " Γ:61 " ⊢ " e:61 " : " t:61 => Types p Γ e t
