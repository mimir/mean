import LambdaGraph.Basic

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

notation:40 n:41 " ≻[" p:min "] " m:41 => Nests p n m
notation:40 n:41 " ⊁[" p:min "] " m:41 => ¬n ≻[p] m

/-- The reflexive closure of the nesting relation. -/
inductive NestsEq (p : Program) (n : Nat) : Nat → Prop where
  | refl (_ : n < p.size) : NestsEq p n n
  | nests (m : Nat) : Nests p n m → NestsEq p n m

notation:40 n:41 " ≽[" p:min "] " m:41 => NestsEq p n m
notation:40 n:41 " ⋡[" p:min "] " m:41 => ¬n ≽[p] m

/-- An expression is closed if it has no free variables. -/
def Expr.Closed (p : Program) (e : Expr) : Prop := ∀ n, ¬e.Free p n

/-- A program is well-formed if no function nests itself. -/
def Program.WF (p : Program) : Prop := ∀ n, n ⊁[p] n

/--
Free variables of a computation.

A variable occurs free in a computation if it occurs free in the computation's
expression.
-/
def Computation.Free (p : Computation) (n : Nat) := p.expr.Free p.toProgram n

/-- A computation is closed if its expression is closed in its program. -/
def Computation.Closed (p : Computation) : Prop := ∀ n, ¬p.Free n

@[simp]
theorem not_closed_var {p : Program} {n : Nat} : ¬(Expr.var n).Closed p :=
  fun h => h n .var

theorem fn_closed_iff {p : Program} {m : Nat} :
    (Expr.fn m).Closed p ↔ ∀ n ≠ m, (_ : m < p.size) → ¬p.fn[m].Free p n := by
  constructor
  · intro hc n hn _
    intro hne
    solve_by_elim
  · intro hf n hn
    cases hn with
    | fn _ _ hne hn =>
      solve_by_elim

@[simp]
theorem app_closed_iff {p : Program} {f e : Expr} :
    (f.app e).Closed p ↔ f.Closed p ∧ e.Closed p := by
  constructor
  · intro h
    constructor <;> solve_by_elim [Expr.Free.appL, Expr.Free.appR]
  · rintro ⟨hf, he⟩ n (- | -) <;> solve_by_elim

@[simp]
theorem bool_closed (p : Program) (b : Bool) : (Expr.bool b).Closed p := nofun

@[simp]
theorem cond_closed_iff {p : Program} {c et ef : Expr} :
    (c.cond et ef).Closed p ↔ c.Closed p ∧ et.Closed p ∧ ef.Closed p := by
  constructor
  · intro h
    open Expr.Free in
    and_intros <;> solve_by_elim [condC, condT, condF]
  · rintro ⟨hc, het, hef⟩ n (- | - | -) <;> solve_by_elim

theorem lt_size_of_free {p : Program} {e : Expr} {n : Nat} (hp : p.ValidRefs)
    (he : e.ValidRefs p) (hf : e.Free p n) : n < p.size := by
  induction hf with cases he <;> apply_rules

theorem lt_size_left_of_nests {p : Program} {m n : Nat} (hp : p.ValidRefs)
    (h : m ≻[p] n) : m < p.size := by
  induction h with apply_rules [lt_size_of_free]

theorem lt_size_right_of_nests {p : Program} {m n : Nat} : n ≻[p] m → m < p.size
  | .free _ hm _ _ => hm
  | .step _ _ hm _ _ _ => hm

theorem lt_size_left_of_nestsEq {p : Program} {m n : Nat} (hp : p.ValidRefs) :
    m ≽[p] n → m < p.size
  | .refl h => h
  | .nests _ h => lt_size_left_of_nests hp h

theorem nests_self {p : Program} {n : Nat} :
    (h : n ≻[p] n) → ∃ m ≠ n, (p.fn[n]'(lt_size_right_of_nests h)).Free p m
  | .free _ _ hne _ => nomatch hne
  | .step k _ _ hne hf _ => ⟨k, hne, hf⟩

theorem nests_trans {p : Program} {m n k : Nat} (h : m ≻[p] n) (h' : n ≻[p] k) :
    m ≻[p] k := by
  induction h' with apply Nests.step <;> assumption
