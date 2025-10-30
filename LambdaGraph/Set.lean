/-!
This module defines sets and set syntax in the style of Mathlib, though only a
small subset of the functionality is needed here.
-/

universe u
variable {α : Type u}

/-- A set of elements of type `α`, represented as its membership predicate. -/
def Set (α : Type u) := α → Prop

/-- A membership predicate interpreted as a set. -/
def setOf (p : α → Prop) : Set α := p

syntax "{" ident (" : " term)? " | " term "}" : term

macro_rules
  | `({ $x $[: $t]? | $p }) => `(setOf fun $x $[: $t]? => $p)

@[app_unexpander setOf]
def unexpandSetOf : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident => $p) => `({$x | $p})
  | _ => throw ()

namespace Set

def univ : Set α := setOf fun _ => True

instance : EmptyCollection (Set α) where
  emptyCollection := setOf fun _ => False

instance : Singleton α (Set α) where
  singleton a := setOf (· = a)

instance : Membership α (Set α) where
  mem s a := s a

instance : HasSubset (Set α) where
  Subset s₁ s₂ := ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

instance : Insert α (Set α) where
  insert a s := {b | b = a ∨ b ∈ s}

@[ext]
protected theorem ext {α : Type u} (s₁ s₂ : Set α) (h : ∀ a, a ∈ s₁ ↔ a ∈ s₂) :
    s₁ = s₂ := funext fun a => propext (h a)

@[simp]
theorem mem_univ (a : α) : a ∈ univ := trivial

@[simp]
theorem notMem_empty (a : α) : a ∉ (∅ : Set α) := nofun

@[simp]
theorem mem_setOf {a : α} {p : α → Prop} : a ∈ setOf p ↔ p a := Iff.rfl

@[simp]
theorem mem_singleton {a b : α} : a ∈ ({b} : Set α) ↔ a = b := Iff.rfl

@[simp]
theorem mem_insert_self {a : α} {s : Set α} : a ∈ insert a s := Or.inl rfl

@[simp]
theorem mem_insert {a b : α} {s : Set α} : a ∈ insert b s ↔ a = b ∨ a ∈ s := by
  simp [insert]

@[simp]
theorem empty_subset (s : Set α) : ∅ ⊆ s := nofun

@[refl, simp]
theorem subset_refl (s : Set α) : s ⊆ s := fun _ h => h

@[simp]
theorem insert_empty (a : α) : insert a ∅ = ({a} : Set α) := by
  simp [insert, singleton]

theorem insert_insert (a b : α) (s : Set α) :
    insert a (insert b s) = insert b (insert a s) := by
  ext c
  constructor <;> rintro (rfl | h) <;>
    solve | solve_by_elim [Or.inl, Or.inr]
          | cases h <;> solve_by_elim [Or.inr]

@[simp]
theorem subset_insert (a : α) (s : Set α) : s ⊆ insert a s := fun _ => Or.inr

@[simp]
theorem insert_subset_insert (a : α) {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) :
    insert a s₁ ⊆ insert a s₂ :=
  fun _ hb =>
    match hb with
    | Or.inl hb => Or.inl hb
    | Or.inr hb => Or.inr (h hb)

@[simp]
theorem singleton_subset_insert (a : α) (s : Set α) : {a} ⊆ insert a s := by
  simp [Subset]

variable (a b : α) (s s₁ s₂ : Set α)

instance : Decidable (a ∈ univ) := isTrue trivial

instance : Decidable (a ∈ (∅ : Set α)) := isFalse nofun

instance [Decidable (a = b)] : Decidable (a ∈ ({b} : Set α)) :=
  inferInstanceAs (Decidable (a = b))

instance {p : α → Prop} [Decidable (p a)] : Decidable (a ∈ setOf p) :=
  inferInstanceAs (Decidable (p a))

instance [Decidable (a = b)] [Decidable (a ∈ s)] : Decidable (a ∈ insert b s) :=
  inferInstanceAs (Decidable (_ ∨ _))

end Set
