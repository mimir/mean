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

@[simp]
theorem mem_univ (a : α) : a ∈ univ := trivial

@[simp]
theorem notMem_empty (a : α) : a ∉ (∅ : Set α) := nofun

@[simp]
theorem subset_insert (a : α) (s : Set α) : s ⊆ insert a s := fun _ => Or.inr

@[simp]
theorem insert_subset_insert (a : α) {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) :
    insert a s₁ ⊆ insert a s₂ :=
  fun _ hb =>
    match hb with
    | Or.inl hb => Or.inl hb
    | Or.inr hb => Or.inr (h hb)

end Set
