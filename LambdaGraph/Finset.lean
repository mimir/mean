module

public section

structure Finset : Type where
  mem : Nat → Prop
  bound : Nat
  not_mem_of_ge_bound : ∀ m ≥ bound, ¬mem m

instance : Membership Nat Finset := ⟨Finset.mem⟩

instance : HasSubset Finset where
  Subset s₁ s₂ := ∀ n ∈ s₁, n ∈ s₂

instance : HasSSubset Finset where
  SSubset s₁ s₂ := s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁

instance : EmptyCollection Finset := ⟨fun _ => False, 0, by simp⟩

instance : Singleton Nat Finset where
  singleton n := ⟨fun m => m = n, n + 1, by lia⟩

open Classical in
noncomputable def Finset.size (s : Finset) : Nat := aux s.bound (Nat.le_refl _)
  where
    aux (i : Nat) (h : i ≤ s.bound) : Nat :=
      match i with
      | 0 => 0
      | i + 1 => aux i (by lia) + if i ∈ s then 1 else 0

end

def Finset.withBound (s : Finset) (b : Nat) (h : ∀ n ≥ b, n ∉ s) : Finset where
  mem := s.mem
  bound := b
  not_mem_of_ge_bound := by simpa [Membership.mem] using h

@[grind →]
theorem Finset.notMem_of_ge_bound {s : Finset} {n : Nat} (h : s.bound ≤ n) :
    n ∉ s := s.not_mem_of_ge_bound n h

theorem Finset.size_le_bound {s : Finset} : s.size ≤ s.bound := by
  suffices ∀ i hi, size.aux s i hi ≤ i from this _ (Nat.le_refl _)
  intro i hi
  fun_induction size.aux with grind

@[simp, grind =]
theorem Finset.mem_withBound_iff {s : Finset} {b n : Nat} (h : ∀ m ≥ b, m ∉ s) :
    n ∈ s.withBound b h ↔ n ∈ s := by
  simp [Membership.mem, withBound]

theorem Finset.size_withBound {s : Finset} {b : Nat} (h : ∀ n ≥ b, n ∉ s) :
    (s.withBound b h).size = s.size := by
  have h₁ : ∀ i (hi : i ≤ s.bound.min b),
      size.aux (s.withBound b h) i (by grind [withBound]) = size.aux s i (by grind) := by
    intro i hi
    fun_induction size.aux s i (by grind) with grind [size.aux]
  have h₂ : ∀ i hile (higt : s.bound.min b < i),
      size.aux s i hile = size.aux s (s.bound.min b) (by lia) := by
    intro i hile higt
    fun_induction size.aux s i hile with grind
  have h₃ : ∀ i hile (hige : s.bound.min b < i),
      size.aux (s.withBound b h) i hile = size.aux (s.withBound b h) (s.bound.min b) (by lia) := by
    intro i hile higt
    fun_induction size.aux _ i hile with grind
  grind [size]

public section

def Finset.insert (s : Finset) (n : Nat) : Finset where
  mem := fun m => m = n ∨ s.mem m
  bound := (n + 1).max s.bound
  not_mem_of_ge_bound := by grind [not_mem_of_ge_bound]

instance : Insert Nat Finset where
  insert n s := s.insert n

protected def Finset.union (s₁ s₂ : Finset) : Finset where
  mem := fun n => s₁.mem n ∨ s₂.mem n
  bound := s₁.bound.max s₂.bound
  not_mem_of_ge_bound := by grind [not_mem_of_ge_bound]

instance : Union Finset := ⟨Finset.union⟩

def Finset.filter (s : Finset) (p : Nat → Prop) : Finset where
  mem := fun n => s.mem n ∧ p n
  bound := s.bound
  not_mem_of_ge_bound := by grind [not_mem_of_ge_bound]

@[grind →]
theorem Finset.mem_of_subset {s₁ s₂ : Finset} {n : Nat} (h : s₁ ⊆ s₂)
    (hn : n ∈ s₁) : n ∈ s₂ := h _ hn

@[simp, grind .]
theorem Finset.notMem_emptyCollection {n : Nat} : n ∉ (∅ : Finset) := by
  simp [Membership.mem, EmptyCollection.emptyCollection]

@[simp, grind =]
theorem Finset.singleton_eq_insert {n : Nat} : {n} = (∅ : Finset).insert n := by
  simp [EmptyCollection.emptyCollection, Singleton.singleton, Finset.insert]

@[simp, grind =]
theorem Finset.mem_insert_iff {s : Finset} {m n : Nat} :
    n ∈ s.insert m ↔ n = m ∨ n ∈ s := by
  simp [Membership.mem, Finset.insert]

@[simp, grind =]
theorem Finset.mem_union_iff {s₁ s₂ : Finset} {n : Nat} :
    n ∈ s₁ ∪ s₂ ↔ n ∈ s₁ ∨ n ∈ s₂ := by
  simp [Membership.mem, Union.union, Finset.union]

@[simp, grind =]
theorem Finset.mem_filter_iff {s : Finset} {p : Nat → Prop} {n : Nat} :
    n ∈ s.filter p ↔ n ∈ s ∧ p n := by
  simp [Membership.mem, Finset.filter]

@[grind →]
theorem Finset.ssubset_of_subset {s₁ s₂ : Finset} {n : Nat} (h : s₁ ⊆ s₂)
    (h₁ : n ∉ s₁) (h₂ : n ∈ s₂) : s₁ ⊂ s₂ := ⟨h, fun h => h₁ (h _ h₂)⟩

@[simp, grind =]
theorem Finset.size_emptyCollection : (∅ : Finset).size = 0 := by
  simp [EmptyCollection.emptyCollection, size, size.aux]

theorem Finset.size_insert_of_mem {s : Finset} {n : Nat} (h : n ∈ s) :
    (s.insert n).size = s.size := by
  have hn : n < s.bound := by grind
  have hb : (s.insert n).bound = s.bound := by grind [insert]
  suffices ∀ i hi, size.aux (s.insert n) i hi = size.aux s i (hb ▸ hi) by
    have := this s.bound (hb ▸ Nat.le_refl _)
    simpa [hb, size]
  intro i hi
  fun_induction size.aux with grind [size.aux]

theorem Finset.size_insert_of_notMem {s : Finset} {n : Nat} (h : n ∉ s) :
    (s.insert n).size = s.size + 1 := by
  let b := (n + 1).max s.bound
  have hb : ∀ m ≥ b, m ∉ s := by grind [notMem_of_ge_bound]
  rw [← size_withBound hb]
  suffices ∀ i hi,
      size.aux (s.insert n) i hi =
        size.aux (s.withBound b hb) i hi + if n < i then 1 else 0 by
    have := this b (Nat.le_refl _)
    simpa [show n < b by grind]
  intro i hi
  fun_induction size.aux (s.insert n) i hi with grind [size.aux]

@[grind →]
theorem Finset.size_le_size {s₁ s₂ : Finset} (h : s₁ ⊆ s₂) :
    s₁.size ≤ s₂.size := by
  have hb : ∀ n ≥ s₂.bound, n ∉ s₁ := by grind [notMem_of_ge_bound]
  rw [← size_withBound hb]
  suffices ∀ i (hi : i ≤ s₂.bound),
      size.aux (s₁.withBound s₂.bound hb) i hi ≤ size.aux s₂ i hi from
    this _ _
  intro i hi
  fun_induction size.aux s₂ i hi with grind [size.aux]

@[grind →]
theorem Finset.size_lt_size {s₁ s₂ : Finset} (h : s₁ ⊂ s₂) :
    s₁.size < s₂.size := by
  obtain ⟨hsub, hex⟩ := h
  simp only [Subset, Classical.not_forall] at hex
  obtain ⟨n, h₂, h₁⟩ := hex
  calc s₁.size
    _ < (s₁.insert n).size := by
      rw [size_insert_of_notMem h₁]
      exact Nat.lt_succ_self _
    _ ≤ s₂.size := by
      apply size_le_size
      intro m h
      simp only [mem_insert_iff] at h
      obtain rfl | h := h
      · exact h₂
      · exact hsub _ h

theorem Finset.size_le_of_all_lt {s : Finset} {b : Nat} (h : ∀ n ∈ s, n < b) :
    s.size ≤ b := by
  have hb : ∀ n ≥ b, n ∉ s := by grind
  rw [← size_withBound hb]
  exact size_le_bound

end
