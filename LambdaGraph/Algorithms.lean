module

import Std.Data.HashSet
public import Std.Data.HashSet.Basic

import LambdaGraph.Finset
public import LambdaGraph.Nest

public section

@[expose]
def Expr.ty (p : Program) : Expr → Option Ty
  | var n => if _ : n < p.size then p.ty[n] else none
  | fn n => if _ : n < p.size then p.ty[n].fn p.ret[n] else none
  | const c => c.ty
  | bin .app e₁ e₂ => do
    let .fn t₁ t₂ ← e₁.ty p | none
    let t₁' ← e₂.ty p
    guard <| t₁ = t₁'
    t₂
  | bin .pair e₁ e₂ => do
    let t₁ ← e₁.ty p
    let t₂ ← e₂.ty p
    t₁.prod t₂
  | cond c et ef => do
    let tc ← c.ty p
    guard <| tc = .bool
    let t ← et.ty p
    let t' ← ef.ty p
    guard <| t = t'
    t
  | proj e i => do
    let .prod t₁ t₂ ← e.ty p | none
    if i = 0 then t₁ else t₂

theorem Expr.ty_correct {p : Program} {e : Expr} {t : Ty} :
    e.ty p = some t ↔ p ⊢ e : t := by
  constructor <;> intro h
  · induction e generalizing t with
    | var n =>
      simp only [ty, Option.dite_none_right_eq_some, Option.some.injEq] at h
      obtain ⟨hn, rfl⟩ := h
      constructor
    | fn n =>
      simp only [ty, Option.dite_none_right_eq_some, Option.some.injEq] at h
      obtain ⟨hn, rfl⟩ := h
      constructor
    | const c =>
      simp only [ty, Option.some.injEq] at h
      obtain rfl := h
      constructor
    | bin k e₁ e₂ ih₁ ih₂ =>
      cases k with
      | app =>
        cases h₁ : e₁.ty p with
        | none => simp [ty, h₁] at h
        | some tf =>
          cases tf <;> try solve | simp [ty, h₁] at h
          rename_i t₁ t₂
          cases h₂ : e₂.ty p with
          | none => simp [ty, h₁, h₂] at h
          | some t₁' =>
            have ht₁ := ih₁ h₁
            have ht₂ := ih₂ h₂
            by_cases heq : t₁ = t₁'
            · rw [← heq] at ht₂
              simp only [ty, h₁, h₂, heq, guard, Option.pure_def, Option.bind_eq_bind,
                Option.bind_some, ↓reduceIte, Option.some.injEq] at h
              subst t
              constructor <;> assumption
            · simp! [guard, failure, h₁, h₂, heq] at h
      | pair =>
        cases h₁ : e₁.ty p with
        | none => simp! [h₁] at h
        | some t₁ =>
          cases h₂ : e₂.ty p with
          | none => simp! [h₁, h₂] at h
          | some t₂ =>
            have ht₁ := ih₁ h₁
            have ht₂ := ih₂ h₂
            simp only [ty, h₁, h₂, Option.bind_eq_bind, Option.bind, Option.some.injEq] at h
            subst t
            constructor <;> assumption
    | cond c et ef ihc ihet ihef =>
      cases hc : c.ty p with
      | none => simp! [hc] at h
      | some tc =>
        cases tc <;> try solve | simp! [guard, failure, hc] at h
        cases het : et.ty p with
        | none => simp! [hc, het] at h
        | some tt =>
          cases hef : ef.ty p with
          | none => simp! [hc, het, hef] at h
          | some tf =>
            have htc := ihc hc
            have htet := ihet het
            have htef := ihef hef
            by_cases heq : tt = tf
            · simp [ty, hc, het, heq, hef, guard, Option.pure_def, Option.bind_eq_bind,
                Option.bind_some, ↓reduceIte, Option.some.injEq] at h
              subst tt tf
              constructor <;> assumption
            · simp! [guard, failure, *] at h
    | proj e i ih =>
      cases he : e.ty p with
      | none => simp! [he] at h
      | some te =>
        cases te <;> try solve | simp! [he] at h
        rename_i t₁ t₂
        have ht := ih he
        by_cases hi : i = 0
        · subst i
          simp only [ty, he, Fin.isValue, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq] at h
          subst t
          constructor
          assumption
        · obtain rfl : i = 1 := by omega
          simp only [ty, he, hi, Fin.isValue, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq] at h
          subst t
          constructor
          assumption
  · induction h with simp! [guard, *]

instance {p : Program} {e : Expr} {t : Ty} : Decidable (p ⊢ e : t) :=
  decidable_of_iff (e.ty p = some t) Expr.ty_correct

instance {p : Program} : Decidable (⊢ p) :=
  inferInstanceAs (Decidable (∀ n (_ : n < p.size), p ⊢ p.fn[n] : p.ret[n]))

instance {c : Computation} {t : Ty} : Decidable (⊢ c : t) :=
  decidable_of_iff (⊢ c.toProgram ∧ c.toProgram ⊢ c.expr : t) <| by
    grind [Computation.Types]

end

def Expr.locals : Expr → Std.HashSet Nat × Std.HashSet Nat
  | var n => ({n}, ∅)
  | fn n => (∅, {n})
  | const _ => (∅, ∅)
  | bin _ e₁ e₂ =>
    let (v₁, f₁) := e₁.locals
    let (v₂, f₂) := e₂.locals
    (v₁ ∪ v₂, f₁ ∪ f₂)
  | cond c et ef =>
    let (vc, fc) := c.locals
    let (vt, ft) := et.locals
    let (vf, ff) := ef.locals
    (vc ∪ vt ∪ vf, fc ∪ ft ∪ ff)
  | proj e _ => e.locals

theorem Expr.var_in_locals_iff {e : Expr} {n : Nat} :
    n ∈ e.locals.1 ↔ e.LocalVar n := by
  constructor <;> intro h <;> fun_induction locals <;>
    grind [Std.HashSet.singleton_eq_insert, Std.HashSet.mem_union_iff]

theorem Expr.fn_in_locals_iff {e : Expr} {n : Nat} :
    n ∈ e.locals.2 ↔ e.LocalFn n := by
  constructor <;> intro h <;> fun_induction locals <;>
    grind [Std.HashSet.singleton_eq_insert, Std.HashSet.mem_union_iff]

instance {e : Expr} {n : Nat} {r : RefKind} : Decidable (e.Local n r) :=
  match r with
  | .var => decidable_of_bool (e.locals.1.contains n) Expr.var_in_locals_iff
  | .fn => decidable_of_bool (e.locals.2.contains n) Expr.fn_in_locals_iff

instance {e : Expr} {q : Nat → RefKind → Prop} [DecidableRel q] :
    Decidable (∀ n r, e.Local n r → q n r) :=
  let (eq := hlc) (lv, lf) := e.locals
  decidable_of_bool (lv.all (decide <| q · .var) && lf.all (decide <| q · .fn)) <| by
    grind [cases RefKind, Expr.var_in_locals_iff, Expr.fn_in_locals_iff,
      Std.HashSet.all_eq_true_iff_forall_mem]

instance {e : Expr} {n : Nat} : Decidable (e.Bounded n) :=
  inferInstanceAs (Decidable (∀ m r, e.Local m r → m < n))

abbrev Rel : Type := Nat → Nat → Prop

inductive Path (r : Rel) : Nat → Nat → Type where
  | refl n : Path r n n
  | step m n k : r m n → Path r n k → Path r m k

def Path.length {r : Rel} {m n : Nat} : Path r m n → Nat
  | refl _ => 0
  | step _ _ _ _ path => path.length + 1

def Path.labels {r : Rel} {m n : Nat} : Path r m n → Finset
  | refl n => {n}
  | step n _ _ _ path => path.labels.insert n

inductive Path.Mem {r : Rel} (l : Nat) : ∀ {m n}, Path r m n → Prop where
  | head n (path : Path r l n) : path.Mem l
  | tail m n k hs (path : Path r n k) : path.Mem l → (path.step m n k hs).Mem l

instance {r : Rel} {m n : Nat} : Membership Nat (Path r m n) where
  mem path l := path.Mem l

@[simp, grind =]
theorem Path.length_refl {r : Rel} {n : Nat} : (@Path.refl r n).length = 0 := by
  simp [length]

@[simp, grind =]
theorem Path.length_step {r : Rel} {m n k : Nat} {path : Path r n k}
    (h : r m n) : (path.step _ _ _ h).length = path.length + 1 := by
  simp [length]

@[simp, grind =]
theorem Path.length_eq_zero_iff {r : Rel} {m n : Nat} {path : Path r m n} :
    path.length = 0 ↔ ∃ (h : m = n), path = h ▸ .refl m := by
  constructor
  · intro h
    cases path with
    | refl _ => exact ⟨rfl, rfl⟩
    | step _ k n hs path => simp at h
  · rintro ⟨rfl, rfl⟩
    simp

theorem Path.end_mem {r : Rel} {m n : Nat} (path : Path r m n) : n ∈ path :=
  match path with
  | refl _ => .head _ _
  | step _ _ _ _ path => .tail _ _ _ _ _ path.end_mem

@[simp, grind =]
theorem Path.mem_refl_iff {r : Rel} {l n : Nat} :
    l ∈ @Path.refl r n ↔ l = n := by
  constructor
  · intro h
    have .head _ _ := h
    rfl
  · intro rfl
    constructor

@[simp, grind =]
theorem Path.mem_step_iff {r : Rel} {l m n k : Nat} {path : Path r n k}
    (hs : r m n) : l ∈ path.step _ _ _ hs ↔ l = m ∨ l ∈ path := by
  constructor
  · intro h
    cases h with
    | head _ _ => exact .inl rfl
    | tail _ _ _ _ _ h => exact .inr h
  · rintro (rfl | h) <;> constructor <;> assumption

def Path.Bounded {r : Rel} {m k : Nat} (path : Path r m k) (n : Nat) : Prop :=
  ∀ ⦃l⦄, l ∈ path → l < n

theorem Path.labels_correct {r : Rel} {l m n : Nat} {path : Path r m n} :
    l ∈ path.labels ↔ l ∈ path := by
  constructor <;> intro h
  · fun_induction labels
    next n =>
      simp only [Finset.singleton_eq_insert, Finset.mem_insert_iff,
        Finset.notMem_emptyCollection, or_false] at h
      subst n
      constructor
    next k m n hs path ih =>
      simp only [Finset.mem_insert_iff] at h
      obtain rfl | h := h
      · constructor
      · apply_rules [Mem.tail]
  · induction h with grind [labels, cases Path]

def Path.push {r : Rel} {m n k : Nat} (path : Path r m n) (h : r n k) :
    Path r m k :=
  match path with
  | refl _ => .step _ _ _ h (.refl _)
  | step _ _ _ hs path => .step _ _ _ hs (path.push h)

@[simp, grind =]
theorem Path.length_push {r : Rel} {m n k : Nat} {path : Path r m n}
    (h : r n k) : (path.push h).length = path.length + 1 := by
  induction path with simp [length, push, *]

@[simp, grind =]
theorem Path.mem_push_iff {r : Rel} {l m n k : Nat} {path : Path r m n}
    (h : r n k) : l ∈ path.push h ↔ l ∈ path ∨ l = k := by
  induction path with grind [push]

def Path.concat {r : Rel} {m n k : Nat} (path₁ : Path r m n)
    (path₂ : Path r n k) : Path r m k :=
  match path₁ with
  | refl m => path₂
  | step l m n hs path₁ => .step l m k hs (path₁.concat path₂)

@[simp, grind =]
theorem Path.length_concat {r : Rel} {m n k : Nat} {path₁ : Path r m n}
    {path₂ : Path r n k} :
    (path₁.concat path₂).length = path₁.length + path₂.length := by
  induction path₁ with simp +arith [concat, *]

theorem Path.split_last {r : Rel} {m n : Nat} (path : Path r m n) :
    (∃ (h : m = n), path = h ▸ .refl _) ∨
      ∃ k h, ∃ path' : Path r m k, path = path'.push h := by
  induction path with
  | refl m => exact .inl ⟨rfl, rfl⟩
  | step m k n hs path ih =>
    obtain ⟨rfl, rfl⟩ | ⟨l, hs', path, rfl⟩ := ih
    · exact .inr ⟨_, hs, .refl _, rfl⟩
    · exact .inr ⟨_, hs', .step _ _ _ hs path, rfl⟩

inductive Path.Acyclic {r : Rel} : ∀ {m n}, Path r m n → Prop where
  | refl n : (Path.refl n).Acyclic
  | step m n k hs (path : Path r n k) :
    m ∉ path → path.Acyclic → (path.step m n k hs).Acyclic

theorem Path.size_labels_eq_of_acyclic {r : Rel} {m n : Nat} {path : Path r m n}
    (h : path.Acyclic) : path.labels.size = path.length + 1 := by
  induction h with
    simp_all! [labels_correct, Finset.size_insert_of_mem,
      Finset.size_insert_of_notMem]

theorem Path.length_lt_size_of_acyclic {r : Rel} {n m k : Nat}
    {path : Path r m k} (h : path.Acyclic) (hb : path.Bounded n) :
    path.length < n := by
  apply Nat.lt_of_succ_le
  simp only [Nat.succ_eq_add_one, ← size_labels_eq_of_acyclic h]
  apply Finset.size_le_of_all_lt
  intro k hk
  rw [labels_correct] at hk
  exact hb hk

theorem Path.exists_of_mem {r : Rel} {l m n : Nat} {path : Path r m n}
    (h : l ∈ path) : ∃ (path' : Path r l n),
      path'.length ≤ path.length ∧ ∀ k ∈ path', k ∈ path := by
  induction h with grind

theorem Path.exists_acyclic.aux {r : Rel} {b m n : Nat} {path : Path r m n}
    (hb : path.length ≤ b) : ∃ (path' : Path r m n),
      path'.Acyclic ∧ ∀ l ∈ path', l ∈ path := by
  induction b generalizing m n path with
  | zero =>
    cases path with
    | refl _ => exact ⟨.refl m, .refl m, fun _ h => h⟩
    | step _ k n hs path => simp [length] at hb
  | succ b ih =>
    cases path with
    | refl _ => exact ⟨.refl m, .refl m, fun _ h => h⟩
    | step _ k n hs path =>
      simp only [length, Nat.add_le_add_iff_right] at hb
      by_cases hm : m ∈ path
      · obtain ⟨path', hlen, h⟩ := exists_of_mem hm
        grind
      · obtain ⟨path', ha, h⟩ := ih hb
        replace hm : m ∉ path' := fun hm' => hm (h _ hm')
        refine ⟨.step m k n hs path', .step _ _ _ _ _ hm ha, ?_⟩
        grind

theorem Path.exists_acyclic {r : Rel} {m n : Nat} (path : Path r m n) :
    ∃ (path' : Path r m n), path'.Acyclic ∧ ∀ l ∈ path', l ∈ path :=
  exists_acyclic.aux (Nat.le_refl _)

theorem Program.pathWithout_iff {p : Program} {m n k : Nat} :
    m ⟶[p, n]* k ↔ ∃ path : Path p.Succ m k, n ∉ path := by
  constructor
  · intro h
    induction h with
    | refl m hne =>
      exists .refl _
      grind
    | step m l k hne hs h ih =>
      obtain ⟨path, hn⟩ := ih
      exists .step _ _ _ hs path
      grind
  · rintro ⟨path, h⟩
    induction path with grind [intro PathWithout]

theorem Program.bounded_path_succ {p : Program} {m n : Nat}
    {path : Path p.Succ m n} (hn : n < p.size) : path.Bounded p.size := by
  intro l hl
  induction hl with
  | head n path =>
    cases path with
    | refl _ => exact hn
    | step _ k n hs path => exact hs.1
  | tail m k n hs path hl ih => exact ih hn

theorem Expr.free_iff' {p : Program} {e : Expr} {n : Nat} :
    e.Free p n ↔
      e.LocalVar n ∨ ∃ (m k : Nat) (hk : k < p.size) (path : Path p.Succ m k),
        e.LocalFn m ∧ p.fn[k].LocalVar n ∧ n ∉ path ∧
        path.length < p.size := by
  constructor
  · intro hf
    obtain hlv | ⟨m, k, hk, hlf, hpath, hlv⟩ := free_iff.mp hf
    · exact .inl hlv
    · obtain ⟨path, hn⟩ := Program.pathWithout_iff.mp hpath
      obtain ⟨path', ha, h⟩ := path.exists_acyclic
      have hlen :=
        Path.length_lt_size_of_acyclic ha (Program.bounded_path_succ hk)
      exact .inr ⟨m, k, hk, path', hlf, hlv, fun hn' => hn (h _ hn'), hlen⟩
  · rintro (hlv | ⟨m, k, hk, path, hlf, hlv, hn, hlen⟩)
    · exact free_of_localVar hlv
    · have hpath := Program.pathWithout_iff.mpr ⟨path, hn⟩
      exact free_iff.mpr <| .inr ⟨m, k, hk, hlf, hpath, hlv⟩

def Program.FnFree (p : Program) (m n : Nat) : Prop :=
  ∃ hm, n < p.size ∧ n ≠ m ∧ (p.fn[m]'hm).Free p n

theorem Program.bounded_path_fnFree {p : Program} {m n : Nat}
    {path : Path p.FnFree m n} (hn : n < p.size) : path.Bounded p.size := by
  intro l hl
  induction path with
  | refl n => simp_all
  | step m k n hs path ih =>
    obtain ⟨hm, hk, hne, hf⟩ := hs
    cases hl with
    | head _ _ => exact hm
    | tail _ _ _ hs _ hl => exact ih hn hl

theorem Program.nestsEq_iff_exists_path {p : Program} {n m : Nat} :
      n ≽[p] m ↔ n < p.size ∧ ∃ path : Path p.FnFree m n, path.length < p.size := by
  suffices n ≽[p] m ↔ n < p.size ∧ ∃ path : Path p.FnFree m n, True by
    rw [this]
    constructor <;> rintro ⟨hn, path, -⟩
    · obtain ⟨path', ha, h⟩ := path.exists_acyclic
      exact ⟨hn, path',
        Path.length_lt_size_of_acyclic ha (bounded_path_fnFree hn)⟩
    · exact ⟨hn, path, .intro⟩
  constructor
  · intro h
    cases h with
    | refl hn => exact ⟨hn, .refl _, .intro⟩
    | nests _ h =>
      induction h with
      | free n m hn hm hne hf =>
        exact ⟨hn, .step _ _ _ ⟨hm, hn, hne, hf⟩ (.refl _), by grind⟩
      | trans n k m h₁ h₂ ih₁ ih₂ =>
        obtain ⟨hn, path₁, -⟩ := ih₁
        obtain ⟨hk, path₂, -⟩ := ih₂
        exact ⟨hn, path₂.concat path₁, .intro⟩
  · rintro ⟨hn, path, -⟩
    induction path with
    | refl n => exact .refl hn
    | step m k n hs path ih =>
      obtain ⟨hm, hk, hkm, hf⟩ := hs
      have h := Nests.free _ _ hk hm hkm hf
      cases ih hn with
      | refl hk => exact .nests _ h
      | nests _ h' =>
        exact .nests _ (.trans _ _ _ h' h)

def flatMap (s : Std.HashSet Nat) (f : Nat → Std.HashSet Nat) : Std.HashSet Nat :=
  aux ∅ s.toList
  where
    aux s
      | [] => s
      | n :: ns => aux (s ∪ f n) ns

@[simp, grind =]
theorem mem_flatMap_iff {s : Std.HashSet Nat} {f : Nat → Std.HashSet Nat}
    {n : Nat} : n ∈ flatMap s f ↔ ∃ m ∈ s, n ∈ f m := by
  suffices ∀ t l, n ∈ flatMap.aux f t l ↔ n ∈ t ∨ ∃ m ∈ l, n ∈ f m by
    replace := this ∅ s.toList
    simpa
  intro t l
  induction l generalizing t with grind [flatMap.aux, Std.HashSet.mem_union_iff]

@[simp, grind =]
theorem mem_union_iff {s₁ s₂ : Std.HashSet Nat} {n : Nat} :
    n ∈ s₁ ∪ s₂ ↔ n ∈ s₁ ∨ n ∈ s₂ := by grind [Std.HashSet.mem_union_iff]

public section

def Program.fnFreeVars (p : Program) : Vector (Std.HashSet Nat) p.size :=
  let (lvs, lfs) := Vector.ofFn (p.fn[·].locals) |>.unzip
  aux lfs lvs p.size
  where
    aux lfs v : Nat → _
      | 0 => v
      | n + 1 =>
        let update free lf :=
          free ∪ flatMap lf fun m =>
            if hm : m < p.size then v[m].erase m else ∅
        aux lfs (v.zipWith update lfs) n

theorem Program.fnFreeVars_correct {p : Program} {m n : Nat} (hm : m < p.size) :
    n ∈ p.fnFreeVars[m] ↔ p.fn[m].Free p n := by
  let (eq := hlc) (lvs, lfs) := Vector.ofFn (n := p.size) (p.fn[·].locals) |>.unzip
  have hlvs : ∀ {i} (hi : i < p.size) k, k ∈ lvs[i] ↔ p.fn[i].LocalVar k := by
    grind [Expr.var_in_locals_iff]
  have hlfs : ∀ {i} (hi : i < p.size) k, k ∈ lfs[i] ↔ p.fn[i].LocalFn k := by
    grind [Expr.fn_in_locals_iff]
  suffices ∀ v i, n ∈ (fnFreeVars.aux p lfs v i)[m]'hm ↔
      n ∈ v[m] ∨ ∃ (k l : Nat) (hl : l < p.size) (path : Path p.Succ k l),
        p.fn[m].LocalFn k ∧ n ∈ v[l] ∧ n ∉ path ∧ path.length < i by
    have := this lvs p.size
    unfold fnFreeVars
    rw [hlc, this]
    simp only [hlvs, Expr.free_iff']
  intro v i
  induction i generalizing v with
  | zero => simp [fnFreeVars.aux]
  | succ i ih =>
    let update free lf :=
      free ∪ flatMap lf fun m =>
        if hm : m < p.size then v[m].erase m else ∅
    specialize ih (v.zipWith update lfs)
    constructor
    · intro h
      obtain hn | ⟨k, l, hl, path, hlf, hn, hmem, hlen⟩ := ih.mp h <;>
        simp only [Vector.getElem_zipWith, mem_union_iff, mem_flatMap_iff, update] at hn
      · obtain hn | ⟨k, hlf, hn⟩ := hn
        · exact .inl hn
        · rw [hlfs] at hlf
          have hk : k < p.size := by grind
          simp only [hk, ↓reduceDIte, Std.HashSet.mem_erase, beq_eq_false_iff_ne, ne_eq] at hn
          obtain ⟨hne, hn⟩ := hn
          exact .inr <| ⟨_, _, hk, .refl _, hlf, hn, by grind⟩
      · obtain hn | ⟨o, hlf', hn⟩ := hn
        · exact .inr ⟨_, _, hl, path, hlf, hn, hmem, by lia⟩
        · rw [hlfs] at hlf'
          have ho : o < p.size := by grind
          simp only [ho, ↓reduceDIte, Std.HashSet.mem_erase, beq_eq_false_iff_ne, ne_eq] at hn
          obtain ⟨hne, hn⟩ := hn
          exact .inr <| ⟨_, _, ho, path.push ⟨hl, hlf'⟩, hlf, hn, by grind⟩
    · erw [ih]
      rintro (hn | ⟨k, l, hl, path, hlf, hn, hmem, hlen⟩)
      · simp [update, hn]
      · obtain h | ⟨o, hs, path, rfl⟩ := path.split_last
        · grind
        · simp only [Path.length_push, Nat.add_lt_add_iff_right] at hlen
          have ho := hs.1
          have hn' : n ∈ (v.zipWith update lfs)[o] := by grind [Succ]
          exact .inr ⟨_, _, ho, path, hlf, hn', by grind, hlen⟩

def Expr.freeVars (e : Expr) (p : Program) :=
  let (lv, lf) := e.locals
  let ffs := p.fnFreeVars
  lv ∪ flatMap lf fun m => if hm : m < p.size then ffs[m].erase m else ∅

theorem Expr.freeVars_correct {p : Program} {e : Expr} {n : Nat} :
    n ∈ e.freeVars p ↔ e.Free p n := by
  simp only [freeVars, mem_union_iff, var_in_locals_iff, mem_flatMap_iff, fn_in_locals_iff]
  constructor
  · rintro (hlv | ⟨m, hlf, hn⟩)
    · exact free_of_localVar hlv
    · have hm : m < p.size := by grind
      simp only [hm, ↓reduceDIte, Std.HashSet.mem_erase, beq_eq_false_iff_ne,
        Program.fnFreeVars_correct] at hn
      obtain ⟨hne, hf⟩ := hn
      exact free_of_localFn_of_free hm hne.symm hlf hf
  · intro hf
    obtain hlv | ⟨m, k, hk, hlf, hpath, hlv⟩ := free_iff.mp hf
    · exact .inl hlv
    · have hm : m < p.size := by cases hpath <;> grind [Program.Succ]
      refine .inr ⟨m, hlf, ?_⟩
      simp only [hm, ↓reduceDIte, Std.HashSet.mem_erase, beq_eq_false_iff_ne,
        Program.fnFreeVars_correct]
      have hne := hpath.ne_start
      exact ⟨hne.symm, (Program.free_in_fn_iff hm hne).mpr ⟨_, hk, hlv, hpath⟩⟩

instance {p : Program} {e : Expr} {n : Nat} : Decidable (e.Free p n) :=
  decidable_of_bool ((e.freeVars  p).contains n) Expr.freeVars_correct

instance {p : Program} {e : Expr} {q : Nat → Prop} [DecidablePred q] :
    Decidable (∀ n, e.Free p n → q n) :=
  decidable_of_bool ((e.freeVars p).all (decide <| q ·)) <| by
    simp [Expr.freeVars_correct, Std.HashSet.all_eq_true_iff_forall_mem]

instance {p : Program} {e : Expr} : Decidable (e.Closed p) :=
  inferInstanceAs (Decidable (∀ n, ¬e.Free p n))

instance {c : Computation} {n : Nat} : Decidable (c.Free n) :=
  inferInstanceAs (Decidable (c.expr.Free c.toProgram n))

instance {c : Computation} : Decidable c.Closed :=
  inferInstanceAs (Decidable (c.expr.Closed c.toProgram))

def Program.nesters (p : Program) : Vector (Std.HashSet Nat) p.size :=
  let fvs := p.fnFreeVars.mapIdx fun i v => (v.erase i).filter (· < p.size)
  aux fvs fvs (p.size - 1)
  where
    aux fvs v : Nat → _
      | 0 => v
      | n + 1 =>
        let update free fv :=
          free ∪ flatMap fv fun m =>
            if hm : m < p.size then v[m] else ∅
        aux fvs (v.zipWith update fvs) n

theorem Program.nesters_correct {p : Program} {m n : Nat} (hm : m < p.size) :
    n ∈ p.nesters[m] ↔ n ≻[p] m := by
  let fvs := p.fnFreeVars.mapIdx fun i v => (v.erase i).filter (· < p.size)
  have hfvs : ∀ {i} (hi : i < p.size) k, k ∈ fvs[i] ↔ k < p.size ∧ k ≠ i ∧ p.fn[i].Free p k := by
    grind [fnFreeVars_correct]
  suffices ∀ v i, (∀ (k : Nat) hk, n ∈ v[k]'hk → n < p.size) →
    (n ∈ (nesters.aux p fvs v i)[m]'hm ↔
      n < p.size ∧ (n ∈ v[m] ∨ ∃ (k : Nat) (hk : k < p.size) (path : Path p.FnFree m k),
        n ∈ v[k] ∧ path.length ≤ i)) by
    have := this fvs (p.size - 1) (by grind)
    unfold nesters
    rw [this]
    simp only [hfvs]
    constructor
    · rintro ⟨hn, ⟨hk, hne, hf⟩ | ⟨k, hk, path, ⟨hn, hne, hf⟩, hlen⟩⟩
      · exact .free _ _ hn hm hne hf
      · have h := nestsEq_iff_exists_path.mpr ⟨hk, path, by grind⟩
        exact nests_iff'.mpr ⟨_, _, hn, hne, hf, h⟩
    · intro h
      obtain ⟨k, hk, hn, hne, hf, h⟩ := nests_iff'.mp h
      obtain ⟨-, path, hlen⟩ := nestsEq_iff_exists_path.mp h
      exact ⟨hn, .inr ⟨_, hk, path, ⟨hn, hne, hf⟩, by grind⟩⟩
  intro v i
  induction i generalizing v with
  | zero =>
    intro himp
    constructor
    · intro hv
      simp only [nesters.aux] at hv
      exact ⟨himp _ hm hv, .inl hv⟩
    · rintro ⟨hn, hv | ⟨k, hk, path, hv, hlen⟩⟩
      · simpa [nesters.aux] using hv
      · simp only [Nat.le_zero_eq, Path.length_eq_zero_iff] at hlen
        obtain ⟨rfl, rfl⟩ := hlen
        simpa [nesters.aux] using hv
  | succ i ih =>
    let update free fv :=
      free ∪ flatMap fv fun m =>
        if hm : m < p.size then v[m] else ∅
    intro himp
    replace himp : ∀ (k : Nat) hk, n ∈ (v.zipWith update fvs)[k]'hk → n < p.size := by
      simp only [Vector.getElem_zipWith, mem_union_iff, mem_flatMap_iff, update]
      rintro k hk (hv | ⟨l, hf, hv⟩)
      · exact himp _ hk hv
      · have hl : l < p.size := by grind
        simp only [hl, ↓reduceDIte] at hv
        exact himp _ hl hv
    specialize ih (v.zipWith update fvs) himp
    constructor
    · intro h
      obtain ⟨hn, hv | ⟨k, hk, path, hv, hlen⟩⟩ := ih.mp h <;>
        simp only [Vector.getElem_zipWith, mem_union_iff, mem_flatMap_iff, update] at hv
      · obtain hv | ⟨k, hf, hv⟩ := hv
        · exact ⟨hn, .inl hv⟩
        · rw [hfvs] at hf
          obtain ⟨hk, hne, hf⟩ := hf
          simp only [hk, ↓reduceDIte] at hv
          exact ⟨hn, .inr <| ⟨_, hk, .step _ _ _ ⟨hm, hk, hne, hf⟩ (.refl _), hv, by grind⟩⟩
      · obtain hv | ⟨l, hf, hv⟩ := hv
        · exact ⟨hn, .inr ⟨_, hk, path, hv, by lia⟩⟩
        · rw [hfvs] at hf
          obtain ⟨hl, hne, hf⟩ := hf
          simp only [hl, ↓reduceDIte] at hv
          exact ⟨hn, .inr ⟨_, hl, path.push ⟨hk, hl, hne, hf⟩, hv, by grind⟩⟩
    · erw [ih]
      rintro ⟨hn, hv | ⟨k, hk, path, hv, hlen⟩⟩
      · exact ⟨hn, .inl (by simp [update, hv])⟩
      · obtain ⟨rfl, rfl⟩ | ⟨l, hs, path, rfl⟩ := path.split_last
        · exact ⟨hn, .inl (by simp [update, hv])⟩
        · simp only [Path.length_push, Nat.add_le_add_iff_right] at hlen
          obtain ⟨hl, hk, hne, hf⟩ := hs
          replace hv : n ∈ (v.zipWith update fvs)[l] := by grind
          exact ⟨hn, .inr ⟨_, hl, path, hv, hlen⟩⟩

instance {p : Program} {n m : Nat} : Decidable (n ≻[p] m) :=
  decidable_of_iff (∃ hm : m < p.size, p.nesters[m].contains n) <| by
    grind [Program.nesters_correct]

instance {p : Program} {n m : Nat} : Decidable (n ≽[p] m) :=
  decidable_of_iff (∃ hm : m < p.size, n = m ∨ n ≻[p] m) <| by
    grind [Program.NestsEq]

instance {p : Program} : Decidable p.WF :=
  decidable_of_iff (∀ n < p.size, n ⊁[p] n) <| by grind [Program.WF]

end
