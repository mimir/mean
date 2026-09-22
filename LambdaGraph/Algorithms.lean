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

inductive Path (p : Program) : Nat → Nat → Type where
  | refl n : n < p.size → Path p n n
  | step m n k : m ⟶[p] n → Path p n k → Path p m k

def Path.length {p : Program} {m n : Nat} : Path p m n → Nat
  | refl _ _ => 0
  | step _ _ _ _ path => path.length + 1

def Path.labels {p : Program} {m n : Nat} : Path p m n → Finset
  | refl n _ => {n}
  | step n _ _ _ path => path.labels.insert n

inductive Path.Mem {p : Program} (l : Nat) : ∀ {m n}, Path p m n → Prop where
  | head n (path : Path p l n) : path.Mem l
  | tail m n k hs (path : Path p n k) : path.Mem l → (path.step m n k hs).Mem l

instance {p : Program} {m n : Nat} : Membership Nat (Path p m n) where
  mem path l := path.Mem l

@[simp, grind =]
theorem Path.length_refl {p : Program} {n : Nat} (hn : n < p.size) :
    (Path.refl n hn).length = 0 := by simp [length]

@[simp, grind =]
theorem Path.length_step {p : Program} {m n k : Nat} {path : Path p n k}
    (h : m ⟶[p] n) : (path.step _ _ _ h).length = path.length + 1 := by
  simp [length]

@[simp, grind =]
theorem Path.mem_refl_iff {p : Program} {l n : Nat} (hn : n < p.size) :
    l ∈ Path.refl n hn ↔ l = n := by
  constructor
  · intro h
    have .head _ _ := h
    rfl
  · intro rfl
    constructor

@[simp, grind =]
theorem Path.mem_step_iff {p : Program} {l m n k : Nat} {path : Path p n k}
    (hs : m ⟶[p] n) : l ∈ path.step _ _ _ hs ↔ l = m ∨ l ∈ path := by
  constructor
  · intro h
    cases h with
    | head _ _ => exact .inl rfl
    | tail _ _ _ _ _ h => exact .inr h
  · rintro (rfl | h) <;> constructor <;> assumption

theorem Path.lt_size_of_mem {p : Program} {l m n : Nat} {path : Path p m n}
    (h : l ∈ path) : l < p.size := by
  induction h with
  | head n path =>
    cases path with
    | refl _ hl => exact hl
    | step _ m _ hs path => exact hs.1
  | tail m n k hs path h hl => exact hl

theorem Path.lt_size_right {p : Program} {m n : Nat} (path : Path p m n) :
    n < p.size := by
  induction path with
  | refl n hn => exact hn
  | step m k n hs path ih => exact ih

theorem Path.labels_correct {p : Program} {l m n : Nat} {path : Path p m n} :
    l ∈ path.labels ↔ l ∈ path := by
  constructor <;> intro h
  · fun_induction labels
    next n hn =>
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

def Path.push {p : Program} {m n k : Nat} (path : Path p m n) (hk : k < p.size)
    (h : n ⟶[p] k) : Path p m k :=
  match path with
  | refl _ hm => .step _ _ _ h (.refl _ hk)
  | step _ _ _ hs path => .step _ _ _ hs (path.push hk h)

@[simp, grind =]
theorem Path.length_push {p : Program} {m n k : Nat} {path : Path p m n}
    (hk : k < p.size) (h : n ⟶[p] k) :
    (path.push hk h).length = path.length + 1 := by
  induction path with simp [length, push, *]

@[simp, grind =]
theorem Path.mem_push_iff {p : Program} {l m n k : Nat} {path : Path p m n}
    (hk : k < p.size) (h : n ⟶[p] k) :
    l ∈ path.push hk h ↔ l ∈ path ∨ l = k := by
  induction path with grind [push]

theorem Path.split_last {p : Program} {m n : Nat} (path : Path p m n) :
    (∃ (h : m = n) (hm : m < p.size), path = h ▸ .refl _ hm) ∨
      ∃ k hk h, ∃ path' : Path p m k, path = path'.push hk h := by
  induction path with
  | refl m hm => exact .inl ⟨rfl, hm, rfl⟩
  | step m k n hs path ih =>
    obtain ⟨rfl, hm, rfl⟩ | ⟨l, hn, hs', path, rfl⟩ := ih
    · exact .inr ⟨_, hm, hs, .refl _ hs.1, rfl⟩
    · exact .inr ⟨_, hn, hs', .step _ _ _ hs path, rfl⟩

inductive Path.Acyclic {p : Program} : ∀ {m n}, Path p m n → Prop where
  | refl n hn : (Path.refl n hn).Acyclic
  | step m n k hs (path : Path p n k) :
    m ∉ path → path.Acyclic → (path.step m n k hs).Acyclic

theorem Path.size_labels_eq_of_acyclic {p : Program} {m n : Nat}
    {path : Path p m n} (h : path.Acyclic) :
    path.labels.size = path.length + 1 := by
  induction h with
    simp_all! [labels_correct, Finset.size_insert_of_mem,
      Finset.size_insert_of_notMem]

theorem Path.length_lt_size_of_acyclic {p : Program} {m n : Nat}
    {path : Path p m n} (h : path.Acyclic) : path.length < p.size := by
  apply Nat.lt_of_succ_le
  simp only [Nat.succ_eq_add_one, ← size_labels_eq_of_acyclic h]
  apply Finset.size_le_of_all_lt
  intro k
  rw [labels_correct]
  exact lt_size_of_mem

theorem Path.exists_of_mem {p : Program} {l m n : Nat} {path : Path p m n}
    (h : l ∈ path) : ∃ (path' : Path p l n),
      path'.length ≤ path.length ∧ ∀ k ∈ path', k ∈ path := by
  induction h with grind

theorem Path.exists_acyclic.aux {p : Program} {b m n : Nat} {path : Path p m n}
    (hb : path.length ≤ b) : ∃ (path' : Path p m n),
      path'.Acyclic ∧ ∀ l ∈ path', l ∈ path := by
  induction b generalizing m n path with
  | zero =>
    cases path with
    | refl _ hm => exact ⟨.refl m hm, .refl m hm, fun _ h => h⟩
    | step _ k n hs path => simp [length] at hb
  | succ b ih =>
    cases path with
    | refl _ hm => exact ⟨.refl m hm, .refl m hm, fun _ h => h⟩
    | step _ k n hs path =>
      simp only [length, Nat.add_le_add_iff_right] at hb
      by_cases hm : m ∈ path
      · obtain ⟨path', hlen, h⟩ := exists_of_mem hm
        grind
      · obtain ⟨path', ha, h⟩ := ih hb
        replace hm : m ∉ path' := fun hm' => hm (h _ hm')
        refine ⟨.step m k n hs path', .step _ _ _ _ _ hm ha, ?_⟩
        grind

theorem Path.exists_acyclic {p : Program} {m n : Nat} (path : Path p m n) :
    ∃ (path' : Path p m n), path'.Acyclic ∧ ∀ l ∈ path', l ∈ path :=
  exists_acyclic.aux (Nat.le_refl _)

theorem Program.pathWithout_iff {p : Program} {m n k : Nat} (hk : k < p.size) :
    m ⟶[p, n]* k ↔ ∃ path : Path p m k, n ∉ path := by
  constructor
  · intro h
    induction h with
    | refl m hne =>
      exists .refl _ hk
      grind
    | step m l k hne hs h ih =>
      obtain ⟨path, hn⟩ := ih hk
      exists .step _ _ _ hs path
      grind
  · rintro ⟨path, h⟩
    induction path with grind [intro PathWithout]

theorem Expr.free_iff' {p : Program} {e : Expr} {n : Nat} :
    e.Free p n ↔
      e.LocalVar n ∨ ∃ (m k : Nat) (path : Path p m k),
        e.LocalFn m ∧ (p.fn[k]'path.lt_size_right).LocalVar n ∧ n ∉ path ∧
        path.length < p.size := by
  constructor
  · intro hf
    obtain hlv | ⟨m, k, hk, hlf, hpath, hlv⟩ := free_iff.mp hf
    · exact .inl hlv
    · obtain ⟨path, hn⟩ := (Program.pathWithout_iff hk).mp hpath
      obtain ⟨path', ha, h⟩ := path.exists_acyclic
      have hlen := Path.length_lt_size_of_acyclic ha
      exact .inr ⟨m, k, path', hlf, hlv, fun hn' => hn (h _ hn'), hlen⟩
  · rintro (hlv | ⟨m, k, path, hlf, hlv, hn, hlen⟩)
    · exact free_of_localVar hlv
    · have hk := path.lt_size_right
      have hpath := (Program.pathWithout_iff hk).mpr ⟨path, hn⟩
      exact free_iff.mpr <| .inr ⟨m, k, hk, hlf, hpath, hlv⟩

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
      n ∈ v[m] ∨ ∃ (k l : Nat) (path : Path p k l), p.fn[m].LocalFn k ∧
        n ∈ v[l]'path.lt_size_right ∧ n ∉ path ∧ path.length < i by
    have := this lvs p.size
    unfold fnFreeVars
    rw [hlc, this]
    simp only [hlvs, Expr.free_iff']
  intro v i
  induction i generalizing v with
  | zero => grind [fnFreeVars.aux]
  | succ i ih =>
    let update free lf :=
      free ∪ flatMap lf fun m =>
        if hm : m < p.size then v[m].erase m else ∅
    specialize ih (v.zipWith update lfs)
    constructor
    · intro h
      obtain hn | ⟨k, l, path, hlf, hn, hmem, hlen⟩ := ih.mp h <;>
        simp only [Vector.getElem_zipWith, mem_union_iff, mem_flatMap_iff, update] at hn
      · obtain hn | ⟨k, hlf, hn⟩ := hn
        · exact .inl hn
        · rw [hlfs] at hlf
          have hk : k < p.size := by grind
          simp only [hk, ↓reduceDIte, Std.HashSet.mem_erase, beq_eq_false_iff_ne, ne_eq] at hn
          obtain ⟨hne, hn⟩ := hn
          exact .inr <| ⟨_, _, .refl _ hk, hlf, hn, by grind⟩
      · obtain hn | ⟨o, hlf', hn⟩ := hn
        · exact .inr ⟨_, _, path, hlf, hn, hmem, by lia⟩
        · rw [hlfs] at hlf'
          have hl := path.lt_size_right
          have ho : o < p.size := by grind
          simp only [ho, ↓reduceDIte, Std.HashSet.mem_erase, beq_eq_false_iff_ne, ne_eq] at hn
          obtain ⟨hne, hn⟩ := hn
          exact .inr <| ⟨_, _, path.push ho ⟨hl, hlf'⟩, hlf, hn, by grind⟩
    · rintro (hn | ⟨k, l, path, hlf, hn, hmem, hlen⟩)
      · simp [fnFreeVars.aux, update, *]
      · have hl := path.lt_size_right
        obtain h | ⟨o, ho, hs, path, rfl⟩ := path.split_last
        · grind [fnFreeVars.aux]
        · simp only [Path.length_push, Nat.add_lt_add_iff_right] at hlen
          have ho := path.lt_size_right
          have hn' : n ∈ (v.zipWith update lfs)[o] := by grind [Succ]
          exact ih.mpr <| .inr ⟨_, _, path, hlf, hn', by grind, hlen⟩

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

end
