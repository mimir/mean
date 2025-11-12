import LambdaGraph.Basic

@[simp]
theorem not_closed_var {p : Env} {n : Nat} : ¬(Expr.var n).Closed p :=
  fun h => h n .var

theorem fn_closed_iff {p : Env} {m : Nat} :
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
theorem app_closed_iff {p : Env} {f e : Expr} :
    (f.app e).Closed p ↔ f.Closed p ∧ e.Closed p := by
  constructor
  · intro h
    constructor <;> solve_by_elim [Expr.Free.appL, Expr.Free.appR]
  · rintro ⟨hf, he⟩ n (- | -) <;> solve_by_elim

@[simp]
theorem bool_closed (p : Env) (b : Bool) : (Expr.bool b).Closed p := nofun

@[simp]
theorem cond_closed_iff {p : Env} {c et ef : Expr} :
    (c.cond et ef).Closed p ↔ c.Closed p ∧ et.Closed p ∧ ef.Closed p := by
  constructor
  · intro h
    and_intros <;> solve_by_elim [Expr.Free.condC, Expr.Free.condT, Expr.Free.condF]
  · rintro ⟨hc, het, hef⟩ n (- | - | -) <;> solve_by_elim

theorem value_types_cn {p : Env} {v : Expr} {t : Ty} (h : p ⊢ v : t.cn) :
    v.Value → ∃ n, v = .fn n
  | .fn n => by simp
  | .bool b => nomatch h

theorem value_types_bool {p : Env} {v : Expr} (h : p ⊢ v : .bool) :
    v.Value → ∃ b, v = .bool b
  | .fn n => nomatch h
  | .bool b => by simp

theorem size_le_of_step {p p' : Program} (h : p ⇒ p') : p.size ≤ p'.size := by
  induction h with simp [*, Env.subst, Program.subst]

theorem lt_size_of_step {p p' : Program} {n : Nat} (hn : n < p.size)
    (h : p ⇒ p') : n < p'.size := Nat.lt_of_lt_of_le hn (size_le_of_step h)

theorem fn_eq_of_step {p p' : Program} {n : Nat} (hn : n < p.size) (h : p ⇒ p')
    : p.fn[n] = p'.fn[n]'(lt_size_of_step hn h) := by
  induction h with simp [*, Env.subst, Program.subst]

theorem ty_eq_of_step {p p' : Program} {n : Nat} (hn : n < p.size) (h : p ⇒ p')
    : p.ty[n] = p'.ty[n]'(lt_size_of_step hn h) := by
  induction h with simp [*, Env.subst, Program.subst]

theorem types_of_step {p p' : Program} {e : Expr} {t : Ty} (ht : p.toEnv ⊢ e : t)
    (hs : p ⇒ p') : p'.toEnv ⊢ e : t := by
  induction ht with
    (try rw [ty_eq_of_step ‹_› hs]) <;> constructor <;> assumption

theorem env_subst_size_le {p : Env} {v : Expr} {n : Nat} {map : LabelMap p} :
    p.size ≤ (p.subst map n v).size := by
  simp [Env.subst]

theorem lt_subst_size {p : Env} (v : Expr) {n : Nat} (map : LabelMap p)
    (hn : n < p.size) : n < (p.subst map n v).size :=
  Nat.lt_of_lt_of_le hn env_subst_size_le

theorem subst_fn_eq {p : Env} (v : Expr) {m n : Nat} (map : LabelMap p)
    (hn : m < p.size) :
    (p.subst map n v).fn[m]'(lt_subst_size v map hn) = p.fn[m] := by
  simp [hn, Env.subst]

theorem subst_ty_eq {p : Env} (v : Expr) {m n : Nat} (map : LabelMap p)
    (hn : m < p.size) :
    (p.subst map n v).ty[m]'(lt_subst_size v map hn) = p.ty[m] := by
  simp [hn, Env.subst]

theorem expr_types_in_subst {p : Env} {e : Expr} (v : Expr) {t : Ty} (n : Nat)
    (map : LabelMap p) (ht : p ⊢ e : t) :
    p.subst map n v ⊢ e : t := by
  induction ht with try constructor <;> assumption
  | var m hm =>
    rw [← subst_ty_eq v map hm]
    constructor
  | fn m hm =>
    rw [← subst_ty_eq v map hm]
    constructor

theorem Depends.lt {p : Env} {m n : Nat} : Depends p m n → m < p.size
  | free _ _ hm _ _ => hm
  | step _ _ _ hm _ _ _ => hm

theorem depends_self {p : Env} {n : Nat} :
    (h : Depends p n n) → ∃ m ≠ n, (p.fn[n]'h.lt).Free p m
  | .free _ _ _ hne _ => nomatch hne
  | .step _ k _ _ hne hf _ => ⟨k, hne, hf⟩

structure LabelMap.ValidNew {p : Env} (map : LabelMap p) {i : Nat}
    (h : i < p.size) : Prop where
  fwd_ge : p.size ≤ map.fwd[i]
  fwd_lt : map.fwd[i] < p.size + map.inv.size
  inv_fwd_sub : map.inv[map.fwd[i] - p.size] = i

structure LabelMap.Valid {p : Env} (map : LabelMap p) (n : Nat) : Prop where
  lt : n < p.size
  not_depends : ∀ {i} (h : i < p.size), ¬Depends p i n → map.fwd[i] = i
  depends : ∀ {i} (h : i < p.size), Depends p i n → map.ValidNew h

theorem LabelMap.Valid.eq_or_new {p : Env} {map : LabelMap p} {n : Nat}
    (hmap : map.Valid n) {i : Nat} (hi : i < p.size) :
    map.fwd[i] = i ∨ map.ValidNew hi := by
  by_cases h : Depends p i n
  · right
    exact hmap.depends hi h
  · left
    exact hmap.not_depends hi h

theorem LabelMap.Valid.fwd_lt {p : Env} {map : LabelMap p} {n : Nat}
    (hmap : map.Valid n) {i : Nat} (hi : i < p.size) :
    map.fwd[i] < p.size + map.inv.size := by
  rcases hmap.eq_or_new hi with h | h
  · rw [h]
    omega
  · exact h.fwd_lt

theorem labelMap_valid (p : Env) {n : Nat} (hn : n < p.size) :
    (p.labelMap n).Valid n where
  lt := hn
  not_depends := by
    intro i hi h
    unfold Env.labelMap
    simp [aux_le_not_depends hi (Nat.zero_le i) h]
  depends := by
    intro i hi h
    unfold Env.labelMap
    exact aux_le_depends hi (Nat.zero_le i) h
where
  aux_gt_map {i j map inv} (hi : i < p.size) (hj : i < j) :
      (Env.labelMap.aux p n j map inv).1[i] = map[i] := by
    have (eq := hd) d := p.size - j
    induction d generalizing j map inv with unfold Env.labelMap.aux
    | zero => simp [show ¬j < p.size by omega]
    | succ d ih =>
      split
      · split
        · have : map[i] = (map.set j (p.size + inv.size) ‹j < p.size›)[i] := by
            simp [show j ≠ i by omega]
          rw [this]
          apply ih <;> omega
        · apply ih <;> omega
      · simp
  aux_inv_size_ge {j map inv} :
      inv.size ≤ (Env.labelMap.aux p n j map inv).2.size := by
    have (eq := hd) d := p.size - j
    induction d generalizing j map inv with unfold Env.labelMap.aux
    | zero => simp [show ¬j < p.size by omega]
    | succ d ih =>
      have hj : j < p.size := by omega
      simp only [hj, ↓reduceDIte, ge_iff_le]
      split
      · have hle : inv.size ≤ (inv.push ⟨j, hj⟩).size := by simp
        apply Nat.le_trans hle
        apply ih
        omega
      · apply ih
        omega
  aux_gt_inv {i j k map inv} (hk : k < inv.size)
      (hk' : k < (Env.labelMap.aux p n j map inv).2.size) :
      (Env.labelMap.aux p n j map inv).2[k] = inv[k] := by
    have (eq := hd) d := p.size - j
    induction d generalizing j map inv with unfold Env.labelMap.aux
    | zero => simp [show ¬j < p.size by omega]
    | succ d ih =>
      have hj : j < p.size := by omega
      simp [hj]
      split
      · have : inv[k] = (inv.push ⟨j, hj⟩)[k]'(by rw [Array.size_push]; omega) :=
          Eq.symm (Array.getElem_push_lt hk)
        rw [this]
        apply ih
        omega
      · apply ih
        omega
  aux_le_not_depends {i j map inv} (hi : i < p.size) (hj : j ≤ i)
      (h : ¬Depends p i n) :
      (Env.labelMap.aux p n j map inv).1[i] = map[i] := by
    have (eq := hd) d := i - j
    induction d generalizing j map inv with unfold Env.labelMap.aux
    | zero =>
      simp only [*, show j = i by omega]
      apply aux_gt_map
      simp
    | succ d ih =>
      have hj' := Nat.lt_of_le_of_lt hj hi
      simp only [hj', ↓reduceDIte]
      split
      · have : map[i] = (map.set j (p.size + inv.size) hj')[i] := by
          simp [show j ≠ i by omega]
        rw [this]
        apply ih <;> omega
      · apply ih <;> omega
  aux_le_depends {i j map inv} (hi : i < p.size) (hj : j ≤ i)
      (h : Depends p i n) :
      let (map', inv') := Env.labelMap.aux p n j map inv
      LabelMap.ValidNew ⟨map', inv'⟩ hi := by
    have (eq := hd) d := i - j
    induction d generalizing j map inv with unfold Env.labelMap.aux
    | zero =>
      simp [*, show j = i by omega]
      refine ⟨?_, ?_, ?_⟩
      · simp [aux_gt_map]
      · have hlt : inv.size < (inv.push ⟨i, hi⟩).size := by simp
        simp only [Nat.lt_add_one, aux_gt_map, Vector.getElem_set_self,
          Nat.add_lt_add_iff_left]
        apply Nat.lt_of_lt_of_le hlt
        simp only [aux_inv_size_ge]
      · simp only [Nat.lt_add_one, aux_gt_map, Vector.getElem_set_self,
          Nat.add_sub_cancel_left]
        have : i = (inv.push ⟨i, hi⟩)[inv.size] := by simp
        conv => rhs; rw [this]
        rw [aux_gt_inv]
        exact 0 -- what?
    | succ d ih =>
      have hj' : j < p.size := by omega
      simp [hj']
      split <;> apply ih <;> omega

theorem subst_ty_map_eq {p : Env} {v : Expr} {m n : Nat} {map : LabelMap p}
    (hm : m < p.size) (hmap : map.Valid n) :
    (p.subst map n v).ty[map.fwd[m]]'(hmap.fwd_lt hm) = p.ty[m] := by
  rcases hmap.eq_or_new hm with h | ⟨hle, hlt, hinv⟩
  · simp [h, hm, Env.subst]
  · simp [*, Env.subst]

theorem expr_subst_types {p : Env} {e v : Expr} {t : Ty} {n : Nat}
    {map : LabelMap p} (hmap : map.Valid n) (ht : p ⊢ e : t)
    (htv : p ⊢ v : p.ty[n]'hmap.lt) :
    p.subst map n v ⊢ e.subst map n v : t := by
  induction ht with try constructor <;> assumption
  | var m hm =>
    by_cases hnm : n = m
    · subst m
      simp [Expr.subst]
      exact expr_types_in_subst _ _ _ htv
    · have hm' : m < map.fwd.size := hm
      simp [hnm, hm', Expr.subst]
      rw [← subst_ty_map_eq hm hmap]
      constructor
  | fn m hm =>
    simp only [Expr.subst, hm, getElem?_pos, Option.getD_some]
    rw [← subst_ty_map_eq hm hmap]
    constructor

theorem subst_types {p : Env} {e v : Expr} {t : Ty} {n : Nat} (hn : n < p.size)
    (ht : ⊢ ⟨p, e⟩ : t) (htv : p ⊢ v : p.ty[n]) :
    ⊢ Program.subst ⟨p, e⟩ n v : t := by
  obtain ⟨htp, ht⟩ := ht
  dsimp only at *
  constructor
  · intro m hm
    simp [Env.subst, Program.subst]
    by_cases hm' : m < p.size
    · simp [hm']
      exact expr_types_in_subst _ _ _ (htp _)
    · simp at hm'
      simp [hm']
      exact expr_subst_types (labelMap_valid _ hn) (htp _) htv
  · exact expr_subst_types (labelMap_valid _ hn) ht htv

inductive Expr.ValidRefs (p : Env) : Expr → Prop where
  | var (n : Nat) : n < p.size → (Expr.var n).ValidRefs p
  | fn (n : Nat) : n < p.size → (Expr.fn n).ValidRefs p
  | app (f e : Expr) : f.ValidRefs p → e.ValidRefs p → (f.app e).ValidRefs p
  | bool (b : Bool) : (Expr.bool b).ValidRefs p
  | cond (c et ef : Expr) : c.ValidRefs p → et.ValidRefs p → ef.ValidRefs p →
    (c.cond et ef).ValidRefs p

theorem Expr.Types.validRefs {p : Env} {e : Expr} {t : Ty} (ht : p ⊢ e : t) :
    e.ValidRefs p := by
  induction ht with constructor <;> assumption

def Env.ValidRefs (p : Env) : Prop :=
  ∀ {i} (_ : i < p.size), p.fn[i].ValidRefs p

theorem Env.Types.validRefs {p : Env} (ht : ⊢ p) : p.ValidRefs :=
  fun hi => (ht hi).validRefs

theorem lt_size_of_free {p : Env} {e : Expr} {n : Nat} (hp : p.ValidRefs)
    (he : e.ValidRefs p) (hf : e.Free p n) : n < p.size := by
  induction hf with cases he <;> apply_rules

theorem subst_eq_var {p : Env} {e v : Expr} {m n : Nat}
    {map : LabelMap p} (he : e.ValidRefs p) (hc : v.Closed p)
    (h : e.subst map n v = .var m) :
    ∃ (i : Fin p.size), m = map.fwd[i] ∧ e = .var i := by
  cases e with simp only [Expr.subst] at h <;> try contradiction
  | var k =>
    have .var _ hk := he
    by_cases hnk : n = k
    · simp only [hnk, ↓reduceIte] at h
      subst v
      exfalso
      exact hc m .var
    · exists ⟨k, hk⟩
      simpa [hnk, hk, eq_comm] using h

theorem subst_ne_subst_var {p : Env} {e v : Expr} {n : Nat}
    {map : LabelMap p} (hmap : map.Valid n) (hv : v.Value) :
    e.subst map n v ≠ .var n := by
  cases e with simp only [Expr.subst] <;> try intro; contradiction
  | var m =>
    split
    · intro rfl
      nomatch hv
    · by_cases hm : m < p.size
      · rcases hmap.eq_or_new hm with hm | ⟨hle, hlt, hinv⟩
        · simp [*, Ne.symm]
        · simp [hm]
          intro h
          rw [h] at hle
          have := hmap.lt
          omega
      · simp [*, Ne.symm]

theorem subst_eq_fn {p : Env} {e v : Expr} {m n : Nat} {map : LabelMap p}
    (he : e.ValidRefs p) (h : e.subst map n v = .fn m) :
    e = .var n ∨ ∃ i : Fin p.size, m = map.fwd[i] ∧ e = .fn i := by
  cases e with simp only [Expr.subst] at h <;> try contradiction
  | var k =>
    split at h
    · simp [*]
    · simp at h
  | fn k =>
    right
    have .fn _ hk := he
    exists ⟨k, hk⟩
    simpa [hk, eq_comm] using h

theorem subst_eq_app {p : Env} {e e₁ e₂ v : Expr} {n : Nat} {map : LabelMap p}
    (hv : v.Value) (h : e.subst map n v = e₁.app e₂) :
    ∃ e₁' e₂' : Expr, e = e₁'.app e₂' := by
  cases e with try solve | simp [Expr.subst] at h
  | var m =>
    by_cases hnm : n = m
    · simp only [Expr.subst, hnm, ↓reduceIte] at h
      subst v
      nomatch hv
    · simp [hnm, Expr.subst] at h
  | app e₁' e₂' =>
    simp only [Expr.subst, Expr.app.injEq] at h
    exists e₁', e₂'

theorem subst_eq_cond {p : Env} {e c et ef v : Expr} {n : Nat} {map : LabelMap p}
    (hv : v.Value) (h : e.subst map n v = c.cond et ef) :
    ∃ c' et' ef' : Expr, e = c'.cond et' ef' := by
  cases e with try solve | simp [Expr.subst] at h
  | var m =>
    by_cases hnm : n = m
    · simp only [Expr.subst, hnm, ↓reduceIte] at h
      subst v
      nomatch hv
    · simp [hnm, Expr.subst] at h
  | cond c' et' ef' =>
    simp only [Expr.subst, Expr.cond.injEq] at h
    exists c', et', ef'

theorem free_of_free_in_subst {p : Env} {e v : Expr} {m n : Nat}
    {map : LabelMap p} (hp : p.ValidRefs) (he : e.ValidRefs p)
    (hf : e.Free (p.subst map n v) m) : e.Free p m := by
  generalize hp' : p.subst map n v = p' at hf
  open Expr.Free in
  induction hf with
    try solve | cases he; solve_by_elim [appL, appR, condC, condT, condF]
  | fn k hk' hne hf ih =>
    have .fn _ hk := he
    constructor
    · exact hne
    · subst p'
      rw [subst_fn_eq _ _ hk] at ih
      exact ih (hp hk)

theorem not_free_in_subst {p : Env} {e v : Expr} {n : Nat} {map : LabelMap p}
    (hmap : map.Valid n) (hp : p.ValidRefs) (he : e.ValidRefs p)
    (hv : v.ValidRefs p) (hc : v.Closed p) (hvv : v.Value) :
    ¬(e.subst map n v).Free (p.subst map n v) n := by
  intro hf
  generalize hp' : p.subst map n v = p', he' : e.subst map n v = e' at hf
  induction hf generalizing e with
  | var => exact subst_ne_subst_var hmap hvv he'
  | fn m hm' hne hf ih =>
    subst p'
    rcases subst_eq_fn he he' with rfl | ⟨⟨i, hi⟩, rfl, rfl⟩
    · simp only [Expr.subst, ↓reduceIte] at he'
      subst v
      have .fn _ hm := hv
      rw [subst_fn_eq _ _ hm] at hf
      replace hf := free_of_free_in_subst hp (hp hm) hf
      exact hc n (.fn _ _ hne hf)
    · by_cases hd : Depends p i n
      · obtain ⟨hle, hlt, hinv⟩ := hmap.depends hi hd
        exact ih (hp hi) (by simp [*, Env.subst])
      · have hi' := hmap.not_depends hi hd
        simp only [Fin.getElem_fin, hi', subst_fn_eq _ _ hi] at hf
        simp only [Fin.getElem_fin, hi', ne_eq] at hne
        replace hf := free_of_free_in_subst hp (hp hi) hf
        exact hd (.free _ _ _ hne hf)
  | appL f e'' hf ih =>
    obtain ⟨f', e''', rfl, rfl⟩ := subst_eq_app hvv he'
    simp only [Expr.subst] at he'
    obtain ⟨rfl, rfl⟩ := he'
    replace .app _ _ hf he := he
    exact ih hf rfl
  | appR f e'' hf ih =>
    obtain ⟨f', e''', rfl, rfl⟩ := subst_eq_app hvv he'
    simp only [Expr.subst] at he'
    obtain ⟨rfl, rfl⟩ := he'
    replace .app _ _ hf he := he
    exact ih he rfl
  | condC c et ef hf ih =>
    obtain ⟨c', et', ef', rfl, rfl, rfl⟩ := subst_eq_cond hvv he'
    simp only [Expr.subst] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    have .cond _ _ _ hc het hef := he
    exact ih hc rfl
  | condT c et ef hf ih =>
    obtain ⟨c', et', ef', rfl, rfl, rfl⟩ := subst_eq_cond hvv he'
    simp only [Expr.subst] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    have .cond _ _ _ hc het hef := he
    exact ih het rfl
  | condF c et ef hf ih =>
    obtain ⟨c', et', ef', rfl, rfl, rfl⟩ := subst_eq_cond hvv he'
    simp only [Expr.subst] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    have .cond _ _ _ hc het hef := he
    exact ih hef rfl

theorem eq_map_of_free_in_subst {p : Env} {e v : Expr} {m n : Nat}
    {map : LabelMap p} (hmap : map.Valid n) (hp : p.ValidRefs)
    (he : e.ValidRefs p) (hv : v.ValidRefs p) (hc : v.Closed p)
    (hvv : v.Value) (hf : (e.subst map n v).Free (p.subst map n v) m) :
    ∃ (i : Fin p.size), m = map.fwd[i] ∧ e.Free p i := by
  generalize hp' : p.subst map n v = p', he' : e.subst map n v = e' at hf
  induction hf generalizing e with
  | var =>
    obtain ⟨⟨i, hi⟩, rfl, rfl⟩ := subst_eq_var he hc he'
    exists ⟨i, hi⟩
    simp [Expr.Free.var]
  | fn k hk' hne hf ih =>
    subst p'
    rcases subst_eq_fn he he' with rfl | ⟨⟨i, hi⟩, rfl, rfl⟩
    · simp only [Expr.subst, ↓reduceIte] at he'
      subst v
      have .fn _ hk := hv
      rw [subst_fn_eq _ _ hk] at hf
      replace hf := free_of_free_in_subst hp (hp hk) hf
      exfalso
      exact hc m (.fn _ _ hne hf)
    · by_cases hd : Depends p i n
      · obtain ⟨hle, hlt, hinv⟩ := hmap.depends hi hd
        obtain ⟨j, rfl, hj⟩ := ih (hp hi) (by simp [*, Env.subst])
        have hij : j ≠ i := by
          intro rfl
          contradiction
        exact ⟨j, rfl, .fn _ hi hij hj⟩
      · obtain hi' := hmap.not_depends hi hd
        simp only [Fin.getElem_fin, hi', subst_fn_eq v map hi] at hf
        replace hf := free_of_free_in_subst hp (hp hi) hf
        simp [hi'] at hne
        have hm : ¬Depends p m n := fun h => hd (.step _ _ _ hi hne hf h)
        have hlt := lt_size_of_free hp (hp hi) hf
        have hm' := hmap.not_depends hlt hm
        refine ⟨⟨m, hlt⟩, by simp [hm'], .fn _ hi hne hf⟩
  | appL f e'' hf ih =>
    obtain ⟨f', e''', rfl, rfl⟩ := subst_eq_app hvv he'
    simp only [Expr.subst] at he'
    obtain ⟨rfl, rfl⟩ := he'
    replace .app _ _ hf he := he
    obtain ⟨i, rfl, hf'⟩ := ih hf rfl
    exact ⟨i, rfl, .appL _ _ hf'⟩
  | appR f e'' hf ih =>
    obtain ⟨f', e''', rfl, rfl⟩ := subst_eq_app hvv he'
    simp only [Expr.subst] at he'
    obtain ⟨rfl, rfl⟩ := he'
    replace .app _ _ hf he := he
    obtain ⟨i, rfl, hf'⟩ := ih he rfl
    exact ⟨i, rfl, .appR _ _ hf'⟩
  | condC c et ef hf ih =>
    obtain ⟨c', et', ef', rfl, rfl, rfl⟩ := subst_eq_cond hvv he'
    simp only [Expr.subst] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    have .cond _ _ _ hc het hef := he
    obtain ⟨i, rfl, hf'⟩ := ih hc rfl
    exact ⟨i, rfl, .condC _ _ _ hf'⟩
  | condT c et ef hf ih =>
    obtain ⟨c', et', ef', rfl, rfl, rfl⟩ := subst_eq_cond hvv he'
    simp only [Expr.subst] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    have .cond _ _ _ hc het hef := he
    obtain ⟨i, rfl, hf'⟩ := ih het rfl
    exact ⟨i, rfl, .condT _ _ _ hf'⟩
  | condF c et ef hf ih =>
    obtain ⟨c', et', ef', rfl, rfl, rfl⟩ := subst_eq_cond hvv he'
    simp only [Expr.subst] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he'
    have .cond _ _ _ hc het hef := he
    obtain ⟨i, rfl, hf'⟩ := ih hef rfl
    exact ⟨i, rfl, .condF _ _ _ hf'⟩

theorem closed_of_step {p p' : Program} {e : Expr} (hp : p.ValidRefs)
    (he : e.ValidRefs p.toEnv) (hc : e.Closed p.toEnv) (hs : p ⇒ p') :
    e.Closed p'.toEnv := by
  intro m hf
  apply hc m
  induction hs with
    dsimp only at * <;> apply_rules
  | app =>
    dsimp only [Program.subst] at *
    exact free_of_free_in_subst hp he hf

theorem progress {p : Program} {t : Ty} (ht : ⊢ p : t) (hc : p.Closed) :
    p.expr.Value ∨ ∃ p', p ⇒ p' := by
  obtain ⟨p, e⟩ := p
  obtain ⟨htp, hte⟩ := ht
  simp only at *
  induction hte with
  | var n hn => exfalso; exact hc n .var
  | fn n hn => left; constructor
  | app f e t htf hte ihf ihe =>
    right
    obtain ⟨hcf, hce⟩ := app_closed_iff.mp hc
    rcases ihf hcf with hvf | ⟨p', hp⟩
    · rcases ihe hce with hve | ⟨p', hp⟩
      · obtain ⟨n, rfl⟩ := value_types_cn htf hvf
        cases htf
        solve_by_elim [Exists.intro]
      · exact ⟨_, Step.appR _ _ _ _ _ hvf hp⟩
    · exact ⟨_, Step.appL _ _ _ _ _ hp⟩
  | bool b => left; constructor
  | cond c et ef t htc htet htef ihc ihet ihef =>
    right
    obtain ⟨hcc, hcet, hcef⟩ := cond_closed_iff.mp hc
    rcases ihc hcc with hvc | ⟨p', hp⟩
    · rcases value_types_bool htc hvc with ⟨_ | _, rfl⟩ <;> repeat constructor
    · exact ⟨_, Step.condC _ _ _ _ _ _ hp⟩

theorem preservation_types {p p' : Program} {t : Ty} (ht : ⊢ p : t)
  (hs : p ⇒ p') : ⊢ p' : t := by
  obtain ⟨htp, ht⟩ := ht
  induction hs generalizing t with
  | app p n e h hv =>
    have .app _ _ t htf hte := ht
    cases htf
    solve_by_elim [subst_types]
  | appL p p' f f' e hs ih =>
    have .app _ _ t htf hte := ht
    obtain ⟨htp', htf'⟩ := ih htp htf
    constructor
    · exact htp'
    · dsimp only at *
      constructor
      · exact htf'
      · exact types_of_step hte hs
  | appR p p' f e e' hvf hs ih =>
    have .app _ _ t htf hte := ht
    obtain ⟨htp', hte'⟩ := ih htp hte
    constructor
    · exact htp'
    · dsimp only at *
      constructor
      · exact types_of_step htf hs
      · exact hte'
  | condT p et ef => cases ht; constructor <;> assumption
  | condF p et ef => cases ht; constructor <;> assumption
  | condC p p' c c' et ef hs ih =>
    have .cond _ _ _ _ htc htet htef := ht
    obtain ⟨htp', htc'⟩ := ih htp htc
    constructor
    · exact htp'
    · dsimp only at *
      constructor
      · exact htc'
      · exact types_of_step htet hs
      · exact types_of_step htef hs

theorem preservation_closed {p p' : Program} {t : Ty} (ht : ⊢ p : t)
    (hc : p.Closed) (hs : p ⇒ p') : p'.Closed := by
  obtain ⟨htp, ht⟩ := ht
  induction hs generalizing t with
  | app p n e hn hve =>
    intro m hm
    obtain ⟨hcf, hce⟩ := app_closed_iff.mp hc
    have .app _ _ t' htf hte := ht
    have hmap : (p.labelMap n).Valid n := labelMap_valid _ hn
    have hp : p.ValidRefs := htp.validRefs
    have hfn := hp hn
    have he := hte.validRefs
    have hne : n ≠ m := by
      intro rfl
      simp [Program.subst, Program.Free] at hm
      exact not_free_in_subst hmap hp hfn he hce hve hm
    obtain ⟨⟨i, hi⟩, rfl, hf⟩ :=
      eq_map_of_free_in_subst hmap hp hfn he hce hve hm
    simp only [Fin.getElem_fin] at hne
    simp only at hf
    have hd : ¬Depends p n n := by
      intro hd
      obtain ⟨m, hm, hf⟩ := depends_self hd
      exact hcf m (.fn _ _ hm hf)
    have hne : i ≠ n := by
      intro rfl
      simp [hmap.not_depends hi hd] at hne
    exact hcf i (.fn _ hn hne hf)
  | appL p p' f f' e hs ih =>
    obtain ⟨hcf, hce⟩ := app_closed_iff.mp hc
    apply app_closed_iff.mpr
    have .app _ _ t' htf hte := ht
    dsimp only at *
    constructor
    · exact ih hcf htp htf
    · exact closed_of_step htp.validRefs hte.validRefs hce hs
  | appR p p' f e e' hvf hs ih =>
    obtain ⟨hcf, hce⟩ := app_closed_iff.mp hc
    apply app_closed_iff.mpr
    have .app _ _ t' htf hte := ht
    dsimp only at *
    constructor
    · exact closed_of_step htp.validRefs htf.validRefs hcf hs
    · exact ih hce htp hte
  | condT p et ef =>
    obtain ⟨-, hcet, -⟩ := cond_closed_iff.mp hc
    exact hcet
  | condF p et ef =>
    obtain ⟨-, -, hcef⟩ := cond_closed_iff.mp hc
    exact hcef
  | condC p p' c c' et ef hs ih =>
    obtain ⟨hcc, hcet, hcef⟩ := cond_closed_iff.mp hc
    apply cond_closed_iff.mpr
    have .cond _ _ _ _ htc htet htef := ht
    and_intros
    · exact ih hcc htp htc
    · apply closed_of_step htp.validRefs htet.validRefs hcet
      exact (.condC _ _ _ _ _ _ hs)
    · apply closed_of_step htp.validRefs htef.validRefs hcef
      exact (.condC _ _ _ _ _ _ hs)
