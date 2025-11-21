import LambdaGraph.Nest

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
noncomputable def Program.labelMap (p : Program) (n : Nat) : LabelMap p :=
  aux 0 (Vector.ofFn Fin.val) #[]
where
  aux i map inv :=
    if h : i < p.size then
      if n ≻[p] i then
        aux (i + 1) (map.set i (p.size + inv.size)) (inv.push ⟨i, h⟩)
      else
        aux (i + 1) map inv
    else
      ⟨map, inv⟩

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
noncomputable def Program.subst (p : Program) (map : LabelMap p) (n : Nat)
    (v : Expr) : Program :=
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
noncomputable def Computation.subst (p : Computation) (n : Nat) (v : Expr) :
    Computation :=
  let map := p.labelMap n
  ⟨p.toProgram.subst map n v, p.expr.subst map n v⟩

theorem program_subst_size_le {p : Program} {v : Expr} {n : Nat}
    {map : LabelMap p} : p.size ≤ (p.subst map n v).size := by
  simp [Program.subst]

theorem lt_subst_size {p : Program} (v : Expr) {n : Nat} (map : LabelMap p)
    (hn : n < p.size) : n < (p.subst map n v).size :=
  Nat.lt_of_lt_of_le hn program_subst_size_le

theorem subst_fn_eq {p : Program} (v : Expr) {m n : Nat} (map : LabelMap p)
    (hn : m < p.size) :
    (p.subst map n v).fn[m]'(lt_subst_size v map hn) = p.fn[m] := by
  simp [hn, Program.subst]

theorem subst_ty_eq {p : Program} (v : Expr) {m n : Nat} (map : LabelMap p)
    (hn : m < p.size) :
    (p.subst map n v).ty[m]'(lt_subst_size v map hn) = p.ty[m] := by
  simp [hn, Program.subst]

theorem expr_types_in_subst {p : Program} {e : Expr} (v : Expr) {t : Ty}
    (n : Nat) (map : LabelMap p) (ht : p ⊢ e : t) :
    p.subst map n v ⊢ e : t := by
  induction ht with try constructor <;> assumption
  | var m hm =>
    rw [← subst_ty_eq v map hm]
    constructor
  | fn m hm =>
    rw [← subst_ty_eq v map hm]
    constructor

structure LabelMap.ValidNew {p : Program} (map : LabelMap p) {i : Nat}
    (h : i < p.size) : Prop where
  fwd_ge : p.size ≤ map.fwd[i]
  fwd_lt : map.fwd[i] < p.size + map.inv.size
  inv_fwd_sub : map.inv[map.fwd[i] - p.size] = i

structure LabelMap.Valid {p : Program} (map : LabelMap p) (n : Nat) : Prop where
  lt : n < p.size
  not_nests : ∀ {i} (h : i < p.size), n ⊁[p] i → map.fwd[i] = i
  nests : ∀ {i} (h : i < p.size), n ≻[p] i → map.ValidNew h

theorem LabelMap.Valid.eq_or_new {p : Program} {map : LabelMap p} {n : Nat}
    (hmap : map.Valid n) {i : Nat} (hi : i < p.size) :
    map.fwd[i] = i ∨ map.ValidNew hi := by
  by_cases h : n ≻[p] i
  · right
    exact hmap.nests hi h
  · left
    exact hmap.not_nests hi h

theorem LabelMap.Valid.fwd_lt {p : Program} {map : LabelMap p} {n : Nat}
    (hmap : map.Valid n) {i : Nat} (hi : i < p.size) :
    map.fwd[i] < p.size + map.inv.size := by
  rcases hmap.eq_or_new hi with h | h
  · rw [h]
    omega
  · exact h.fwd_lt

theorem labelMap_valid (p : Program) {n : Nat} (hn : n < p.size) :
    (p.labelMap n).Valid n where
  lt := hn
  not_nests := by
    intro i hi h
    unfold Program.labelMap
    simp [aux_le_not_nests hi (Nat.zero_le i) h]
  nests := by
    intro i hi h
    unfold Program.labelMap
    exact aux_le_nests hi (Nat.zero_le i) h
where
  aux_gt_map {i j fwd inv} (hi : i < p.size) (hj : i < j) :
      (Program.labelMap.aux p n j fwd inv).fwd[i] = fwd[i] := by
    have (eq := hd) d := p.size - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
    | zero => simp [show ¬j < p.size by omega]
    | succ d ih =>
      split
      · split
        · have : fwd[i] = (fwd.set j (p.size + inv.size) ‹j < p.size›)[i] := by
            simp [show j ≠ i by omega]
          rw [this]
          apply ih <;> omega
        · apply ih <;> omega
      · simp
  aux_inv_size_ge {j fwd inv} :
      inv.size ≤ (Program.labelMap.aux p n j fwd inv).inv.size := by
    have (eq := hd) d := p.size - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
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
  aux_gt_inv {i j k fwd inv} (hk : k < inv.size)
      (hk' : k < (Program.labelMap.aux p n j fwd inv).inv.size) :
      (Program.labelMap.aux p n j fwd inv).inv[k] = inv[k] := by
    have (eq := hd) d := p.size - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
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
  aux_le_not_nests {i j fwd inv} (hi : i < p.size) (hj : j ≤ i) (h : n ⊁[p] i) :
      (Program.labelMap.aux p n j fwd inv).fwd[i] = fwd[i] := by
    have (eq := hd) d := i - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
    | zero =>
      simp only [*, show j = i by omega]
      apply aux_gt_map
      simp
    | succ d ih =>
      have hj' := Nat.lt_of_le_of_lt hj hi
      simp only [hj', ↓reduceDIte]
      split
      · have : fwd[i] = (fwd.set j (p.size + inv.size) hj')[i] := by
          simp [show j ≠ i by omega]
        rw [this]
        apply ih <;> omega
      · apply ih <;> omega
  aux_le_nests {i j fwd inv} (hi : i < p.size) (hj : j ≤ i) (h : n ≻[p] i) :
      (Program.labelMap.aux p n j fwd inv).ValidNew hi := by
    have (eq := hd) d := i - j
    induction d generalizing j fwd inv with unfold Program.labelMap.aux
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

theorem subst_ty_map_eq {p : Program} {v : Expr} {m n : Nat} {map : LabelMap p}
    (hm : m < p.size) (hmap : map.Valid n) :
    (p.subst map n v).ty[map.fwd[m]]'(hmap.fwd_lt hm) = p.ty[m] := by
  rcases hmap.eq_or_new hm with h | ⟨hle, hlt, hinv⟩
  · simp [h, hm, Program.subst]
  · simp [*, Program.subst]

theorem expr_subst_types {p : Program} {e v : Expr} {t : Ty} {n : Nat}
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

theorem subst_types {p : Program} {e v : Expr} {t : Ty} {n : Nat}
    (hn : n < p.size) (ht : ⊢ ⟨p, e⟩ : t) (htv : p ⊢ v : p.ty[n]) :
    ⊢ Computation.subst ⟨p, e⟩ n v : t := by
  obtain ⟨htp, ht⟩ := ht
  dsimp only at *
  constructor
  · intro m hm
    simp [Program.subst, Computation.subst]
    by_cases hm' : m < p.size
    · simp [hm']
      exact expr_types_in_subst _ _ _ (htp _)
    · simp at hm'
      simp [hm']
      exact expr_subst_types (labelMap_valid _ hn) (htp _) htv
  · exact expr_subst_types (labelMap_valid _ hn) ht htv

theorem subst_eq_var {p : Program} {e v : Expr} {m n : Nat}
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

theorem subst_ne_subst_var {p : Program} {e v : Expr} {n : Nat}
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

theorem subst_eq_fn {p : Program} {e v : Expr} {m n : Nat} {map : LabelMap p}
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

theorem subst_eq_app {p : Program} {e e₁ e₂ v : Expr} {n : Nat}
    {map : LabelMap p} (hv : v.Value) (h : e.subst map n v = e₁.app e₂) :
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

theorem subst_eq_cond {p : Program} {e c et ef v : Expr} {n : Nat}
    {map : LabelMap p} (hv : v.Value) (h : e.subst map n v = c.cond et ef) :
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

theorem free_of_free_in_subst {p : Program} {e v : Expr} {m n : Nat}
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

theorem not_free_in_subst {p : Program} {e v : Expr} {n : Nat}
    {map : LabelMap p} (hmap : map.Valid n) (hp : p.ValidRefs)
    (he : e.ValidRefs p) (hv : v.ValidRefs p) (hc : v.Closed p) (hvv : v.Value)
    : ¬(e.subst map n v).Free (p.subst map n v) n := by
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
    · by_cases hd : n ≻[p] i
      · obtain ⟨hle, hlt, hinv⟩ := hmap.nests hi hd
        exact ih (hp hi) (by simp [*, Program.subst])
      · have hi' := hmap.not_nests hi hd
        simp only [Fin.getElem_fin, hi', subst_fn_eq _ _ hi] at hf
        simp only [Fin.getElem_fin, hi', ne_eq] at hne
        replace hf := free_of_free_in_subst hp (hp hi) hf
        exact hd (.free _ _ hne hf)
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

theorem eq_map_of_free_in_subst {p : Program} {e v : Expr} {m n : Nat}
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
    · by_cases hd : n ≻[p] i
      · obtain ⟨hle, hlt, hinv⟩ := hmap.nests hi hd
        obtain ⟨j, rfl, hj⟩ := ih (hp hi) (by simp [*, Program.subst])
        have hij : j ≠ i := by
          intro rfl
          contradiction
        exact ⟨j, rfl, .fn _ hi hij hj⟩
      · obtain hi' := hmap.not_nests hi hd
        simp only [Fin.getElem_fin, hi', subst_fn_eq v map hi] at hf
        replace hf := free_of_free_in_subst hp (hp hi) hf
        simp [hi'] at hne
        have hm : n ⊁[p] m := fun h => hd (.step _ _ hi hne hf h)
        have hlt := lt_size_of_free hp (hp hi) hf
        have hm' := hmap.not_nests hlt hm
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
