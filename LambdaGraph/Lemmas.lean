import LambdaGraph.Basic

@[simp]
theorem Env.apply_update_self {L : Type} [DecidableEq L] (σ : Env L) (l : L)
  (e : Expr L) : ([l ↦ e] σ) l = e := by
  simp [Env.update]

@[simp]
theorem Env.apply_update_ne {L : Type} [DecidableEq L] (σ : Env L) {l l' : L}
  (e : Expr L) (h : l ≠ l') : ([l ↦ e] σ) l' = σ l' := by
  simp [h, Env.update]

@[simp]
theorem Env.vars_update_value {L : Type} [DecidableEq L] (σ : Env L) (l : L)
  {v : Expr L} (h : v.Value) : ([l ↦ v] σ).vars = insert l σ.vars := by
  ext l'
  constructor <;> intro hl'
  · simp only [vars, Env.update, Set.mem_setOf] at hl'
    split at hl'
    · left; symm; assumption
    · right; assumption
  · by_cases hl : l' = l
    · subst l'; cases h <;> simp [Env.update, Env.vars]
    · simp [*] at hl'
      simp [Env.update, Env.vars, Ne.symm hl]
      exact hl'

theorem value_types_cn {L : Type} {p : Program L} {Γv Γf : Set L} {v : Expr L}
  {t : Ty} (ht : p / Γv, Γf ⊢ v : t.cn) (hv : v.Value) :
    ∃ l σ, v = .clos l σ := by
  rcases hv with ⟨l, σ⟩ | b
  · exists l, σ
  · cases ht

theorem value_types_bool {L : Type} {p : Program L} {Γv Γf : Set L} {v : Expr L}
  (ht : p / Γv, Γf ⊢ v : .bool) (hv : v.Value) : ∃ b, v = .bool b := by
  rcases hv with ⟨l, σ⟩ | b
  · cases ht
  · exists b

theorem types_in_superset {L : Type} {p : Program L} {Γv Γv' Γf Γf' : Set L}
  {e : Expr L} {t : Ty} (h : p / Γv, Γf ⊢ e : t) (hv : Γv ⊆ Γv') (hf : Γf ⊆ Γf')
  : p / Γv', Γf' ⊢ e : t := by
  induction h generalizing Γv' Γf' with
    try solve | constructor <;> apply_rules
  | fnNew Γv Γf l h ih =>
    apply Types.fnNew
    apply ih <;> simp [*]

theorem types_of_types_in_insert_fn {L : Type} {p : Program L} {l : L}
  {Γv Γf : Set L} {e : Expr L} {t : Ty}
  (hl : p / Γv, insert l Γf ⊢ p.fn l : .bot) (h : p / Γv, insert l Γf ⊢ e : t) :
    p / Γv, Γf ⊢ e : t := by
  generalize hΓf' : insert l Γf = Γf' at h
  have ht : p / Γv, Γf ⊢ .fn l : (p.ty l).cn := by
    apply Types.fnNew
    apply types_in_superset hl <;> simp
  induction h generalizing Γf with subst hΓf' <;>
    try solve | constructor <;> apply_rules
  | fnRec Γv _ l' hl' =>
    rcases hl' with hl' | hl'
    · subst l'
      apply types_in_superset ht <;> rfl
    · constructor
      assumption
  | fnNew Γv _ l' h ih =>
    apply Types.fnNew
    apply ih
    · apply types_in_superset hl <;> simp
    · simp [Set.insert_insert]
    · apply types_in_superset ht <;> simp

theorem types_subst {L : Type} {p : Program L} {e : Expr L} {t : Ty} {σ : Env L}
  (h : p / σ.vars, ∅ ⊢ e : t)
  (hσ : ∀ l ∈ σ.vars, p / ∅, ∅ ⊢ σ l : p.ty l) : p / ∅, ∅ ⊢ e.subst σ : t := by
  generalize hΓv : σ.vars = Γv at h
  generalize hΓf : (∅ : Set L) = Γf at h
  induction h with subst hΓv hΓf <;>
    try solve | (try constructor) <;> apply_rules
  | fnNew _ _ l h ih =>
    constructor
    · apply types_in_superset h <;> simp
    · exact hσ

theorem progress {L : Type} [DecidableEq L] {p : Program L} {e : Expr L}
  {t : Ty} (h : p / ∅, ∅ ⊢ e : t) : e.Value ∨ ∃ e', p / e ⇒ e' := by
  generalize hΓv : (∅ : Set L) = Γv
  generalize hΓf : (∅ : Set L) = Γf
  conv at h => arg 2; rw [hΓv]
  conv at h => arg 3; rw [hΓf]
  induction h with subst hΓv hΓf
  | var _ _ l hl => simp at hl
  | fnRec _ _ l hl => simp at hl
  | fnNew _ _ l h ih => right; repeat constructor
  | app _ _ f e t hf he ihf ihe =>
    right
    rcases ihf rfl rfl with hvf | ⟨f', hsf⟩
    · rcases ihe rfl rfl with hve | ⟨e', hse⟩
      · obtain ⟨l, σ, rfl⟩ := value_types_cn hf hvf
        exact ⟨_, Step.app _ _ _ hve⟩
      · exact ⟨_, Step.appR _ _ _ hvf hse⟩
    · exact ⟨_, Step.appL _ _ _ hsf⟩
  | clos _ _ l σ h ih => left; constructor
  | bool _ _ b => left; constructor
  | cond _ _ c et ef t hc het hef ihc ihet ihef =>
    right
    rcases ihc rfl rfl with hvc | ⟨c', hsc⟩
    · obtain ⟨b, rfl⟩ := value_types_bool hc hvc
      cases b <;> repeat constructor
    · exact ⟨_, Step.condC _ _ _ _ hsc⟩

theorem preservation {L : Type} [DecidableEq L] {p : Program L} {e e' : Expr L}
  {t : Ty} (h : p / ∅, ∅ ⊢ e : t) (hs : p / e ⇒ e') : p / ∅, ∅ ⊢ e' : t := by
  induction hs generalizing t with
    try solve | cases h <;> apply_rules [Types.app, Types.cond]
  | fn l =>
    cases h with
    | fnRec _ _ _ hl => nomatch hl
    | fnNew _ _ _ h =>
      constructor
      · apply types_in_superset h <;> simp
      · nofun
  | app l σ e hve =>
    cases h with
    | app _ _ _ _ t h he =>
      cases h with
      | clos _ _ Γ _ h hσ =>
        apply types_subst
        · simp only [hve, Env.vars_update_value]
          rw [← Set.insert_empty] at h
          exact types_of_types_in_insert_fn h h
        · simp only [hve, Env.vars_update_value, Set.mem_insert]
          intro l' hl'
          by_cases hl : l = l'
          · subst l'
            simp [*]
          · cases hl' <;> simp_all
