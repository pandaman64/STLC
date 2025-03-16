-- See `study_plan.md` for the plan.

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max

set_option autoImplicit false

inductive Ty where
  | base
  | arrow (dom cod : Ty)
deriving Repr, DecidableEq

-- structure FVar where
--   id : Nat
-- deriving Repr, DecidableEq

def FVar := Nat

instance : Repr FVar := inferInstanceAs (Repr Nat)

instance : ToString FVar := inferInstanceAs (ToString Nat)

instance : DecidableEq FVar := inferInstanceAs (DecidableEq Nat)

instance : LinearOrder FVar := inferInstanceAs (LinearOrder Nat)

def Finset.choose_fresh (s : Finset FVar) : FVar :=
  if h : s.Nonempty then
    (s.max' h).succ
  else
    Nat.zero

theorem Finset.choose_fresh_spec (s : Finset FVar) : s.choose_fresh ∉ s := by
  unfold Finset.choose_fresh
  split
  next h =>
    intro h'
    have := Finset.le_max' s _ h'
    exact Nat.not_succ_le_self _ this
  next h =>
    simp at h
    simp [h]

def Finset.choose_fresh' (s : Finset FVar) : { x : FVar // x ∉ s } :=
  ⟨s.choose_fresh, s.choose_fresh_spec⟩

inductive Term where
  | bvar (k : Nat)
  | fvar (x : FVar)
  | app (t₁ t₂ : Term)
  | lam (t : Term)
deriving Repr, DecidableEq

namespace Term

def fv (t : Term) : Finset FVar :=
  match t with
  | bvar _ => ∅
  | fvar x => {x}
  | app t₁ t₂ => t₁.fv ∪ t₂.fv
  | lam t => t.fv

def openAt (t : Term) (k : Nat) (u : Term) : Term :=
  match t with
  | bvar i => if k = i then u else t
  | fvar _ => t
  | app t₁ t₂ => app (openAt t₁ k u) (openAt t₂ k u)
  | lam t => lam (openAt t (k + 1) u)

def openT (t s : Term) : Term := t.openAt 0 s

@[simp]
theorem openAt_bvar {i k u} : (bvar i).openAt k u = if k = i then u else bvar i := by
  split
  next h => simp [openAt, h]
  next h =>
    simp [openAt]
    aesop

@[simp]
theorem openAt_fvar {x k u} : (fvar x).openAt k u = fvar x := by
  simp [openAt]

@[simp]
theorem openAt_app {t₁ t₂ k u} : (app t₁ t₂).openAt k u = app (t₁.openAt k u) (t₂.openAt k u) := by
  simp [openAt]

@[simp]
theorem openAt_lam {t k u} : (lam t).openAt k u = lam (t.openAt (k + 1) u) := by
  simp [openAt]

@[simp]
theorem openT_bvar {i u} : (bvar i).openT u = if 0 = i then u else bvar i := by
  simp [openT]

@[simp]
theorem openT_fvar {x u} : (fvar x).openT u = fvar x := by
  simp [openT]

@[simp]
theorem openT_app {t₁ t₂ u} : (app t₁ t₂).openT u = app (t₁.openT u) (t₂.openT u) := by
  simp [openT]

@[simp]
theorem openT_lam {t u} : (lam t).openT u = lam (t.openAt 1 u) := by
  simp [openT]

def closeAt (t : Term) (x : FVar) (k : Nat) : Term :=
  match t with
  | bvar _ => t
  | fvar y => if x = y then bvar k else t
  | app t₁ t₂ => app (closeAt t₁ x k) (closeAt t₂ x k)
  | lam t => lam (closeAt t x (k + 1))

def close (t : Term) (x : FVar) : Term := closeAt t x 0

@[simp]
theorem closeAt_bvar {i x k} : (bvar i).closeAt x k = bvar i := by
  simp [closeAt]

@[simp]
theorem closeAt_fvar {y x k} : (fvar y).closeAt x k = if x = y then bvar k else fvar y := by
  simp [closeAt]

@[simp]
theorem closeAt_app {t₁ t₂ x k} : (app t₁ t₂).closeAt x k = app (t₁.closeAt x k) (t₂.closeAt x k) := by
  simp [closeAt]

@[simp]
theorem closeAt_lam {t x k} : (lam t).closeAt x k = lam (t.closeAt x (k + 1)) := by
  simp [closeAt]

@[simp]
theorem close_bvar {i x} : (bvar i).close x = bvar i := by
  simp [close]

@[simp]
theorem close_fvar {x y} : (fvar x).close y = if y = x then bvar 0 else fvar x := by
  simp [close]

@[simp]
theorem close_app {t₁ t₂ x} : (app t₁ t₂).close x = app (t₁.close x) (t₂.close x) := by
  simp [close]

@[simp]
theorem close_lam {t x} : (lam t).close x = lam (t.closeAt x 1) := by
  simp [close]

def subst (t : Term) (x : FVar) (u : Term) : Term :=
  match t with
  | bvar _ => t
  | fvar y => if x = y then u else t
  | app t₁ t₂ => app (subst t₁ x u) (subst t₂ x u)
  | lam t => lam (subst t x u)

@[simp]
theorem subst_bvar {k x u} : (bvar k).subst x u = bvar k := by
  simp [subst]

@[simp]
theorem subst_fvar {y x u} : (fvar y).subst x u = if x = y then u else fvar y := by
  simp [subst]

@[simp]
theorem subst_app {t₁ t₂ x u} : (app t₁ t₂).subst x u = app (t₁.subst x u) (t₂.subst x u) := by
  simp [subst]

@[simp]
theorem subst_lam {t x u} : (lam t).subst x u = lam (t.subst x u) := by
  simp [subst]

inductive LC : Term → Prop where
  | lc_fvar (x : FVar) : LC (.fvar x)
  | lc_app {t₁ t₂ : Term} (h₁ : LC t₁) (h₂ : LC t₂) : LC (.app t₁ t₂)
  | lc_lam {t : Term} (L : Finset FVar) (h : ∀ x ∉ L, LC (t.openT (.fvar x))) : LC (.lam t)

def IsBody (t : Term) : Prop := ∃ L : Finset FVar, ∀ x ∉ L, (t.openT (.fvar x)).LC

@[simp]
theorem LC.fvar {x : FVar} : LC (.fvar x) := by
  exact .lc_fvar x

@[simp]
theorem LC.app_iff {t₁ t₂ : Term} : LC (.app t₁ t₂) ↔ LC t₁ ∧ LC t₂ := by
  apply Iff.intro
  . intro h
    match h with
    | .lc_app h₁ h₂ => exact ⟨h₁, h₂⟩
  . intro ⟨h₁, h₂⟩
    exact .lc_app h₁ h₂

@[simp]
theorem LC.lam_iff {t : Term} : t.lam.LC ↔ t.IsBody := by
  apply Iff.intro
  . intro lc
    match lc with
    | .lc_lam L h => exact ⟨L, h⟩
  . intro ⟨L, h⟩
    exact .lc_lam L h

theorem openAt_eq_of_LCAux {t u v : Term} {i j : Nat} (ne : i ≠ j) (h : (t.openAt i u).openAt j v = t.openAt i u) :
  t.openAt j v = t := by
  induction t generalizing i j with
  | bvar k =>
    simp
    intro eq
    subst k
    simp [ne] at h
    simp [h]
  | fvar x => simp
  | app t₁ t₂ ih₁ ih₂ =>
    simp at h
    simp [ih₁, ih₂]
    exact ⟨ih₁ ne h.1, ih₂ ne h.2⟩
  | lam t ih =>
    simp at h
    simp
    exact ih (by omega) h

theorem openAt_eq_of_LC {t : Term} {k : Nat} {u : Term} (lc : t.LC) :
  t.openAt k u = t := by
  induction lc generalizing k with
  | lc_fvar x => simp
  | lc_app h₁ h₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | @lc_lam t L h ih =>
    let x := L.choose_fresh
    simp
    apply openAt_eq_of_LCAux (by omega) (ih x L.choose_fresh_spec)

theorem openAt_subst {t u w : Term} {x : FVar} {i : Nat} (lc : u.LC) :
  (t.openAt i w).subst x u = (t.subst x u).openAt i (w.subst x u) := by
  induction t generalizing i with
  | bvar k =>
    if h : i = k then
      simp [h]
    else
      simp [h]
  | fvar z =>
    if h : x = z then
      simp [h, openAt_eq_of_LC lc]
    else
      simp [h]
  | app t₁ t₂ ih₁ ih₂ =>
    simp [ih₁, ih₂]
  | lam t ih =>
    simp [ih]

theorem open_subst {t u w : Term} {x : FVar} (lc : u.LC) :
  (t.openT w).subst x u = (t.subst x u).openT (w.subst x u) :=
  openAt_subst lc

theorem openAt_var_subst {t u : Term} {x y : FVar} {i : Nat} (ne : x ≠ y) (lc : u.LC) :
  (t.openAt i (fvar y)).subst x u = (t.subst x u).openAt i (fvar y) := by
  calc (t.openAt i (fvar y)).subst x u
    _ = (t.subst x u).openAt i ((fvar y).subst x u) := openAt_subst lc
    _ = (t.subst x u).openAt i (fvar y) := by simp [ne]

theorem open_var_subst {t u : Term} {x y : FVar} (ne : x ≠ y) (lc : u.LC) :
  (t.openT (fvar y)).subst x u = (t.subst x u).openT (fvar y) :=
  openAt_var_subst ne lc

theorem subst_fresh {t : Term} {x : FVar} {u : Term} (h : x ∉ t.fv) : t.subst x u = t := by
  induction t with
  | bvar k => rfl
  | fvar y =>
    simp [fv] at h
    simp [subst, h]
  | app t₁ t₂ ih₁ ih₂ =>
    simp [fv] at h
    simp [h] at ih₁ ih₂
    simp [subst, ih₁, ih₂]
  | lam t ih =>
    simp [fv] at h
    simp [subst, ih h]

theorem subst_intro' {t : Term} {k : Nat} {x : FVar} {u : Term} (h : x ∉ t.fv) :
  (t.openAt k (.fvar x)).subst x u = t.openAt k u := by
  induction t generalizing k with
  | bvar i =>
    if h' : k = i then
      simp [h']
    else
      simp [h']
  | fvar y =>
    simp [fv] at h
    simp [h]
  | app t₁ t₂ ih₁ ih₂ =>
    simp [fv] at h
    simp [h] at ih₁ ih₂
    simp [ih₁, ih₂]
  | lam t ih =>
    simp [fv] at h
    simp [h] at ih
    simp [ih]

theorem subst_intro {t : Term} {x : FVar} {u : Term} (h : x ∉ t.fv) :
  (t.openT (.fvar x)).subst x u = t.openT u :=
  subst_intro' h

theorem LC_subst {t u : Term} {x : FVar} (lc₁ : t.LC) (lc₂ : u.LC) : (t.subst x u).LC := by
  induction lc₁ with
  | lc_fvar y =>
    simp
    split <;> simp [lc₂]
  | lc_app h₁ h₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | @lc_lam t L h ih =>
    simp
    exists L ∪ {x}
    intro y hy
    simp at hy
    have ne : x ≠ y := fun eq => by simp [eq] at hy
    rw [←open_var_subst ne lc₂]
    apply ih y hy.1

theorem LC_open_body {t u : Term} (h : t.IsBody) (lc : u.LC) : (t.openT u).LC := by
  have ⟨L, hL⟩ := h
  let L' := L ∪ t.fv
  let ⟨x, hx⟩ := L'.choose_fresh'
  simp [L'] at hx
  rw [←subst_intro hx.2]
  apply LC_subst ?_ lc
  exact hL x hx.1

inductive IsValue : Term → Prop where
  | value_lam {t : Term} (h : t.IsBody) : IsValue (.lam t)

inductive Cbv : Term → Term → Prop where
  | cbv_beta {t u : Term} (h : t.IsBody) (val : u.IsValue) : Cbv (.app (.lam t) u) (t.openT u)
  | cbv_app_left {t t' u : Term} (h : Cbv t t') (lc : u.LC) : Cbv (.app t u) (.app t' u)
  | cbv_app_right {t u u' : Term} (val : t.IsValue) (h : Cbv u u') : Cbv (.app t u) (.app t u')

theorem LC_of_value {t : Term} (val : t.IsValue) : t.LC := by
  cases val with
  | value_lam h => simp [h]

theorem LC_of_cbv {t t' : Term} (step : Cbv t t') : t.LC ∧ t'.LC := by
  induction step with
  | cbv_beta h val => simp [h, val, LC_of_value, LC_open_body]
  | cbv_app_left h lc ih => simp [ih, lc]
  | cbv_app_right val h ih => simp [ih, LC_of_value val]

theorem no_cbv_of_value {t t' : Term} (val : t.IsValue) : ¬ Cbv t t' := by
  intro step
  nomatch val, step

theorem cbv_deterministic {t t' t'' : Term} (step₁ : Cbv t t') (step₂ : Cbv t t'') : t' = t'' := by
  induction step₁ generalizing t'' with
  | cbv_beta h₁ val₁ =>
    cases step₂ with
    | cbv_beta h₂ val₂ => rfl
    | cbv_app_left h₂ lc₂ => exact False.elim (no_cbv_of_value (.value_lam h₁) h₂)
    | cbv_app_right val₂ h₂ => exact False.elim (no_cbv_of_value val₁ h₂)
  | cbv_app_left h₁ lc₁ ih₁ =>
    cases step₂ with
    | cbv_beta h₂ val₂ => exact False.elim (no_cbv_of_value (.value_lam h₂) h₁)
    | cbv_app_left h₂ lc₂ => simp [ih₁ h₂]
    | cbv_app_right val₂ h₂ => exact False.elim (no_cbv_of_value val₂ h₁)
  | cbv_app_right val₁ h₁ ih₁ =>
    cases step₂ with
    | cbv_beta h₂ val₂ => exact False.elim (no_cbv_of_value val₂ h₁)
    | cbv_app_left h₂ lc₂ => exact False.elim (no_cbv_of_value val₁ h₂)
    | cbv_app_right val₂ h₂ => simp [ih₁ h₂]

end Term

@[simp]
theorem Finset.singleton_inter_empty_left {α : Type} [DecidableEq α] {a : α} {s : Finset α} : {a} ∩ s = ∅ ↔ a ∉ s := by
  apply Iff.intro
  · intro a_1
    apply Aesop.BuiltinRules.not_intro
    intro a_2
    simp_all only [singleton_inter_of_mem, singleton_ne_empty]
  · intro a_1
    simp_all only [not_false_eq_true, singleton_inter_of_not_mem]

@[simp]
theorem Finset.singleton_inter_empty_right {α : Type} [DecidableEq α] {a : α} {s : Finset α} : s ∩ {a} = ∅ ↔ a ∉ s := by
  apply Iff.intro
  · intro a_1
    apply Aesop.BuiltinRules.not_intro
    intro a_2
    simp_all only [inter_singleton_of_mem, singleton_ne_empty]
  · intro a_1
    simp_all only [not_false_eq_true, inter_singleton_of_not_mem]

abbrev TyCtx := List (FVar × Ty)

namespace TyCtx

def dom (Γ : TyCtx) : Finset FVar := Γ.foldr (init := ∅) (fun (x, _) acc => acc ∪ {x})

@[simp]
theorem dom_nil : dom [] = ∅ := rfl

@[simp]
theorem dom_cons {p : FVar × Ty} {Γ : TyCtx} : dom (p :: Γ) = dom Γ ∪ {p.1} := by
  simp [dom]

theorem mem_dom_iff {x : FVar} {Γ : TyCtx} : x ∈ Γ.dom ↔ ∃ T, (x, T) ∈ Γ := by
  induction Γ with
  | nil => simp [dom]
  | cons p Γ ih =>
    let ⟨y, yT⟩ := p
    simp [ih]
    apply Iff.intro
    . intro h
      match h with
      | .inl ⟨T, mem⟩ => exact ⟨T, .inr mem⟩
      | .inr h => exact ⟨yT, .inl ⟨h, rfl⟩⟩
    . intro ⟨T, h⟩
      match h with
      | .inl ⟨h₁, _⟩ => exact .inr h₁
      | .inr h => exact .inl ⟨T, h⟩

@[simp]
theorem mem_dom_append {x : FVar} {Γ₁ Γ₂ : TyCtx} : x ∈ (Γ₁ ++ Γ₂).dom ↔ x ∈ Γ₁.dom ∨ x ∈ Γ₂.dom := by
  induction Γ₁ with
  | nil => simp
  | cons p Γ₁ ih =>
    simp [ih]
    aesop

def ok : TyCtx → Prop
  | [] => True
  | (x, _) :: (Γ : TyCtx) => x ∉ Γ.dom ∧ ok Γ

@[simp]
theorem ok_nil : ok [] := by simp [ok]

theorem ok_cons {x : FVar} {T : Ty} {Γ : TyCtx} (h₁ : x ∉ Γ.dom) (h₂ : ok Γ) : ok ((x, T) :: Γ) := by
  simp [ok]
  exact ⟨h₁, h₂⟩

@[simp]
theorem ok_cons_iff {p : FVar × Ty} {Γ : TyCtx} : ok (p :: Γ) ↔ p.1 ∉ Γ.dom ∧ ok Γ := by
  simp [ok]

@[simp]
theorem ok_append {Γ₁ Γ₂ : TyCtx} : ok (Γ₁ ++ Γ₂) ↔ ok Γ₁ ∧ ok Γ₂ ∧ Γ₁.dom ∩ Γ₂.dom = ∅ := by
  induction Γ₁ with
  | nil => simp
  | cons p Γ₁ ih =>
    simp [ih, Finset.union_inter_distrib_right]
    aesop

theorem ok_append_symm {Γ₁ Γ₂ : TyCtx} (h : ok (Γ₁ ++ Γ₂)) : ok (Γ₂ ++ Γ₁) := by
  simp_all [Finset.inter_comm]

end TyCtx

namespace Term

inductive HasType : TyCtx → Term → Ty → Prop where
  | type_var {Γ : TyCtx} {x : FVar} {T : Ty} (ok : Γ.ok) (mem : (x, T) ∈ Γ) : HasType Γ (.fvar x) T
  | type_app {Γ : TyCtx} {t₁ t₂ : Term} {T U : Ty}
    (h₁ : HasType Γ t₁ (T.arrow U)) (h₂ : HasType Γ t₂ T) : HasType Γ (.app t₁ t₂) U
  | type_lam {Γ : TyCtx} {t : Term} {T₁ T₂ : Ty} (L : Finset FVar)
    (h : ∀ x ∉ L, HasType (Γ.cons (x, T₁)) (t.openT (.fvar x)) T₂) : HasType Γ (.lam t) (T₁.arrow T₂)

theorem LC_of_hasType {Γ : TyCtx} {t : Term} {T : Ty} (typing : t.HasType Γ T) : t.LC := by
  induction typing with
  | type_var ok mem => simp
  | type_app h₁ h₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | type_lam L h ih =>
    simp
    exact ⟨L, ih⟩

namespace HasType

theorem weaken' {G F E : TyCtx} {t : Term} {T : Ty} (ty : t.HasType (G ++ E) T) (ok : (G ++ F ++ E).ok) : t.HasType (G ++ F ++ E) T := by
  generalize hΓ : G ++ E = Γ at ty
  induction ty generalizing G with
  | @type_var Γ x T ok' mem =>
    subst hΓ
    have : (x, T) ∈ G ++ F ++ E := by
      simp_all only [List.append_assoc, List.mem_append]
      cases mem with
      | inl h => simp [h]
      | inr h => simp [h]
    exact .type_var ok this
  | @type_app Γ t₁ t₂ T₁ T₂ h₁ h₂ ih₁ ih₂ => exact type_app (ih₁ ok hΓ) (ih₂ ok hΓ)
  | @type_lam Γ t T₁ T₂ L h ih =>
    subst hΓ
    apply type_lam (L ∪ G.dom ∪ F.dom ∪ E.dom)
    intro x hx
    simp at hx
    have ok' : TyCtx.ok (((x, T₁) :: G) ++ F ++ E) := by
      refine TyCtx.ok_cons ?_ ok
      simp [hx]
    exact ih x (by simp [hx]) ok' (by simp)

theorem weaken {E F : TyCtx} {t : Term} {T : Ty} (ty : t.HasType E T) (ok : (F ++ E).ok) : t.HasType (F ++ E) T := by
  have ok' : TyCtx.ok ([] ++ F ++ E) := by simp [ok]
  have : t.HasType ([] ++ F ++ E) T := weaken' (by simp [ty]) ok'
  simp at this
  exact this

theorem substitution' {E F : TyCtx} {t u : Term} {x : FVar} {T U : Ty} (ty : t.HasType (F ++ (x, U) :: E) T) (h : u.HasType E U) :
  (t.subst x u).HasType (F ++ E) T := by
  generalize hΓ : F ++ (x, U) :: E = Γ at ty
  induction ty generalizing E F with
  | @type_var Γ y T ok mem =>
    subst hΓ
    simp_all [Finset.inter_union_distrib_left]
    have ok' : (F ++ E).ok := by simp [ok]
    split
    next eq =>
      simp [←eq] at mem
      match mem with
      | .inl mem =>
        have : x ∈ F.dom := TyCtx.mem_dom_iff.mpr ⟨_, mem⟩
        simp [this] at ok
      | .inr (.inl tyeq) =>
        subst tyeq
        exact weaken h ok'
      | .inr (.inr mem) =>
        have : x ∈ E.dom := TyCtx.mem_dom_iff.mpr ⟨_, mem⟩
        simp [this] at ok
    next ne =>
      match mem with
      | .inl mem => exact type_var ok' (by simp [mem])
      | .inr (.inl eq) => simp [eq] at ne
      | .inr (.inr mem) => exact type_var ok' (by simp [mem])
  | type_app h₁ h₂ ih₁ ih₂ =>
    simp
    exact .type_app (ih₁ h hΓ) (ih₂ h hΓ)
  | @type_lam Γ t T₁ T₂ L _ ih =>
    subst hΓ
    apply type_lam (L ∪ F.dom ∪ E.dom ∪ {x})
    intro y hy
    simp at hy
    have ty' : HasType (((y, T₁) :: F) ++ E) ((t.openT (fvar y)).subst x u) T₂ := ih y (by simp [hy]) h (by simp)
    rw [open_var_subst (Ne.symm (by simp [hy])) (LC_of_hasType h)] at ty'
    exact ty'

theorem substitution {E : TyCtx} {t u : Term} {x : FVar} {T U : Ty} (ty : t.HasType ((x, U) :: E) T) (h : u.HasType E U) :
  (t.subst x u).HasType E T :=
  (substitution' ty h : (t.subst x u).HasType ([] ++ E) T)

end HasType

theorem progress {t : Term} {T : Ty} (typing : t.HasType [] T) : t.IsValue ∨ ∃ t', Cbv t t' := by
  generalize h : [] = Γ at typing
  induction typing with
  | type_var ok mem =>
    subst h
    simp at mem
  | @type_app Γ t₁ t₂ T₁ T₂ ty₁ ty₂ ih₁ ih₂ =>
    subst h
    simp at ih₁ ih₂
    match ih₁, ih₂ with
    | .inl val₁, .inl val₂ =>
      match val₁ with
      | @IsValue.value_lam t₁ h => exact .inr ⟨t₁.openT t₂, .cbv_beta h val₂⟩
    | .inl val₁, .inr ⟨t₂', step₂⟩ => exact .inr ⟨.app t₁ t₂', .cbv_app_right val₁ step₂⟩
    | .inr ⟨t₁', step₁⟩, _ => exact .inr ⟨.app t₁' t₂, .cbv_app_left step₁ (LC_of_hasType ty₂)⟩
  | @type_lam Γ t T₁ T₂ L h' ih =>
    subst h
    have : t.IsBody := by
      exists L
      intro x mem
      exact LC_of_hasType (h' x mem)
    exact .inl (.value_lam this)

theorem preservation {Γ : TyCtx} {t t' : Term} {T : Ty} (ty : t.HasType Γ T) (step : Cbv t t') : t'.HasType Γ T := by
  induction step generalizing T with
  | @cbv_beta t u h val =>
    cases ty with
    | @type_app _ _ _ U _ ty₁ ty₂ =>
      cases ty₁ with
      | type_lam L h =>
        let ⟨x, hx⟩ := (L ∪ t.fv).choose_fresh'
        simp at hx
        have ty' : HasType ((x, U) :: Γ) (t.openT (.fvar x)) T := h x hx.1
        have ty'' : HasType Γ ((t.openT (.fvar x)).subst x u) T := ty'.substitution ty₂
        simp [open_subst (LC_of_hasType ty₂), subst_fresh hx.2] at ty''
        exact ty''
  | cbv_app_left step lc ih =>
    cases ty with
    | type_app ty₁ ty₂ => exact .type_app (ih ty₁) ty₂
  | cbv_app_right val step ih =>
    cases ty with
    | type_app ty₁ ty₂ => exact .type_app ty₁ (ih ty₂)

end Term
