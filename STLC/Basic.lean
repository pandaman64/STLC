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

@[simp]
theorem fv_bvar {k : Nat} : (bvar k).fv = ∅ := rfl

@[simp]
theorem fv_fvar {x : FVar} : (fvar x).fv = {x} := rfl

@[simp]
theorem fv_app {t₁ t₂ : Term} : (app t₁ t₂).fv = t₁.fv ∪ t₂.fv := rfl

@[simp]
theorem fv_lam {t : Term} : (lam t).fv = t.fv := rfl

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

inductive Cbvs : Term → Term → Prop where
  | refl {t : Term} : Cbvs t t
  | next {t t' t'' : Term} (step : Cbv t t') (cbvs : Cbvs t' t'') : Cbvs t t''

theorem cbvs_snoc {t t' t'' : Term} (cbvs : Cbvs t t') (step : Cbv t' t'') : Cbvs t t'' := by
  induction cbvs with
  | refl => exact .next step .refl
  | @next t₁ t₂ t₃ step' cbvs ih => exact .next step' (ih step)

theorem cbvs_app_right {t u u' : Term} (val : t.IsValue) (cbvs : Cbvs u u') : Cbvs (.app t u) (.app t u') := by
  induction cbvs with
  | refl => exact .refl
  | next step cbvs ih => exact .next (.cbv_app_right val step) ih

def halts (t : Term) : Prop := ∃ u, Cbvs t u ∧ u.IsValue

theorem halts_of_value {t : Term} (val : t.IsValue) : t.halts := ⟨t, .refl, val⟩

theorem halts_of_step_halts {t t' : Term} (step : Cbv t t') (h : t'.halts) : t.halts := by
  have ⟨u, cbvs, val⟩ := h
  exact ⟨u, .next step cbvs, val⟩

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
    (h : ∀ x ∉ L, HasType ((x, T₁) :: Γ) (t.openT (.fvar x)) T₂) : HasType Γ (.lam t) (T₁.arrow T₂)

theorem LC_of_hasType {Γ : TyCtx} {t : Term} {T : Ty} (typing : t.HasType Γ T) : t.LC := by
  induction typing with
  | type_var ok mem => simp
  | type_app h₁ h₂ ih₁ ih₂ => simp [ih₁, ih₂]
  | type_lam L h ih =>
    simp
    exact ⟨L, ih⟩

namespace HasType

theorem ok {Γ : TyCtx} {t : Term} {T : Ty} (ty : t.HasType Γ T) : Γ.ok := by
  induction ty with
  | type_var ok mem => exact ok
  | type_app h₁ h₂ ih₁ ih₂ => exact ih₁
  | type_lam L h ih =>
    let ⟨x, hx⟩ := L.choose_fresh'
    have ok := ih x hx
    simp at ok
    exact ok.2

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

inductive SN : Term → Prop where
  | intro {t : Term} (h : ∀ t', Cbv t t' → SN t') : SN t

theorem SN_of_value {t : Term} (val : t.IsValue) : SN t :=
  .intro (fun _ step => False.elim (no_cbv_of_value val step))

theorem SN_iff_of_cbv {t t' : Term} (step : Cbv t t') : SN t ↔ SN t' := by
  apply Iff.intro
  . intro sn
    match sn with
    | .intro h => exact h t' step
  . intro sn
    match sn with
    | .intro h =>
      apply SN.intro
      intro t'' step'
      have := cbv_deterministic step step'
      exact this ▸ sn

theorem SN_iff_of_cbvs {t t' : Term} (steps : Cbvs t t') : SN t ↔ SN t' := by
  induction steps with
  | refl => rfl
  | next step steps ih => rw [SN_iff_of_cbv step, ih]

theorem SN_of_halts {t : Term} (halts : t.halts) : SN t := by
  have ⟨u, steps, val⟩ := halts
  exact (SN_iff_of_cbvs steps).mpr (SN_of_value val)

theorem halts_of_hasType_SN {T : Ty} {t : Term} (ty : t.HasType [] T) (sn : SN t) : t.halts := by
  induction sn with
  | @intro t h ih =>
    match progress ty with
    | .inl val => exact halts_of_value val
    | .inr ⟨t', step⟩ =>
      have ty' := preservation ty step
      have halts' := ih t' step ty'
      exact halts_of_step_halts step halts'

def TypedSN (T : Ty) (t : Term) : Prop :=
  match T with
  | .base => t.HasType [] T ∧ SN t
  | .arrow T₁ T₂ => t.HasType [] (.arrow T₁ T₂) ∧ SN t ∧ ∀ u, TypedSN T₁ u → TypedSN T₂ (.app t u)

theorem SN_of_TypedSN {t : Term} {T : Ty} (tsn : TypedSN T t) : SN t := by
  cases T with
  | base => exact tsn.2
  | arrow T₁ T₂ =>
    simp [TypedSN] at tsn
    exact tsn.2.1

theorem HasType_of_TypedSN {T : Ty} {t : Term} (tsn : TypedSN T t) : t.HasType [] T := by
  cases T with
  | base => simp_all [TypedSN]
  | arrow T₁ T₂ => simp_all [TypedSN]

theorem LC_of_TypedSN {T : Ty} {t : Term} (tsn : TypedSN T t) : t.LC :=
  LC_of_hasType (HasType_of_TypedSN tsn)

theorem halts_of_TypedSN {T : Ty} {t : Term} (tsn : TypedSN T t) : t.halts :=
  halts_of_hasType_SN (HasType_of_TypedSN tsn) (SN_of_TypedSN tsn)

theorem TypedSN_of_cbv {t t' : Term} {T : Ty} (step : Cbv t t') (tsn : TypedSN T t) : TypedSN T t' := by
  induction T generalizing t t' with
  | base =>
    simp [TypedSN] at *
    exact ⟨preservation tsn.1 step, (SN_iff_of_cbv step).mp tsn.2⟩
  | arrow T₁ T₂ ih₁ ih₂ =>
    simp [TypedSN] at *
    refine ⟨preservation tsn.1 step, (SN_iff_of_cbv step).mp tsn.2.1, ?_⟩
    intro u tsn'
    have step' : Cbv (.app t u) (.app t' u) := .cbv_app_left step (LC_of_TypedSN tsn')
    exact ih₂ step' (tsn.2.2 u tsn')

theorem TypedSN_of_cbv_rev {t t' : Term} {T : Ty} (ty : t.HasType [] T) (step : Cbv t t') (tsn : TypedSN T t') : TypedSN T t := by
  induction T generalizing t t' with
  | base =>
    simp [TypedSN] at *
    exact ⟨ty, (SN_iff_of_cbv step).mpr tsn.2⟩
  | arrow T₁ T₂ ih₁ ih₂ =>
    simp [TypedSN] at *
    refine ⟨ty, (SN_iff_of_cbv step).mpr tsn.2.1, ?_⟩
    intro u tsn'
    have step' : Cbv (.app t u) (.app t' u) := .cbv_app_left step (LC_of_TypedSN tsn')
    exact ih₂ (.type_app ty (HasType_of_TypedSN tsn')) step' (tsn.2.2 u tsn')

theorem TypedSN_of_cbvs {t t' : Term} {T : Ty} (steps : Cbvs t t') (tsn : TypedSN T t) : TypedSN T t' := by
  induction steps with
  | refl => exact tsn
  | next step _ ih => exact ih (TypedSN_of_cbv step tsn)

theorem TypedSN_of_cbvs_rev {t t' : Term} {T : Ty} (ty : t.HasType [] T) (steps : Cbvs t t') (tsn : TypedSN T t') : TypedSN T t := by
  induction steps with
  | refl => exact tsn
  | @next t₁ t₂ t₃ step _ ih => exact TypedSN_of_cbv_rev ty step (ih (preservation ty step) tsn)

def closed (t : Term) : Prop := t.fv = ∅

@[simp]
theorem closed_app {t u : Term} : closed (.app t u) ↔ closed t ∧ closed u := by
  simp [closed]

@[simp]
theorem closed_lam {t : Term} : closed (.lam t) ↔ closed t := by
  simp [closed]

theorem closed_subst {x : FVar} {u : Term} {t : Term} (h : closed t) : t.subst x u = t := by
  simp [closed] at h
  exact subst_fresh (by simp [h])

theorem fv_openAt_sub {t : Term} {k : Nat} {u : Term} : (t.openAt k u).fv ⊆ t.fv ∪ u.fv := by
  induction t generalizing k with
  | bvar i =>
    simp
    split <;> simp
  | fvar x => simp
  | app t₁ t₂ ih₁ ih₂ =>
    simp [ih₁, ih₂]
    calc (t₁.openAt k u).fv ∪ (t₂.openAt k u).fv
      _ ⊆ (t₁.fv ∪ u.fv) ∪ (t₂.fv ∪ u.fv) := Finset.union_subset_union ih₁ ih₂
      _ = _ := by aesop
  | lam t ih => simp [ih]

theorem fv_openT_sub {t u : Term} : (t.openT u).fv ⊆ t.fv ∪ u.fv := fv_openAt_sub

theorem fv_sub_openAt {t : Term} {k : Nat} {u : Term} : t.fv ⊆ (t.openAt k u).fv := by
  induction t generalizing k with
  | bvar i => simp
  | fvar x => simp
  | app t₁ t₂ ih₁ ih₂ =>
    simp
    exact Finset.union_subset_union ih₁ ih₂
  | lam t ih => simp [ih]

theorem fv_sub_openT {t u : Term} : t.fv ⊆ (t.openT u).fv := fv_sub_openAt

theorem fv_sub_dom_of_hasType {Γ : TyCtx} {t : Term} {T : Ty} (ty : t.HasType Γ T) : t.fv ⊆ Γ.dom := by
  induction ty with
  | type_var ok mem =>
    simp [TyCtx.mem_dom_iff]
    exact ⟨_, mem⟩
  | type_app h₁ h₂ ih₁ ih₂ =>
    simp
    exact Finset.union_subset ih₁ ih₂
  | @type_lam Γ t T₁ T₂ L h ih =>
    simp
    let ⟨x, hx⟩ := (L ∪ t.fv).choose_fresh'
    simp at hx
    have sub := ih x hx.1
    simp at sub
    have sub' : t.fv ⊆ Γ.dom ∪ {x} := Finset.Subset.trans fv_sub_openT sub
    rw [Finset.subset_iff]
    intro y mem
    have mem' := Finset.mem_of_subset sub' mem
    simp at mem'
    cases mem' with
    | inl mem => exact mem
    | inr eq =>
      subst y
      exact False.elim (hx.2 mem)

theorem closed_of_hasType_empty {t : Term} {T : Ty} (ty : t.HasType [] T) : closed t := by
  have : t.fv ⊆ ∅ := fv_sub_dom_of_hasType ty
  simp at this
  simp [this, closed]

theorem closed_of_TypedSN {T : Ty} {t : Term} (tsn : TypedSN T t) : closed t :=
  closed_of_hasType_empty (HasType_of_TypedSN tsn)

def substs (ts : List (FVar × Term)) (t : Term) : Term :=
  ts.foldl (init := t) (fun t (x, u) => t.subst x u)

@[simp]
theorem substs_nil {t : Term} : substs [] t = t := rfl

@[simp]
theorem substs_cons {p : FVar × Term} {ts : List (FVar × Term)} {t : Term} :
  substs (p :: ts) t = substs ts (t.subst p.1 p.2) := rfl

theorem closed_substs {ts : List (FVar × Term)} {t : Term} (h : closed t) : substs ts t = t := by
  induction ts generalizing t with
  | nil => simp [h]
  | cons p ts ih => simp [closed_subst, h, ih h]

theorem substs_app {t u : Term} {ts : List (FVar × Term)} : (substs ts (.app t u)) = (substs ts t).app (substs ts u) := by
  induction ts generalizing t u with
  | nil => simp
  | cons p ts ih => simp [ih]

theorem substs_lam {t : Term} {ts : List (FVar × Term)} : (substs ts (.lam t)) = (.lam (substs ts t)) := by
  induction ts generalizing t with
  | nil => simp
  | cons p ts ih => simp [ih]

def dom_substs (ts : List (FVar × Term)) : Finset FVar := ts.foldr (init := ∅) (fun (x, _) dom => dom ∪ {x})

@[simp]
theorem dom_substs_nil : dom_substs [] = ∅ := rfl

@[simp]
theorem dom_substs_cons {p : FVar × Term} {ts : List (FVar × Term)} : dom_substs (p :: ts) = dom_substs ts ∪ {p.1} := by
  simp [dom_substs]

theorem mem_dom_substs_iff {ts : List (FVar × Term)} {x : FVar} : x ∈ dom_substs ts ↔ ∃ u, (x, u) ∈ ts := by
  induction ts with
  | nil => simp
  | cons p ts ih =>
    simp [ih]
    apply Iff.intro
    . intro mem
      match mem with
      | .inl ⟨u, mem⟩ => exact ⟨u, .inr mem⟩
      | .inr eq => exact ⟨p.2, .inl (by simp [eq])⟩
    . intro ⟨u, mem⟩
      cases mem with
      | inl eq => simp [←eq]
      | inr mem => exact .inl ⟨u, mem⟩

def ok_substs (ts : List (FVar × Term)) : Prop :=
  match ts with
  | [] => True
  | (x, _) :: ts => x ∉ dom_substs ts ∧ ok_substs ts

@[simp]
theorem ok_substs_nil : ok_substs [] := by simp [ok_substs]

@[simp]
theorem ok_substs_cons {p : FVar × Term} {ts : List (FVar × Term)} : ok_substs (p :: ts) ↔ p.1 ∉ dom_substs ts ∧ ok_substs ts := by
  simp [ok_substs]

-- A list of substitutions instantiates a type context when the order of the variables matches and each substituted term is "normalizing".
inductive Instantiates : TyCtx → List (FVar × Term) → Prop where
  | inst_nil : Instantiates [] []
  | inst_cons {x : FVar} {T : Ty} {u : Term} {Γ : TyCtx} {ts : List (FVar × Term)}
    (tsn : TypedSN T u) (rest : Instantiates Γ ts) : Instantiates ((x, T) :: Γ) ((x, u) :: ts)

theorem open_substs {t u : Term} {Γ : TyCtx} {ts : List (FVar × Term)} (inst : Instantiates Γ ts) :
  (t.openT u).substs ts = (t.substs ts).openT (u.substs ts) := by
  induction inst generalizing t u with
  | inst_nil => simp
  | @inst_cons x T t' Γ ts tsn rest ih => simp [open_subst (LC_of_TypedSN tsn), ih]

theorem open_var_substs {t : Term} {y : FVar} {Γ : TyCtx} {ts : List (FVar × Term)} (inst : Instantiates Γ ts) (h : y ∉ dom_substs ts) :
  (t.openT (fvar y)).substs ts = (t.substs ts).openT (fvar y) := by
  induction inst generalizing t with
  | inst_nil => simp
  | @inst_cons x T u Γ ts tsn rest ih =>
    simp
    simp at h
    have : (t.openT (fvar y)).subst x u = (t.subst x u).openT (fvar y) := open_var_subst (Ne.symm h.2) (LC_of_TypedSN tsn)
    rw [this]
    exact ih h.1

theorem dom_substs_eq_dom_of_instantiates {Γ : TyCtx} {ts : List (FVar × Term)} (inst : Instantiates Γ ts) : dom_substs ts = Γ.dom := by
  induction inst with
  | inst_nil => simp
  | inst_cons tsn rest ih =>
    simp
    rw [ih]

theorem ok_substs_of_ok_instantiates {Γ : TyCtx} {ts : List (FVar × Term)} (inst : Instantiates Γ ts) (ok : Γ.ok) : ok_substs ts := by
  induction inst with
  | inst_nil => simp
  | inst_cons tsn rest ih =>
    simp at *
    refine ⟨?_, ih ok.2⟩
    intro mem
    rw [dom_substs_eq_dom_of_instantiates rest] at mem
    exact ok.1 mem

theorem ok_of_ok_substs_instantiates {Γ : TyCtx} {ts : List (FVar × Term)} (inst : Instantiates Γ ts) (ok : ok_substs ts) : Γ.ok := by
  induction inst with
  | inst_nil => simp
  | inst_cons tsn rest ih =>
    simp at *
    refine ⟨?_, ih ok.2⟩
    intro mem
    rw [←dom_substs_eq_dom_of_instantiates rest] at mem
    exact ok.1 mem

theorem HasType_substs {E F : TyCtx} {ts : List (FVar × Term)} {t : Term} {T : Ty} (inst : Instantiates E ts) (ty : t.HasType (E ++ F) T) :
  (substs ts t).HasType F T := by
  induction inst generalizing t with
  | inst_nil => exact ty
  | @inst_cons x U u E ts tsn rest ih =>
    simp
    have eq_ctx : E ++ F ++ [] = E ++ F := by simp
    have ok : (E ++ F).ok := by
      have := ty.ok
      simp at this
      simp [this]
    have : u.HasType [] U := HasType_of_TypedSN tsn
    have : u.HasType (E ++ F) U := by
      rw [←eq_ctx]
      apply HasType.weaken this
      rw [eq_ctx]
      exact ok
    have ty' : HasType (E ++ F) (t.subst x u) T := HasType.substitution ty this
    exact ih ty'

theorem TypedSN_of_mem_instantiates {Γ : TyCtx} {ts : List (FVar × Term)} {x : FVar} {t : Term} {T : Ty}
  (ok : Γ.ok) (inst : Instantiates Γ ts) (mem₁ : (x, t) ∈ ts) (mem₂ : (x, T) ∈ Γ) : TypedSN T t := by
  induction inst generalizing t with
  | inst_nil => simp at mem₁
  | @inst_cons x' T' t' Γ ts tsn rest ih =>
    simp at mem₁ mem₂ ok
    match mem₁, mem₂ with
    | .inl ⟨eq₁, eq₂⟩, .inl ⟨eq₃, eq₄⟩ =>
      subst x' t' T'
      exact tsn
    | .inl ⟨eq₁, eq₂⟩, .inr mem₂' =>
      subst x'
      exact False.elim (ok.1 (TyCtx.mem_dom_iff.mpr ⟨T, mem₂'⟩))
    | .inr mem₁', .inl ⟨eq₃, eq₄⟩ =>
      subst x'
      have nmem : x ∉ dom_substs ts := by
        intro mem
        rw [dom_substs_eq_dom_of_instantiates rest] at mem
        exact ok.1 mem
      have mem := mem_dom_substs_iff.mpr ⟨t, mem₁'⟩
      exact False.elim (nmem mem)
    | .inr mem₁, .inr mem₂ => exact ih ok.2 mem₁ mem₂

theorem closed_of_instantiates {Γ : TyCtx} {ts : List (FVar × Term)} (x : FVar) (u : Term) (inst : Instantiates Γ ts) (mem : (x, u) ∈ ts) : closed u := by
  induction inst with
  | inst_nil => simp at mem
  | inst_cons tsn rest ih =>
    simp at mem
    cases mem with
    | inl eq =>
      simp [eq]
      exact closed_of_TypedSN tsn
    | inr mem => exact ih mem

theorem mem_dom_of_instantiates {Γ : TyCtx} {ts : List (FVar × Term)} {x : FVar} {u : Term} (inst : Instantiates Γ ts) (mem : (x, u) ∈ ts) : x ∈ Γ.dom := by
  induction inst with
  | inst_nil => simp at mem
  | inst_cons tsn rest ih =>
    simp at mem
    cases mem with
    | inl eq => simp [eq]
    | inr mem =>
      simp
      exact .inl (ih mem)

theorem substs_var {Γ : TyCtx} {ts : List (FVar × Term)} {x : FVar} {u : Term} (inst : Instantiates Γ ts) (ok : Γ.ok) (mem : (x, u) ∈ ts) :
  substs ts (.fvar x) = u := by
  induction ts generalizing Γ with
  | nil => simp at mem
  | cons p ts ih =>
    let ⟨x', u'⟩ := p
    have : closed u' := closed_of_instantiates x' u' inst (by simp)
    cases inst with
    | @inst_cons _ T' _ Γ ts tsn rest =>
      simp at mem
      cases mem with
      | inl eq => simp [eq, closed_substs this]
      | inr mem =>
        simp at ok
        simp
        split
        next eq =>
          subst x'
          exact False.elim (ok.1 (mem_dom_of_instantiates rest mem))
        next ne => exact ih rest ok.2 mem

theorem mem_of_mem_instantiates {Γ : TyCtx} {ts : List (FVar × Term)} {x : FVar} (inst : Instantiates Γ ts) (mem : x ∈ Γ.dom) : ∃ u, (x, u) ∈ ts := by
  induction inst with
  | inst_nil => simp at mem
  | @inst_cons x' T' u' Γ ts tsn rest ih =>
    simp at mem
    simp
    cases mem with
    | inl mem =>
      have ⟨u, h⟩ := ih mem
      exact ⟨u, .inr h⟩
    | inr eq => exact ⟨u', .inl ⟨eq, rfl⟩⟩

theorem LC_substs {Γ : TyCtx} {ts : List (FVar × Term)} {t : Term} (inst : Instantiates Γ ts) (lc : t.LC) : (substs ts t).LC := by
  induction inst generalizing t with
  | inst_nil => exact lc
  | @inst_cons x T u Γ ts tsn rest ih =>
    simp
    exact ih (LC_subst lc (LC_of_TypedSN tsn))

theorem substitutions {F E : TyCtx} {ts : List (FVar × Term)} {t : Term} {T : Ty}
  (ok : (F ++ E).ok) (ty : t.HasType (F ++ E) T) (inst : Instantiates F ts) :
  (substs ts t).HasType E T := by
  induction inst generalizing t with
  | inst_nil => exact ty
  | @inst_cons x' T' u' F ts tsn rest ih =>
    simp
    simp at ok
    apply ih (by simp [ok])
    have ty' : HasType (F ++ E ++ []) u' T' := (HasType_of_TypedSN tsn).weaken (F := F ++ E) (by simp [ok])
    simp at ty'
    apply HasType.substitution ty ty'

theorem TypedSN_substs {Γ : TyCtx} {ts : List (FVar × Term)} {t : Term} {T : Ty} (ty : t.HasType Γ T) (inst : Instantiates Γ ts) :
  (substs ts t).TypedSN T := by
  induction ty generalizing ts with
  | @type_var Γ x T ok mem =>
    have := TyCtx.mem_dom_iff.mpr ⟨T, mem⟩
    have ⟨u, h⟩ := mem_of_mem_instantiates inst this
    rw [substs_var inst ok h]
    exact TypedSN_of_mem_instantiates ok inst h mem
  | @type_app Γ t u T U h₁ h₂ ih₁ ih₂ =>
    rw [substs_app]
    have ih₁ := ih₁ inst
    simp [TypedSN] at ih₁
    exact ih₁.2.2 (substs ts u) (ih₂ inst)
  | @type_lam Γ t T₁ T₂ L h ih =>
    simp [TypedSN]
    have ty : HasType [] (substs ts t.lam) (T₁.arrow T₂) := by
      have ty : HasType Γ t.lam (T₁.arrow T₂) := .type_lam L h
      exact HasType_substs inst (by simp [ty])
    have body : (substs ts t).IsBody := by
      refine ⟨L ∪ dom_substs ts, ?_⟩
      intro x mem
      simp at mem
      have : substs ts (t.openT (fvar x)) = (substs ts t).openT (fvar x) := open_var_substs inst mem.2
      rw [←this]
      have lc : (t.openT (fvar x)).LC := LC_of_hasType (h x mem.1)
      exact LC_substs inst lc
    have sn : (substs ts t.lam).SN := by
      simp [substs_lam]
      exact SN_of_value (.value_lam body)

    refine ⟨ty, sn, ?_⟩
    simp [substs_lam]
    intro u tsn
    have ⟨u', steps, val⟩ := halts_of_TypedSN tsn
    have tsn' : TypedSN T₁ u' := TypedSN_of_cbvs steps tsn
    have steps : Cbvs ((substs ts t).lam.app u) ((substs ts t).lam.app u') := cbvs_app_right (.value_lam body) steps
    have beta : Cbv ((substs ts t).lam.app u') ((substs ts t).openT u') := .cbv_beta body val

    let L' := L ∪ dom_substs ts ∪ t.fv
    let ⟨y, hy⟩ := L'.choose_fresh'
    simp [L'] at hy

    have : ((substs ts t).openT u') = (substs ((y, u') :: ts) (t.openT (.fvar y))) :=
      calc ((substs ts t).openT u')
        _ = substs ts (t.openT u') := by
          rw [open_substs inst, closed_substs (closed_of_TypedSN tsn')]
        _ = substs ts ((t.openT (.fvar y)).subst y u') := by
          simp [open_subst (LC_of_value val), subst_fresh hy.2.2]
        _ = substs ((y, u') :: ts) (t.openT (.fvar y)) := by
          simp
    rw [this] at beta

    have inst' : Instantiates ((y, T₁) :: Γ) ((y, u') :: ts) := .inst_cons tsn' inst
    have tsn'' : TypedSN T₂ ((substs ((y, u') :: ts) (t.openT (fvar y)))) := ih y hy.1 inst'
    have steps : Cbvs ((substs ts t).lam.app u) ((substs ((y, u') :: ts) (t.openT (fvar y)))) := cbvs_snoc steps beta
    have ty' : HasType [] ((substs ts t).lam.app u) T₂ := by
      simp [substs_lam] at ty
      exact .type_app (T := T₁) ty (HasType_of_TypedSN tsn)
    exact TypedSN_of_cbvs_rev ty' steps tsn''

end Term
