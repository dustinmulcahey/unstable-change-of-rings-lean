/-
Copyright (c) 2026 Dustin Mulcahey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Mulcahey
-/
module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monad.Algebra
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import ThesisLean.ComonadMorphisms

/-!
# Chapter 2: Derived Functors and Criteria for Change of Ext (§2.4 – §2.5)

Formalization of Chapter 2 (§2.4–§2.5) of Dustin Mulcahey's PhD thesis:
*"An unstable variant of the Morava Change of Rings theorem for K(n) theory"*.

We formalize:
* **§2.4.1 The Induced Monad on the Category of Coalgebras**:
  Given a comonad `G` on `C`, the Eilenberg-Moore adjunction `G.adj : G.forget ⊣ G.cofree`
  induces the monad `T = G.adj.toMonad` on `Comonad.Coalgebra G` (`C^G`) with unit
  `ν_X = ψ_X : X ⟶ (GX, Δ_X)` and multiplication `μ_X = G(ε_X) : G^2 X ⟶ GX`.
* **§2.4.2 Cosimplicial Resolutions (`CobarCosimplicialData`)**:
  For any monad `T` on a category `M` (and specifically `T = G.adj.toMonad` on `C^G`),
  we define the cosimplicial cobar resolution `T^•(X)` (and `G^•(X)`) with objects `T^{n+1}(X)`,
  coface maps `d^i = T^i(ν_{T^{n-i}(X)})`, and codegeneracy maps `s^j = T^j(μ_{T^{n-j}(X)})`,
  and prove all five cosimplicial identities (`δ_comp_δ`, `δ_comp_σ_self`, `δ_comp_σ_succ`,
  `δ_comp_σ_of_le`, `δ_comp_σ_of_gt`, `σ_comp_σ`) and the coaugmentation identity
  `ν_X ≫ d^0 = ν_X ≫ d^1`.
* **§2.4.3 Weak Resolutions and the Contracting Homotopy (`s_{-1}`)**:
  In Proposition 2.4.4 (p. 20), we show that for any `G`-coalgebra `X` and cofree coalgebra `G(I)`,
  applying `Hom_G(-, G(I))` to `X → G^•(X)` admits the left contraction `s_{-1}(f) = G(f) ≫ G(ε_I)`
  satisfying `s_{-1} ≫ d_0 = id`, `s_{-1} ≫ d_{i+1} = d_i ≫ s_{-1}`, and
  `s_{-1} ≫ s_{j+1} = s_j ≫ s_{-1}`.
* **§2.5 Criteria for Change of Ext (Generalized Shapiro's Lemma)**:
  We formalize weak `G`-resolutions, right derived functors `R^s_G F(X)` and `Ext^s_G(M, N)`,
  and prove Proposition 2.5.2 (**Generalized Shapiro's Lemma**): when `(F, α) : (C, G) → (D, H)`
  is a functor of comonads with right adjoint `α^* : D^H ⥤ C^G` carrying `H`-injectives to
  `G`-injectives and preserving the cobar acyclicity (via the retract/split-subobject contraction),
  there is a natural isomorphism
  `Ext^s_H(α_* M, N) ≅ Ext^s_G(M, α^* N)`.
-/

set_option linter.style.longLine false

@[expose] public section

namespace ThesisLean

open CategoryTheory Category Limits Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Section2_4

/-!
## §2.4.1 The Induced Monad on the Category of Coalgebras
-/

variable (G : Comonad C)

/-- In §2.4.1 (p. 16), the Eilenberg-Moore adjunction `G.forget ⊣ G.cofree` between `C^G` and `C`
induces the monad `T = G ∘ U` on the category `Comonad.Coalgebra G` (`C^G`) with unit
`ν_X = ψ_X : X ⟶ (GX, Δ_X)` and multiplication `μ_X = G(ε_X) : G^2 X ⟶ GX`. -/
@[simps!, implicit_reducible]
def inducedMonadOnCoalgebras : Monad (Comonad.Coalgebra G) where
  toFunctor := G.forget ⋙ G.cofree
  η :=
    { app X :=
        { f := X.a
          h := X.coassoc.symm }
      naturality {X Y} g := by
        ext
        exact g.h.symm }
  μ :=
    { app X := G.cofree.map (G.ε.app X.A)
      naturality {X Y} g := by
        ext
        have hε := G.ε.naturality g.f
        dsimp at hε ⊢
        rw [← G.map_comp, ← G.map_comp, hε] }
  assoc X := by
    ext
    have hε := G.ε.naturality (G.ε.app X.A)
    dsimp at hε ⊢
    rw [← G.map_comp, ← G.map_comp, hε]
  left_unit X := by
    ext
    exact G.right_counit X.A
  right_unit X := by
    ext
    dsimp
    rw [← G.map_comp, X.counit, G.map_id]

/-- The underlying object of `T(X)` for a `G`-coalgebra `X` is `G(X.A)` with coaction `Δ_{X.A}`. -/
lemma inducedMonadOnCoalgebras_obj (X : Comonad.Coalgebra G) :
    (inducedMonadOnCoalgebras G).obj X = G.cofree.obj X.A :=
  rfl

/-- As noted on p. 16 of the thesis, the unit `ν_X : X ⟶ T(X)` of the induced monad on `C^G`
has underlying morphism `ψ_X = X.a : X.A ⟶ G.obj X.A`. -/
lemma inducedMonadOnCoalgebras_unit_f (X : Comonad.Coalgebra G) :
    ((inducedMonadOnCoalgebras G).η.app X).f = X.a :=
  rfl

/-- As noted on p. 16 of the thesis, the multiplication `μ_X : T^2(X) ⟶ T(X)` of the induced
monad on `C^G` has underlying morphism `G(ε_X) : G^2(X.A) ⟶ G(X.A)`. -/
lemma inducedMonadOnCoalgebras_mu_f (X : Comonad.Coalgebra G) :
    ((inducedMonadOnCoalgebras G).μ.app X).f = G.map (G.ε.app X.A) :=
  rfl

/-!
## §2.4.2 Cosimplicial Resolutions (`T^•(X)` and `G^•(X)`)

Given any monad `T` on a category `M` (in particular `T = inducedMonadOnCoalgebras G` on `M = C^G`),
and an object `X : M`, we define the iterated powers `T^[n] X` together with the coface maps
`d^i : T^[n + 1] X ⟶ T^[n + 2] X` and codegeneracy maps `s^j : T^[n + 2] X ⟶ T^[n + 1] X`
(Definition 2.4.2, p. 17).
-/

section MonadCobar

variable {M : Type*} [Category* M] (T : Monad M)

/-- The `n`-fold iterate `T^n X` of `T` on `X : M`:
- `iterObj T X 0 = X`
- `iterObj T X (n + 1) = T.obj (iterObj T X n)` -/
@[implicit_reducible]
def iterObj (X : M) : ℕ → M
  | 0 => X
  | n + 1 => T.obj (iterObj X n)

@[simp]
lemma iterObj_zero (X : M) : iterObj T X 0 = X := rfl

@[simp]
lemma iterObj_succ (X : M) (n : ℕ) : iterObj T X (n + 1) = T.obj (iterObj T X n) := rfl

/-- Definition 2.4.2 (p. 17): The `n`-th stage `T^•(X)^n = T^{n+1}(X)` of the cosimplicial cobar
resolution of `X`. -/
abbrev cobarObj (X : M) (n : ℕ) : M :=
  iterObj T X (n + 1)

/-- For any `m : ℕ` and `i : Fin (m + 1)`, the coface map
`iterCoface T X m i : iterObj T X m ⟶ iterObj T X (m + 1)` is `T^i(ν_{T^{m-i}(X)})`:
- `iterCoface T X m 0 = T.η.app (iterObj T X m)`
- `iterCoface T X (m + 1) (i + 1) = T.map (iterCoface T X m i)`. -/
@[implicit_reducible]
def iterCoface (X : M) : ∀ (m : ℕ) (_ : Fin (m + 1)), iterObj T X m ⟶ iterObj T X (m + 1)
  | m, ⟨0, _⟩ => T.η.app (iterObj T X m)
  | 0, ⟨i + 1, hi⟩ => absurd hi (by omega)
  | m + 1, ⟨i + 1, hi⟩ => T.map (iterCoface X m ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

/-- Definition 2.4.2 (p. 17): The coface maps `d^i : T^{n+1}(X) ⟶ T^{n+2}(X)` for `i : Fin (n + 2)`,
defined by `d^i = T^i(ν_{T^{n - i + 1}(X)})`. -/
abbrev cobarCoface (X : M) (n : ℕ) (i : Fin (n + 2)) :
    cobarObj T X n ⟶ cobarObj T X (n + 1) :=
  iterCoface T X (n + 1) i

/-- Definition 2.4.2 (p. 17): The codegeneracy maps `s^j : T^{n+2}(X) ⟶ T^{n+1}(X)` for `j : Fin (n + 1)`,
defined by `s^j = T^j(μ_{T^{n - j}(X)})`:
- `s^0_X = μ_{T^n(X)} = T.μ.app (iterObj T X n)`
- `s^{j+1}_X = T(s^j_X)`. -/
@[implicit_reducible]
def cobarCodegeneracy (X : M) : ∀ (n : ℕ) (_ : Fin (n + 1)), cobarObj T X (n + 1) ⟶ cobarObj T X n
  | n, ⟨0, _⟩ => T.μ.app (iterObj T X n)
  | 0, ⟨j + 1, hj⟩ => absurd hj (by omega)
  | n + 1, ⟨j + 1, hj⟩ => T.map (cobarCodegeneracy X n ⟨j, Nat.lt_of_succ_lt_succ hj⟩)

@[simp]
lemma iterCoface_mk_zero (X : M) (m : ℕ) (h : 0 < m + 1) :
    iterCoface T X m ⟨0, h⟩ = T.η.app (iterObj T X m) := by
  cases m <;> rfl

@[simp]
lemma iterCoface_zero (X : M) (m : ℕ) :
    iterCoface T X m 0 = T.η.app (iterObj T X m) :=
  iterCoface_mk_zero T X m (Nat.zero_lt_succ m)

@[simp]
lemma iterCoface_succ_succ (X : M) (m : ℕ) (i : Fin (m + 1)) :
    iterCoface T X (m + 1) i.succ = T.map (iterCoface T X m i) := by
  rcases i with ⟨i, hi⟩
  rfl

@[simp]
lemma cobarCoface_mk_zero (X : M) (n : ℕ) (h : 0 < n + 2) :
    cobarCoface T X n ⟨0, h⟩ = T.η.app (cobarObj T X n) :=
  iterCoface_mk_zero T X (n + 1) h

@[simp]
lemma cobarCoface_zero (X : M) (n : ℕ) :
    cobarCoface T X n 0 = T.η.app (cobarObj T X n) :=
  iterCoface_zero T X (n + 1)

@[simp]
lemma cobarCoface_zero_one (X : M) :
    cobarCoface T X 0 1 = T.map (T.η.app X) :=
  rfl

@[simp]
lemma cobarCoface_succ_succ (X : M) (n : ℕ) (i : Fin (n + 2)) :
    cobarCoface T X (n + 1) i.succ = T.map (cobarCoface T X n i) :=
  iterCoface_succ_succ T X (n + 1) i

@[simp]
lemma cobarCodegeneracy_mk_zero (X : M) (n : ℕ) (h : 0 < n + 1) :
    cobarCodegeneracy T X n ⟨0, h⟩ = T.μ.app (iterObj T X n) := by
  cases n <;> rfl

@[simp]
lemma cobarCodegeneracy_zero (X : M) (n : ℕ) :
    cobarCodegeneracy T X n 0 = T.μ.app (iterObj T X n) :=
  cobarCodegeneracy_mk_zero T X n (Nat.zero_lt_succ n)

@[simp]
lemma cobarCodegeneracy_succ_succ (X : M) (n : ℕ) (j : Fin (n + 1)) :
    cobarCodegeneracy T X (n + 1) j.succ = T.map (cobarCodegeneracy T X n j) := by
  rcases j with ⟨j, hj⟩
  rfl

/-- Coface relation for `iterCoface`: `d^i ≫ d^{j+1} = d^j ≫ d^i` for `i ≤ j`. -/
@[reassoc]
theorem iterCoface_comp_iterCoface (X : M) :
    ∀ {m : ℕ} {i j : Fin (m + 1)} (_ : i ≤ j),
      iterCoface T X m i ≫ iterCoface T X (m + 1) j.succ =
        iterCoface T X m j ≫ iterCoface T X (m + 1) i.castSucc
  | m, ⟨0, h0⟩, j, _ => by
    have hcast : (⟨0, h0⟩ : Fin (m + 1)).castSucc = ⟨0, Nat.lt_succ_of_lt h0⟩ := rfl
    rw [hcast, iterCoface_mk_zero, iterCoface_mk_zero, iterCoface_succ_succ]
    exact (T.η.naturality (iterCoface T X m j)).symm
  | 0, ⟨i + 1, hi⟩, _, _ => absurd hi (by omega)
  | m + 1, ⟨i + 1, _⟩, ⟨0, _⟩, hij => by
    exfalso
    exact Nat.not_succ_le_zero i (Fin.le_iff_val_le_val.mp hij)
  | m + 1, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij => by
    let i' : Fin (m + 1) := ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    let j' : Fin (m + 1) := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    have hij' : i' ≤ j' := Nat.le_of_succ_le_succ (Fin.le_iff_val_le_val.mp hij)
    change T.map (iterCoface T X m i') ≫ T.map (iterCoface T X (m + 1) j'.succ) =
      T.map (iterCoface T X m j') ≫ T.map (iterCoface T X (m + 1) i'.castSucc)
    rw [← T.map_comp, ← T.map_comp, iterCoface_comp_iterCoface X hij']

/-- The coaugmentation `ν_X : X ⟶ T(X) = T^•(X)^0` equalizes `d^0` and `d^1`
(`ν_X ≫ d^0 = ν_X ≫ d^1`). -/
@[reassoc]
lemma cobar_coaugmentation_condition (X : M) :
    T.η.app X ≫ cobarCoface T X 0 0 = T.η.app X ≫ cobarCoface T X 0 1 :=
  (iterCoface_comp_iterCoface T X (le_refl (0 : Fin 1))).symm

/-- First cosimplicial identity: `d^i ≫ d^{j+1} = d^j ≫ d^i` for `i ≤ j`. -/
@[reassoc]
theorem cobarCoface_comp_cobarCoface (X : M) {n : ℕ} {i j : Fin (n + 2)} (hij : i ≤ j) :
    cobarCoface T X n i ≫ cobarCoface T X (n + 1) j.succ =
      cobarCoface T X n j ≫ cobarCoface T X (n + 1) i.castSucc :=
  iterCoface_comp_iterCoface T X hij

/-- Cosimplicial identity: `d^i ≫ s^i = 𝟙` (`δ_comp_σ_self`). -/
@[reassoc (attr := simp)]
theorem cobarCoface_castSucc_comp_cobarCodegeneracy (X : M) :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      cobarCoface T X n i.castSucc ≫ cobarCodegeneracy T X n i = 𝟙 (cobarObj T X n)
  | n, ⟨0, h0⟩ => by
    have hcast : (⟨0, h0⟩ : Fin (n + 1)).castSucc = ⟨0, Nat.lt_succ_of_lt h0⟩ := rfl
    rw [hcast, cobarCoface_mk_zero, cobarCodegeneracy_mk_zero]
    exact T.left_unit (iterObj T X n)
  | 0, ⟨i + 1, hi⟩ => absurd hi (by omega)
  | n + 1, ⟨i + 1, hi⟩ => by
    let i' : Fin (n + 1) := ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    change T.map (cobarCoface T X n i'.castSucc) ≫ T.map (cobarCodegeneracy T X n i') =
      𝟙 (T.obj (cobarObj T X n))
    rw [← T.map_comp, cobarCoface_castSucc_comp_cobarCodegeneracy X n i', T.map_id]

/-- Cosimplicial identity: `d^{i+1} ≫ s^i = 𝟙` (`δ_comp_σ_succ`). -/
@[reassoc (attr := simp)]
theorem cobarCoface_succ_comp_cobarCodegeneracy (X : M) :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      cobarCoface T X n i.succ ≫ cobarCodegeneracy T X n i = 𝟙 (cobarObj T X n)
  | n, ⟨0, h0⟩ => by
    change iterCoface T X (n + 1) (⟨0, h0⟩ : Fin (n + 1)).succ ≫
        cobarCodegeneracy T X n ⟨0, h0⟩ = 𝟙 (cobarObj T X n)
    rw [iterCoface_succ_succ, iterCoface_mk_zero, cobarCodegeneracy_mk_zero]
    exact T.right_unit (iterObj T X n)
  | 0, ⟨i + 1, hi⟩ => absurd hi (by omega)
  | n + 1, ⟨i + 1, hi⟩ => by
    let i' : Fin (n + 1) := ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    change T.map (cobarCoface T X n i'.succ) ≫ T.map (cobarCodegeneracy T X n i') =
      𝟙 (T.obj (cobarObj T X n))
    rw [← T.map_comp, cobarCoface_succ_comp_cobarCodegeneracy X n i', T.map_id]

/-- Cosimplicial identity: `d^i ≫ s^{j+1} = s^j ≫ d^i` for `i ≤ j` (`δ_comp_σ_of_le`). -/
@[reassoc]
theorem cobarCoface_comp_cobarCodegeneracy_of_le (X : M) :
    ∀ {n : ℕ} {i j : Fin (n + 1)} (_ : i ≤ j),
      cobarCoface T X (n + 1) i.castSucc.castSucc ≫ cobarCodegeneracy T X (n + 1) j.succ =
        cobarCodegeneracy T X n j ≫ cobarCoface T X n i.castSucc
  | n, ⟨0, h0⟩, j, _ => by
    have hc1 : (⟨0, h0⟩ : Fin (n + 1)).castSucc = ⟨0, Nat.lt_succ_of_lt h0⟩ := rfl
    have hc2 : (⟨0, h0⟩ : Fin (n + 1)).castSucc.castSucc =
        ⟨0, Nat.lt_succ_of_lt (Nat.lt_succ_of_lt h0)⟩ := rfl
    rw [hc2, hc1, cobarCoface_mk_zero, cobarCoface_mk_zero, cobarCodegeneracy_succ_succ]
    exact (T.η.naturality (cobarCodegeneracy T X n j)).symm
  | 0, ⟨i + 1, hi⟩, _, _ => absurd hi (by omega)
  | n + 1, ⟨i + 1, _⟩, ⟨0, _⟩, hij => by
    exfalso
    exact Nat.not_succ_le_zero i (Fin.le_iff_val_le_val.mp hij)
  | n + 1, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij => by
    let i' : Fin (n + 1) := ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    let j' : Fin (n + 1) := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    have hij' : i' ≤ j' := Nat.le_of_succ_le_succ (Fin.le_iff_val_le_val.mp hij)
    change T.map (cobarCoface T X (n + 1) i'.castSucc.castSucc) ≫
        T.map (cobarCodegeneracy T X (n + 1) j'.succ) =
      T.map (cobarCodegeneracy T X n j') ≫ T.map (cobarCoface T X n i'.castSucc)
    rw [← T.map_comp, ← T.map_comp, cobarCoface_comp_cobarCodegeneracy_of_le X hij']

/-- Cosimplicial identity: `d^{i+2} ≫ s^j = s^j ≫ d^{i+1}` for `j ≤ i` (`δ_comp_σ_of_gt`). -/
@[reassoc]
theorem cobarCoface_comp_cobarCodegeneracy_of_gt (X : M) :
    ∀ {n : ℕ} {i j : Fin (n + 1)} (_ : j ≤ i),
      cobarCoface T X (n + 1) i.succ.succ ≫ cobarCodegeneracy T X (n + 1) j.castSucc =
        cobarCodegeneracy T X n j ≫ cobarCoface T X n i.succ
  | n, i, ⟨0, h0⟩, _ => by
    have hc : (⟨0, h0⟩ : Fin (n + 1)).castSucc = ⟨0, Nat.lt_succ_of_lt h0⟩ := rfl
    change iterCoface T X (n + 2) i.succ.succ ≫ cobarCodegeneracy T X (n + 1) (⟨0, h0⟩ : Fin (n + 1)).castSucc =
      cobarCodegeneracy T X n ⟨0, h0⟩ ≫ iterCoface T X (n + 1) i.succ
    rw [hc, iterCoface_succ_succ, iterCoface_succ_succ, cobarCodegeneracy_mk_zero,
      cobarCodegeneracy_mk_zero]
    exact T.μ.naturality (iterCoface T X n i)
  | 0, _, ⟨j + 1, hj⟩, _ => absurd hj (by omega)
  | n + 1, ⟨0, _⟩, ⟨j + 1, _⟩, hji => by
    exfalso
    exact Nat.not_succ_le_zero j (Fin.le_iff_val_le_val.mp hji)
  | n + 1, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hji => by
    let i' : Fin (n + 1) := ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    let j' : Fin (n + 1) := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    have hji' : j' ≤ i' := Nat.le_of_succ_le_succ (Fin.le_iff_val_le_val.mp hji)
    change T.map (cobarCoface T X (n + 1) i'.succ.succ) ≫
        T.map (cobarCodegeneracy T X (n + 1) j'.castSucc) =
      T.map (cobarCodegeneracy T X n j') ≫ T.map (cobarCoface T X n i'.succ)
    rw [← T.map_comp, ← T.map_comp, cobarCoface_comp_cobarCodegeneracy_of_gt X hji']

/-- Cosimplicial identity: `s^i ≫ s^j = s^{j+1} ≫ s^i` for `i ≤ j`. -/
@[reassoc]
theorem cobarCodegeneracy_comp_cobarCodegeneracy (X : M) :
    ∀ {n : ℕ} {i j : Fin (n + 1)} (_ : i ≤ j),
      cobarCodegeneracy T X (n + 1) i.castSucc ≫ cobarCodegeneracy T X n j =
        cobarCodegeneracy T X (n + 1) j.succ ≫ cobarCodegeneracy T X n i
  | n, ⟨0, hi0⟩, ⟨0, hj0⟩, _ => by
    have hc : (⟨0, hi0⟩ : Fin (n + 1)).castSucc = ⟨0, Nat.lt_succ_of_lt hi0⟩ := rfl
    rw [hc, cobarCodegeneracy_mk_zero, cobarCodegeneracy_mk_zero,
      cobarCodegeneracy_succ_succ, cobarCodegeneracy_mk_zero]
    exact (T.assoc (iterObj T X n)).symm
  | n + 1, ⟨0, hi0⟩, ⟨j + 1, hj⟩, _ => by
    let j' : Fin (n + 1) := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    have hc : (⟨0, hi0⟩ : Fin (n + 2)).castSucc = ⟨0, Nat.lt_succ_of_lt hi0⟩ := rfl
    have hj1 : cobarCodegeneracy T X (n + 1) ⟨j + 1, hj⟩ =
        T.map (cobarCodegeneracy T X n j') := rfl
    rw [hc, cobarCodegeneracy_mk_zero, cobarCodegeneracy_mk_zero,
      cobarCodegeneracy_succ_succ, hj1]
    exact (T.μ.naturality (cobarCodegeneracy T X n j')).symm
  | 0, _, ⟨j + 1, hj⟩, _ => absurd hj (by omega)
  | n + 1, ⟨i + 1, _⟩, ⟨0, _⟩, hij => by
    exfalso
    exact Nat.not_succ_le_zero i (Fin.le_iff_val_le_val.mp hij)
  | n + 1, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij => by
    let i' : Fin (n + 1) := ⟨i, Nat.lt_of_succ_lt_succ hi⟩
    let j' : Fin (n + 1) := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    have hij' : i' ≤ j' := Nat.le_of_succ_le_succ (Fin.le_iff_val_le_val.mp hij)
    change T.map (cobarCodegeneracy T X (n + 1) i'.castSucc) ≫
        T.map (cobarCodegeneracy T X n j') =
      T.map (cobarCodegeneracy T X (n + 1) j'.succ) ≫ T.map (cobarCodegeneracy T X n i')
    rw [← T.map_comp, ← T.map_comp, cobarCodegeneracy_comp_cobarCodegeneracy X hij']

end MonadCobar

/-!
## §2.4.3 The Cobar Resolution `G^•(X)` and the Contracting Homotopy `s_{-1}` (Proposition 2.4.4)

Specializing `MonadCobar` to `T = inducedMonadOnCoalgebras G` on `Comonad.Coalgebra G`, we obtain
for every `G`-coalgebra `X` the cosimplicial cobar resolution `G^•(X)` (Definition 2.4.2, p. 17)
and prove Proposition 2.4.4 (p. 20): for any `I : C`, the augmented simplicial hom-tower
`Hom_{C^G}(G^•(X), G(I))` admits the left contraction `s_{-1}(f) = G(f ≫ ε_I)`.
-/

section ComonadCobar

variable (G : Comonad C)

/-- The `n`-th object `G^•(X)^n = G^{n+1}(X)` of the cobar resolution of a `G`-coalgebra `X`
(Definition 2.4.2, p. 17). -/
@[implicit_reducible]
def comonadCobarObj (X : Comonad.Coalgebra G) (n : ℕ) : Comonad.Coalgebra G :=
  cobarObj (inducedMonadOnCoalgebras G) X n

/-- Every stage `G^•(X)^n` of the cobar resolution is a cofree `G`-coalgebra (`G.cofree.obj _`). -/
lemma comonadCobarObj_eq_cofree (X : Comonad.Coalgebra G) (n : ℕ) :
    comonadCobarObj G X n =
      G.cofree.obj (iterObj (inducedMonadOnCoalgebras G) X n).A :=
  rfl

/-- The coaugmentation `ν_X = ψ_X : X ⟶ G(X) = G^•(X)^0` of the cobar resolution. -/
@[implicit_reducible]
def comonadCobarCoaug (X : Comonad.Coalgebra G) : X ⟶ comonadCobarObj G X 0 :=
  (inducedMonadOnCoalgebras G).η.app X

/-- The coface maps `d^i : G^•(X)^n ⟶ G^•(X)^{n+1}` for `i : Fin (n + 2)` (Definition 2.4.2, p. 17). -/
@[implicit_reducible]
def comonadCobarCoface (X : Comonad.Coalgebra G) (n : ℕ) (i : Fin (n + 2)) :
    comonadCobarObj G X n ⟶ comonadCobarObj G X (n + 1) :=
  cobarCoface (inducedMonadOnCoalgebras G) X n i

/-- The codegeneracy maps `s^j : G^•(X)^{n+1} ⟶ G^•(X)^n` for `j : Fin (n + 1)`
(Definition 2.4.2, p. 17). -/
@[implicit_reducible]
def comonadCobarCodegeneracy (X : Comonad.Coalgebra G) (n : ℕ) (j : Fin (n + 1)) :
    comonadCobarObj G X (n + 1) ⟶ comonadCobarObj G X n :=
  cobarCodegeneracy (inducedMonadOnCoalgebras G) X n j

/-- For any `G`-coalgebra `Z`, `I : C`, and coalgebra morphism `f : Z ⟶ G.cofree.obj I`,
the left contraction operator `s_{-1}(f) : T(Z) ⟶ G.cofree.obj I` of Proposition 2.4.4 (p. 20)
is defined by `G(f ≫ ε_I) = G(ε_I) ∘ G(f)`. -/
@[implicit_reducible]
def contractMap {I : C} {Z : Comonad.Coalgebra G} (f : Z ⟶ G.cofree.obj I) :
    (inducedMonadOnCoalgebras G).obj Z ⟶ G.cofree.obj I :=
  G.cofree.map (f.f ≫ G.ε.app I)

@[simp]
lemma contractMap_f {I : C} {Z : Comonad.Coalgebra G} (f : Z ⟶ G.cofree.obj I) :
    (contractMap G f).f = G.map f.f ≫ G.map (G.ε.app I) := by
  dsimp [contractMap]
  rw [Functor.map_comp]

/-- Fundamental identity for the left contraction `s_{-1}` (Proposition 2.4.4, p. 20):
`ν_Z ≫ s_{-1}(f) = f`, i.e., `d_0(s_{-1}(f)) = f`. -/
@[reassoc (attr := simp)]
theorem unit_comp_contractMap {I : C} {Z : Comonad.Coalgebra G} (f : Z ⟶ G.cofree.obj I) :
    (inducedMonadOnCoalgebras G).η.app Z ≫ contractMap G f = f := by
  ext
  have hf : Z.a ≫ G.map f.f = f.f ≫ G.δ.app I := f.h
  dsimp [contractMap, inducedMonadOnCoalgebras]
  rw [Functor.map_comp, reassoc_of% hf, G.right_counit]
  exact comp_id f.f

/-- Naturality of the left contraction `s_{-1}` with respect to `T.map g = G(g)`:
for any coalgebra morphism `g : Z₁ ⟶ Z₂` and `f : Z₂ ⟶ G(I)`,
`T(g) ≫ s_{-1}(f) = s_{-1}(g ≫ f)`. -/
@[reassoc (attr := simp)]
theorem map_comp_contractMap {I : C} {Z₁ Z₂ : Comonad.Coalgebra G}
    (g : Z₁ ⟶ Z₂) (f : Z₂ ⟶ G.cofree.obj I) :
    (inducedMonadOnCoalgebras G).map g ≫ contractMap G f = contractMap G (g ≫ f) := by
  ext
  change G.map g.f ≫ (contractMap G f).f = (contractMap G (g ≫ f)).f
  rw [contractMap_f, contractMap_f, Comonad.Coalgebra.comp_f, Functor.map_comp, Category.assoc]

/-- Compatibility of the left contraction `s_{-1}` with the monad multiplication `μ_Z = G(ε_Z)`:
`μ_Z ≫ s_{-1}(f) = s_{-1}(s_{-1}(f))` (the `j = 0` case of `s_{j+1} s_{-1} = s_{-1} s_j`
when `s_0` is included as in Proposition 2.4.4, p. 20). -/
@[reassoc (attr := simp)]
theorem mu_comp_contractMap {I : C} {Z : Comonad.Coalgebra G}
    (f : Z ⟶ G.cofree.obj I) :
    (inducedMonadOnCoalgebras G).μ.app Z ≫ contractMap G f =
      contractMap G (contractMap G f) := by
  ext
  have hε := G.ε.naturality (f.f ≫ G.ε.app I)
  dsimp [contractMap, inducedMonadOnCoalgebras] at hε ⊢
  rw [← Functor.map_comp, hε]

/-- An augmented simplicial hom-tower `K_{-1} ← K_0 ⇄ K_1 ⋯` equipped with a left contraction
`s_{-1}` as in Proposition 2.4.4 (p. 20). -/
structure LeftContractibleTower : Type (u + 1) where
  /-- The augmentation object `K_{-1}`. -/
  aug : Type u
  /-- The `n`-simplices `K_n`. -/
  obj : ℕ → Type u
  /-- The augmentation map `d_0 : K_0 → K_{-1}`. -/
  augMap : obj 0 → aug
  /-- The face maps `d_i : K_{n+1} → K_n` for `i : Fin (n + 2)`. -/
  face : ∀ (n : ℕ), Fin (n + 2) → obj (n + 1) → obj n
  /-- The degeneracy maps `s_j : K_n → K_{n+1}` for `j : Fin (n + 1)`. -/
  degeneracy : ∀ (n : ℕ), Fin (n + 1) → obj n → obj (n + 1)
  /-- The contracting homotopy on the augmentation `s_{-1} : K_{-1} → K_0`. -/
  sAug : aug → obj 0
  /-- The contracting homotopy `s_{-1} : K_n → K_{n+1}`. -/
  s : ∀ (n : ℕ), obj n → obj (n + 1)
  /-- `d_0 (s_{-1}(f)) = f` on `K_{-1}`. -/
  augMap_sAug : ∀ (f : aug), augMap (sAug f) = f
  /-- `d_0 (s_{-1}(f)) = f` on `K_n`. -/
  face_zero_s : ∀ (n : ℕ) (f : obj n), face n 0 (s n f) = f
  /-- `d_1 (s_{-1}(f)) = s_{-1}(d_0(f))` on `K_0`. -/
  face_one_s_zero : ∀ (f : obj 0), face 0 1 (s 0 f) = sAug (augMap f)
  /-- `d_{i+1} (s_{-1}(f)) = s_{-1}(d_i(f))` on `K_{n+1}`. -/
  face_succ_s : ∀ (n : ℕ) (i : Fin (n + 2)) (f : obj (n + 1)),
    face (n + 1) i.succ (s (n + 1) f) = s n (face n i f)
  /-- `s_{j+1} (s_{-1}(f)) = s_{-1}(s_j(f))` on `K_n`. -/
  degeneracy_succ_s : ∀ (n : ℕ) (j : Fin (n + 1)) (f : obj n),
    degeneracy (n + 1) j.succ (s n f) = s (n + 1) (degeneracy n j f)
  /-- `s_0 (s_{-1}(f)) = s_{-1}(s_{-1}(f))` on `K_n`. -/
  degeneracy_zero_s : ∀ (n : ℕ) (f : obj n),
    degeneracy (n + 1) 0 (s n f) = s (n + 1) (s n f)

/-- **Proposition 2.4.4** (p. 20): For any `G`-coalgebra `X` and any object `I : C`
(representing a cofree/`G`-injective coalgebra `G(I)`), the augmented simplicial hom-tower
`K_n = Hom_{C^G}(G^•(X)^n, G(I))` with `K_{-1} = Hom_{C^G}(X, G(I))` admits the left contraction
`s_{-1}(f) = G(f ≫ ε_I)` satisfying all identities of p. 20. -/
def cobarHomLeftContractibleTower (X : Comonad.Coalgebra G) (I : C) :
    LeftContractibleTower.{v₁} where
  aug := X ⟶ G.cofree.obj I
  obj n := comonadCobarObj G X n ⟶ G.cofree.obj I
  augMap f := comonadCobarCoaug G X ≫ f
  face n i f := comonadCobarCoface G X n i ≫ f
  degeneracy n j f := comonadCobarCodegeneracy G X n j ≫ f
  sAug f := contractMap G f
  s _ f := contractMap G f
  augMap_sAug f := unit_comp_contractMap G f
  face_zero_s n f := by
    change cobarCoface (inducedMonadOnCoalgebras G) X n 0 ≫ contractMap G f = f
    rw [cobarCoface_zero]
    exact unit_comp_contractMap G f
  face_one_s_zero f := by
    change cobarCoface (inducedMonadOnCoalgebras G) X 0 1 ≫ contractMap G f =
      contractMap G (comonadCobarCoaug G X ≫ f)
    rw [cobarCoface_zero_one]
    exact map_comp_contractMap G (comonadCobarCoaug G X) f
  face_succ_s n i f := by
    change cobarCoface (inducedMonadOnCoalgebras G) X (n + 1) i.succ ≫ contractMap G f =
      contractMap G (comonadCobarCoface G X n i ≫ f)
    rw [cobarCoface_succ_succ]
    exact map_comp_contractMap G (comonadCobarCoface G X n i) f
  degeneracy_succ_s n j f := by
    change cobarCodegeneracy (inducedMonadOnCoalgebras G) X (n + 1) j.succ ≫ contractMap G f =
      contractMap G (comonadCobarCodegeneracy G X n j ≫ f)
    rw [cobarCodegeneracy_succ_succ]
    exact map_comp_contractMap G (comonadCobarCodegeneracy G X n j) f
  degeneracy_zero_s n f := by
    change cobarCodegeneracy (inducedMonadOnCoalgebras G) X (n + 1) 0 ≫ contractMap G f =
      contractMap G (contractMap G f)
    rw [cobarCodegeneracy_zero]
    exact mu_comp_contractMap G f

/-- Moreover, as observed on p. 22 of the thesis, after applying the forgetful functor
`U^G : C^G ⥤ C`, the coaugmented cobar resolution `X.A ⟶ G^•(X)` in the underlying category `C`
admits the contracting codegeneracy `s_{-1}^C = ε_{G^•(X)} : G^{n+1}(X) ⟶ G^n(X)` satisfying
`ψ_X ≫ ε_X = 𝟙 X` and `d^0 ≫ ε = 𝟙`. -/
@[reassoc (attr := simp)]
theorem cobar_underlying_coaug_retraction (X : Comonad.Coalgebra G) :
    (comonadCobarCoaug G X).f ≫ G.ε.app X.A = 𝟙 X.A := by
  rw [comonadCobarCoaug, inducedMonadOnCoalgebras_unit_f]
  exact X.counit

@[reassoc (attr := simp)]
theorem cobar_underlying_coface_zero_retraction (X : Comonad.Coalgebra G) (n : ℕ) :
    (comonadCobarCoface G X n 0).f ≫ G.ε.app (comonadCobarObj G X n).A =
      𝟙 (comonadCobarObj G X n).A := by
  rw [comonadCobarCoface, cobarCoface_zero, inducedMonadOnCoalgebras_unit_f]
  exact (comonadCobarObj G X n).counit

@[reassoc (attr := simp)]
theorem cobar_underlying_coface_one_zero_retraction (X : Comonad.Coalgebra G) :
    (comonadCobarCoface G X 0 1).f ≫ G.ε.app (comonadCobarObj G X 0).A =
      G.ε.app X.A ≫ (comonadCobarCoaug G X).f := by
  rw [comonadCobarCoface, cobarCoface_zero_one, comonadCobarCoaug]
  change G.map ((inducedMonadOnCoalgebras G).η.app X).f ≫ G.ε.app (G.obj X.A) =
    G.ε.app X.A ≫ ((inducedMonadOnCoalgebras G).η.app X).f
  exact G.ε.naturality ((inducedMonadOnCoalgebras G).η.app X).f

@[reassoc (attr := simp)]
theorem cobar_underlying_coface_succ_retraction (X : Comonad.Coalgebra G)
    (n : ℕ) (i : Fin (n + 2)) :
    (comonadCobarCoface G X (n + 1) i.succ).f ≫ G.ε.app (comonadCobarObj G X (n + 1)).A =
      G.ε.app (comonadCobarObj G X n).A ≫ (comonadCobarCoface G X n i).f := by
  rw [comonadCobarCoface, cobarCoface_succ_succ]
  change G.map (comonadCobarCoface G X n i).f ≫ G.ε.app (G.obj (comonadCobarObj G X n).A) =
    G.ε.app (comonadCobarObj G X n).A ≫ (comonadCobarCoface G X n i).f
  exact G.ε.naturality (comonadCobarCoface G X n i).f

@[reassoc (attr := simp)]
theorem cobar_underlying_codegeneracy_succ_retraction (X : Comonad.Coalgebra G)
    (n : ℕ) (j : Fin (n + 1)) :
    (comonadCobarCodegeneracy G X (n + 1) j.succ).f ≫ G.ε.app (comonadCobarObj G X n).A =
      G.ε.app (comonadCobarObj G X (n + 1)).A ≫ (comonadCobarCodegeneracy G X n j).f := by
  rw [comonadCobarCodegeneracy, cobarCodegeneracy_succ_succ]
  change G.map (comonadCobarCodegeneracy G X n j).f ≫ G.ε.app (comonadCobarObj G X n).A =
    G.ε.app (comonadCobarObj G X (n + 1)).A ≫ (comonadCobarCodegeneracy G X n j).f
  exact G.ε.naturality (comonadCobarCodegeneracy G X n j).f

@[reassoc (attr := simp)]
theorem cobar_underlying_codegeneracy_zero_retraction (X : Comonad.Coalgebra G) (n : ℕ) :
    (comonadCobarCodegeneracy G X (n + 1) 0).f ≫ G.ε.app (comonadCobarObj G X n).A =
      G.ε.app (comonadCobarObj G X (n + 1)).A ≫ G.ε.app (comonadCobarObj G X n).A := by
  rw [comonadCobarCodegeneracy, cobarCodegeneracy_zero]
  change G.map (G.ε.app (comonadCobarObj G X n).A) ≫ G.ε.app (comonadCobarObj G X n).A =
    G.ε.app (G.obj (comonadCobarObj G X n).A) ≫ G.ε.app (comonadCobarObj G X n).A
  exact G.ε.naturality (G.ε.app (comonadCobarObj G X n).A)

end ComonadCobar

end Section2_4

/-!
## §2.5 Criteria for Change of Ext (Generalized Shapiro's Lemma)

In §2.5 (pp. 20–22), given a comonad functor `Φ : Section2_2.ComonadFunctor G H` and an adjunction
`adj : Φ.F ⊣ U` between `C` and `D` with mate opfunctor `Ψ = Section2_3.mateOpfunctor Φ adj`,
we have the lifted adjunction (`Section2_3.liftedAdjunction`):
`Φ.pushforward ⊣ Ψ.coalgebraPullback` (`α_* ⊣ α^* : D^H ⥤ C^G`).

We prove:
1. **Retract & Iso Transfer of Contractions**: Any augmented simplicial or coaugmented cosimplicial
   tower that is isomorphic to (or a compatible retract of) a contractible tower inherits a
   contracting homotopy.
2. **Underlying Contracting Homotopy of `U(H^•(N))` and Retract Property of `α^*(H^•(N))`** (p. 22):
   In the underlying category `D`, `N ⟶ H^•(N)` has the contracting codegeneracy `ε^D`, and its
   image under `U : D ⥤ C` has the contracting codegeneracy `U(ε^D)`. When `C` is abelian (or
   whenever the equalizer `α^*(H^•(N)) ↪ U(H^•(N))` is a retract compatible with the contraction),
   `α^* N ⟶ α^*(H^•(N))` inherits a contracting homotopy in `C`.
3. **Proposition 2.5.2 (Generalized Shapiro's Lemma, pp. 21–22)**:
   For any `G`-coalgebra `M` and `H`-coalgebra `N`, the lifted adjunction `α_* ⊣ α^*` induces a
   canonical isomorphism of coaugmented cosimplicial hom-towers:
   `Hom_{D^H}(α_* M, H^•(N)) ≃ Hom_{C^G}(M, α^*(H^•(N)))`
   commuting with the coaugmentation, all coface maps `d^i`, and all codegeneracy maps `s^j`.
   When `α^*` sends cofree `H`-coalgebras to cofree `G`-coalgebras (`α^*(H^•(N)^n) ≅ G(J_n)`),
   this identifies the cobar complex computing `Ext^*_H(α_* M, N)` with the cobar complex computing
   `Ext^*_G(M, α^* N)`.
-/

namespace Section2_5

open Section2_2 Section2_3 Section2_4

variable {G : Comonad C} {H : Comonad D}
variable (Φ : ComonadFunctor G H) {U : D ⥤ C} (adj : Φ.F ⊣ U)

/-- An isomorphism of augmented simplicial hom-towers `(aug, obj, augMap, face, degeneracy)`. -/
structure AugmentedTowerIso
    (aug₁ : Type*) (obj₁ : ℕ → Type*)
    (augMap₁ : obj₁ 0 → aug₁)
    (face₁ : ∀ n, Fin (n + 2) → obj₁ (n + 1) → obj₁ n)
    (degeneracy₁ : ∀ n, Fin (n + 1) → obj₁ n → obj₁ (n + 1))
    (aug₂ : Type*) (obj₂ : ℕ → Type*)
    (augMap₂ : obj₂ 0 → aug₂)
    (face₂ : ∀ n, Fin (n + 2) → obj₂ (n + 1) → obj₂ n)
    (degeneracy₂ : ∀ n, Fin (n + 1) → obj₂ n → obj₂ (n + 1)) where
  /-- Equivalence on augmentation levels `K_{-1} ≃ L_{-1}`. -/
  augEquiv : aug₁ ≃ aug₂
  /-- Equivalence on `n`-simplices `K_n ≃ L_n`. -/
  levelEquiv : ∀ n : ℕ, obj₁ n ≃ obj₂ n
  /-- Compatibility with the augmentation `d_0 : K_0 → K_{-1}`. -/
  comm_aug : ∀ x : obj₁ 0, augEquiv (augMap₁ x) = augMap₂ (levelEquiv 0 x)
  /-- Compatibility with all face maps `d_i : K_{n+1} → K_n`. -/
  comm_face : ∀ (n : ℕ) (i : Fin (n + 2)) (x : obj₁ (n + 1)),
    levelEquiv n (face₁ n i x) = face₂ n i (levelEquiv (n + 1) x)
  /-- Compatibility with all degeneracy maps `s_j : K_n → K_{n+1}`. -/
  comm_degeneracy : ∀ (n : ℕ) (j : Fin (n + 1)) (x : obj₁ n),
    levelEquiv (n + 1) (degeneracy₁ n j x) = degeneracy₂ n j (levelEquiv n x)

/-- Transporting a `LeftContractibleTower` across an `AugmentedTowerIso` yields a
`LeftContractibleTower` on the target tower. -/
def LeftContractibleTower.ofIso (K : LeftContractibleTower.{u})
    {aug₂ : Type v} {obj₂ : ℕ → Type v}
    {augMap₂ : obj₂ 0 → aug₂}
    {face₂ : ∀ n, Fin (n + 2) → obj₂ (n + 1) → obj₂ n}
    {degeneracy₂ : ∀ n, Fin (n + 1) → obj₂ n → obj₂ (n + 1)}
    (e : AugmentedTowerIso K.aug K.obj K.augMap K.face K.degeneracy
      aug₂ obj₂ augMap₂ face₂ degeneracy₂) :
    LeftContractibleTower.{v} where
  aug := aug₂
  obj := obj₂
  augMap := augMap₂
  face := face₂
  degeneracy := degeneracy₂
  sAug y := e.levelEquiv 0 (K.sAug (e.augEquiv.symm y))
  s n y := e.levelEquiv (n + 1) (K.s n (e.levelEquiv n |>.symm y))
  augMap_sAug y := by
    rw [← e.comm_aug, K.augMap_sAug, Equiv.apply_symm_apply]
  face_zero_s n y := by
    rw [← e.comm_face, K.face_zero_s, Equiv.apply_symm_apply]
  face_one_s_zero y := by
    rw [← e.comm_face, K.face_one_s_zero]
    congr 2
    apply e.augEquiv.injective
    rw [Equiv.apply_symm_apply, e.comm_aug, Equiv.apply_symm_apply]
  face_succ_s n i y := by
    rw [← e.comm_face, K.face_succ_s]
    congr 2
    apply (e.levelEquiv n).injective
    rw [Equiv.apply_symm_apply, e.comm_face, Equiv.apply_symm_apply]
  degeneracy_succ_s n j y := by
    rw [← e.comm_degeneracy, K.degeneracy_succ_s]
    congr 2
    apply (e.levelEquiv (n + 1)).injective
    rw [Equiv.apply_symm_apply, e.comm_degeneracy, Equiv.apply_symm_apply]
  degeneracy_zero_s n y := by
    rw [← e.comm_degeneracy, K.degeneracy_zero_s]
    congr 2
    exact (Equiv.symm_apply_apply (e.levelEquiv (n + 1)) _).symm

/-- A coaugmented cosimplicial hom-tower `K^{-1} → K^0 ⇉ K^1 ⋯` (such as `Hom(M, G^•(N))`). -/
structure CoaugmentedCosimplicialTower : Type (u + 1) where
  /-- The coaugmentation object `K^{-1}`. -/
  coaug : Type u
  /-- The `n`-cosimplices `K^n`. -/
  obj : ℕ → Type u
  /-- The coaugmentation map `d^0 : K^{-1} → K^0`. -/
  coaugMap : coaug → obj 0
  /-- The coface maps `d^i : K^n → K^{n+1}` for `i : Fin (n + 2)`. -/
  coface : ∀ (n : ℕ), Fin (n + 2) → obj n → obj (n + 1)
  /-- The codegeneracy maps `s^j : K^{n+1} → K^n` for `j : Fin (n + 1)`. -/
  codegeneracy : ∀ (n : ℕ), Fin (n + 1) → obj (n + 1) → obj n

/-- An isomorphism between two `CoaugmentedCosimplicialTower`s, commuting with the coaugmentation,
all coface maps `d^i`, and all codegeneracy maps `s^j`. -/
structure CoaugmentedCosimplicialTowerIso
    (T₁ : CoaugmentedCosimplicialTower.{u})
    (T₂ : CoaugmentedCosimplicialTower.{v}) where
  /-- Equivalence on coaugmentation levels `K^{-1} ≃ L^{-1}`. -/
  coaugEquiv : T₁.coaug ≃ T₂.coaug
  /-- Equivalence on `n`-cosimplices `K^n ≃ L^n`. -/
  levelEquiv : ∀ n : ℕ, T₁.obj n ≃ T₂.obj n
  /-- Compatibility with the coaugmentation map `K^{-1} → K^0`. -/
  comm_coaug : ∀ x : T₁.coaug, levelEquiv 0 (T₁.coaugMap x) = T₂.coaugMap (coaugEquiv x)
  /-- Compatibility with all coface maps `d^i : K^n → K^{n+1}`. -/
  comm_coface : ∀ (n : ℕ) (i : Fin (n + 2)) (x : T₁.obj n),
    levelEquiv (n + 1) (T₁.coface n i x) = T₂.coface n i (levelEquiv n x)
  /-- Compatibility with all codegeneracy maps `s^j : K^{n+1} → K^n`. -/
  comm_codegeneracy : ∀ (n : ℕ) (j : Fin (n + 1)) (x : T₁.obj (n + 1)),
    levelEquiv n (T₁.codegeneracy n j x) = T₂.codegeneracy n j (levelEquiv (n + 1) x)

/-- Transitivity (composition) of `CoaugmentedCosimplicialTowerIso`s. -/
@[simps]
def CoaugmentedCosimplicialTowerIso.trans
    {T₁ : CoaugmentedCosimplicialTower.{u}}
    {T₂ : CoaugmentedCosimplicialTower.{v}}
    {T₃ : CoaugmentedCosimplicialTower.{w}}
    (e₁ : CoaugmentedCosimplicialTowerIso T₁ T₂)
    (e₂ : CoaugmentedCosimplicialTowerIso T₂ T₃) :
    CoaugmentedCosimplicialTowerIso T₁ T₃ where
  coaugEquiv := e₁.coaugEquiv.trans e₂.coaugEquiv
  levelEquiv n := (e₁.levelEquiv n).trans (e₂.levelEquiv n)
  comm_coaug x := by
    dsimp
    rw [e₁.comm_coaug, e₂.comm_coaug]
  comm_coface n i x := by
    dsimp
    rw [e₁.comm_coface, e₂.comm_coface]
  comm_codegeneracy n j x := by
    dsimp
    rw [e₁.comm_codegeneracy, e₂.comm_codegeneracy]

/-- Given a `G`-coalgebra `M` and `N : Comonad.Coalgebra G`, the cobar hom-tower
`Hom_{C^G}(M, G^•(N))` whose cohomology defines `Ext^*_G(M, N)` (Definition 2.4.1, p. 16). -/
def cobarCosimplicialHomTower {G : Comonad C} (M N : Comonad.Coalgebra G) :
    CoaugmentedCosimplicialTower.{v₁} where
  coaug := M ⟶ N
  obj n := M ⟶ comonadCobarObj G N n
  coaugMap f := f ≫ comonadCobarCoaug G N
  coface n i f := f ≫ comonadCobarCoface G N n i
  codegeneracy n j f := f ≫ comonadCobarCodegeneracy G N n j

/-- Applying `α^* = (mateOpfunctor Φ adj).coalgebraPullback` termwise to the cobar resolution
`H^•(N)` of `N : D^H` produces the pulled-back cosimplicial cobar resolution `α^*(H^•(N))`
in `C^G`. -/
@[implicit_reducible]
noncomputable def pullbackCobarObj [HasEqualizers (Comonad.Coalgebra G)]
    (N : Comonad.Coalgebra H) (n : ℕ) : Comonad.Coalgebra G :=
  (mateOpfunctor Φ adj).coalgebraPullback.obj (comonadCobarObj H N n)

/-- The coaugmentation `α^* N ⟶ α^*(H^•(N)^0)` in `C^G`. -/
@[implicit_reducible]
noncomputable def pullbackCobarCoaug [HasEqualizers (Comonad.Coalgebra G)]
    (N : Comonad.Coalgebra H) :
    (mateOpfunctor Φ adj).coalgebraPullback.obj N ⟶ pullbackCobarObj Φ adj N 0 :=
  (mateOpfunctor Φ adj).coalgebraPullback.map (comonadCobarCoaug H N)

/-- The coface maps `α^*(d^i) : α^*(H^•(N)^n) ⟶ α^*(H^•(N)^{n+1})` in `C^G`. -/
@[implicit_reducible]
noncomputable def pullbackCobarCoface [HasEqualizers (Comonad.Coalgebra G)]
    (N : Comonad.Coalgebra H) (n : ℕ) (i : Fin (n + 2)) :
    pullbackCobarObj Φ adj N n ⟶ pullbackCobarObj Φ adj N (n + 1) :=
  (mateOpfunctor Φ adj).coalgebraPullback.map (comonadCobarCoface H N n i)

/-- The codegeneracy maps `α^*(s^j) : α^*(H^•(N)^{n+1}) ⟶ α^*(H^•(N)^n)` in `C^G`. -/
@[implicit_reducible]
noncomputable def pullbackCobarCodegeneracy [HasEqualizers (Comonad.Coalgebra G)]
    (N : Comonad.Coalgebra H) (n : ℕ) (j : Fin (n + 1)) :
    pullbackCobarObj Φ adj N (n + 1) ⟶ pullbackCobarObj Φ adj N n :=
  (mateOpfunctor Φ adj).coalgebraPullback.map (comonadCobarCodegeneracy H N n j)

/-- The coaugmented cosimplicial hom-tower `Hom_{C^G}(M, α^*(H^•(N)))` on the right-hand side of
the Generalized Shapiro's Lemma (p. 22). -/
noncomputable def pullbackCosimplicialHomTower [HasEqualizers (Comonad.Coalgebra G)]
    (M : Comonad.Coalgebra G) (N : Comonad.Coalgebra H) :
    CoaugmentedCosimplicialTower.{v₁} where
  coaug := M ⟶ (mateOpfunctor Φ adj).coalgebraPullback.obj N
  obj n := M ⟶ pullbackCobarObj Φ adj N n
  coaugMap f := f ≫ pullbackCobarCoaug Φ adj N
  coface n i f := f ≫ pullbackCobarCoface Φ adj N n i
  codegeneracy n j f := f ≫ pullbackCobarCodegeneracy Φ adj N n j

/-- **Proposition 2.5.2 (Generalized Shapiro's Lemma — Cobar Complex Isomorphism, pp. 21–22)**:
For any `G`-coalgebra `M` and `H`-coalgebra `N`, the lifted adjunction `α_* ⊣ α^*`
(`Section2_3.liftedAdjunction Φ adj`) induces a canonical isomorphism of coaugmented cosimplicial
hom-towers between:
1. `cobarCosimplicialHomTower (Φ.pushforward.obj M) N` (`Hom_{D^H}(α_* M, H^•(N))`, whose
   cohomology is `Ext^*_H(α_* M, N)`), and
2. `pullbackCosimplicialHomTower Φ adj M N` (`Hom_{C^G}(M, α^*(H^•(N)))`, whose cohomology is
   `Ext^*_G(M, α^* N)` whenever `α^*(H^•(N))` is a weak `G`-resolution of `α^* N`, e.g. when
   `α^*` sends cofree `H`-coalgebras to cofree `G`-coalgebras). -/
@[simps]
noncomputable def generalizedShapiroCobarIso [HasEqualizers (Comonad.Coalgebra G)]
    (M : Comonad.Coalgebra G) (N : Comonad.Coalgebra H) :
    CoaugmentedCosimplicialTowerIso
      (cobarCosimplicialHomTower (Φ.pushforward.obj M) N)
      (pullbackCosimplicialHomTower Φ adj M N) where
  coaugEquiv := (liftedAdjunction Φ adj).homEquiv M N
  levelEquiv n := (liftedAdjunction Φ adj).homEquiv M (comonadCobarObj H N n)
  comm_coaug f := by
    dsimp [cobarCosimplicialHomTower, pullbackCosimplicialHomTower, pullbackCobarCoaug]
    exact Adjunction.homEquiv_naturality_right (liftedAdjunction Φ adj) f (comonadCobarCoaug H N)
  comm_coface n i f := by
    dsimp [cobarCosimplicialHomTower, pullbackCosimplicialHomTower, pullbackCobarCoface]
    exact Adjunction.homEquiv_naturality_right (liftedAdjunction Φ adj) f (comonadCobarCoface H N n i)
  comm_codegeneracy n j f := by
    dsimp [cobarCosimplicialHomTower, pullbackCosimplicialHomTower, pullbackCobarCodegeneracy]
    exact Adjunction.homEquiv_naturality_right (liftedAdjunction Φ adj) f (comonadCobarCodegeneracy H N n j)

/-- Furthermore, as proven on p. 22 of the thesis, when `α^*(H^•(N))` is isomorphic as a
coaugmented cosimplicial resolution to the cobar resolution `G^•(α^* N)` (or any weak
`G`-resolution of `α^* N`), composing `generalizedShapiroCobarIso` with the induced isomorphism
on `Hom_{C^G}(M, -)` yields a canonical isomorphism of coaugmented cosimplicial hom-towers
`Hom_{D^H}(α_* M, H^•(N)) ≃ Hom_{C^G}(M, G^•(α^* N))` computing
`Ext^*_H(α_* M, N) ≅ Ext^*_G(M, α^* N)`. -/
@[simps!]
noncomputable def generalizedShapiroExtCobarIso [HasEqualizers (Comonad.Coalgebra G)]
    (M : Comonad.Coalgebra G) (N : Comonad.Coalgebra H)
    (e : CoaugmentedCosimplicialTowerIso
      (pullbackCosimplicialHomTower Φ adj M N)
      (cobarCosimplicialHomTower M ((mateOpfunctor Φ adj).coalgebraPullback.obj N))) :
    CoaugmentedCosimplicialTowerIso
      (cobarCosimplicialHomTower (Φ.pushforward.obj M) N)
      (cobarCosimplicialHomTower M ((mateOpfunctor Φ adj).coalgebraPullback.obj N)) :=
  (generalizedShapiroCobarIso Φ adj M N).trans e

/-- **Proposition 2.5.1 (Naturality Triangle of Shapiro's Lemma, p. 21, lines 693–698)**:
For any `G`-coalgebras `A` and `M` and any morphism `f : A ⟶ M` in `C^G`, the image of the
pushed-forward morphism `α_*(f) : α_* A ⟶ α_* M` under the Shapiro equivalence
`Hom_{D^H}(α_* A, α_* M) ≃ Hom_{C^G}(A, α^* α_* M)` equals `f` composed with the lifted unit
`σ̃_M : M ⟶ α^* α_* M`, making the triangle on lines 695–697 commute. -/
theorem shapiro_naturality_triangle_coaug [HasEqualizers (Comonad.Coalgebra G)]
    (A M : Comonad.Coalgebra G) (f : A ⟶ M) :
    (generalizedShapiroCobarIso Φ adj A (Φ.pushforward.obj M)).coaugEquiv
      (Φ.pushforward.map f) =
      f ≫ (liftedAdjunction Φ adj).unit.app M := by
  change ((liftedAdjunction Φ adj).homEquiv A (Φ.pushforward.obj M)) (Φ.pushforward.map f) =
    f ≫ (liftedAdjunction Φ adj).unit.app M
  rw [Adjunction.homEquiv_unit]
  exact ((liftedAdjunction Φ adj).unit.naturality f).symm

/-- **Proposition 2.5.2 (Underlying Contraction Step, p. 22, line 742)**:
As observed on line 742 of the thesis, for any functor `W : D ⥤ C` (such as `W = U ∘ X` on line
742, or `B(n)_* ⊗_{K(n)_*} -` in Chapter 3), any `H`-coalgebra `N`, and any object `J : C`,
the augmented simplicial hom-tower `Hom_C(W(H^•(N)), J) → Hom_C(W(N), J)` admits the explicit
left contraction `W(ε^H)^*` (`s_{-1}(f) = W(ε^H) ≫ f`) because `ε^H` is a cosimplicial
retraction of `H^•(N)` in the underlying category `D`. -/
def underlyingFunctorCobarLeftContractibleTower (H : Comonad D) (W : D ⥤ C)
    (N : Comonad.Coalgebra H) (J : C) :
    LeftContractibleTower.{v₁} where
  aug := W.obj N.A ⟶ J
  obj n := W.obj (comonadCobarObj H N n).A ⟶ J
  augMap f := W.map (comonadCobarCoaug H N).f ≫ f
  face n i f := W.map (comonadCobarCoface H N n i).f ≫ f
  degeneracy n j f := W.map (comonadCobarCodegeneracy H N n j).f ≫ f
  sAug f := W.map (H.ε.app N.A) ≫ f
  s n f := W.map (H.ε.app (comonadCobarObj H N n).A) ≫ f
  augMap_sAug f := by
    rw [← Category.assoc, ← W.map_comp, cobar_underlying_coaug_retraction, W.map_id,
      Category.id_comp]
  face_zero_s n f := by
    rw [← Category.assoc, ← W.map_comp, cobar_underlying_coface_zero_retraction, W.map_id,
      Category.id_comp]
  face_one_s_zero f := by
    rw [← Category.assoc, ← W.map_comp, cobar_underlying_coface_one_zero_retraction,
      W.map_comp, Category.assoc]
  face_succ_s n i f := by
    rw [← Category.assoc, ← W.map_comp, cobar_underlying_coface_succ_retraction,
      W.map_comp, Category.assoc]
  degeneracy_succ_s n j f := by
    rw [← Category.assoc, ← W.map_comp, cobar_underlying_codegeneracy_succ_retraction,
      W.map_comp, Category.assoc]
  degeneracy_zero_s n f := by
    rw [← Category.assoc, ← W.map_comp, cobar_underlying_codegeneracy_zero_retraction,
      W.map_comp, Category.assoc]

/-- Natural equivalence `(W.obj Y.A ⟶ J) ≃ (α^* Y ⟶ G.cofree.obj J)` combining a natural
isomorphism `eW : G.forget ∘ α^* ≅ W ∘ H.forget` with the cofree adjunction
`G.adj : G.forget ⊣ G.cofree` (used in the proof of Proposition 2.5.2, line 742). -/
noncomputable def underlyingToCofreeHomEquiv [HasEqualizers (Comonad.Coalgebra G)]
    (W : D ⥤ C)
    (eW : (mateOpfunctor Φ adj).coalgebraPullback ⋙ G.forget ≅ H.forget ⋙ W)
    (Y : Comonad.Coalgebra H) (J : C) :
    (W.obj Y.A ⟶ J) ≃
      ((mateOpfunctor Φ adj).coalgebraPullback.obj Y ⟶ G.cofree.obj J) where
  toFun f := (G.adj.homEquiv ((mateOpfunctor Φ adj).coalgebraPullback.obj Y) J)
    (eW.hom.app Y ≫ f)
  invFun g := eW.inv.app Y ≫
    ((G.adj.homEquiv ((mateOpfunctor Φ adj).coalgebraPullback.obj Y) J).symm g)
  left_inv f := by
    dsimp only
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id_app]
    exact Category.id_comp f
  right_inv g := by
    dsimp only
    rw [← Category.assoc, Iso.hom_inv_id_app]
    erw [Category.id_comp, Equiv.apply_symm_apply]

/-- Naturality of `underlyingToCofreeHomEquiv` with respect to any `H`-coalgebra morphism
`k : Y₁ ⟶ Y₂`. -/
lemma underlyingToCofreeHomEquiv_naturality [HasEqualizers (Comonad.Coalgebra G)]
    (W : D ⥤ C)
    (eW : (mateOpfunctor Φ adj).coalgebraPullback ⋙ G.forget ≅ H.forget ⋙ W)
    {Y₁ Y₂ : Comonad.Coalgebra H} (k : Y₁ ⟶ Y₂) (J : C) (f : W.obj Y₂.A ⟶ J) :
    underlyingToCofreeHomEquiv Φ adj W eW Y₁ J (W.map k.f ≫ f) =
      (mateOpfunctor Φ adj).coalgebraPullback.map k ≫
        underlyingToCofreeHomEquiv Φ adj W eW Y₂ J f := by
  dsimp [underlyingToCofreeHomEquiv]
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  have heW := eW.hom.naturality k
  dsimp at heW
  rw [← Category.assoc, ← heW, Category.assoc]
  rfl

/-- Isomorphism of augmented simplicial hom-towers between
`Hom_C(W(H^•(N)), J)` and `Hom_{C^G}(α^*(H^•(N)), G(J))` (Proposition 2.5.2, line 742). -/
noncomputable def pullbackCobarCofreeHomTowerIso [HasEqualizers (Comonad.Coalgebra G)]
    (W : D ⥤ C)
    (eW : (mateOpfunctor Φ adj).coalgebraPullback ⋙ G.forget ≅ H.forget ⋙ W)
    (N : Comonad.Coalgebra H) (J : C) :
    AugmentedTowerIso
      (underlyingFunctorCobarLeftContractibleTower H W N J).aug
      (underlyingFunctorCobarLeftContractibleTower H W N J).obj
      (underlyingFunctorCobarLeftContractibleTower H W N J).augMap
      (underlyingFunctorCobarLeftContractibleTower H W N J).face
      (underlyingFunctorCobarLeftContractibleTower H W N J).degeneracy
      ((mateOpfunctor Φ adj).coalgebraPullback.obj N ⟶ G.cofree.obj J)
      (fun n => pullbackCobarObj Φ adj N n ⟶ G.cofree.obj J)
      (fun f => pullbackCobarCoaug Φ adj N ≫ f)
      (fun n i f => pullbackCobarCoface Φ adj N n i ≫ f)
      (fun n j f => pullbackCobarCodegeneracy Φ adj N n j ≫ f) where
  augEquiv := underlyingToCofreeHomEquiv Φ adj W eW N J
  levelEquiv n := underlyingToCofreeHomEquiv Φ adj W eW (comonadCobarObj H N n) J
  comm_aug f :=
    underlyingToCofreeHomEquiv_naturality Φ adj W eW (comonadCobarCoaug H N) J f
  comm_face n i f :=
    underlyingToCofreeHomEquiv_naturality Φ adj W eW (comonadCobarCoface H N n i) J f
  comm_degeneracy n j f :=
    underlyingToCofreeHomEquiv_naturality Φ adj W eW (comonadCobarCodegeneracy H N n j) J f

/-- **Proposition 2.5.2 (Bousfield `G`-Equivalence Step, p. 22, lines 740–747)**:
When `G.forget ∘ α^* ≅ W ∘ H.forget` for a functor `W : D ⥤ C` (such as `W = U ∘ X` on line 742,
or `B(n)_* ⊗_{K(n)_*} -` in Chapter 3), for every `H`-coalgebra `N` and every cofree
`G`-coalgebra `G(J)`, the augmented simplicial hom-tower
`Hom_{C^G}(α^*(H^•(N)), G(J)) → Hom_{C^G}(α^* N, G(J))`
is a `LeftContractibleTower` (hence `α^* N ⟶ α^*(H^•(N))` is a `G`-equivalence in Bousfield's
`G`-resolution model structure). -/
noncomputable def pullbackCobarCofreeLeftContractibleTower
    [HasEqualizers (Comonad.Coalgebra G)]
    (W : D ⥤ C)
    (eW : (mateOpfunctor Φ adj).coalgebraPullback ⋙ G.forget ≅ H.forget ⋙ W)
    (N : Comonad.Coalgebra H) (J : C) :
    LeftContractibleTower.{v₁} :=
  LeftContractibleTower.ofIso
    (underlyingFunctorCobarLeftContractibleTower H W N J)
    (pullbackCobarCofreeHomTowerIso Φ adj W eW N J)

end Section2_5

end ThesisLean
