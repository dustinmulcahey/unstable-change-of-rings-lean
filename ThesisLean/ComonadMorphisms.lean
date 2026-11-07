/-
Copyright (c) 2026 Dustin Mulcahey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Mulcahey
-/
module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Monad.Algebra
public import Mathlib.CategoryTheory.Monad.Kleisli
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Monad.Equalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Chapter 2: The Theory of Comonads (§2.1 – §2.3)

Formalization of Chapter 2 (§2.1–2.3) of Dustin Mulcahey's PhD thesis:
*"An unstable variant of the Morava Change of Rings theorem for K(n) theory"*.

We build on Mathlib's `CategoryTheory.Comonad`, `Comonad.Coalgebra` (`C^G`), and `Cokleisli` (`C_G`)
to formalize:
* **§2.1 Proposition 2.1.1**: The functors `i : C_G ⥤ C^G` and `j : C^G ⥤ C_G` between
  `Comonad.Coalgebra G` and `Cokleisli G`, and full faithfulness of `i`.
* **§2.2 Definition 2.2.1 & Proposition 2.2.1**: Functors of comonads `(F, α) : (C, G) → (D, H)`
  and the induced functor `α_* : Coalgebra G ⥤ Coalgebra H`.
* **§2.2 Definition 2.2.2 & Proposition 2.2.2**: Opfunctors of comonads `(U, β) : (D, H) → (C, G)`
  and the induced functor `β_* : Cokleisli H ⥤ Cokleisli G`.
* **§2.2 Proposition 2.2.3**: Extending `β_*` to Eilenberg-Moore coalgebras
  `Coalgebra H ⥤ Coalgebra G` via the equalizer of
  `(G.map (U.map Y.a), G.δ.app (U.obj Y.A) ≫ G.map (β.app Y.A))`.
* **§2.3 Propositions 2.3.1, 2.3.2, and 2.3.3**: Constructing the mate comonad opfunctor `(U, β)`
  from a comonad functor `(F, α)` along an adjunction `F ⊣ U`, proving the fundamental relations,
  and lifting the adjunction to `α_* ⊣ β_*` between categories of Eilenberg-Moore coalgebras.
-/

set_option linter.style.longLine false

@[expose] public section

namespace ThesisLean

open CategoryTheory Category Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Section2_1

variable (G : Comonad C)

/-- Proposition 2.1.1: The functor `i : C_G ⥤ C^G` sending `X` to the cofree coalgebra `(GX, Δ_X)`.
This is the composite of `Cokleisli.Adjunction.fromCokleisli G : C_G ⥤ C` and
`Comonad.cofree G : C ⥤ C^G`. -/
@[simps, implicit_reducible]
def cokleisliToCoalgebra : Cokleisli G ⥤ Comonad.Coalgebra G where
  obj X :=
    { A := G.obj X.of
      a := G.δ.app X.of
      counit := G.left_counit X.of
      coassoc := (G.coassoc X.of).symm }
  map {X Y} f :=
    { f := G.δ.app X.of ≫ G.map f.of
      h := by
        dsimp
        rw [G.map_comp, G.coassoc_assoc, assoc, G.delta_naturality] }
  map_id X := by
    ext
    dsimp
    exact G.right_counit X.of
  map_comp {X Y Z} f g := by
    ext
    simp [G.coassoc_assoc, G.delta_naturality_assoc]

/-- Proposition 2.1.1: The functor `j : C^G ⥤ C_G` sending `(X, ψ_X)` to `X`.
As shown in the diagram in Proposition 2.1.1 of the thesis (p. 6):
for a coalgebra map `f : (X, ψ_X) → (Y, ψ_Y)`, `j(f) : GX → Y` is `ε_Y ∘ G(f) = f ∘ ε_X`.
Note that the comparison functor `Comonad.comparison (Cokleisli.Adjunction.adj G)` goes in the
opposite direction `C_G ⥤ C^G` (`cokleisliToCoalgebra`), expressing `C_G` as the full subcategory
of cofree coalgebras in `C^G`. -/
@[simps, implicit_reducible]
def coalgebraToCokleisli : Comonad.Coalgebra G ⥤ Cokleisli G where
  obj X := Cokleisli.mk G X.A
  map {X Y} f := ⟨G.ε.app X.A ≫ f.f⟩
  map_id X := by
    ext
    simp
  map_comp {X Y Z} f g := by
    ext
    simp [G.counit_naturality_assoc, G.left_counit_assoc]

/-- The functor `i : C_G ⥤ C^G` (`cokleisliToCoalgebra G`) is fully faithful, exhibiting the
co-Kleisli category `C_G` as the full subcategory of cofree coalgebras in `C^G`. -/
def cokleisliToCoalgebraFullyFaithful : (cokleisliToCoalgebra G).FullyFaithful where
  preimage {X Y} g := ⟨g.f ≫ G.ε.app Y.of⟩
  map_preimage {X Y} g := by
    ext
    have hg : G.δ.app X.of ≫ G.map g.f = g.f ≫ G.δ.app Y.of := g.h
    dsimp
    rw [G.map_comp, reassoc_of% hg, G.right_counit]
    exact comp_id _
  preimage_map {X Y} f := by
    ext
    dsimp
    rw [assoc, G.counit_naturality, ← assoc, G.left_counit, id_comp]

end Section2_1

namespace Section2_2

/-!
## §2.2 Morphisms of comonads and induced functors

We formalize:
* **Definition 2.2.1 (`ComonadFunctor`)**: A functor of comonads `(F, α) : (C, G) → (D, H)`
  consisting of `F : C ⥤ D` and `α : G ⋙ F ⟶ F ⋙ H` (written `F ∘ G → H ∘ F` in traditional
  right-to-left composition) satisfying compatibility with `δ` and `ε`.
* **Proposition 2.2.1 (`ComonadFunctor.pushforward`)**: The induced functor `α_* : C^G ⥤ D^H`
  commuting with the forgetful functors.
* **Definition 2.2.2 (`ComonadOpfunctor`)**: An opfunctor of comonads `(U, β) : (D, H) → (C, G)`
  consisting of `U : D ⥤ C` and `β : U ⋙ G ⟶ H ⋙ U` (`G ∘ U → U ∘ H`).
* **Proposition 2.2.2 (`ComonadOpfunctor.cokleisliPushforward`)**: The induced functor
  `β_* : D_H ⥤ C_G` on co-Kleisli categories.
* **Proposition 2.2.3 (`ComonadOpfunctor.coalgebraPullback`)**: Extending `β_*` to a functor
  `α^* = β_* : D^H ⥤ C^G` on Eilenberg-Moore coalgebras via the equalizer of
  `(G.map (U.map Y.a), G.δ.app (U.obj Y.A) ≫ G.map (β.app Y.A))`.
-/

/-- Definition 2.2.1: A functor of comonads `(F, α) : (C, G) → (D, H)` consists of a functor
`F : C ⥤ D` and a natural transformation `α : G ⋙ F ⟶ F ⋙ H` (`F ∘ G → H ∘ F`) compatible
with comultiplication and counit:
1. `α_X ≫ Δ^H_{FX} = F(Δ^G_X) ≫ α_{GX} ≫ H(α_X)`
2. `α_X ≫ ε^H_{FX} = F(ε^G_X)` -/
structure ComonadFunctor (G : Comonad C) (H : Comonad D) where
  /-- The underlying functor `F : C ⥤ D`. -/
  F : C ⥤ D
  /-- The natural transformation `α : F ∘ G ⟶ H ∘ F`. -/
  α : (G : C ⥤ C) ⋙ F ⟶ F ⋙ (H : D ⥤ D)
  /-- Condition (1) of Definition 2.2.1: compatibility with comultiplication `Δ`. -/
  comm_δ (X : C) :
    α.app X ≫ H.δ.app (F.obj X) =
      F.map (G.δ.app X) ≫ α.app (G.obj X) ≫ H.map (α.app X) := by cat_disch
  /-- Condition (2) of Definition 2.2.1: compatibility with counit `ε`. -/
  comm_ε (X : C) :
    α.app X ≫ H.ε.app (F.obj X) = F.map (G.ε.app X) := by cat_disch

attribute [reassoc] ComonadFunctor.comm_δ ComonadFunctor.comm_ε

namespace ComonadFunctor

variable {G : Comonad C} {H : Comonad D} (Φ : ComonadFunctor G H)

/-- Proposition 2.2.1: A functor of comonads `(F, α) : (C, G) → (D, H)` induces a functor
`α_* : C^G ⥤ D^H` sending `(X, ψ_X)` to `(FX, α_X ∘ F(ψ_X))`. -/
@[simps, implicit_reducible]
def pushforward : Comonad.Coalgebra G ⥤ Comonad.Coalgebra H where
  obj X :=
    { A := Φ.F.obj X.A
      a := Φ.F.map X.a ≫ Φ.α.app X.A
      counit := by
        rw [assoc, Φ.comm_ε, ← Φ.F.map_comp, X.counit, Φ.F.map_id]
      coassoc := by
        have hα := Φ.α.naturality X.a
        dsimp at hα
        rw [assoc, Φ.comm_δ, ← assoc (Φ.F.map X.a), ← Φ.F.map_comp, X.coassoc,
          Φ.F.map_comp, assoc, assoc, H.map_comp, ← reassoc_of% hα] }
  map {X X'} f :=
    { f := Φ.F.map f.f
      h := by
        have hα := Φ.α.naturality f.f
        dsimp at hα ⊢
        rw [assoc, ← hα, ← assoc, ← Φ.F.map_comp, f.h, Φ.F.map_comp, assoc] }

/-- Proposition 2.2.1: The diagram of `α_*` and the forgetful functors commutes strictly. -/
@[simps!]
def pushforwardCommForget : Φ.pushforward ⋙ Comonad.forget H ≅ Comonad.forget G ⋙ Φ.F :=
  Iso.refl _

end ComonadFunctor

/-- Definition 2.2.2: An opfunctor of comonads `(U, β) : (D, H) → (C, G)` consists of a functor
`U : D ⥤ C` and a natural transformation `β : U ⋙ G ⟶ H ⋙ U` (`G ∘ U → U ∘ H`) such that:
1. `β_Y ≫ U(Δ^H_Y) = Δ^G_{UY} ≫ G(β_Y) ≫ β_{HY}`
2. `β_Y ≫ U(ε^H_Y) = ε^G_{UY}` -/
structure ComonadOpfunctor (H : Comonad D) (G : Comonad C) where
  /-- The underlying functor `U : D ⥤ C`. -/
  U : D ⥤ C
  /-- The natural transformation `β : G ∘ U ⟶ U ∘ H`. -/
  β : U ⋙ (G : C ⥤ C) ⟶ (H : D ⥤ D) ⋙ U
  /-- Condition (1) of Definition 2.2.2: compatibility with comultiplication `Δ`. -/
  comm_δ (Y : D) :
    β.app Y ≫ U.map (H.δ.app Y) =
      G.δ.app (U.obj Y) ≫ G.map (β.app Y) ≫ β.app (H.obj Y) := by cat_disch
  /-- Condition (2) of Definition 2.2.2: compatibility with counit `ε`. -/
  comm_ε (Y : D) :
    β.app Y ≫ U.map (H.ε.app Y) = G.ε.app (U.obj Y) := by cat_disch

attribute [reassoc] ComonadOpfunctor.comm_δ ComonadOpfunctor.comm_ε

namespace ComonadOpfunctor

variable {H : Comonad D} {G : Comonad C} (Ψ : ComonadOpfunctor H G)

/-- Proposition 2.2.2: A comonad opfunctor `(U, β) : (D, H) → (C, G)` induces a functor
`β_* : D_H ⥤ C_G` on co-Kleisli categories sending `Y` to `UY` and `(f : HY → Y')` to
`U(f) ∘ β_Y : GUY → UY'`. -/
@[simps, implicit_reducible]
def cokleisliPushforward : Cokleisli H ⥤ Cokleisli G where
  obj Y := Cokleisli.mk G (Ψ.U.obj Y.of)
  map {Y Y'} f := ⟨Ψ.β.app Y.of ≫ Ψ.U.map f.of⟩
  map_id Y := by
    ext
    simp [Ψ.comm_ε]
  map_comp {Y Y' Y''} f g := by
    ext
    have hβ := Ψ.β.naturality f.of
    dsimp at hβ
    simp [Ψ.comm_δ_assoc, reassoc_of% hβ]

/-- Proposition 2.2.2: The induced functor `β_* : D_H ⥤ C_G` commutes with the canonical functors
from the base categories `D ⥤ D_H` and `C ⥤ C_G`. -/
@[simps!]
def cokleisliPushforwardCommToCokleisli :
    Cokleisli.Adjunction.toCokleisli H ⋙ Ψ.cokleisliPushforward ≅
      Ψ.U ⋙ Cokleisli.Adjunction.toCokleisli G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {Y Y'} f => by
    ext
    simp [Ψ.comm_ε_assoc])

/-!
### Proposition 2.2.3: Extending `β_*` from the co-Kleisli category to Eilenberg-Moore coalgebras

Given an opfunctor of comonads `(U, β) : (D, H) → (C, G)` and an `H`-coalgebra `(Y, ψ_Y)`,
we consider the parallel pair of morphisms in `C^G` between cofree `G`-coalgebras:
`topMap Y : (G(UY), Δ_{UY}) ⟶ (G(U(HY)), Δ_{U(HY)})` given by `G(U(ψ_Y))`, and
`bottomMap Y : (G(UY), Δ_{UY}) ⟶ (G(U(HY)), Δ_{U(HY)})` given by `Δ^G_{UY} ≫ G(β_Y)`.
In `C`, their equalizer (when `C` has equalizers and `G` preserves them, or directly as the
equalizer in `C^G`) yields the extended functor `β_* : D^H ⥤ C^G`.
-/

/-- The first ("top") morphism `G(U(ψ_Y)) : (GUY, Δ_{UY}) ⟶ (GUHY, Δ_{UHY})` of cofree `G`-coalgebras
in Proposition 2.2.3. -/
@[simps!]
def pullbackTopMap (Y : Comonad.Coalgebra H) :
    (Comonad.cofree G).obj (Ψ.U.obj Y.A) ⟶ (Comonad.cofree G).obj (Ψ.U.obj (H.obj Y.A)) :=
  (Comonad.cofree G).map (Ψ.U.map Y.a)

/-- The second ("bottom") morphism `G(β_Y) ∘ Δ^G_{UY} : (GUY, Δ_{UY}) ⟶ (GUHY, Δ_{UHY})` of cofree
`G`-coalgebras in Proposition 2.2.3. -/
@[simps]
def pullbackBottomMap (Y : Comonad.Coalgebra H) :
    (Comonad.cofree G).obj (Ψ.U.obj Y.A) ⟶ (Comonad.cofree G).obj (Ψ.U.obj (H.obj Y.A)) where
  f := G.δ.app (Ψ.U.obj Y.A) ≫ G.map (Ψ.β.app Y.A)
  h := by
    dsimp
    rw [G.map_comp, G.coassoc_assoc, assoc, G.delta_naturality]

/-- Naturality of `pullbackTopMap` with respect to a morphism `f : Y ⟶ Y'` of `H`-coalgebras. -/
@[reassoc]
lemma pullbackTopMap_naturality {Y Y' : Comonad.Coalgebra H} (f : Y ⟶ Y') :
    (Comonad.cofree G).map (Ψ.U.map f.f) ≫ Ψ.pullbackTopMap Y' =
      Ψ.pullbackTopMap Y ≫ (Comonad.cofree G).map (Ψ.U.map (H.map f.f)) := by
  ext
  dsimp [pullbackTopMap]
  rw [← G.map_comp, ← Ψ.U.map_comp, ← f.h, Ψ.U.map_comp, G.map_comp]

/-- Naturality of `pullbackBottomMap` with respect to a morphism `f : Y ⟶ Y'` of `H`-coalgebras. -/
@[reassoc]
lemma pullbackBottomMap_naturality {Y Y' : Comonad.Coalgebra H} (f : Y ⟶ Y') :
    (Comonad.cofree G).map (Ψ.U.map f.f) ≫ Ψ.pullbackBottomMap Y' =
      Ψ.pullbackBottomMap Y ≫ (Comonad.cofree G).map (Ψ.U.map (H.map f.f)) := by
  ext
  have hβ := Ψ.β.naturality f.f
  dsimp [pullbackBottomMap] at hβ ⊢
  rw [G.delta_naturality_assoc, ← G.map_comp, hβ, G.map_comp, assoc]

/-- Proposition 2.2.3: When `Comonad.Coalgebra G` has equalizers (for instance, when `C` has
equalizers and `G` preserves them), the opfunctor `(U, β)` induces a functor
`β_* : Comonad.Coalgebra H ⥤ Comonad.Coalgebra G` (also denoted `α^*` in §2.3) defined by taking
the equalizer of `(pullbackTopMap Y, pullbackBottomMap Y)`. -/
@[simps, implicit_reducible]
noncomputable def coalgebraPullback [HasEqualizers (Comonad.Coalgebra G)] :
    Comonad.Coalgebra H ⥤ Comonad.Coalgebra G where
  obj Y := equalizer (Ψ.pullbackTopMap Y) (Ψ.pullbackBottomMap Y)
  map {Y Y'} f :=
    equalizer.lift
      (equalizer.ι (Ψ.pullbackTopMap Y) (Ψ.pullbackBottomMap Y) ≫
        (Comonad.cofree G).map (Ψ.U.map f.f))
      (by
        rw [assoc, Ψ.pullbackTopMap_naturality, ← assoc, equalizer.condition, assoc,
          ← Ψ.pullbackBottomMap_naturality f, assoc])
  map_id Y := by
    apply equalizer.hom_ext
    simp
  map_comp {Y Y' Y''} f g := by
    apply equalizer.hom_ext
    simp

end ComonadOpfunctor

end Section2_2

namespace Section2_3

open Section2_2

/-!
## §2.3 Induced Adjunctions

Suppose `F : C ⥤ D` and `U : D ⥤ C` form an adjunction `adj : F ⊣ U` (with unit `σ = adj.unit`
and counit `τ = adj.counit`), `G` is a comonad on `C`, `H` is a comonad on `D`, and
`Φ = (F, α) : (C, G) → (D, H)` is a functor of comonads.

We formalize:
* **Proposition 2.3.1 (`mateOpfunctor`)**: The induced mate natural transformation
  `β_Y = σ_{GUY} ≫ U(α_{UY}) ≫ U(H(τ_Y)) : G(U(Y)) ⟶ U(H(Y))` makes `(U, β)` a comonad opfunctor.
* **Proposition 2.3.2 (`mate_fundamental_rel_counit` & `mate_fundamental_rel_unit`)**:
  The fundamental relations:
  - `F(β_Y) ≫ τ_{HY} = α_{UY} ≫ H(τ_Y)` (Proposition 2.3.2, p. 11)
  - `G(σ_X) ≫ β_{FX} = σ_{GX} ≫ U(α_X)` (used in Proposition 2.3.3, p. 14)
* **Proposition 2.3.3 (`liftedAdjunction`)**: When `Comonad.Coalgebra G` has equalizers,
  `α_* : Comonad.Coalgebra G ⥤ Comonad.Coalgebra H` is left adjoint to
  `α^* = β_* : Comonad.Coalgebra H ⥤ Comonad.Coalgebra G`.
-/

variable {G : Comonad C} {H : Comonad D}
variable (Φ : ComonadFunctor G H) {U : D ⥤ C} (adj : Φ.F ⊣ U)

/-- The mate natural transformation `β : U ⋙ G ⟶ H ⋙ U` defined in Proposition 2.3.1 (p. 11):
`β_Y : G(U(Y)) ⟶ U(F(G(U(Y)))) ⟶ U(H(F(U(Y)))) ⟶ U(H(Y))`
via `σ_{GUY} ≫ U(α_{UY}) ≫ U(H(τ_Y))`. -/
@[simps]
def mateNatTrans : U ⋙ (G : C ⥤ C) ⟶ (H : D ⥤ D) ⋙ U where
  app Y := adj.unit.app (G.obj (U.obj Y)) ≫ U.map (Φ.α.app (U.obj Y)) ≫ U.map (H.map (adj.counit.app Y))
  naturality {Y Y'} f := by
    have hσ := adj.unit.naturality (G.map (U.map f))
    have hα := Φ.α.naturality (U.map f)
    have hτ := adj.counit.naturality f
    dsimp at hσ hα hτ ⊢
    rw [reassoc_of% hσ, ← U.map_comp_assoc, hα, U.map_comp_assoc,
      ← U.map_comp, ← H.map_comp, hτ, H.map_comp, U.map_comp, assoc, assoc]

/-- Proposition 2.3.2 (p. 11): The fundamental relation governing `τ, α, β, F, U, G, H`:
`F(β_Y) ≫ τ_{HY} = α_{UY} ≫ H(τ_Y)`. -/
@[reassoc]
lemma mate_fundamental_rel_counit (Y : D) :
    Φ.F.map ((mateNatTrans Φ adj).app Y) ≫ adj.counit.app (H.obj Y) =
      Φ.α.app (U.obj Y) ≫ H.map (adj.counit.app Y) := by
  dsimp [mateNatTrans]
  have h1 := adj.counit.naturality (Φ.α.app (U.obj Y))
  have h2 := adj.counit.naturality (H.map (adj.counit.app Y))
  dsimp at h1 h2
  rw [Φ.F.map_comp, Φ.F.map_comp, assoc, assoc, h2, ← assoc (Φ.F.map (U.map _)), h1,
    assoc, reassoc_of% (adj.left_triangle_components (G.obj (U.obj Y)))]

/-- The dual fundamental relation governing the unit `σ` (used in Proposition 2.3.3, p. 14):
`G(σ_X) ≫ β_{FX} = σ_{GX} ≫ U(α_X)`. -/
@[reassoc]
lemma mate_fundamental_rel_unit (X : C) :
    G.map (adj.unit.app X) ≫ (mateNatTrans Φ adj).app (Φ.F.obj X) =
      adj.unit.app (G.obj X) ≫ U.map (Φ.α.app X) := by
  dsimp [mateNatTrans]
  have h1 := adj.unit.naturality (G.map (adj.unit.app X))
  have h2 := Φ.α.naturality (adj.unit.app X)
  dsimp at h1 h2
  rw [reassoc_of% h1, ← U.map_comp_assoc, h2, U.map_comp_assoc,
    ← U.map_comp, ← H.map_comp, adj.left_triangle_components, H.map_id, U.map_id, comp_id]

/-- Proposition 2.3.1 (p. 11): Given a comonad functor `(F, α) : (C, G) → (D, H)` and a right
adjoint `U` to `F`, the mate `(U, β)` is a comonad opfunctor `(D, H) → (C, G)`. -/
@[simps, implicit_reducible]
def mateOpfunctor : ComonadOpfunctor H G where
  U := U
  β := mateNatTrans Φ adj
  comm_δ Y := by
    -- Following the thesis proof (p. 12): we prove equality in `C` using `adj.homEquiv`
    -- (i.e. adjointing both sides to `D` and verifying they are equal).
    apply (adj.homEquiv (G.obj (U.obj Y)) (H.obj (H.obj Y))).symm.injective
    dsimp [Adjunction.homEquiv]
    have hrel := mate_fundamental_rel_counit Φ adj
    have hτδ := adj.counit.naturality (H.δ.app Y)
    have hαβ := Φ.α.naturality ((mateNatTrans Φ adj).app Y)
    dsimp at hτδ hαβ
    rw [Φ.F.map_comp, assoc, hτδ, reassoc_of% (hrel Y), H.delta_naturality]
    rw [Φ.F.map_comp, Φ.F.map_comp, assoc, assoc, hrel (H.obj Y),
      ← assoc (Φ.F.map (G.map _)), hαβ,
      reassoc_of% (Φ.comm_δ (U.obj Y)),
      assoc, ← H.map_comp, ← hrel Y, H.map_comp]
  comm_ε Y := by
    apply (adj.homEquiv (G.obj (U.obj Y)) Y).symm.injective
    dsimp [Adjunction.homEquiv]
    have hrel := mate_fundamental_rel_counit Φ adj Y
    have hτε := adj.counit.naturality (H.ε.app Y)
    dsimp at hτε
    rw [Φ.F.map_comp, assoc, hτε, reassoc_of% hrel, H.counit_naturality,
      Φ.comm_ε_assoc]

/-!
### Proposition 2.3.3: Lifting the Adjunction to Coalgebra Categories

Suppose `Φ = (F, α) : (C, G) → (D, H)` is a comonad functor, `adj : F ⊣ U`, and `Comonad.Coalgebra G`
has equalizers so that `(mateOpfunctor Φ adj).coalgebraPullback : Comonad.Coalgebra H ⥤ Comonad.Coalgebra G`
is defined. Then `Φ.pushforward ⊣ (mateOpfunctor Φ adj).coalgebraPullback`.

We construct both the explicit unit `σ̃_X` (pp. 13–14) and the adjunction `liftedAdjunction`
(Proposition 2.3.3, pp. 13–15).
-/

variable [HasEqualizers (Comonad.Coalgebra G)]

/-- Given any morphism `g : Φ.pushforward.obj X ⟶ Y` in `D^H`, its mate `X.A ⟶ U.obj Y.A`
composed with `Comonad.CofreeEqualizer.ι X` gives a coalgebra map `X ⟶ G.cofree.obj (U.obj Y.A)`. -/
@[simps!]
def homToCofreeMate {X : Comonad.Coalgebra G} {Y : Comonad.Coalgebra H}
    (g : Φ.pushforward.obj X ⟶ Y) :
    X ⟶ (Comonad.cofree G).obj ((mateOpfunctor Φ adj).U.obj Y.A) :=
  Comonad.CofreeEqualizer.ι X ≫ (Comonad.cofree G).map (adj.homEquiv X.A Y.A g.f)

omit [HasEqualizers (Comonad.Coalgebra G)] in
/-- The coalgebra map `homToCofreeMate Φ adj g` equalizes `pullbackTopMap Y` and `pullbackBottomMap Y`. -/
lemma homToCofreeMate_condition {X : Comonad.Coalgebra G} {Y : Comonad.Coalgebra H}
    (g : Φ.pushforward.obj X ⟶ Y) :
    homToCofreeMate Φ adj g ≫ (mateOpfunctor Φ adj).pullbackTopMap Y =
      homToCofreeMate Φ adj g ≫ (mateOpfunctor Φ adj).pullbackBottomMap Y := by
  have hg : (Φ.F.map X.a ≫ Φ.α.app X.A) ≫ H.map g.f = g.f ≫ Y.a := g.h
  ext
  simp only [Comonad.Coalgebra.comp_f, homToCofreeMate_f,
    ComonadOpfunctor.pullbackTopMap_f, ComonadOpfunctor.pullbackBottomMap_f,
    mateOpfunctor_U, mateOpfunctor_β]
  dsimp [Adjunction.homEquiv]
  have hunit := adj.unit.naturality X.a
  have hrel := mate_fundamental_rel_unit Φ adj X.A
  have hβ := (mateNatTrans Φ adj).naturality g.f
  dsimp at hunit hrel hβ
  rw [assoc, assoc, G.delta_naturality_assoc, X.coassoc_assoc,
    ← G.map_comp, ← G.map_comp, ← G.map_comp]
  congr 2
  rw [assoc, G.map_comp, assoc, hβ, ← assoc (G.map (adj.unit.app X.A)), hrel,
    assoc, reassoc_of% hunit, ← U.map_comp, ← U.map_comp, ← U.map_comp,
    ← assoc (Φ.F.map X.a), hg]

/-- The lifted unit `σ̃_X : X ⟶ α^*(α_* X)` of Proposition 2.3.3 (p. 13), induced by applying
`homToCofreeMate` to `𝟙 (α_* X)`. -/
noncomputable def liftedUnitApp (X : Comonad.Coalgebra G) :
    X ⟶ (mateOpfunctor Φ adj).coalgebraPullback.obj (Φ.pushforward.obj X) :=
  equalizer.lift (homToCofreeMate Φ adj (𝟙 (Φ.pushforward.obj X)))
    (homToCofreeMate_condition Φ adj (𝟙 (Φ.pushforward.obj X)))

/-- Conversely, given a morphism `k : X ⟶ α^* Y` in `C^G`, we compose with the equalizer inclusion
`α^* Y ⟶ G(U(Y))` and the counit `ε^G_{UY} : G(U(Y)) ⟶ U(Y)` in `C`, then take the left adjoint
transpose `F(X) ⟶ Y` in `D`. -/
@[implicit_reducible]
noncomputable def cofreeMateToHomUnderlying {X : Comonad.Coalgebra G} {Y : Comonad.Coalgebra H}
    (k : X ⟶ (mateOpfunctor Φ adj).coalgebraPullback.obj Y) :
    Φ.F.obj X.A ⟶ Y.A :=
  (adj.homEquiv X.A Y.A).symm
    ((k ≫ equalizer.ι ((mateOpfunctor Φ adj).pullbackTopMap Y)
      ((mateOpfunctor Φ adj).pullbackBottomMap Y)).f ≫ G.ε.app (U.obj Y.A))

/-- Key identity in `C` for a coalgebra map `s : X ⟶ G.cofree.obj (U.obj Y.A)` that equalizes
`(pullbackTopMap Y, pullbackBottomMap Y)`: its mate `m = s.f ≫ ε^G_{UY}` satisfies
`m ≫ U(ψ_Y) = X.a ≫ G(m) ≫ β_Y`. -/
lemma mate_equalizer_identity {X : Comonad.Coalgebra G} {Y : Comonad.Coalgebra H}
    (k : X ⟶ (mateOpfunctor Φ adj).coalgebraPullback.obj Y) :
    let s := k ≫ equalizer.ι ((mateOpfunctor Φ adj).pullbackTopMap Y)
      ((mateOpfunctor Φ adj).pullbackBottomMap Y)
    (s.f ≫ G.ε.app (U.obj Y.A)) ≫ U.map Y.a =
      X.a ≫ G.map (s.f ≫ G.ε.app (U.obj Y.A)) ≫ (mateNatTrans Φ adj).app Y.A := by
  intro s
  have hs_cond : s.f ≫ G.map (U.map Y.a) =
      s.f ≫ G.δ.app (U.obj Y.A) ≫ G.map ((mateNatTrans Φ adj).app Y.A) := by
    have h := congrArg Comonad.Coalgebra.Hom.f
      (k ≫= equalizer.condition ((mateOpfunctor Φ adj).pullbackTopMap Y)
        ((mateOpfunctor Φ adj).pullbackBottomMap Y))
    simp only [Comonad.Coalgebra.comp_f,
      ComonadOpfunctor.pullbackTopMap_f, ComonadOpfunctor.pullbackBottomMap_f,
      mateOpfunctor_U, mateOpfunctor_β] at h
    simpa [s, assoc] using h
  have hs_coalg : X.a ≫ G.map s.f = s.f ≫ G.δ.app (U.obj Y.A) := s.h
  have hs_rel : X.a ≫ G.map (s.f ≫ G.ε.app (U.obj Y.A)) = s.f := by
    rw [G.map_comp, ← assoc, hs_coalg, assoc, G.right_counit]
    exact comp_id _
  have hcounit2 := G.ε.naturality ((mateNatTrans Φ adj).app Y.A)
  dsimp at hcounit2
  rw [← assoc (X.a), hs_rel, assoc, ← G.counit_naturality,
    ← assoc, hs_cond, assoc, assoc, hcounit2,
    ← assoc (G.δ.app _), G.left_counit, id_comp]

/-- The underlying map `cofreeMateToHomUnderlying Φ adj k` is a morphism of `H`-coalgebras
`α_* X ⟶ Y` (corresponding to the counit diagram on p. 14 of the thesis). -/
lemma cofreeMateToHomUnderlying_is_coalgebra_hom {X : Comonad.Coalgebra G} {Y : Comonad.Coalgebra H}
    (k : X ⟶ (mateOpfunctor Φ adj).coalgebraPullback.obj Y) :
    (Φ.F.map X.a ≫ Φ.α.app X.A) ≫ H.map (cofreeMateToHomUnderlying Φ adj k) =
      cofreeMateToHomUnderlying Φ adj k ≫ Y.a := by
  let s := k ≫ equalizer.ι ((mateOpfunctor Φ adj).pullbackTopMap Y)
    ((mateOpfunctor Φ adj).pullbackBottomMap Y)
  let m : X.A ⟶ U.obj Y.A := s.f ≫ G.ε.app (U.obj Y.A)
  have hm : m ≫ U.map Y.a = X.a ≫ G.map m ≫ (mateNatTrans Φ adj).app Y.A :=
    mate_equalizer_identity Φ adj k
  unfold cofreeMateToHomUnderlying
  dsimp [Adjunction.homEquiv]
  change (Φ.F.map X.a ≫ Φ.α.app X.A) ≫ H.map (Φ.F.map m ≫ adj.counit.app Y.A) =
    (Φ.F.map m ≫ adj.counit.app Y.A) ≫ Y.a
  have hτ := adj.counit.naturality Y.a
  have hα := Φ.α.naturality m
  have hrel := mate_fundamental_rel_counit Φ adj Y.A
  dsimp at hτ hα
  symm
  rw [assoc, ← hτ, ← assoc, ← Φ.F.map_comp, hm,
    Φ.F.map_comp, Φ.F.map_comp, assoc, assoc, hrel,
    ← assoc (Φ.F.map (G.map m)), hα, assoc, ← H.map_comp, ← assoc]

/-- Forward direction of the lifted adjunction hom-equivalence `Hom_{D^H}(α_* X, Y) → Hom_{C^G}(X, α^* Y)`. -/
@[implicit_reducible]
noncomputable def liftedHomEquivToFun {X : Comonad.Coalgebra G} {Y : Comonad.Coalgebra H}
    (g : Φ.pushforward.obj X ⟶ Y) :
    X ⟶ (mateOpfunctor Φ adj).coalgebraPullback.obj Y :=
  equalizer.lift (homToCofreeMate Φ adj g) (homToCofreeMate_condition Φ adj g)

/-- Inverse direction of the lifted adjunction hom-equivalence `Hom_{C^G}(X, α^* Y) → Hom_{D^H}(α_* X, Y)`. -/
@[simps, implicit_reducible]
noncomputable def liftedHomEquivInvFun {X : Comonad.Coalgebra G} {Y : Comonad.Coalgebra H}
    (k : X ⟶ (mateOpfunctor Φ adj).coalgebraPullback.obj Y) :
    Φ.pushforward.obj X ⟶ Y where
  f := cofreeMateToHomUnderlying Φ adj k
  h := cofreeMateToHomUnderlying_is_coalgebra_hom Φ adj k

/-- Proposition 2.3.3 (pp. 13–15): Under the hypotheses that `F ⊣ U`, `(F, α) : (C, G) → (D, H)` is a
functor of comonads, and `Comonad.Coalgebra G` has equalizers so that `β_* = α^*` extends to
`Comonad.Coalgebra H ⥤ Comonad.Coalgebra G`, `α_*` (`Φ.pushforward`) is left adjoint to
`β_*` (`(mateOpfunctor Φ adj).coalgebraPullback`). -/
noncomputable def liftedAdjunction :
    Φ.pushforward ⊣ (mateOpfunctor Φ adj).coalgebraPullback :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := liftedHomEquivToFun Φ adj
          invFun := liftedHomEquivInvFun Φ adj
          left_inv := fun g => by
            ext
            dsimp [liftedHomEquivInvFun, cofreeMateToHomUnderlying, liftedHomEquivToFun]
            have hι := congrArg Comonad.Coalgebra.Hom.f
              (equalizer.lift_ι (homToCofreeMate Φ adj g) (homToCofreeMate_condition Φ adj g))
            simp only [Comonad.Coalgebra.comp_f, homToCofreeMate_f] at hι
            rw [hι, assoc, G.counit_naturality,
              ← assoc (X.a), X.counit, id_comp, Equiv.symm_apply_apply]
          right_inv := fun k => by
            apply equalizer.hom_ext
            have hι := equalizer.lift_ι
              (homToCofreeMate Φ adj (liftedHomEquivInvFun Φ adj k))
              (homToCofreeMate_condition Φ adj (liftedHomEquivInvFun Φ adj k))
            change liftedHomEquivToFun Φ adj (liftedHomEquivInvFun Φ adj k) ≫ _ = _ at hι
            rw [hι]
            ext
            dsimp [homToCofreeMate, liftedHomEquivInvFun, cofreeMateToHomUnderlying]
            rw [Equiv.apply_symm_apply]
            let s := k ≫ equalizer.ι ((mateOpfunctor Φ adj).pullbackTopMap Y)
              ((mateOpfunctor Φ adj).pullbackBottomMap Y)
            have hs : X.a ≫ G.map s.f = s.f ≫ G.δ.app (U.obj Y.A) := s.h
            have hgoal : X.a ≫ G.map (s.f ≫ G.ε.app (U.obj Y.A)) = s.f := by
              rw [G.map_comp, ← assoc, hs, assoc, G.right_counit]
              exact comp_id _
            exact hgoal }
      homEquiv_naturality_left_symm := fun {X' X Y} h k => by
        ext
        dsimp [liftedHomEquivInvFun, cofreeMateToHomUnderlying]
        rw [← Adjunction.homEquiv_naturality_left_symm]
        congr 1
        simp only [assoc]
      homEquiv_naturality_right := fun {X Y Y'} g h => by
        apply equalizer.hom_ext
        dsimp [liftedHomEquivToFun, ComonadOpfunctor.coalgebraPullback]
        rw [equalizer.lift_ι, assoc, equalizer.lift_ι, ← assoc, equalizer.lift_ι]
        ext
        dsimp [homToCofreeMate]
        rw [Adjunction.homEquiv_naturality_right, G.map_comp, assoc] }

end Section2_3

end ThesisLean
