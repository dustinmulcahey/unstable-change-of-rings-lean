/-
Copyright (c) 2026 Dustin Mulcahey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dustin Mulcahey
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import ThesisLean.CobarResolution

/-!
# Chapter 3: An Unstable Change of Rings (§3.1 – §3.2)

Formalization of Chapter 3 of Dustin Mulcahey's PhD thesis:
*"An unstable variant of the Morava Change of Rings theorem for K(n) theory"*.

We formalize:
* **§3.1 The Stable Case & Canonical Coalgebra Equalizers**:
  - For any comonad `H` on `D` and any `H`-coalgebra `(N, ψ_N)`, the diagram
    `N ⟶ H(N) ⇉ H^2(N)` with maps `ψ_N` and `(H(ψ_N), Δ^H_N)` is a split equalizer in `D`
    (with retractions `ε^H_N` and `ε^H_{HN}`) and an equalizer in `D^H`.
  - Application of Generalized Shapiro's Lemma to the stable Hopf algebroid change-of-rings
    adjunction `π_* ⊣ π^*`.
* **§3.2.2 The Comonad `U_Σ` of Unstable `Σ(n)`-Comodules (Definition 3.2.1 & Theorem 3.2.1)**:
  - Given a comonad `U_Γ` on `C` (representing `BP_*`-modules) and an adjunction
    `adj : F ⊣ U` between `C` and `D` (where `F = K(n)_* ⊗_{BP_*} -` and `U` is restriction of
    scalars) whose counit `τ : F ⋙ U ⟶ 𝟭 D` is an isomorphism (`K(n)_* ⊗_{BP_*} N ≅ N`),
    we define the functor `U_Σ = U ⋙ U_Γ ⋙ F : D ⥤ D`, the counit
    `ε^Σ_N = F(ε^Γ_{UN}) ≫ τ_N`, and the comultiplication
    `Δ^Σ_N = F(Δ^Γ_{UN}) ≫ F(U_Γ(σ_{U_Γ UN}))`, and prove **Theorem 3.2.1**:
    `U_Σ` is a comonad on `D`.
* **§3.2.3 The Morphism of Comonads `U_Γ → U_Σ` (Definition 3.2.2 & Theorem 3.2.2)**:
  - We define `α_M = F(U_Γ(σ_M)) : F(U_Γ M) ⟶ U_Σ(F M)` and prove **Theorem 3.2.2**:
    `(F, α)` is a functor of comonads `(C, U_Γ) → (D, U_Σ)`.
* **§3.2.4 The Unstable Cotensor `α^*` (Theorem 3.2.3)**:
  - We prove that the mate natural transformation `β_N : U_Γ(U N) ⟶ U(U_Σ N)` of `(F, α)`
    simplifies to the adjunction unit `σ_{U_Γ(U N)}` (`π ⊗ 1` on line 1044 of the thesis),
    and deduce **Theorem 3.2.3**: `α_* : C^{U_Γ} ⥤ D^{U_Σ}` has a right adjoint
    `α^* : D^{U_Σ} ⥤ C^{U_Γ}` given by the equalizer of `U_Γ(U ψ_N)` and `Δ^Γ_{UN} ≫ U_Γ(β_N)`.
* **§3.2.5 The Counit of the Adjunction (Theorem 3.2.4)**:
  - We prove that applying `F` to the defining equalizer pair of `α^* N` yields the canonical
    `U_Σ`-coalgebra equalizer pair `(U_Σ(ψ_N), Δ^Σ_N) : U_Σ(N) ⇉ U_Σ^2(N)`, whose equalizer is
    `(N, ψ_N)`.
* **§3.2.6 The Unit & Unstable Change of Rings (Propositions 3.2.2–3.2.5 & Theorem 3.2.5)**:
  - When `M` is a `U_Γ`-comodule of height `n` and connectivity `≥ 2p^n + 1`, the lifted unit
    `σ̃_M : M ⟶ α^* α_* M` is an isomorphism of `U_Γ`-comodules (**Proposition 3.2.5**).
  - Combining this isomorphism with Generalized Shapiro's Lemma (`generalizedShapiroCobarIso`)
    yields **Theorem 3.2.5 (Unstable Change of Rings)**:
    `Ext_{U_Γ}(BP_*, M) ≃ Ext_{U_Σ}(K(n)_*, K(n)_* ⊗_{BP_*} M)`.
-/

set_option linter.style.longLine false

@[expose] public section

namespace ThesisLean

open CategoryTheory Category Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-!
## §3.1 The Stable Case & Canonical Equalizer Presentations of Coalgebras
-/

namespace Section3_1

open Section2_2 Section2_3 Section2_4 Section2_5

section CanonicalCoalgebraEqualizer

variable (H : Comonad D) (N : Comonad.Coalgebra H)

/-- For any `H`-coalgebra `(N, ψ_N)`, the coaction `ψ_N : N ⟶ H.cofree.obj N.A` is a morphism
of `H`-coalgebras (`(inducedMonadOnCoalgebras H).η.app N`). -/
@[implicit_reducible]
def coalgebraCoactionHom : N ⟶ H.cofree.obj N.A :=
  (inducedMonadOnCoalgebras H).η.app N

/-- The first ("top") parallel morphism `H(ψ_N) : H(N) ⟶ H^2(N)` in the canonical equalizer
presentation of an `H`-coalgebra `(N, ψ_N)` (line 1097 of the thesis). -/
@[implicit_reducible]
def coalgebraCanonicalTop : H.cofree.obj N.A ⟶ H.cofree.obj (H.obj N.A) :=
  H.cofree.map N.a

/-- The second ("bottom") parallel morphism `Δ^H_N : H(N) ⟶ H^2(N)` in the canonical equalizer
presentation of an `H`-coalgebra `(N, ψ_N)` (line 1097 of the thesis). -/
@[implicit_reducible]
def coalgebraCanonicalBottom : H.cofree.obj N.A ⟶ H.cofree.obj (H.obj N.A) :=
  (inducedMonadOnCoalgebras H).η.app (H.cofree.obj N.A)

/-- The coaction `ψ_N : N ⟶ H(N)` equalizes `H(ψ_N)` and `Δ^H_N` in `Comonad.Coalgebra H`. -/
@[reassoc]
lemma coalgebraCoactionHom_condition :
    coalgebraCoactionHom H N ≫ coalgebraCanonicalTop H N =
      coalgebraCoactionHom H N ≫ coalgebraCanonicalBottom H N := by
  ext
  exact N.coassoc.symm

/-- Moreover, in the underlying category `D`, the fork `N.A ⟶ H(N.A) ⇉ H^2(N.A)` is a
split equalizer (split by `ε^H_{N.A}` and `ε^H_{H(N.A)}`), so `(N, ψ_N)` is canonically the
equalizer of `(H(ψ_N), Δ^H_N)` in `Comonad.Coalgebra H` (used on line 1099 of the thesis). -/
def coalgebraCanonicalEqualizerIso :
    IsLimit (Fork.ofι (coalgebraCoactionHom H N) (coalgebraCoactionHom_condition H N)) :=
  Fork.IsLimit.mk
    (Fork.ofι (coalgebraCoactionHom H N) (coalgebraCoactionHom_condition H N))
    (fun s =>
      { f := s.ι.f ≫ H.ε.app N.A
        h := by
          have hs := congrArg Comonad.Coalgebra.Hom.f s.condition
          dsimp [coalgebraCanonicalTop, coalgebraCanonicalBottom, inducedMonadOnCoalgebras,
            Comonad.cofree] at hs ⊢
          have hι : s.pt.a ≫ H.map s.ι.f = s.ι.f ≫ H.δ.app N.A := s.ι.h
          have hε : H.map N.a ≫ H.ε.app (H.obj N.A) = H.ε.app N.A ≫ N.a := H.ε.naturality N.a
          rw [H.map_comp, reassoc_of% hι, H.right_counit]
          erw [comp_id]
          symm
          rw [assoc, ← hε, ← assoc, hs, assoc, H.left_counit]
          exact comp_id s.ι.f })
    (fun s => by
      ext
      have hs := congrArg Comonad.Coalgebra.Hom.f s.condition
      dsimp [coalgebraCoactionHom, coalgebraCanonicalTop, coalgebraCanonicalBottom,
        inducedMonadOnCoalgebras, Comonad.cofree] at hs ⊢
      have hε : H.map N.a ≫ H.ε.app (H.obj N.A) = H.ε.app N.A ≫ N.a := H.ε.naturality N.a
      rw [assoc, ← hε, ← assoc, hs, assoc, H.left_counit]
      exact comp_id s.ι.f)
    (fun s m hm => by
      ext
      have hm' := congrArg Comonad.Coalgebra.Hom.f hm
      dsimp [coalgebraCoactionHom, inducedMonadOnCoalgebras, Comonad.cofree] at hm' ⊢
      rw [← hm', assoc, N.counit, comp_id])

end CanonicalCoalgebraEqualizer

/-- **Stable Change of Rings (§3.1.4, p. 26, line 897)**:
Given a comonad functor `Φ : ComonadFunctor G H` (induced by a morphism of Hopf algebroids
`π : (A, Γ) → (B, Σ)`) and an adjunction `adj : Φ.F ⊣ U` (extension and restriction of scalars),
for any `Γ`-comodule `M` and `Σ`-comodule `N`, the cobar complex computing
`Ext_Σ(π_* M, N)` is canonically isomorphic to the pulled-back cobar complex computing
`Ext_Γ(M, π^* N)`. -/
@[simps!]
noncomputable def stableChangeOfRingsCobarIso
    {G : Comonad C} {H : Comonad D}
    (Φ : ComonadFunctor G H) {U : D ⥤ C} (adj : Φ.F ⊣ U)
    [HasEqualizers (Comonad.Coalgebra G)]
    (M : Comonad.Coalgebra G) (N : Comonad.Coalgebra H) :
    CoaugmentedCosimplicialTowerIso
      (cobarCosimplicialHomTower (Φ.pushforward.obj M) N)
      (pullbackCosimplicialHomTower Φ adj M N) :=
  generalizedShapiroCobarIso Φ adj M N

end Section3_1

/-!
## §3.2 The Unstable Case: The Comonad `U_Σ`, the Unstable Cotensor, and Unstable Change of Rings
-/

namespace Section3_2

open Section2_2 Section2_3 Section2_4 Section2_5 Section3_1

variable (U_Γ : Comonad C) {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U)

/-!
### §3.2.2 The Category of Unstable `Σ(n)`-Comodules (Definition 3.2.1 & Theorem 3.2.1)

Let `F : C ⥤ D` (`K(n)_* ⊗_{BP_*} -`) and `U : D ⥤ C` (restriction of scalars from `K(n)_*` to
`BP_*`) form an adjunction `adj : F ⊣ U` whose counit `τ : F ⋙ U ⟶ 𝟭 D` is an isomorphism
(`K(n)_* ⊗_{BP_*} N ≅ N`, line 948).
-/

/-- Helper lemma: When the counit `τ : F ⋙ U ⟶ 𝟭 D` of `adj : F ⊣ U` is an isomorphism
(as holds for the localization/quotient `BP_* → K(n)_*` where `K(n)_* ⊗_{BP_*} N ≅ N`),
the unit `σ = adj.unit` satisfies `σ_{U(F(Z))} = U(F(σ_Z))` for every `Z : C`. -/
lemma unit_app_U_F_eq_U_map_F_map_unit [IsIso adj.counit] (Z : C) :
    adj.unit.app (U.obj (F.obj Z)) = U.map (F.map (adj.unit.app Z)) := by
  have h1 : adj.unit.app (U.obj (F.obj Z)) ≫ U.map (adj.counit.app (F.obj Z)) =
      𝟙 (U.obj (F.obj Z)) :=
    adj.right_triangle_components (F.obj Z)
  have h2 : U.map (F.map (adj.unit.app Z)) ≫ U.map (adj.counit.app (F.obj Z)) =
      𝟙 (U.obj (F.obj Z)) := by
    rw [← U.map_comp, adj.left_triangle_components Z]
    exact U.map_id (F.obj Z)
  have : IsIso (adj.counit.app (F.obj Z)) := NatIso.isIso_app_of_isIso adj.counit (F.obj Z)
  have : IsIso (U.map (adj.counit.app (F.obj Z))) := Functor.map_isIso U (adj.counit.app (F.obj Z))
  rw [← cancel_mono (U.map (adj.counit.app (F.obj Z))), h1, h2]

/-- **Definition 3.2.1 & Theorem 3.2.1 (pp. 27–28, lines 935–973)**:
Given any comonad `U_Γ` on `C` and any adjunction `adj : F ⊣ U`,
`U_Σ(N) = F(U_Γ(U(N)))` (`K(n)_* ⊗_{BP_*} U_Γ(N)`) equipped with:
- counit `ε^Σ_N = F(ε^Γ_{UN}) ≫ τ_N : F(U_Γ(U N)) ⟶ F(U N) ⟶ N` (line 948), and
- comultiplication `Δ^Σ_N = F(Δ^Γ_{UN}) ≫ F(U_Γ(σ_{U_Γ(U N)}))` (line 943)
forms a comonad on `D` (`K(n)_*`-modules).
(Remarkably, the comonad axioms hold for *any* adjunction `F ⊣ U`, without even requiring `τ` to
be an isomorphism!) -/
@[simps!, implicit_reducible]
def unstableSigmaComonad : Comonad D where
  toFunctor := U ⋙ (U_Γ : C ⥤ C) ⋙ F
  ε :=
    { app N := F.map (U_Γ.ε.app (U.obj N)) ≫ adj.counit.app N
      naturality {N N'} g := by
        have hε := U_Γ.ε.naturality (U.map g)
        have hτ := adj.counit.naturality g
        dsimp at hε hτ ⊢
        rw [← assoc, ← F.map_comp, hε, F.map_comp, assoc, hτ, assoc] }
  δ :=
    { app N :=
        F.map (U_Γ.δ.app (U.obj N)) ≫ F.map (U_Γ.map (adj.unit.app (U_Γ.obj (U.obj N))))
      naturality {N N'} g := by
        have hδ := U_Γ.δ.naturality (U.map g)
        have hσ := adj.unit.naturality (U_Γ.map (U.map g))
        dsimp at hδ hσ ⊢
        rw [← F.map_comp, ← F.map_comp, reassoc_of% hδ, ← U_Γ.map_comp, hσ, U_Γ.map_comp,
          F.map_comp, F.map_comp, assoc] }
  coassoc N := by
    -- This is the landscape diagram on p. 28 (lines 964–967) of the thesis!
    dsimp
    have hσ_nat := adj.unit.naturality (U_Γ.δ.app (U.obj N))
    have hδ_nat := U_Γ.δ.naturality (adj.unit.app (U_Γ.obj (U.obj N)))
    have hσ_nat2 := adj.unit.naturality (U_Γ.map (adj.unit.app (U_Γ.obj (U.obj N))))
    dsimp at hσ_nat hδ_nat hσ_nat2
    rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp]
    congr 1
    rw [assoc, ← U_Γ.map_comp, F.map_comp, U.map_comp,
      ← assoc (adj.unit.app _), ← hσ_nat, assoc, U_Γ.map_comp,
      reassoc_of% (U_Γ.coassoc (U.obj N)), ← hσ_nat2, U_Γ.map_comp,
      ← reassoc_of% hδ_nat, assoc]
  left_counit N := by
    dsimp
    have hε := U_Γ.ε.naturality (adj.unit.app (U_Γ.obj (U.obj N)))
    dsimp at hε
    rw [assoc, ← assoc (F.map (U_Γ.map _)), ← F.map_comp (U_Γ.map _), hε, F.map_comp,
      assoc, adj.left_triangle_components, comp_id, ← F.map_comp, U_Γ.left_counit, F.map_id]
  right_counit N := by
    dsimp
    have hσ := adj.unit.naturality (U_Γ.ε.app (U.obj N))
    dsimp at hσ
    rw [assoc, ← F.map_comp, ← F.map_comp, ← U_Γ.map_comp, U.map_comp,
      reassoc_of% hσ.symm, adj.right_triangle_components, comp_id, U_Γ.right_counit]
    exact F.map_id (U_Γ.obj (U.obj N))

/-!
### §3.2.3 The Morphism of Comonads `U_Γ → U_Σ` (Definition 3.2.2 & Theorem 3.2.2)
-/

/-- **Definition 3.2.2 & Theorem 3.2.2 (pp. 29–30, lines 979–1025)**:
The pair `(F, α)` where `α_M = F(U_Γ(σ_M)) : F(U_Γ M) ⟶ U_Σ(F M) = F(U_Γ(U(F M)))` is a
functor of comonads from `U_Γ` to `U_Σ`. -/
@[simps, implicit_reducible]
def unstableComonadFunctor :
    ComonadFunctor U_Γ (unstableSigmaComonad U_Γ adj) where
  F := F
  α :=
    { app M := F.map (U_Γ.map (adj.unit.app M))
      naturality {M M'} g := by
        have hσ := adj.unit.naturality g
        dsimp at hσ ⊢
        rw [← F.map_comp, ← F.map_comp, ← U_Γ.map_comp, ← U_Γ.map_comp, hσ] }
  comm_δ M := by
    -- Diagram on lines 998–1006 of the thesis
    dsimp [unstableSigmaComonad]
    have hδ := U_Γ.δ.naturality (adj.unit.app M)
    have hσ := adj.unit.naturality (U_Γ.map (adj.unit.app M))
    dsimp at hδ hσ
    rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp]
    congr 1
    rw [reassoc_of% hδ, ← U_Γ.map_comp, ← U_Γ.map_comp, hσ]
  comm_ε M := by
    -- Diagram on lines 1013–1021 of the thesis
    dsimp [unstableSigmaComonad]
    have hε := U_Γ.ε.naturality (adj.unit.app M)
    dsimp at hε
    rw [← assoc, ← F.map_comp, hε, F.map_comp, assoc, adj.left_triangle_components, comp_id]

/-!
### §3.2.4 The Unstable Cotensor `α^*` (Theorem 3.2.3)
-/

/-- As noted in the proof of Theorem 3.2.3 (line 1044 of the thesis), the mate natural
transformation `β_N : U_Γ(U N) ⟶ U(U_Σ N) = U(F(U_Γ(U N)))` associated to
`unstableComonadFunctor` simplifies directly to the adjunction unit
`σ_{U_Γ(U N)} = π ⊗ 1_{U_Γ(N)}`. -/
@[simp]
theorem unstableMateNatTrans_app (N : D) :
    (mateNatTrans (unstableComonadFunctor U_Γ adj) adj).app N =
      adj.unit.app (U_Γ.obj (U.obj N)) := by
  dsimp [mateNatTrans, unstableComonadFunctor, unstableSigmaComonad]
  rw [← U.map_comp, ← F.map_comp, ← U_Γ.map_comp, adj.right_triangle_components,
    U_Γ.map_id, F.map_id, U.map_id, comp_id]

/-- The compatibility diagram checked in step 3 of the proof of Theorem 3.2.3 (lines 1048–1050):
`U_Γ(σ_M) ≫ β_{FM} = σ_{U_Γ M} ≫ U(α_M)`. -/
theorem unstable_mate_compatibility (M : C) :
    U_Γ.map (adj.unit.app M) ≫ (mateNatTrans (unstableComonadFunctor U_Γ adj) adj).app (F.obj M) =
      adj.unit.app (U_Γ.obj M) ≫ U.map ((unstableComonadFunctor U_Γ adj).α.app M) :=
  mate_fundamental_rel_unit (unstableComonadFunctor U_Γ adj) adj M

/-- The pushforward functor `α_* : Comonad.Coalgebra U_Γ ⥤ Comonad.Coalgebra U_Σ` (line 1027). -/
@[implicit_reducible]
def unstablePushforward :
    Comonad.Coalgebra U_Γ ⥤ Comonad.Coalgebra (unstableSigmaComonad U_Γ adj) :=
  (unstableComonadFunctor U_Γ adj).pushforward

/-- The unstable cotensor functor `α^* : Comonad.Coalgebra U_Σ ⥤ Comonad.Coalgebra U_Γ`
(Theorem 3.2.3, lines 1033–1065). -/
@[implicit_reducible]
noncomputable def unstableCotensor
    [HasEqualizers (Comonad.Coalgebra U_Γ)] :
    Comonad.Coalgebra (unstableSigmaComonad U_Γ adj) ⥤ Comonad.Coalgebra U_Γ :=
  (mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).coalgebraPullback

/-- **Theorem 3.2.3 (p. 30, line 1033)**:
The pushforward `α_* : U_Γ-comod ⥤ U_Σ-comod` is left adjoint to the unstable cotensor
`α^* : U_Σ-comod ⥤ U_Γ-comod`. -/
noncomputable def unstableLiftedAdjunction
    [HasEqualizers (Comonad.Coalgebra U_Γ)] :
    unstablePushforward U_Γ adj ⊣ unstableCotensor U_Γ adj :=
  liftedAdjunction (unstableComonadFunctor U_Γ adj) adj

/-!
### §3.2.5 The Counit of the Adjunction (Theorem 3.2.4, lines 1075–1101)

In the proof of Theorem 3.2.4 (lines 1087–1099), for any `U_Σ`-comodule `(N, ψ_N)`,
`α^* N` is the equalizer of:
- `top = U_Γ(U(ψ_N)) : U_Γ(U N) ⟶ U_Γ(U(U_Σ N))`, and
- `bottom = Δ^Γ_{UN} ≫ U_Γ(β_N) = Δ^Γ_{UN} ≫ U_Γ(σ_{U_Γ(U N)}) : U_Γ(U N) ⟶ U_Γ(U(U_Σ N))`.
Applying `F = K(n)_* ⊗_{BP_*} -` to these two underlying morphisms in `C` produces literally the
canonical `U_Σ`-coalgebra equalizer pair `(U_Σ(ψ_N), Δ^Σ_N) : U_Σ(N) ⇉ U_Σ^2(N)` of line 1097,
whose equalizer in `D^{U_Σ}` is `(N, ψ_N)` by `coalgebraCanonicalEqualizerIso`!
-/

/-- **Theorem 3.2.4 (Key Identity 1, lines 1093–1097)**:
Applying `F` (`K(n)_* ⊗_{BP_*} -`) to the underlying top morphism `U_Γ(U(ψ_N))` of the equalizer
defining `α^* N` yields the canonical top morphism `U_Σ(ψ_N) : U_Σ(N) ⟶ U_Σ^2(N)`. -/
theorem unstable_F_map_pullbackTopMap
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj)) :
    F.map (((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackTopMap N).f) =
      (coalgebraCanonicalTop (unstableSigmaComonad U_Γ adj) N).f :=
  rfl

/-- **Theorem 3.2.4 (Key Identity 2, lines 1091–1097)**:
Applying `F` (`K(n)_* ⊗_{BP_*} -`) to the underlying bottom morphism
`Δ^Γ_{UN} ≫ U_Γ(β_N)` of the equalizer defining `α^* N` yields the canonical bottom morphism
`Δ^Σ_N : U_Σ(N) ⟶ U_Σ^2(N)`. -/
theorem unstable_F_map_pullbackBottomMap
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj)) :
    F.map (((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackBottomMap N).f) =
      (coalgebraCanonicalBottom (unstableSigmaComonad U_Γ adj) N).f := by
  dsimp [ComonadOpfunctor.pullbackBottomMap, mateOpfunctor, coalgebraCanonicalBottom,
    inducedMonadOnCoalgebras]
  rw [unstableMateNatTrans_app, F.map_comp]

/-- **Theorem 3.2.4 (p. 31, lines 1075–1101)**:
The canonical equalizer diagram `(U_Σ(ψ_N), Δ^Σ_N) : U_Σ(N) ⇉ U_Σ^2(N)` obtained in lines
1093–1097 by tensoring the defining equalizer diagram of `α^* N` with `K(n)_*` has `(N, ψ_N)`
as its equalizer in `Comonad.Coalgebra (unstableSigmaComonad U_Γ adj)`. -/
def unstableCanonicalEqualizerIsLimit
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj)) :
    IsLimit (Fork.ofι
      (coalgebraCoactionHom (unstableSigmaComonad U_Γ adj) N)
      (coalgebraCoactionHom_condition (unstableSigmaComonad U_Γ adj) N)) :=
  coalgebraCanonicalEqualizerIso (unstableSigmaComonad U_Γ adj) N

/-- Pushing forward a cofree `U_Γ`-coalgebra `U_Γ.cofree.obj (U.obj Y)` along `α_*` produces
literally the cofree `U_Σ`-coalgebra `(unstableSigmaComonad U_Γ adj).cofree.obj Y` on the nose. -/
theorem unstablePushforward_obj_cofree (Y : D) :
    (unstablePushforward U_Γ adj).obj (U_Γ.cofree.obj (U.obj Y)) =
      (unstableSigmaComonad U_Γ adj).cofree.obj Y :=
  rfl

/-- Applying `α_*` (`unstablePushforward U_Γ adj`) to the top morphism `pullbackTopMap N` in
`Comonad.Coalgebra U_Γ` yields on the nose the canonical top morphism
`coalgebraCanonicalTop U_Σ N` in `Comonad.Coalgebra U_Σ`. -/
theorem unstablePushforward_map_pullbackTopMap
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj)) :
    (unstablePushforward U_Γ adj).map
      ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackTopMap N) =
      coalgebraCanonicalTop (unstableSigmaComonad U_Γ adj) N :=
  rfl

/-- Applying `α_*` (`unstablePushforward U_Γ adj`) to the bottom morphism `pullbackBottomMap N` in
`Comonad.Coalgebra U_Γ` yields on the nose the canonical bottom morphism
`coalgebraCanonicalBottom U_Σ N` in `Comonad.Coalgebra U_Σ`. -/
theorem unstablePushforward_map_pullbackBottomMap
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj)) :
    (unstablePushforward U_Γ adj).map
      ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackBottomMap N) =
      coalgebraCanonicalBottom (unstableSigmaComonad U_Γ adj) N := by
  ext
  exact unstable_F_map_pullbackBottomMap U_Γ adj N

/-- For any `U_Σ`-comodule `N`, applying `α_*` (`K(n)_* ⊗_{BP_*} -`) to the equalizer inclusion
`ι_N : α^* N ⟶ U_Γ(U N)` gives a morphism `α_*(α^* N) ⟶ U_Σ(N)` in `Comonad.Coalgebra U_Σ` that
equalizes the canonical pair `(U_Σ(ψ_N), Δ^Σ_N)` (lines 1091–1097). -/
lemma unstablePushforward_map_equalizer_ι_condition
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj)) :
    (unstablePushforward U_Γ adj).map
      (equalizer.ι ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackTopMap N)
        ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackBottomMap N)) ≫
      coalgebraCanonicalTop (unstableSigmaComonad U_Γ adj) N =
    (unstablePushforward U_Γ adj).map
      (equalizer.ι ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackTopMap N)
        ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackBottomMap N)) ≫
      coalgebraCanonicalBottom (unstableSigmaComonad U_Γ adj) N := by
  rw [← unstablePushforward_map_pullbackTopMap, ← unstablePushforward_map_pullbackBottomMap,
    ← (unstablePushforward U_Γ adj).map_comp, ← (unstablePushforward U_Γ adj).map_comp,
    equalizer.condition]

/-- The fork `α_*(α^* N) ⟶ U_Σ(N) ⇉ U_Σ^2(N)` in `Comonad.Coalgebra U_Σ` obtained by applying
`α_*` (`K(n)_* ⊗_{BP_*} -`) to the defining equalizer diagram of `α^* N` (lines 1091–1097). -/
@[simps!]
noncomputable def unstablePushforwardCotensorFork
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj)) :
    Fork (coalgebraCanonicalTop (unstableSigmaComonad U_Γ adj) N)
      (coalgebraCanonicalBottom (unstableSigmaComonad U_Γ adj) N) :=
  Fork.ofι
    ((unstablePushforward U_Γ adj).map
      (equalizer.ι ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackTopMap N)
        ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackBottomMap N)))
    (unstablePushforward_map_equalizer_ι_condition U_Γ adj N)

/-- The canonical comparison morphism `α_*(α^* N) ⟶ N` induced by the universal property of the
canonical equalizer `N ⟶ U_Σ(N) ⇉ U_Σ^2(N)` is literally the counit
`(unstableLiftedAdjunction U_Γ adj).counit.app N` of the lifted adjunction `α_* ⊣ α^*`! -/
theorem unstableCanonicalEqualizer_lift_eq_liftedCounit
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj)) :
    (unstableCanonicalEqualizerIsLimit U_Γ adj N).lift
      (unstablePushforwardCotensorFork U_Γ adj N) =
      (unstableLiftedAdjunction U_Γ adj).counit.app N := by
  ext
  change (unstablePushforwardCotensorFork U_Γ adj N).ι.f ≫
      (unstableSigmaComonad U_Γ adj).ε.app N.A =
    (liftedHomEquivInvFun (unstableComonadFunctor U_Γ adj) adj
      (𝟙 ((unstableCotensor U_Γ adj).obj N))).f
  dsimp [unstablePushforwardCotensorFork, unstablePushforward, unstableComonadFunctor,
    unstableSigmaComonad, liftedHomEquivInvFun, cofreeMateToHomUnderlying, Adjunction.homEquiv]
  rw [id_comp, F.map_comp, assoc]

/-- **Theorem 3.2.4 (Full Coalgebra Isomorphism, p. 31, lines 1075–1101)**:
For any `U_Σ`-comodule `(N, ψ_N)`, when `α_*` (`K(n)_* ⊗_{BP_*} -`, which is flat over `BP_*`)
preserves the equalizer defining `α^* N` (`hFlat : IsLimit (unstablePushforwardCotensorFork U_Γ adj N)`),
we obtain the canonical isomorphism of `U_Σ`-comodules:
`K(n)_* ⊗_{BP_*} α^* N = α_*(α^* N) ≅ N`. -/
noncomputable def unstablePushforwardCotensorIso
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj))
    (hFlat : IsLimit (unstablePushforwardCotensorFork U_Γ adj N)) :
    (unstablePushforward U_Γ adj).obj ((unstableCotensor U_Γ adj).obj N) ≅ N :=
  IsLimit.conePointUniqueUpToIso hFlat (unstableCanonicalEqualizerIsLimit U_Γ adj N)

/-- **Theorem 3.2.4 (Counit Isomorphism, p. 31, lines 1075–1101)**:
Under the flatness condition `hFlat : IsLimit (unstablePushforwardCotensorFork U_Γ adj N)`,
the counit `(unstableLiftedAdjunction U_Γ adj).counit.app N : α_*(α^* N) ⟶ N` of the lifted
adjunction `α_* ⊣ α^*` is an isomorphism of `U_Σ`-comodules. -/
theorem isIso_unstableLiftedCounit
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj))
    (hFlat : IsLimit (unstablePushforwardCotensorFork U_Γ adj N)) :
    IsIso ((unstableLiftedAdjunction U_Γ adj).counit.app N) := by
  rw [← unstableCanonicalEqualizer_lift_eq_liftedCounit]
  change IsIso (unstablePushforwardCotensorIso U_Γ adj N hFlat).hom
  infer_instance

/-!
### §3.2.6 The Unit of the Adjunction & Unstable Change of Rings (Propositions 3.2.1–3.2.5 & Theorem 3.2.5)

In §3.2.6 (pp. 32–36, lines 1103–1326):
- **Proposition 3.2.1 (lines 1121–1201)**: Shows `K(n)_* BP{ι_k} ≅ U_Σ(K(n)_* ⊗ BP_*{ι_k}) ⊗ B(n)_*`
  for `k ≥ 2p^n + 1` by reducing to the connective case and using right counitality of `U_{σ(n)}`
  (`prop3_2_1_counit_reduction`, lines 1192–1198).
- **Proposition 3.2.2 (lines 1209–1263)**: Shows `U_Γ(K(n)_* ⊗ M) ≅ B(n)_* ⊗_{K(n)_*} U_Σ(K(n)_* ⊗ M)`
  for `M` of connectivity `k ≥ 2p^n + 1`, using the left/right `v_n^{-1}` action identity
  (`prop3_2_2_left_right_inv_action`, lines 1228–1234) and colimit preservation (`prop3_2_2_colimit_iso`,
  lines 1251–1262).
- **Proposition 3.2.3 (lines 1265–1288)**: Deduces `α^* α_* M ≅ B(n)_* ⊗_{BP_*} M` for `M` of
  connectivity `k ≥ 2p^n + 1` by comparing the equalizer defining `α^* α_* M` with `B(n)_* ⊗_{K(n)_*} -`
  applied to the canonical equalizer of `α_* M` (`prop3_2_3_cotensor_iso_of_diagram_iso` &
  `prop3_2_3_unitPullbackIso`).
- **Proposition 3.2.4 (lines 1295–1303)**: For a cofree `U_Σ`-comodule `U_Σ(N)`,
  `α^* U_Σ(N) ≅ B(n)_* ⊗_{BP_*} N` (`prop3_2_4_cotensor_cofree`).
- **Proposition 3.2.5 (lines 1305–1310)**: Concludes that for `M` of height `n` and connectivity
  `≥ 2p^n + 1`, the unit of the adjunction `σ̃_M : M ⟶ α^* α_* M` is an isomorphism of `U_Γ`-comodules.
- **Theorem 3.2.5 (Unstable Change of Rings, line 1313)**: Combines Proposition 3.2.5 with
  Generalized Shapiro's Lemma (`generalizedShapiroCobarIso`) to conclude:
  `Ext_{U_Γ}(BP_*, M) ≃ Ext_{U_Σ}(K(n)_*, K(n)_* ⊗_{BP_*} M)`.
-/

/-- **§3.2.1 Excess Condition for Unstable `BP_*`-Comodules (p. 26, line 908)**:
For a free `BP_*`-module `M`, the unstable cooperation module `U_Γ(M) ⊆ BP_* BP ⊗_{BP_*} M`
is generated by elements `h^I ⊗ m` satisfying `2 * len(I) < deg(m)`. -/
def unstableExcessCondition (lenI degM : ℕ) : Prop :=
  2 * lenI < degM

/-- **Proposition 3.2.1 (Excess of `h_k^{p^n} ⊗ v_n ι_k`, p. 32, line 1145)**:
In the proof of Proposition 3.2.1, the term `h_k^{p^n} ⊗ v_n ι_k` has `len(h_k^{p^n}) = p^n`
and `deg(v_n ι_k) = k + (2p^n - 2)`. For `p^n ≥ 1`, the unstable excess condition
`2 * p^n < k + (2 * p^n - 2)` holds if and only if `k ≥ 3` (i.e., `k - 2 > 0`, valid on the
`3`-sphere and above, line 1145). -/
theorem excess_vn_shift_iff (p n k : ℕ) (hpn : 1 ≤ p ^ n) :
    unstableExcessCondition (p ^ n) (k + (2 * p ^ n - 2)) ↔ 3 ≤ k := by
  dsimp [unstableExcessCondition]
  omega

/-- **Proposition 3.2.1 (Excess of `(h_l^{p^n} - v_n^{p^l - 1} h_l) ⊗ ι_k`, p. 32, lines 1160–1162)**:
To define the `b(n){ι_k}`-module action `u_l ⊗ ι_k ↦ (h_l^{p^n} - v_n^{p^l - 1} h_l) ⊗ ι_k`
where `len(h_l^{p^n}) = p^n` and `deg(ι_k) = k`, the unstable excess condition
`2 * p^n < k` holds if and only if `k ≥ 2 * p ^ n + 1` (the exact connectivity bound of
Propositions 3.2.1–3.2.5 and Theorem 3.2.5). -/
theorem excess_ul_action_iff (p n k : ℕ) :
    unstableExcessCondition (p ^ n) k ↔ 2 * p ^ n + 1 ≤ k := by
  dsimp [unstableExcessCondition]
  omega

/-- **Proposition 3.2.1 (Counit Reduction Step, p. 33, lines 1192–1198)**:
In the proof of Proposition 3.2.1, tensoring the lifted morphism `f̄` on the right with `k(n)_*`
over `b(n)_*{ι_k}` produces a map `g : σ(n)_*{ι_k} ⟶ σ(n)_*{ι_k}` that factors as the
comultiplication `Δ` followed by `U_{σ(n)}(ε)` (diagram on lines 1193–1194). By right counitality
of the comonad `U_{σ(n)}`, this composite is the identity, hence an isomorphism. -/
theorem prop3_2_1_counit_reduction {B : Type*} [Category* B] (G : Comonad B) (X : B)
    (g : G.obj X ⟶ G.obj X) (hg : g = G.δ.app X ≫ G.map (G.ε.app X)) :
    g = 𝟙 (G.obj X) ∧ IsIso g := by
  have hid : g = 𝟙 (G.obj X) := hg.trans (G.right_counit X)
  refine ⟨hid, ?_⟩
  rw [hid]
  infer_instance

/-- **Proposition 3.2.2 (Algebraic Identity for Left/Right `v_n^{-1}` Actions, p. 34, lines 1228–1232)**:
In any ring `R` (modeling the bimodule endomorphisms of `K(n)_* BP{ι_k}` where `v_n` acts on the
left and right), for any invertible element `v : Rˣ` (representing `v_n`) and any element `x : R`,
`v * (x * v⁻¹ - v⁻¹ * x) * v = v * x - x * v`
(which is the exact equation `v_n (1 · v_n^{-1} - v_n^{-1}) · v_n = v_n - 1 · v_n` on lines 1229–1230). -/
theorem prop3_2_2_left_right_inv_action {R : Type*} [Ring R] (v : Rˣ) (x : R) :
    (v : R) * (x * ↑v⁻¹ - ↑v⁻¹ * x) * (v : R) = (v : R) * x - x * (v : R) := by
  calc
    (v : R) * (x * ↑v⁻¹ - ↑v⁻¹ * x) * (v : R)
      = (v : R) * x * (↑v⁻¹ * (v : R)) - ((v : R) * ↑v⁻¹) * x * (v : R) := by
        simp [mul_sub, sub_mul, mul_assoc]
    _ = (v : R) * x - x * (v : R) := by
        rw [Units.inv_mul, Units.mul_inv, mul_one, one_mul]

/-- **Proposition 3.2.2 (Left and Right Actions of `v_n^{-1}` Agree iff `v_n` Actions Agree, lines 1234–1235)**:
As concluded on line 1234 of the thesis, the left and right actions of `v_n^{-1}` on `x` agree
(`x * v⁻¹ = v⁻¹ * x`) if and only if the left and right actions of `v_n` on `x` agree
(`v * x = x * v`). -/
theorem prop3_2_2_left_right_inv_comm {R : Type*} [Ring R] (v : Rˣ) (x : R) :
    x * ↑v⁻¹ = ↑v⁻¹ * x ↔ (v : R) * x = x * (v : R) := by
  constructor
  · intro h
    have h0 : x * ↑v⁻¹ - ↑v⁻¹ * x = 0 := sub_eq_zero.mpr h
    have hid := prop3_2_2_left_right_inv_action v x
    rw [h0, mul_zero, zero_mul] at hid
    exact sub_eq_zero.mp hid.symm
  · intro h
    have h0 : (v : R) * x - x * (v : R) = 0 := sub_eq_zero.mpr h
    have hid := (prop3_2_2_left_right_inv_action v x).trans h0
    have h1 : (v : R) * (x * ↑v⁻¹ - ↑v⁻¹ * x) = 0 := by
      calc
        (v : R) * (x * ↑v⁻¹ - ↑v⁻¹ * x)
          = ((v : R) * (x * ↑v⁻¹ - ↑v⁻¹ * x) * (v : R)) * ↑v⁻¹ := by
            rw [Units.mul_inv_cancel_right]
        _ = 0 := by rw [hid, zero_mul]
    have h2 : x * ↑v⁻¹ - ↑v⁻¹ * x = 0 := by
      calc
        x * ↑v⁻¹ - ↑v⁻¹ * x
          = ↑v⁻¹ * ((v : R) * (x * ↑v⁻¹ - ↑v⁻¹ * x)) := by
            rw [Units.inv_mul_cancel_left]
        _ = 0 := by rw [h1, mul_zero]
    exact sub_eq_zero.mp h2

/-- **Proposition 3.2.2 (Colimit Extension from Generating Spheres, p. 34, lines 1251–1262)**:
If a `k`-connected `U_Γ`-comodule `M` is exhibited as the colimit of a diagram `K : J ⥤ C^{U_Γ}`
of generating spheres `BP_*{ι_{k_i}}` (`k_i ≥ 2p^n + 1`, Definition 3.2.3 on line 1203), and
`L, R : C^{U_Γ} ⥤ C^{U_Γ}` (representing `U_Γ(K(n)_* ⊗ -)` and `B(n)_* ⊗_{K(n)_*} U_Σ(K(n)_* ⊗ -)`)
preserve the colimit of `K`, then a natural isomorphism `eSpheres : K ⋙ L ≅ K ⋙ R` on the
generating spheres induces a canonical isomorphism `L(M) ≅ R(M)` (lines 1255–1259). -/
noncomputable def prop3_2_2_colimit_iso {J : Type*} [Category* J]
    (K : J ⥤ Comonad.Coalgebra U_Γ)
    (c : Cocone K)
    (L R : Comonad.Coalgebra U_Γ ⥤ Comonad.Coalgebra U_Γ)
    (hL : IsColimit (L.mapCocone c))
    (hR : IsColimit (R.mapCocone c))
    (eSpheres : K ⋙ L ≅ K ⋙ R) :
    L.obj c.pt ≅ R.obj c.pt :=
  hL.coconePointUniqueUpToIso ((IsColimit.precomposeHomEquiv eSpheres (R.mapCocone c)).symm hR)

/-- Helper: Applying a functor `BnExtend` (`B(n)_* ⊗_{K(n)_*} -`) to the canonical equalizer diagram
of a `H`-coalgebra `N` produces a fork over `BnExtend.map (coalgebraCanonicalTop H N)` and
`BnExtend.map (coalgebraCanonicalBottom H N)`. -/
@[simps!, implicit_reducible]
def mapCanonicalFork {H : Comonad D} {E : Type*} [Category* E]
    (BnExtend : Comonad.Coalgebra H ⥤ E) (N : Comonad.Coalgebra H) :
    Fork (BnExtend.map (coalgebraCanonicalTop H N))
      (BnExtend.map (coalgebraCanonicalBottom H N)) :=
  Fork.ofι (BnExtend.map (coalgebraCoactionHom H N)) (by
    rw [← BnExtend.map_comp, ← BnExtend.map_comp, coalgebraCoactionHom_condition H N])

/-- **Proposition 3.2.3 (Equalizer Comparison Diagram, p. 35, lines 1275–1288)**:
Given a functor `BnExtend : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj) ⥤ Comonad.Coalgebra U_Γ`
(representing `B(n)_* ⊗_{K(n)_*} -`) and a `U_Σ`-comodule `N` such that:
1. Proposition 3.2.2 provides isomorphisms
   `e₀ : U_Γ.cofree.obj (U.obj N.A) ≅ BnExtend.obj ((unstableSigmaComonad U_Γ adj).cofree.obj N.A)`
   and
   `e₁ : U_Γ.cofree.obj (U.obj ((unstableSigmaComonad U_Γ adj).obj N.A)) ≅ BnExtend.obj ((unstableSigmaComonad U_Γ adj).cofree.obj ((unstableSigmaComonad U_Γ adj).obj N.A))`
   intertwining `(pullbackTopMap N, pullbackBottomMap N)` with `BnExtend` applied to the canonical
   equalizer pair `(coalgebraCanonicalTop U_Σ N, coalgebraCanonicalBottom U_Σ N)` (diagram on lines
   1281–1282), and
2. `BnExtend` preserves the canonical equalizer of `N` (`hBnLim`),
then the equalizer `α^* N` is canonically isomorphic to `BnExtend.obj N` (`B(n)_* ⊗_{K(n)_*} N`). -/
noncomputable def prop3_2_3_cotensor_iso_of_diagram_iso
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (BnExtend : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj) ⥤ Comonad.Coalgebra U_Γ)
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj))
    (e₀ : U_Γ.cofree.obj (U.obj N.A) ≅
      BnExtend.obj ((unstableSigmaComonad U_Γ adj).cofree.obj N.A))
    (e₁ : U_Γ.cofree.obj (U.obj ((unstableSigmaComonad U_Γ adj).obj N.A)) ≅
      BnExtend.obj ((unstableSigmaComonad U_Γ adj).cofree.obj
        ((unstableSigmaComonad U_Γ adj).obj N.A)))
    (hTop : ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackTopMap N) ≫ e₁.hom =
      e₀.hom ≫ BnExtend.map (coalgebraCanonicalTop (unstableSigmaComonad U_Γ adj) N))
    (hBot : ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackBottomMap N) ≫ e₁.hom =
      e₀.hom ≫ BnExtend.map (coalgebraCanonicalBottom (unstableSigmaComonad U_Γ adj) N))
    (hBnLim : IsLimit (mapCanonicalFork BnExtend N)) :
    (unstableCotensor U_Γ adj).obj N ≅ BnExtend.obj N := by
  let top₁ := (mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackTopMap N
  let bot₁ := (mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackBottomMap N
  let top₂ := BnExtend.map (coalgebraCanonicalTop (unstableSigmaComonad U_Γ adj) N)
  let bot₂ := BnExtend.map (coalgebraCanonicalBottom (unstableSigmaComonad U_Γ adj) N)
  have hcond₁ : (equalizer.ι top₁ bot₁ ≫ e₀.hom) ≫ top₂ =
      (equalizer.ι top₁ bot₁ ≫ e₀.hom) ≫ bot₂ := by
    rw [assoc, assoc, ← hTop, ← hBot, ← assoc, ← assoc, equalizer.condition]
  let fork₁ : Fork top₂ bot₂ := Fork.ofι (equalizer.ι top₁ bot₁ ≫ e₀.hom) hcond₁
  let ι₂ := BnExtend.map (coalgebraCoactionHom (unstableSigmaComonad U_Γ adj) N) ≫ e₀.inv
  have hcond₂ : ι₂ ≫ top₁ = ι₂ ≫ bot₁ := by
    rw [← cancel_mono e₁.hom]
    dsimp [ι₂, top₁, bot₁]
    simp only [assoc]
    rw [hTop, hBot, ← assoc e₀.inv, ← assoc e₀.inv, e₀.inv_hom_id, id_comp, id_comp,
      ← BnExtend.map_comp, ← BnExtend.map_comp,
      coalgebraCoactionHom_condition (unstableSigmaComonad U_Γ adj) N]
  refine
    { hom := hBnLim.lift fork₁
      inv := equalizer.lift ι₂ hcond₂
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply equalizer.hom_ext
    have hlift₁ : hBnLim.lift fork₁ ≫
        BnExtend.map (coalgebraCoactionHom (unstableSigmaComonad U_Γ adj) N) =
        equalizer.ι top₁ bot₁ ≫ e₀.hom :=
      hBnLim.fac fork₁ WalkingParallelPair.zero
    rw [assoc, equalizer.lift_ι]
    dsimp [ι₂]
    rw [← assoc, hlift₁, assoc, e₀.hom_inv_id]
    dsimp [top₁, bot₁]
    rw [comp_id, id_comp]
  · apply Fork.IsLimit.hom_ext hBnLim
    have hlift₁ : hBnLim.lift fork₁ ≫ (mapCanonicalFork BnExtend N).ι = fork₁.ι :=
      hBnLim.fac fork₁ WalkingParallelPair.zero
    rw [assoc, hlift₁, id_comp]
    dsimp [fork₁, mapCanonicalFork]
    rw [← assoc, equalizer.lift_ι]
    dsimp [ι₂]
    rw [assoc, e₀.inv_hom_id, comp_id]

/-- **Proposition 3.2.3 (p. 35, lines 1265–1288)**:
For an unstable `U_Γ`-comodule `M` of connectivity `k ≥ 2p^n + 1`, applying
`prop3_2_3_cotensor_iso_of_diagram_iso` to `N = α_* M = K(n)_* ⊗_{BP_*} M` together with the
transitivity isomorphism `B(n)_* ⊗_{K(n)_*} (K(n)_* ⊗_{BP_*} M) ≅ B(n)_* ⊗_{BP_*} M` (line 1286)
yields `α^* α_* M ≅ B(n)_* ⊗_{BP_*} M`. -/
noncomputable def prop3_2_3_unitPullbackIso
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (BnExtend : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj) ⥤ Comonad.Coalgebra U_Γ)
    (BnTensor : Comonad.Coalgebra U_Γ ⥤ Comonad.Coalgebra U_Γ)
    (M : Comonad.Coalgebra U_Γ)
    (e₀ : U_Γ.cofree.obj (U.obj ((unstablePushforward U_Γ adj).obj M).A) ≅
      BnExtend.obj ((unstableSigmaComonad U_Γ adj).cofree.obj
        ((unstablePushforward U_Γ adj).obj M).A))
    (e₁ : U_Γ.cofree.obj (U.obj ((unstableSigmaComonad U_Γ adj).obj
        ((unstablePushforward U_Γ adj).obj M).A)) ≅
      BnExtend.obj ((unstableSigmaComonad U_Γ adj).cofree.obj
        ((unstableSigmaComonad U_Γ adj).obj ((unstablePushforward U_Γ adj).obj M).A)))
    (hTop : ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackTopMap
        ((unstablePushforward U_Γ adj).obj M)) ≫ e₁.hom =
      e₀.hom ≫ BnExtend.map (coalgebraCanonicalTop (unstableSigmaComonad U_Γ adj)
        ((unstablePushforward U_Γ adj).obj M)))
    (hBot : ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackBottomMap
        ((unstablePushforward U_Γ adj).obj M)) ≫ e₁.hom =
      e₀.hom ≫ BnExtend.map (coalgebraCanonicalBottom (unstableSigmaComonad U_Γ adj)
        ((unstablePushforward U_Γ adj).obj M)))
    (hBnLim : IsLimit (mapCanonicalFork BnExtend ((unstablePushforward U_Γ adj).obj M)))
    (eTrans : BnExtend.obj ((unstablePushforward U_Γ adj).obj M) ≅ BnTensor.obj M) :
    (unstableCotensor U_Γ adj).obj ((unstablePushforward U_Γ adj).obj M) ≅ BnTensor.obj M :=
  (prop3_2_3_cotensor_iso_of_diagram_iso U_Γ adj BnExtend ((unstablePushforward U_Γ adj).obj M)
    e₀ e₁ hTop hBot hBnLim).trans eTrans

/-- **Proposition 3.2.4 (p. 35, lines 1295–1303)**:
For any cofree `U_Σ`-comodule `U_Σ(Y) = (unstableSigmaComonad U_Γ adj).cofree.obj Y`,
Proposition 3.2.3 yields `α^*(U_Σ(Y)) ≅ B(n)_* ⊗_{K(n)_*} U_Σ(Y)`. -/
noncomputable def prop3_2_4_cotensor_cofree
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (BnExtend : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj) ⥤ Comonad.Coalgebra U_Γ)
    (Y : D)
    (e₀ : U_Γ.cofree.obj (U.obj (((unstableSigmaComonad U_Γ adj).cofree.obj Y).A)) ≅
      BnExtend.obj ((unstableSigmaComonad U_Γ adj).cofree.obj
        (((unstableSigmaComonad U_Γ adj).cofree.obj Y).A)))
    (e₁ : U_Γ.cofree.obj (U.obj ((unstableSigmaComonad U_Γ adj).obj
        (((unstableSigmaComonad U_Γ adj).cofree.obj Y).A))) ≅
      BnExtend.obj ((unstableSigmaComonad U_Γ adj).cofree.obj
        ((unstableSigmaComonad U_Γ adj).obj (((unstableSigmaComonad U_Γ adj).cofree.obj Y).A))))
    (hTop : ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackTopMap
        ((unstableSigmaComonad U_Γ adj).cofree.obj Y)) ≫ e₁.hom =
      e₀.hom ≫ BnExtend.map (coalgebraCanonicalTop (unstableSigmaComonad U_Γ adj)
        ((unstableSigmaComonad U_Γ adj).cofree.obj Y)))
    (hBot : ((mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).pullbackBottomMap
        ((unstableSigmaComonad U_Γ adj).cofree.obj Y)) ≫ e₁.hom =
      e₀.hom ≫ BnExtend.map (coalgebraCanonicalBottom (unstableSigmaComonad U_Γ adj)
        ((unstableSigmaComonad U_Γ adj).cofree.obj Y)))
    (hBnLim : IsLimit (mapCanonicalFork BnExtend ((unstableSigmaComonad U_Γ adj).cofree.obj Y))) :
    (unstableCotensor U_Γ adj).obj ((unstableSigmaComonad U_Γ adj).cofree.obj Y) ≅
      BnExtend.obj ((unstableSigmaComonad U_Γ adj).cofree.obj Y) :=
  prop3_2_3_cotensor_iso_of_diagram_iso U_Γ adj BnExtend
    ((unstableSigmaComonad U_Γ adj).cofree.obj Y) e₀ e₁ hTop hBot hBnLim

/-- Given an endofunctor `BnTensor : Comonad.Coalgebra U_Γ ⥤ Comonad.Coalgebra U_Γ`
(representing `B(n)_* ⊗_{BP_*} -`), a `U_Γ`-comodule `M` satisfies the height-`n` and
`(2p^n + 1)`-connectivity hypothesis of Propositions 3.2.3–3.2.5 (lines 1265–1310) if:
1. `α^* α_* M ≅ BnTensor.obj M` (Proposition 3.2.3, line 1267, valid for connectivity `k ≥ 2p^n + 1`),
2. `M ≅ BnTensor.obj M` (Definition 3.2.4, line 1292, height `n`), and
3. The composite `M ≅ BnTensor.obj M ≅ α^* α_* M` is induced by the adjunction unit
   `σ̃_M = (unstableLiftedAdjunction U_Γ adj).unit.app M`. -/
structure IsHeightNConnected [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (BnTensor : Comonad.Coalgebra U_Γ ⥤ Comonad.Coalgebra U_Γ)
    (M : Comonad.Coalgebra U_Γ) where
  /-- Proposition 3.2.3 (line 1267): `α^* α_* M ≅ B(n)_* ⊗_{BP_*} M` for `k ≥ 2p^n + 1`. -/
  unitPullbackIso : (unstableCotensor U_Γ adj).obj ((unstablePushforward U_Γ adj).obj M) ≅
    BnTensor.obj M
  /-- Definition 3.2.4 (line 1292): `M` is of height `n`, i.e., `M ≅ B(n)_* ⊗_{BP_*} M`. -/
  heightNIso : M ≅ BnTensor.obj M
  /-- Compatibility of the unit `σ̃_M : M ⟶ α^* α_* M` with the two isomorphisms (Proposition 3.2.5). -/
  unit_comp_iso :
    (unstableLiftedAdjunction U_Γ adj).unit.app M ≫ unitPullbackIso.hom = heightNIso.hom

/-- **Proposition 3.2.5 (p. 35, lines 1305–1310)**:
If `M` is a `U_Γ`-comodule of height `n` and connectivity `≥ 2p^n + 1`, then the unit of the
lifted adjunction `σ̃_M : M ⟶ α^* α_* M` is an isomorphism of `U_Γ`-comodules. -/
theorem isIso_liftedUnit_of_isHeightNConnected
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    {BnTensor : Comonad.Coalgebra U_Γ ⥤ Comonad.Coalgebra U_Γ}
    {M : Comonad.Coalgebra U_Γ} (hM : IsHeightNConnected U_Γ adj BnTensor M) :
    IsIso ((unstableLiftedAdjunction U_Γ adj).unit.app M) := by
  have h : (unstableLiftedAdjunction U_Γ adj).unit.app M =
      hM.heightNIso.hom ≫ hM.unitPullbackIso.inv := by
    rw [← hM.unit_comp_iso, assoc, Iso.hom_inv_id, comp_id]
  rw [h]
  infer_instance

/-- The canonical isomorphism `M ≅ α^* α_* M` of `U_Γ`-comodules for `M` of height `n` and
connectivity `≥ 2p^n + 1` (Proposition 3.2.5). -/
@[simps!]
noncomputable def liftedUnitIsoOfHeightNConnected
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    {BnTensor : Comonad.Coalgebra U_Γ ⥤ Comonad.Coalgebra U_Γ}
    {M : Comonad.Coalgebra U_Γ} (hM : IsHeightNConnected U_Γ adj BnTensor M) :
    M ≅ (unstableCotensor U_Γ adj).obj ((unstablePushforward U_Γ adj).obj M) :=
  have := isIso_liftedUnit_of_isHeightNConnected U_Γ adj hM
  asIso ((unstableLiftedAdjunction U_Γ adj).unit.app M)

/-- Helper: An isomorphism `e : M₁ ≅ M₂` in `M` induces an isomorphism
`iterObj T M₁ m ≅ iterObj T M₂ m` for every `m : ℕ`. -/
@[implicit_reducible]
def iterObjIso {M : Type*} [Category* M] (T : Monad M) {M₁ M₂ : M} (e : M₁ ≅ M₂) :
    ∀ m : ℕ, iterObj T M₁ m ≅ iterObj T M₂ m
  | 0 => e
  | m + 1 => T.mapIso (iterObjIso T e m)

/-- Naturality of `iterCoface` with respect to `iterObjIso`. -/
@[reassoc]
lemma iterObjIso_hom_comp_iterCoface {M : Type*} [Category* M] (T : Monad M)
    {M₁ M₂ : M} (e : M₁ ≅ M₂) :
    ∀ (m : ℕ) (k : Fin (m + 1)),
      (iterObjIso T e m).hom ≫ iterCoface T M₂ m k =
        iterCoface T M₁ m k ≫ (iterObjIso T e (m + 1)).hom
  | m, ⟨0, h0⟩ => by
    rw [iterCoface_mk_zero, iterCoface_mk_zero]
    exact T.η.naturality (iterObjIso T e m).hom
  | 0, ⟨k + 1, hk⟩ => absurd hk (by omega)
  | m + 1, ⟨k + 1, hk⟩ => by
    let k' : Fin (m + 1) := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    change T.map (iterObjIso T e m).hom ≫ T.map (iterCoface T M₂ m k') =
      T.map (iterCoface T M₁ m k') ≫ T.map (iterObjIso T e (m + 1)).hom
    rw [← T.map_comp, ← T.map_comp, iterObjIso_hom_comp_iterCoface T e m k']

/-- Naturality of `cobarCodegeneracy` with respect to `iterObjIso`. -/
@[reassoc]
lemma iterObjIso_hom_comp_cobarCodegeneracy {M : Type*} [Category* M] (T : Monad M)
    {M₁ M₂ : M} (e : M₁ ≅ M₂) :
    ∀ (n : ℕ) (j : Fin (n + 1)),
      (iterObjIso T e (n + 2)).hom ≫ cobarCodegeneracy T M₂ n j =
        cobarCodegeneracy T M₁ n j ≫ (iterObjIso T e (n + 1)).hom
  | n, ⟨0, h0⟩ => by
    rw [cobarCodegeneracy_mk_zero, cobarCodegeneracy_mk_zero]
    exact T.μ.naturality (iterObjIso T e n).hom
  | 0, ⟨j + 1, hj⟩ => absurd hj (by omega)
  | n + 1, ⟨j + 1, hj⟩ => by
    let j' : Fin (n + 1) := ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    change T.map (iterObjIso T e (n + 2)).hom ≫ T.map (cobarCodegeneracy T M₂ n j') =
      T.map (cobarCodegeneracy T M₁ n j') ≫ T.map (iterObjIso T e (n + 1)).hom
    rw [← T.map_comp, ← T.map_comp, iterObjIso_hom_comp_cobarCodegeneracy T e n j']

/-- Any isomorphism of `G`-coalgebras `e : M₁ ≅ M₂` induces a canonical isomorphism of
coaugmented cosimplicial cobar hom-towers
`Hom_{C^G}(B, G^•(M₁)) ≃ Hom_{C^G}(B, G^•(M₂))`. -/
def cobarCosimplicialHomTowerIsoOfIso {G : Comonad C}
    (B : Comonad.Coalgebra G) {M₁ M₂ : Comonad.Coalgebra G} (e : M₁ ≅ M₂) :
    CoaugmentedCosimplicialTowerIso
      (cobarCosimplicialHomTower B M₁)
      (cobarCosimplicialHomTower B M₂) where
  coaugEquiv :=
    { toFun := fun (f : B ⟶ M₁) => f ≫ e.hom
      invFun := fun (f : B ⟶ M₂) => f ≫ e.inv
      left_inv := fun (f : B ⟶ M₁) => by
        change (f ≫ e.hom) ≫ e.inv = f
        rw [assoc, e.hom_inv_id, comp_id]
      right_inv := fun (f : B ⟶ M₂) => by
        change (f ≫ e.inv) ≫ e.hom = f
        rw [assoc, e.inv_hom_id, comp_id] }
  levelEquiv n :=
    { toFun := fun (f : B ⟶ comonadCobarObj G M₁ n) =>
        f ≫ (iterObjIso (inducedMonadOnCoalgebras G) e (n + 1)).hom
      invFun := fun (f : B ⟶ comonadCobarObj G M₂ n) =>
        f ≫ (iterObjIso (inducedMonadOnCoalgebras G) e (n + 1)).inv
      left_inv := fun (f : B ⟶ comonadCobarObj G M₁ n) => by
        change (f ≫ (iterObjIso (inducedMonadOnCoalgebras G) e (n + 1)).hom) ≫
          (iterObjIso (inducedMonadOnCoalgebras G) e (n + 1)).inv = f
        rw [assoc, Iso.hom_inv_id, comp_id]
      right_inv := fun (f : B ⟶ comonadCobarObj G M₂ n) => by
        change (f ≫ (iterObjIso (inducedMonadOnCoalgebras G) e (n + 1)).inv) ≫
          (iterObjIso (inducedMonadOnCoalgebras G) e (n + 1)).hom = f
        rw [assoc, Iso.inv_hom_id, comp_id] }
  comm_coaug (f : B ⟶ M₁) := by
    change (f ≫ comonadCobarCoaug G M₁) ≫
        (iterObjIso (inducedMonadOnCoalgebras G) e 1).hom =
      (f ≫ e.hom) ≫ comonadCobarCoaug G M₂
    dsimp [comonadCobarCoaug, iterObjIso]
    rw [assoc, ← (inducedMonadOnCoalgebras G).η.naturality e.hom, Functor.id_map, assoc]
  comm_coface n i (f : B ⟶ comonadCobarObj G M₁ n) := by
    change (f ≫ comonadCobarCoface G M₁ n i) ≫
        (iterObjIso (inducedMonadOnCoalgebras G) e (n + 2)).hom =
      (f ≫ (iterObjIso (inducedMonadOnCoalgebras G) e (n + 1)).hom) ≫
        comonadCobarCoface G M₂ n i
    dsimp [comonadCobarCoface, cobarCoface]
    rw [assoc, assoc, ← iterObjIso_hom_comp_iterCoface]
  comm_codegeneracy n j (f : B ⟶ comonadCobarObj G M₁ (n + 1)) := by
    change (f ≫ comonadCobarCodegeneracy G M₁ n j) ≫
        (iterObjIso (inducedMonadOnCoalgebras G) e (n + 1)).hom =
      (f ≫ (iterObjIso (inducedMonadOnCoalgebras G) e (n + 2)).hom) ≫
        comonadCobarCodegeneracy G M₂ n j
    dsimp [comonadCobarCodegeneracy]
    rw [assoc, assoc, ← iterObjIso_hom_comp_cobarCodegeneracy]

/-- Symmetry (inverse) of a `CoaugmentedCosimplicialTowerIso`. -/
@[simps]
def CoaugmentedCosimplicialTowerIso.symm
    {T₁ : CoaugmentedCosimplicialTower.{u}}
    {T₂ : CoaugmentedCosimplicialTower.{v}}
    (e : CoaugmentedCosimplicialTowerIso T₁ T₂) :
    CoaugmentedCosimplicialTowerIso T₂ T₁ where
  coaugEquiv := e.coaugEquiv.symm
  levelEquiv n := (e.levelEquiv n).symm
  comm_coaug y := by
    apply (e.levelEquiv 0).injective
    rw [Equiv.apply_symm_apply, e.comm_coaug, Equiv.apply_symm_apply]
  comm_coface n i y := by
    apply (e.levelEquiv (n + 1)).injective
    rw [Equiv.apply_symm_apply, e.comm_coface, Equiv.apply_symm_apply]
  comm_codegeneracy n j y := by
    apply (e.levelEquiv n).injective
    rw [Equiv.apply_symm_apply, e.comm_codegeneracy, Equiv.apply_symm_apply]

/-- Step 1 of Theorem 3.2.5 (lines 1320–1322): By Proposition 3.2.5 (`liftedUnitIsoOfHeightNConnected`),
for `M` of height `n` and connectivity `≥ 2p^n + 1`, the unit isomorphism `M ≅ α^* α_* M`
induces a canonical isomorphism of cobar complexes:
`Hom_{U_Γ}(BP, U_Γ^•(M)) ≃ Hom_{U_Γ}(BP, U_Γ^•(α^* α_* M))`. -/
noncomputable def unstableHeightNUnitCobarIso
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    {BnTensor : Comonad.Coalgebra U_Γ ⥤ Comonad.Coalgebra U_Γ}
    (BP : Comonad.Coalgebra U_Γ)
    {M : Comonad.Coalgebra U_Γ} (hM : IsHeightNConnected U_Γ adj BnTensor M) :
    CoaugmentedCosimplicialTowerIso
      (cobarCosimplicialHomTower BP M)
      (cobarCosimplicialHomTower BP
        ((unstableCotensor U_Γ adj).obj ((unstablePushforward U_Γ adj).obj M))) :=
  cobarCosimplicialHomTowerIsoOfIso BP (liftedUnitIsoOfHeightNConnected U_Γ adj hM)

/-- Step 2 of Theorem 3.2.5 (lines 1320–1322): By Generalized Shapiro's Lemma (Proposition 2.5.2),
the lifted adjunction `α_* ⊣ α^*` induces a canonical isomorphism of coaugmented cosimplicial
hom-towers:
`Hom_{U_Σ}(α_* BP, U_Σ^•(α_* M)) ≃ Hom_{U_Γ}(BP, α^* U_Σ^•(α_* M))`. -/
noncomputable def unstableShapiroCobarIso
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (BP M : Comonad.Coalgebra U_Γ) :
    CoaugmentedCosimplicialTowerIso
      (cobarCosimplicialHomTower
        ((unstablePushforward U_Γ adj).obj BP)
        ((unstablePushforward U_Γ adj).obj M))
      (pullbackCosimplicialHomTower (unstableComonadFunctor U_Γ adj) adj
        BP ((unstablePushforward U_Γ adj).obj M)) :=
  generalizedShapiroCobarIso (unstableComonadFunctor U_Γ adj) adj
    BP ((unstablePushforward U_Γ adj).obj M)

/-- **Theorem 3.2.5 (Unstable Change of Rings, p. 36, lines 1313–1326)**:
Let `BP` be a `U_Γ`-comodule (representing `BP_*`, so `α_* BP = K(n)_* ⊗_{BP_*} BP_* ≅ K(n)_*`),
and let `M` be a `U_Γ`-comodule of height `n` and connectivity `≥ 2p^n + 1`
(`hM : IsHeightNConnected U_Γ adj BnTensor M`).
Combining the height-`n` unit isomorphism `M ≅ α^* α_* M` (`unstableHeightNUnitCobarIso`) with
Generalized Shapiro's Lemma (`generalizedShapiroExtCobarIso`) yields the canonical isomorphism of
coaugmented cosimplicial cobar complexes:
`Hom_{U_Γ}(BP, U_Γ^•(M)) ≃ Hom_{U_Σ}(K(n)_* ⊗_{BP_*} BP, U_Σ^•(K(n)_* ⊗_{BP_*} M))`
computing
`Ext_{U_Γ}(BP_*, M) ≃ Ext_{U_Σ}(K(n)_*, K(n)_* ⊗_{BP_*} M)`. -/
noncomputable def unstableChangeOfRingsCobarIso
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    {BnTensor : Comonad.Coalgebra U_Γ ⥤ Comonad.Coalgebra U_Γ}
    (BP : Comonad.Coalgebra U_Γ)
    {M : Comonad.Coalgebra U_Γ} (hM : IsHeightNConnected U_Γ adj BnTensor M)
    (eRes : CoaugmentedCosimplicialTowerIso
      (pullbackCosimplicialHomTower (unstableComonadFunctor U_Γ adj) adj
        BP ((unstablePushforward U_Γ adj).obj M))
      (cobarCosimplicialHomTower BP
        ((unstableCotensor U_Γ adj).obj ((unstablePushforward U_Γ adj).obj M)))) :
    CoaugmentedCosimplicialTowerIso
      (cobarCosimplicialHomTower BP M)
      (cobarCosimplicialHomTower
        ((unstablePushforward U_Γ adj).obj BP)
        ((unstablePushforward U_Γ adj).obj M)) :=
  (unstableHeightNUnitCobarIso U_Γ adj BP hM).trans
    (CoaugmentedCosimplicialTowerIso.symm
      (generalizedShapiroExtCobarIso (unstableComonadFunctor U_Γ adj) adj
        BP ((unstablePushforward U_Γ adj).obj M) eRes))

/-- **Theorem 3.2.5 (Bousfield Weak `U_Γ`-Resolution Verification, p. 36, lines 1320–1322)**:
By Proposition 3.2.3 & Proposition 3.2.4, when the underlying functor `G.forget ∘ α^*` is
naturally isomorphic to `W ∘ H.forget` (where `W = B(n)_* ⊗_{K(n)_*} -`), for every
`U_Σ`-comodule `N` (such as `N = α_* M = K(n)_* ⊗_{BP_*} M`) and every cofree `U_Γ`-comodule
`U_Γ(J)`, the augmented simplicial hom-tower
`Hom_{U_Γ}(α^* U_Σ^•(N), U_Γ(J)) → Hom_{U_Γ}(α^* N, U_Γ(J))`
is a `LeftContractibleTower`, verifying the Bousfield `U_Γ`-equivalence hypothesis of
Generalized Shapiro's Lemma on line 1320. -/
noncomputable def unstablePullbackCobarLeftContractibleTower
    [HasEqualizers (Comonad.Coalgebra U_Γ)]
    (W : D ⥤ C)
    (eW : (mateOpfunctor (unstableComonadFunctor U_Γ adj) adj).coalgebraPullback ⋙
      U_Γ.forget ≅ (unstableSigmaComonad U_Γ adj).forget ⋙ W)
    (N : Comonad.Coalgebra (unstableSigmaComonad U_Γ adj)) (J : C) :
    LeftContractibleTower.{v₁} :=
  pullbackCobarCofreeLeftContractibleTower (unstableComonadFunctor U_Γ adj) adj W eW N J

end Section3_2

end ThesisLean
