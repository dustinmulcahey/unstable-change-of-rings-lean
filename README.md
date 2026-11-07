# An Unstable Variant of the Morava Change of Rings Theorem for $K(n)$ Theory

**Author:** Dustin Mulcahey  
**Toolchain:** Lean 4 (`v4.36.0-rc2`) + Mathlib4 + `leanblueprint` + `tectonic`

### Live Interactive Links
- **[Interactive Web Blueprint](https://dustinmulcahey.github.io/unstable-change-of-rings-lean/)**
- **[Interactive Dependency Graph](https://dustinmulcahey.github.io/unstable-change-of-rings-lean/dep_graph_document.html)**
- **[Journal-Style `amsart` Paper (PDF)](https://dustinmulcahey.github.io/unstable-change-of-rings-lean/unstable_change_of_rings.pdf)**
- **[Blueprint (PDF)](https://dustinmulcahey.github.io/unstable-change-of-rings-lean/blueprint.pdf)**

This repository contains the complete Lean 4 formalization, an `amsart` journal-style LaTeX paper, and an interactive **Lean Blueprint** (with dependency graph) for Dustin Mulcahey's PhD thesis, *"An unstable variant of the Morava Change of Rings theorem for $K(n)$ theory"*.

---

## Repository Structure

### 1. Lean 4 Formalization (`ThesisLean/`)
All 2,533 lines of Lean 4 code compile with **0 `sorry`s, 0 errors, and 0 warnings**:
- [`ThesisLean/ComonadMorphisms.lean`](ThesisLean/ComonadMorphisms.lean) (**Chapter 2, §2.1–§2.3**):
  - Cokleisli category vs. Eilenberg–Moore coalgebras and comparison adjunction $j \dashv i$ (`Section2_1.cokleisliAdjoint`, Proposition 2.1.1).
  - Comonad functors $(F, \alpha)$, coalgebra pushforward $\alpha_*$ (`Section2_2.ComonadFunctor.pushforward`, Proposition 2.2.1), comonad opfunctors $(U, \beta)$, Cokleisli pushforward (`Section2_2.ComonadOpfunctor.cokleisliPushforward`, Proposition 2.2.2), and coalgebra pullback via equalizers (`Section2_2.ComonadOpfunctor.coalgebraPullback`, Proposition 2.2.3).
  - The mate correspondence (`Section2_3.mateOpfunctor`, `Section2_3.mate_fundamental_rel_counit`, Propositions 2.3.1–2.3.2) and the lifted coalgebra adjunction $\alpha_* \dashv \alpha^*$ (`Section2_3.liftedAdjunction`, Proposition 2.3.3).
- [`ThesisLean/CobarResolution.lean`](ThesisLean/CobarResolution.lean) (**Chapter 2, §2.4–§2.5**):
  - Induced monad on $\mathcal{C}^G$ (`Section2_4.inducedMonadOnCoalgebras`), the cosimplicial cobar complex $C^\bullet_G(X)$ (`Section2_4.cobarObj`), all five cosimplicial identities, and explicit left contractibility of the cobar hom-tower into cofree coalgebras (`Section2_4.cobarHomLeftContractibleTower`, Proposition 2.4.4).
  - Commutative naturality triangle (`Section2_5.shapiro_naturality_triangle_coaug`, Proposition 2.5.1), Bousfield weak-$G$-resolution preservation (`Section2_5.pullbackCobarCofreeLeftContractibleTower`), and the Generalized Shapiro's Lemma for Comonads (`Section2_5.generalizedShapiroCobarIso`, `Section2_5.generalizedShapiroExtCobarIso`, Proposition 2.5.2).
- [`ThesisLean/UnstableChangeOfRings.lean`](ThesisLean/UnstableChangeOfRings.lean) (**Chapter 3, §3.1–§3.2**):
  - Canonical split equalizer presentation of any $G$-coalgebra (`Section3_1.coalgebraCanonicalEqualizerIso`) and the stable Change of Rings cobar isomorphism (`Section3_1.stableChangeOfRingsCobarIso`).
  - General unstable sandwich comonad $U_\Sigma = F \circ U_\Gamma \circ U$ (`Section3_2.unstableSigmaComonad`, Definition 3.2.1 & Theorem 3.2.1).
  - Unstable base-change comonad functor $\alpha = F U_\Gamma(\eta)$ (`Section3_2.unstableComonadFunctor`, Definition 3.2.2 & Theorem 3.2.2).
  - Explicit mate $\beta_N = \eta_{U_\Gamma(UN)}$ and lifted adjunction $\alpha_* \dashv \alpha^*$ (`Section3_2.unstableLiftedAdjunction`, Theorem 3.2.3).
  - Lifted counit isomorphism $\alpha_*(\alpha^* N) \xrightarrow{\sim} N$ (`Section3_2.unstablePushforwardCotensorIso`, `Section3_2.isIso_unstableLiftedCounit`, Theorem 3.2.4).
  - Unstable excess bounds, left/right $v_n^{-1}$ inversion, cotensor identification $\alpha^*\alpha_* M \cong B(n)_* \otimes_{BP_*} M$, height-$n$ unit isomorphism (`Section3_2.liftedUnitIsoOfHeightNConnected`, Propositions 3.2.1–3.2.5), and the **Unstable Morava Change of Rings Theorem** (`Section3_2.unstableChangeOfRingsCobarIso`, `Section3_2.unstablePullbackCobarLeftContractibleTower`, Theorem 3.2.5).

### 2. Journal-Style `amsart` Paper (`paper/`)
- [`paper/unstable_change_of_rings.tex`](paper/unstable_change_of_rings.tex): Self-contained `amsart` article integrating the mathematical exposition with clickable `[Lean 4: ...]` badges and a full concordance table in Section 4.
- [`paper/unstable_change_of_rings.pdf`](paper/unstable_change_of_rings.pdf): Compiled PDF article.

### 3. Interactive Lean Blueprint (`blueprint/`)
- [`blueprint/src/content.tex`](blueprint/src/content.tex): Blueprint source annotated with `\lean{...}`, `\leanok`, and `\uses{...}` macros.
- [`blueprint/web/index.html`](blueprint/web/index.html): Interactive web version of the blueprint.
- [`blueprint/web/dep_graph_document.html`](blueprint/web/dep_graph_document.html): Interactive dependency graph showing every definition, proposition, and theorem verified in green.
- [`blueprint/print/blueprint.pdf`](blueprint/print/blueprint.pdf): Print PDF version of the blueprint.

---

## Building the Project

```bash
# 1. Verify all Lean 4 proofs
lake build

# 2. Compile the amsart paper PDF
cd paper && tectonic unstable_change_of_rings.tex

# 3. Build the interactive web blueprint and verify all \lean{...} declarations
leanblueprint web
leanblueprint checkdecls
```
