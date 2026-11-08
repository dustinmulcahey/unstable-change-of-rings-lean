# An Unstable Variant of the Morava Change of Rings Theorem for $K(n)$ Theory

**Author:** Dustin Mulcahey  
**Original Dissertation:** Ph.D. Thesis, The Graduate Center, City University of New York (Advisors: Robert Thompson & Martin Bendersky)  
**Formalization:** Lean 4 (`v4.36.0-rc2`) + Mathlib4 (`0 sorry`s, `0 warnings`, 2,533 lines of code)

---

## Web Version & PDF Documents

| Resource | Description | Link |
| :--- | :--- | :--- |
| **Interactive Web Blueprint** | Chapter-by-chapter HTML version with clickable `L∃∀N` buttons linking every definition, proposition, and theorem directly to its Lean 4 proof | **[Open Web Blueprint](https://dustinmulcahey.github.io/unstable-change-of-rings-lean/)** |
| **Interactive Dependency Graph** | Full logical dependency graph of the thesis (all nodes verified in dark green); click any node to view its statement and jump to the Lean source | **[Open Dependency Graph](https://dustinmulcahey.github.io/unstable-change-of-rings-lean/dep_graph_document.html)** |
| **Journal-Style `amsart` Paper (PDF)** | Self-contained article version of the thesis updated with the generalized categorical theorems and `[Lean 4]` margin/header badges + full concordance table | **[`unstable_change_of_rings.pdf`](https://dustinmulcahey.github.io/unstable-change-of-rings-lean/unstable_change_of_rings.pdf)** ([repo copy](paper/unstable_change_of_rings.pdf), [LaTeX source](paper/unstable_change_of_rings.tex)) |
| **Blueprint Print Version (PDF)** | Printable PDF companion generated from the Lean Blueprint source | **[`blueprint.pdf`](https://dustinmulcahey.github.io/unstable-change-of-rings-lean/blueprint.pdf)** ([repo copy](blueprint/print/blueprint.pdf), [LaTeX source](blueprint/src/content.tex)) |
| **Original PhD Thesis (PDF)** | Original CUNY Ph.D. dissertation typeset in `CUNY_PhD.cls` | **[`changeofcomonads_original_thesis.pdf`](https://dustinmulcahey.github.io/unstable-change-of-rings-lean/changeofcomonads_original_thesis.pdf)** ([repo copy](paper/changeofcomonads_original_thesis.pdf)) |

---

## Project Overview

This project provides a complete, machine-checked Lean 4 formalization of Dustin Mulcahey's Ph.D. thesis, *"An unstable variant of the Morava Change of Rings theorem for $K(n)$ theory"*.

The mathematical work has two main parts:

1. **Comonadic Base Change and a Generalized Shapiro's Lemma (Chapter 2):**
   - In Bousfield's cosimplicial model structure on the category $\mathbf{c}\mathcal{C}^G$ of cosimplicial Eilenberg–Moore coalgebras over a comonad $G$, the classical cobar resolution $C^\bullet_G(X)$ serves as a resolving object for derived mapping spaces and $\mathrm{Ext}_G$ computations.
   - Given an adjunction $F \dashv U : \mathcal{D} \to \mathcal{C}$ and a functor of comonads $(F, \alpha) : (\mathcal{C}, G) \to (\mathcal{D}, H)$, the mate correspondence of Street and Meyer yields an opfunctor of comonads $(U, \beta) : (\mathcal{D}, H) \to (\mathcal{C}, G)$ and, when $\mathcal{C}^G$ has equalizers, a lifted adjunction $\alpha_* \dashv \alpha^*$ between coalgebra categories $\mathcal{C}^G$ and $\mathcal{D}^H$.
   - **Generalized Shapiro's Lemma for Comonads (Proposition 2.5.2):** When the underlying functor of $\alpha^*$ factors through a functor $W : \mathcal{D} \to \mathcal{C}$ on underlying categories ($U_G \circ \alpha^* \cong W \circ U_H$), $\alpha^*$ preserves the left contractibility of cobar resolutions into cofree coalgebras, inducing an isomorphism of cosimplicial cobar hom-towers and comonadic $\mathrm{Ext}$:
     $$\mathrm{Hom}_{\mathcal{C}^G}\!\big(M,\, \alpha^* C^\bullet_H(N)\big) \;\cong\; \mathrm{Hom}_{\mathcal{D}^H}\!\big(\alpha_* M,\, C^\bullet_H(N)\big), \qquad \mathrm{Ext}_G(M, \alpha^* N) \;\cong\; \mathrm{Ext}_H(\alpha_* M, N).$$

2. **An Unstable Morava Change of Rings Theorem (Chapter 3):**
   - Stably, the Morava change of rings theorem reduces $\mathrm{Ext}_{BP_*BP}(BP_*, M)$ for $v_n$-periodic comodules to $\mathrm{Ext}_{\Sigma(n)}(K(n)_*, K(n)_* \otimes_{BP_*} M)$.
   - Unstably, unstable $BP_*$-comodules are coalgebras over a non-additive comonad $U_\Gamma$ defined via the Bendersky–Curtis–Miller excess condition $2\,\mathrm{len}(I) < \mathrm{deg}(m)$.
   - We construct an unstable Morava stabilizer comonad $U_\Sigma(N) = K(n)_* \otimes_{BP_*} U_\Gamma(N)$ on $K(n)_*$-modules, a base-change comonad functor $\alpha : K(n)_* \otimes_{BP_*} U_\Gamma(-) \to U_\Sigma(K(n)_* \otimes_{BP_*} -)$, and its right adjoint unstable cotensor $\alpha^* = B(n)_* \Box_{\Sigma(n)_*} -$.
   - **Unstable Change of Rings Theorem (Theorem 3.2.5):** By destabilizing the Miller–Ravenel filtration argument in the excess range $k \ge 2p^n + 1$, we prove that for any height-$n$ unstable $U_\Gamma$-comodule $M$ of connectivity $k \ge 2p^n + 1$, the lifted adjunction unit $M \xrightarrow{\sim} \alpha^*\alpha_* M$ is an isomorphism and the Generalized Shapiro's Lemma yields:
     $$\mathrm{Ext}_{U_\Gamma}(BP_*,\, M) \;\cong\; \mathrm{Ext}_{U_\Sigma}\!\big(K(n)_*,\, K(n)_* \otimes_{BP_*} M\big).$$

---

## Mathematical Insights from the Lean 4 Formalization

Translating the thesis into Lean 4 confirmed every theorem in Chapters 2 and 3 and uncovered several clean categorical strengthenings:

1. **General "Sandwich Comonad" Construction (§3.2.2–§3.2.4):**
   In the original text, the comonad laws for $U_\Sigma(N) = K(n)_* \otimes_{BP_*} U_\Gamma(N)$ and the comonad functor $\alpha$ used the localization identity $K(n)_* \otimes_{BP_*} N = N$ ($\varepsilon : F U \xrightarrow{\sim} \mathrm{Id}$). In Lean 4, keeping $F$ and $U$ distinct revealed that for **any** comonad $U_\Gamma$ on $\mathcal{C}$ and **any** adjunction $F \dashv U : \mathcal{D} \to \mathcal{C}$ (without assuming $F U \cong \mathrm{Id}$), the sandwich endofunctor
   $$U_\Sigma := F \circ U_\Gamma \circ U : \mathcal{D} \to \mathcal{D}$$
   is a comonad ([`unstableSigmaComonad`](ThesisLean/UnstableChangeOfRings.lean#L218)), $\alpha := F U_\Gamma(\eta)$ is a comonad functor ([`unstableComonadFunctor`](ThesisLean/UnstableChangeOfRings.lean#L258)), and $\alpha_* \dashv \alpha^*$ lifts to coalgebras ([`unstableLiftedAdjunction`](ThesisLean/UnstableChangeOfRings.lean#L326)).
2. **Definitional Equality on Cofree Coalgebras (`rfl`):**
   In the proof of Theorem 3.2.4 ($\alpha_*\alpha^* N \cong N$), pushing forward a cofree $U_\Gamma$-coalgebra on $U Y$ along $\alpha_*$ produces the cofree $U_\Sigma$-coalgebra on $Y$ **by definitional equality (`rfl`)** in Lean ([`unstablePushforward_obj_cofree`](ThesisLean/UnstableChangeOfRings.lean#L401)). Consequently, the unique comparison isomorphism $\alpha_*\alpha^* N \xrightarrow{\sim} N$ is proved to be literally the counit of the lifted adjunction ([`unstableCanonicalEqualizer_lift_eq_liftedCounit`](ThesisLean/UnstableChangeOfRings.lean#L455)).
3. **Explicit Cobar Cosimplicial Identities and Contracting Homotopies:**
   Rather than axiomatizing Bousfield's model structure, we proved all five cosimplicial identities for $C^\bullet_G(X)$ by induction on cosimplicial degree and constructed the explicit left contracting homotopies on $\mathrm{Hom}_{\mathcal{C}^G}(C^\bullet_G(X), G(J))$ ([`cobarHomLeftContractibleTower`](ThesisLean/CobarResolution.lean#L515)) and $\mathrm{Hom}_{\mathcal{C}^G}(\alpha^* C^\bullet_H(N), G(J))$ ([`pullbackCobarCofreeLeftContractibleTower`](ThesisLean/CobarResolution.lean#L967)).

---

## Theorem-to-Lean Concordance

| Thesis Section & Result | Lean 4 File | Lean 4 Declaration(s) |
| :--- | :--- | :--- |
| **§2.1** Kleisli vs. Eilenberg–Moore coalgebras (Prop. 2.1.1) | [`ComonadMorphisms.lean`](ThesisLean/ComonadMorphisms.lean) | [`cokleisliToCoalgebra`](ThesisLean/ComonadMorphisms.lean#L57), [`coalgebraToCokleisli`](ThesisLean/ComonadMorphisms.lean#L83), [`cokleisliToCoalgebraFullyFaithful`](ThesisLean/ComonadMorphisms.lean#L95) |
| **§2.2** Comonad functors & pushforward $\alpha_*$ (Def. 2.2.1, Prop. 2.2.1) | [`ComonadMorphisms.lean`](ThesisLean/ComonadMorphisms.lean) | [`ComonadFunctor`](ThesisLean/ComonadMorphisms.lean#L135), [`ComonadFunctor.pushforward`](ThesisLean/ComonadMorphisms.lean#L157) |
| **§2.2** Comonad opfunctors & pullback $\alpha^*$ (Def. 2.2.2, Props. 2.2.2–2.2.3) | [`ComonadMorphisms.lean`](ThesisLean/ComonadMorphisms.lean) | [`ComonadOpfunctor`](ThesisLean/ComonadMorphisms.lean#L186), [`cokleisliPushforward`](ThesisLean/ComonadMorphisms.lean#L211), [`coalgebraPullback`](ThesisLean/ComonadMorphisms.lean#L291) |
| **§2.3** Mate correspondence & lifted adjunction $\alpha_* \dashv \alpha^*$ (Props. 2.3.1–2.3.3) | [`ComonadMorphisms.lean`](ThesisLean/ComonadMorphisms.lean) | [`mate_fundamental_rel_counit`](ThesisLean/ComonadMorphisms.lean#L353), [`mateOpfunctor`](ThesisLean/ComonadMorphisms.lean#L392), [`liftedAdjunction`](ThesisLean/ComonadMorphisms.lean#L552) |
| **§2.4** Induced monad & cosimplicial cobar complex $C^\bullet_G(X)$ | [`CobarResolution.lean`](ThesisLean/CobarResolution.lean) | [`inducedMonadOnCoalgebras`](ThesisLean/CobarResolution.lean#L65), [`cobarObj`](ThesisLean/CobarResolution.lean#L155), [`cobarCoface`](ThesisLean/CobarResolution.lean#L160), [`cobarCodegeneracy`](ThesisLean/CobarResolution.lean#L166) |
| **§2.4** Cosimplicial identities & left contractibility (Prop. 2.4.4) | [`CobarResolution.lean`](ThesisLean/CobarResolution.lean) | [`cobarCoface_comp_cobarCoface`](ThesisLean/CobarResolution.lean#L259), [`cobarHomLeftContractibleTower`](ThesisLean/CobarResolution.lean#L515) |
| **§2.5** Shapiro naturality triangle & Generalized Shapiro's Lemma (Props. 2.5.1–2.5.2) | [`CobarResolution.lean`](ThesisLean/CobarResolution.lean) | [`shapiro_naturality_triangle_coaug`](ThesisLean/CobarResolution.lean#L859), [`pullbackCobarCofreeLeftContractibleTower`](ThesisLean/CobarResolution.lean#L967), [`generalizedShapiroExtCobarIso`](ThesisLean/CobarResolution.lean#L834) |
| **§3.1** Canonical coalgebra equalizer & Stable Change of Rings | [`UnstableChangeOfRings.lean`](ThesisLean/UnstableChangeOfRings.lean) | [`coalgebraCanonicalEqualizerIso`](ThesisLean/UnstableChangeOfRings.lean#L148), [`stableChangeOfRingsCobarIso`](ThesisLean/UnstableChangeOfRings.lean#L168) |
| **§3.2.2** Unstable comonad $U_\Sigma$ (Def. 3.2.1, Thm. 3.2.1) | [`UnstableChangeOfRings.lean`](ThesisLean/UnstableChangeOfRings.lean) | [`unstableSigmaComonad`](ThesisLean/UnstableChangeOfRings.lean#L218) |
| **§3.2.3** Unstable comonad morphism $\alpha$ (Def. 3.2.2, Thm. 3.2.2) | [`UnstableChangeOfRings.lean`](ThesisLean/UnstableChangeOfRings.lean) | [`unstableComonadFunctor`](ThesisLean/UnstableChangeOfRings.lean#L258) |
| **§3.2.4** Unstable cotensor & lifted adjunction $\alpha_* \dashv \alpha^*$ (Thm. 3.2.3) | [`UnstableChangeOfRings.lean`](ThesisLean/UnstableChangeOfRings.lean) | [`unstableMateNatTrans_app`](ThesisLean/UnstableChangeOfRings.lean#L291), [`unstableLiftedAdjunction`](ThesisLean/UnstableChangeOfRings.lean#L326) |
| **§3.2.5** Lifted counit isomorphism $\alpha_*\alpha^* N \cong N$ (Thm. 3.2.4) | [`UnstableChangeOfRings.lean`](ThesisLean/UnstableChangeOfRings.lean) | [`unstablePushforwardCotensorIso`](ThesisLean/UnstableChangeOfRings.lean#L469), [`isIso_unstableLiftedCounit`](ThesisLean/UnstableChangeOfRings.lean#L486) |
| **§3.2.6** Excess bounds, $v_n^{-1}$ inversion, cotensor & unit isomorphisms (Props. 3.2.1–3.2.5) | [`UnstableChangeOfRings.lean`](ThesisLean/UnstableChangeOfRings.lean) | [`excess_vn_shift_iff`](ThesisLean/UnstableChangeOfRings.lean#L502), [`excess_ul_action_iff`](ThesisLean/UnstableChangeOfRings.lean#L510), [`prop3_2_2_colimit_iso`](ThesisLean/UnstableChangeOfRings.lean#L571), [`prop3_2_3_unitPullbackIso`](ThesisLean/UnstableChangeOfRings.lean#L624), [`prop3_2_4_cotensor_cofree`](ThesisLean/UnstableChangeOfRings.lean#L644), [`liftedUnitIsoOfHeightNConnected`](ThesisLean/UnstableChangeOfRings.lean#L708) |
| **§3.2.6** **Unstable Change of Rings Theorem** (Thm. 3.2.5) | [`UnstableChangeOfRings.lean`](ThesisLean/UnstableChangeOfRings.lean) | [`unstableChangeOfRingsCobarIso`](ThesisLean/UnstableChangeOfRings.lean#L920), [`unstablePullbackCobarLeftContractibleTower`](ThesisLean/UnstableChangeOfRings.lean#L945) |

---

## Building & Verifying Locally

```bash
# 1. Build and verify all Lean 4 proofs (0 sorrys, 0 warnings)
lake build

# 2. Verify that all 38 blueprint declarations exist in the compiled Lean environment
lake exe checkdecls blueprint/lean_decls

# 3. Compile the journal-style amsart paper PDF
cd paper && tectonic unstable_change_of_rings.tex

# 4. Build the interactive web blueprint and post-process GitHub line links
leanblueprint web
python3 scripts/postprocess_web.py
```
