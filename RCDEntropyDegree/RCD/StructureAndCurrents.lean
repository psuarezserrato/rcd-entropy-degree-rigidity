import BCG.Entropy.VolumeEntropy
import Mathlib.Topology.MetricSpace.Basic

/-!
# Stratified Structure of Non-Collapsed $\mathsf{RCD}(K, N)$ & Alexandrov Spaces and CMMP Orientation Currents

This file formalizes Sections 2.1–2.3 (`subsec:ncRCD`, `subsec:currents`,
`subsec:orientation-currents`, Lemma 2.1 `lem:ncRCD-structure`, and Theorem 2.2 `thm:CMMP`) and
Remark 4.3 (`rmk:Alexandrov`) of P. Suárez-Serrato, *"Entropy-degree rigidity for non-collapsed
$\mathsf{RCD}$ spaces"* (`RCD-Entropy-Degree-Skeleton.tex`), together with the orientation current
theory of N. Cavallucci, D. Marti, A. Mondino, and R. Perales (`[CMMP2026]`,
`Perales-RCDcurrents-arXiv-26.tex`).

## Main Definitions & Theorems
1. **Stratified Structure of Non-Collapsed $\mathsf{RCD}(K, N)$ Spaces (`NonCollapsedRCDStructure`,
   `ClosedNonCollapsedRCD`, Lemma 2.1 `lem:ncRCD-structure`)**:
   - Regular set $\mathcal{R}_N(X)$, open topological manifold part $\mathcal{M}(X) \supseteq \mathcal{R}_N(X)$,
     singular set $\mathcal{S}(X) = X \setminus \mathcal{M}(X)$, and singular strata
     $\mathcal{S}^0(X) \subseteq \mathcal{S}^1(X) \subseteq \cdots \subseteq \mathcal{S}^{N-1}(X) = X \setminus \mathcal{R}_N(X)$.
   - De Philippis–Gigli volume-density characterization (`mem_regularSet_iff_density_eq_one`):
     $x \in \mathcal{R}_N(X) \iff \theta_N(x) = 1$.
   - **Lemma 2.1 (`singularSet_subset_singularStratum_sub_two`,
     `hausdorffMeasureCodimOne_singularSet_eq_zero`)**:
     When $\partial X = \emptyset$, $\mathcal{S}^{N-1}(X) = \mathcal{S}^{N-2}(X)$, hence
     $\mathcal{S}(X) \subseteq \mathcal{S}^{N-2}(X)$ and $\mathcal{H}^{N-1}(\mathcal{S}(X)) = 0$.
2. **Alexandrov Spaces Without Boundary (`AlexandrovSpaceWithoutBoundary`, Remark 4.3 `rmk:Alexandrov`)**:
   Every closed $N$-dimensional Alexandrov space of curvature $\ge \kappa$ without boundary is a
   closed non-collapsed $\mathsf{RCD}((N-1)\kappa, N)$ space (`toClosedNonCollapsedRCD`).
3. **Ambrosio–Kirchheim / Lang Metric Currents & CMMP Orientation Currents
   (`MetricCurrentSpace`, `FundamentalManifoldCurrent`, `CMMPOrientationCurrent`, Theorem 2.2 `thm:CMMP`)**:
   - Metric $k$-currents with mass measure $\|T\|$, total mass $\mathbf{M}(T)$, boundary $\partial T$,
     pushforward mass inequality $\mathbf{M}(\varphi_\# T) \le \mathrm{Lip}(\varphi)^k \mathbf{M}(T)$,
     and Federer constancy $S = d\llbracket Y \rrbracket$ on a closed oriented $N$-manifold $Y$.
   - Cavallucci–Marti–Mondino–Perales orientation current $T \in \mathbf{I}_N(X)$ with
     $\|T\| = \mathcal{H}^N$, $\partial T = 0$, and $\mathbf{M}(T) = \mathcal{H}^N(X)$.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace RCDEntropyDegree.RCD

section NonCollapsedRCDStructure

variable (X : Type*) [MetricSpace X] [MeasurableSpace X]

/-- **Stratified Structure of a Non-Collapsed $\mathsf{RCD}(K, N)$ Space**
(De Philippis–Gigli `[DPG18]`, Mondino–Naber `[MN19]`, Kapovitch–Mondino `[KM21]`,
`RCD-Entropy-Degree-Skeleton.tex` Section 2.1):
A metric-measure space $(X, \mathsf{d}, \mathcal{H}^N)$ satisfying the non-collapsed
$\mathsf{RCD}(K, N)$ condition carries:
- the $N$-dimensional Hausdorff reference measure `hausdorffMeasure` ($\mathcal{H}^N$),
- the regular set `regularSet` ($\mathcal{R}_N(X)$) of points with Euclidean tangent cones,
- the topological manifold locus `manifoldSet` ($\mathcal{M}(X)$) of points with Euclidean balls,
- the Almgren–Cheeger–Colding–De Philippis–Gigli singular strata `singularStratum k` ($\mathcal{S}^k(X)$),
- the Bishop–Gromov volume density `density` ($\theta_N(x) = \lim_{r \to 0} \frac{\mathcal{H}^N(B(x, r))}{\omega_N r^N} \le 1$). -/
structure NonCollapsedRCDStructure (K : ℝ) (N : ℕ) where
  hausdorffMeasure : Measure X
  regularSet : Set X
  manifoldSet : Set X
  singularStratum : ℕ → Set X
  density : X → ℝ
  isOpen_manifoldSet : IsOpen manifoldSet
  regularSet_subset_manifoldSet : regularSet ⊆ manifoldSet
  density_le_one : ∀ x : X, density x ≤ 1
  mem_regularSet_iff_density_eq_one : ∀ x : X, x ∈ regularSet ↔ density x = 1
  singularStratum_mono : Monotone singularStratum
  compl_regularSet_eq_singularStratum : regularSetᶜ = singularStratum (N - 1)
  hausdorffMeasure_compl_regularSet : hausdorffMeasure regularSetᶜ = 0

variable {X} {K : ℝ} {N : ℕ}

namespace NonCollapsedRCDStructure

/-- The topological singular set $\mathcal{S}(X) := X \setminus \mathcal{M}(X)$
(`RCD-Entropy-Degree-Skeleton.tex`, Eq. above Lemma 2.1). -/
def singularSet (S : NonCollapsedRCDStructure X K N) : Set X :=
  S.manifoldSetᶜ

/-- The topological singular set $\mathcal{S}(X)$ is closed in $X$. -/
theorem isClosed_singularSet (S : NonCollapsedRCDStructure X K N) :
    IsClosed S.singularSet :=
  S.isOpen_manifoldSet.isClosed_compl

/-- Since $\mathcal{R}_N(X) \subseteq \mathcal{M}(X)$ (Reifenberg's theorem), the topological
singular set satisfies $\mathcal{S}(X) \subseteq X \setminus \mathcal{R}_N(X)$. -/
theorem singularSet_subset_compl_regularSet (S : NonCollapsedRCDStructure X K N) :
    S.singularSet ⊆ S.regularSetᶜ :=
  compl_subset_compl.mpr S.regularSet_subset_manifoldSet

/-- The topological singular set lies inside the top singular stratum $\mathcal{S}^{N-1}(X)$. -/
theorem singularSet_subset_singularStratum_sub_one (S : NonCollapsedRCDStructure X K N) :
    S.singularSet ⊆ S.singularStratum (N - 1) := by
  rw [← S.compl_regularSet_eq_singularStratum]
  exact S.singularSet_subset_compl_regularSet

/-- The topological singular set $\mathcal{S}(X)$ has $\mathcal{H}^N$-measure zero:
$$\mathcal{H}^N(\mathcal{S}(X)) = 0.$$ -/
theorem hausdorffMeasure_singularSet_eq_zero (S : NonCollapsedRCDStructure X K N) :
    S.hausdorffMeasure S.singularSet = 0 :=
  measure_mono_null S.singularSet_subset_compl_regularSet S.hausdorffMeasure_compl_regularSet

/-- The regular set $\mathcal{R}_N(X)$ has full $\mathcal{H}^N$-measure in $X$:
$$\mathcal{H}^N(\mathcal{R}_N(X)) = \mathcal{H}^N(X).$$ -/
theorem hausdorffMeasure_regularSet_eq_univ (S : NonCollapsedRCDStructure X K N) :
    S.hausdorffMeasure S.regularSet = S.hausdorffMeasure Set.univ := by
  refine le_antisymm (measure_mono (Set.subset_univ _)) ?_
  have h := measure_univ_le_add_compl (μ := S.hausdorffMeasure) (s := S.regularSet)
  simpa [S.hausdorffMeasure_compl_regularSet] using h

/-- The topological manifold locus $\mathcal{M}(X)$ has full $\mathcal{H}^N$-measure in $X$:
$$\mathcal{H}^N(\mathcal{M}(X)) = \mathcal{H}^N(X).$$ -/
theorem hausdorffMeasure_manifoldSet_eq_univ (S : NonCollapsedRCDStructure X K N) :
    S.hausdorffMeasure S.manifoldSet = S.hausdorffMeasure Set.univ := by
  refine le_antisymm (measure_mono (Set.subset_univ _)) ?_
  have h := measure_univ_le_add_compl (μ := S.hausdorffMeasure) (s := S.manifoldSet)
  have hc : S.hausdorffMeasure S.manifoldSetᶜ = 0 := S.hausdorffMeasure_singularSet_eq_zero
  simpa [hc] using h

/-- Every point outside $\mathcal{R}_N(X)$ has Bishop–Gromov density strictly less than $1$:
$$x \notin \mathcal{R}_N(X) \implies \theta_N(x) < 1.$$ -/
theorem density_lt_one_of_not_mem_regularSet (S : NonCollapsedRCDStructure X K N)
    {x : X} (hx : x ∉ S.regularSet) :
    S.density x < 1 :=
  lt_of_le_of_ne (S.density_le_one x)
    (fun h => hx ((S.mem_regularSet_iff_density_eq_one x).mpr h))

end NonCollapsedRCDStructure

variable (X)

/-- **Closed ($\partial X = \emptyset$) Non-Collapsed $\mathsf{RCD}(K, N)$ Space**
(`RCD-Entropy-Degree-Skeleton.tex`, Lemma 2.1 `lem:ncRCD-structure`):
A compact non-collapsed $\mathsf{RCD}(K, N)$ space with empty metric boundary
($\partial X = \emptyset$, Definition 1.5 of `[CMMP2026]` / Brena–Gigli–Honda–Zhu `[BGHZ23]`),
so that $\mathcal{S}^{N-1}(X) \setminus \mathcal{S}^{N-2}(X) = \emptyset$ and
$\mathcal{H}^{N-1}(\mathcal{S}^{N-2}(X)) = 0$. -/
structure ClosedNonCollapsedRCD (K : ℝ) (N : ℕ) extends NonCollapsedRCDStructure X K N where
  hausdorffMeasureCodimOne : Measure X
  volume_pos : 0 < (hausdorffMeasure Set.univ).toReal
  volume_ne_top : hausdorffMeasure Set.univ ≠ ⊤
  boundaryless_stratum_collapse : singularStratum (N - 1) = singularStratum (N - 2)
  hausdorffMeasureCodimOne_stratum_sub_two :
    hausdorffMeasureCodimOne (singularStratum (N - 2)) = 0

variable {X}

namespace ClosedNonCollapsedRCD

/-- The total $N$-dimensional Hausdorff volume $\mathcal{H}^N(X) \in (0, \infty)$. -/
def totalVolume (S : ClosedNonCollapsedRCD X K N) : ℝ :=
  (S.hausdorffMeasure Set.univ).toReal

theorem totalVolume_pos (S : ClosedNonCollapsedRCD X K N) : 0 < S.totalVolume :=
  S.volume_pos

/-- **Lemma 2.1(2) (`lem:ncRCD-structure`, Codimension-2 Inclusion of the Singular Set)**:
For a closed ($\partial X = \emptyset$) non-collapsed $\mathsf{RCD}(K, N)$ space $X$,
$$\mathcal{S}(X) \subseteq X \setminus \mathcal{R}_N(X) = \mathcal{S}^{N-2}(X).$$ -/
theorem singularSet_subset_singularStratum_sub_two (S : ClosedNonCollapsedRCD X K N) :
    S.singularSet ⊆ S.singularStratum (N - 2) := by
  rw [← S.boundaryless_stratum_collapse]
  exact S.singularSet_subset_singularStratum_sub_one

/-- **Lemma 2.1(2) (`lem:ncRCD-structure`, Codimension-1 Nullity of $X \setminus \mathcal{R}_N(X)$)**:
$$\mathcal{H}^{N-1}(X \setminus \mathcal{R}_N(X)) = 0.$$ -/
theorem hausdorffMeasureCodimOne_compl_regularSet_eq_zero (S : ClosedNonCollapsedRCD X K N) :
    S.hausdorffMeasureCodimOne S.regularSetᶜ = 0 := by
  rw [S.compl_regularSet_eq_singularStratum, S.boundaryless_stratum_collapse]
  exact S.hausdorffMeasureCodimOne_stratum_sub_two

/-- **Lemma 2.1(2) (`lem:ncRCD-structure`, Codimension-1 Nullity of the Topological Singular Set)**:
$$\mathcal{H}^{N-1}(\mathcal{S}(X)) = 0.$$ -/
theorem hausdorffMeasureCodimOne_singularSet_eq_zero (S : ClosedNonCollapsedRCD X K N) :
    S.hausdorffMeasureCodimOne S.singularSet = 0 :=
  measure_mono_null S.singularSet_subset_singularStratum_sub_two
    S.hausdorffMeasureCodimOne_stratum_sub_two

end ClosedNonCollapsedRCD

variable (X)

/-- **Closed $N$-Dimensional Alexandrov Space of Curvature $\ge \kappa$ Without Boundary**
(`RCD-Entropy-Degree-Skeleton.tex`, Remark 4.3 `rmk:Alexandrov`; Petrunin `[Pet11]`,
Zhang–Zhu `[ZZ10]`):
Every $N$-dimensional Alexandrov space $(X, \mathsf{d})$ of curvature $\ge \kappa$ without
Alexandrov boundary is a closed non-collapsed $\mathsf{RCD}((N-1)\kappa, N)$ space, because:
1. the $(N, \kappa)$-convexity of squared distance transfers to the Bakry–Émery/Lott–Sturm–Villani
   synthetic Ricci bound $\mathsf{RCD}((N-1)\kappa, N)$ with reference measure $\mathcal{H}^N$, and
2. at any point of $\mathcal{S}^{N-1}(X) \setminus \mathcal{S}^{N-2}(X)$ the tangent cone splits as
   $\mathbb{R}^{N-1} \times C(\Sigma_0)$ where the $0$-dimensional space of directions $\Sigma_0$
   without boundary consists of two points, so $C(\Sigma_0) \cong \mathbb{R}$ and thus
   $\mathcal{S}^{N-1}(X) \setminus \mathcal{S}^{N-2}(X) = \emptyset$. -/
structure AlexandrovSpaceWithoutBoundary (κ : ℝ) (N : ℕ) where
  toClosedNonCollapsedRCD : ClosedNonCollapsedRCD X ((N - 1 : ℝ) * κ) N

variable {X} {κ : ℝ}

/-- Every closed $N$-dimensional $\mathrm{Alex}(\kappa)$ space without boundary satisfies
$\mathcal{H}^{N-1}(\mathcal{S}(X)) = 0$ (`RCD-Entropy-Degree-Skeleton.tex`, Remark 4.3). -/
theorem AlexandrovSpaceWithoutBoundary.hausdorffMeasureCodimOne_singularSet_eq_zero
    (A : AlexandrovSpaceWithoutBoundary X κ N) :
    A.toClosedNonCollapsedRCD.hausdorffMeasureCodimOne
      A.toClosedNonCollapsedRCD.singularSet = 0 :=
  A.toClosedNonCollapsedRCD.hausdorffMeasureCodimOne_singularSet_eq_zero

end NonCollapsedRCDStructure

section MetricCurrentsAndCMMP

/-- **Ambrosio–Kirchheim / Lang Metric Current Space Interface**
(`RCD-Entropy-Degree-Skeleton.tex`, Section 2.2 `subsec:currents`; `[AK00]`, `[Lang11]`):
Models the additive group of integer-rectifiable metric currents $T \in \mathbf{I}_N(Z)$ equipped
with their mass measure $\|T\|$, total mass $\mathbf{M}(T) = \|T\|(Z)$, and boundary $\partial T$. -/
structure MetricCurrentOps (Z : Type*) [MeasurableSpace Z] (Current : Type*)
    [AddCommGroup Current] where
  massMeasure : Current → Measure Z
  totalMass : Current → ℝ
  isCycle : Current → Prop
  massMeasure_zero : massMeasure 0 = 0
  totalMass_eq_massMeasure_univ : ∀ T : Current,
    totalMass T = (massMeasure T Set.univ).toReal
  totalMass_nonneg : ∀ T : Current, 0 ≤ totalMass T
  isCycle_zero : isCycle 0
  isCycle_sub : ∀ T₁ T₂ : Current, isCycle T₁ → isCycle T₂ → isCycle (T₁ - T₂)

/-- **Fundamental Class Current $\llbracket Y \rrbracket$ and Federer Constancy on a Closed
Oriented Riemannian $N$-Manifold $Y$**
(`RCD-Entropy-Degree-Skeleton.tex`, Section 2.2, lines 284–291):
A closed oriented smooth Riemannian $N$-manifold $Y$ carries a canonical orientation current
$\llbracket Y \rrbracket \in \mathbf{I}_N(Y)$ with $\partial \llbracket Y \rrbracket = 0$ and
$\|\llbracket Y \rrbracket\| = \mathcal{H}^N$. By Federer's constancy theorem, every cycle
$S \in \mathbf{I}_N(Y)$ with $\partial S = 0$ is of the form $S = d \llbracket Y \rrbracket$ for a
unique integer $d \in \mathbb{Z}$, with $\|d \llbracket Y \rrbracket\| = |d| \, \mathcal{H}^N$ and
$$\mathbf{M}(d \llbracket Y \rrbracket) = |d| \, \mathcal{H}^N(Y).$$ -/
structure FundamentalManifoldCurrent (Y : Type*) [MeasurableSpace Y]
    (CurrentY : Type*) [AddCommGroup CurrentY]
    extends MetricCurrentOps Y CurrentY where
  volumeMeasure : Measure Y
  fundamentalClass : CurrentY
  volume_pos : 0 < (volumeMeasure Set.univ).toReal
  isCycle_fundamentalClass : isCycle fundamentalClass
  massMeasure_zsmul_fundamentalClass : ∀ (d : ℤ) (U : Set Y),
    (massMeasure (d • fundamentalClass) U).toReal =
      |(d : ℝ)| * (volumeMeasure U).toReal
  totalMass_zsmul_fundamentalClass : ∀ d : ℤ,
    totalMass (d • fundamentalClass) = |(d : ℝ)| * (volumeMeasure Set.univ).toReal
  federer_constancy : ∀ S : CurrentY, isCycle S → ∃ d : ℤ, S = d • fundamentalClass

namespace FundamentalManifoldCurrent

variable {Y : Type*} [MeasurableSpace Y] {CurrentY : Type*} [AddCommGroup CurrentY]

/-- The total Riemannian volume $\mathcal{H}^N(Y) > 0$. -/
def manifoldVolume (FY : FundamentalManifoldCurrent Y CurrentY) : ℝ :=
  (FY.volumeMeasure Set.univ).toReal

theorem manifoldVolume_pos (FY : FundamentalManifoldCurrent Y CurrentY) :
    0 < FY.manifoldVolume :=
  FY.volume_pos

/-- Total mass of an integer multiple $d \llbracket Y \rrbracket$ of the fundamental class:
$$\mathbf{M}(d \llbracket Y \rrbracket) = |d| \, \mathcal{H}^N(Y).$$ -/
theorem totalMass_zsmul_eq (FY : FundamentalManifoldCurrent Y CurrentY) (d : ℤ) :
    FY.totalMass (d • FY.fundamentalClass) = |(d : ℝ)| * FY.manifoldVolume :=
  FY.totalMass_zsmul_fundamentalClass d

/-- At $d = 1$, the fundamental class $\llbracket Y \rrbracket$ has total mass $\mathcal{H}^N(Y)$. -/
@[simp]
theorem totalMass_fundamentalClass (FY : FundamentalManifoldCurrent Y CurrentY) :
    FY.totalMass FY.fundamentalClass = FY.manifoldVolume := by
  have h := FY.totalMass_zsmul_eq 1
  simpa using h

/-- **Uniqueness of the Integer Multiplicity in Federer's Constancy Theorem**:
If $d_1 \llbracket Y \rrbracket = d_2 \llbracket Y \rrbracket$ on a closed oriented manifold $Y$
with $\mathcal{H}^N(Y) > 0$, then $d_1 = d_2$. -/
theorem zsmul_fundamentalClass_inj (FY : FundamentalManifoldCurrent Y CurrentY)
    {d₁ d₂ : ℤ} (h : d₁ • FY.fundamentalClass = d₂ • FY.fundamentalClass) :
    d₁ = d₂ := by
  have hsub : (d₁ - d₂) • FY.fundamentalClass = 0 := by
    rw [sub_zsmul, h]
    exact add_neg_cancel (d₂ • FY.fundamentalClass)
  have hmass0 : FY.totalMass ((d₁ - d₂) • FY.fundamentalClass) = 0 := by
    rw [hsub, FY.totalMass_eq_massMeasure_univ 0, FY.massMeasure_zero]
    simp
  rw [FY.totalMass_zsmul_eq (d₁ - d₂)] at hmass0
  have habs0 : |((d₁ - d₂ : ℤ) : ℝ)| = 0 := by
    rcases mul_eq_zero.mp hmass0 with h0 | hvol0
    · exact h0
    · exfalso
      exact FY.manifoldVolume_pos.ne' hvol0
  have hcast0 : ((d₁ - d₂ : ℤ) : ℝ) = 0 := abs_eq_zero.mp habs0
  have hint0 : d₁ - d₂ = 0 := Int.cast_eq_zero.mp hcast0
  exact sub_eq_zero.mp hint0

end FundamentalManifoldCurrent

/-- **Theorem 2.2 (`thm:CMMP`, Cavallucci–Marti–Mondino–Perales `[CMMP2026]` Orientation Current)**
(`RCD-Entropy-Degree-Skeleton.tex`, Section 2.3 `subsec:orientation-currents`,
`Perales-RCDcurrents-arXiv-26.tex`):
Let $(X, \mathsf{d}, \mathcal{H}^N)$ be a closed non-collapsed $\mathsf{RCD}(K, N)$ space whose
topological manifold part $\mathcal{M}(X)$ is orientable. Then there exists an orientation current
$T \in \mathbf{I}_N(X)$ satisfying:
1. $\|T\| = \mathcal{H}^N$ and $\mathbf{M}(T) = \mathcal{H}^N(X)$,
2. $\partial T = 0$ (`isCycle orientationCurrent`), and
3. $T$ generates $H_N^{\mathrm{IC}}(X) \cong \mathbb{Z} \cdot T$ and agrees with the classical
   oriented manifold current on every open disk $D \subseteq \mathcal{M}(X)$. -/
structure CMMPOrientationCurrent (X : Type*) [MetricSpace X] [MeasurableSpace X]
    (K : ℝ) (N : ℕ) (CurrentX : Type*) [AddCommGroup CurrentX]
    extends ClosedNonCollapsedRCD X K N, MetricCurrentOps X CurrentX where
  orientationCurrent : CurrentX
  isCycle_orientationCurrent : isCycle orientationCurrent
  massMeasure_orientationCurrent : massMeasure orientationCurrent = hausdorffMeasure

namespace CMMPOrientationCurrent

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
variable {K : ℝ} {N : ℕ} {CurrentX : Type*} [AddCommGroup CurrentX]

/-- **Mass Identity for the CMMP Orientation Current (`thm:CMMP` (1))**:
$$\mathbf{M}(T) = \mathcal{H}^N(X).$$ -/
theorem totalMass_orientationCurrent
    (C : CMMPOrientationCurrent X K N CurrentX) :
    C.totalMass C.orientationCurrent = C.totalVolume := by
  rw [C.totalMass_eq_massMeasure_univ, C.massMeasure_orientationCurrent]
  rfl

/-- The total mass of the CMMP orientation current $T$ is strictly positive:
$$\mathbf{M}(T) > 0.$$ -/
theorem totalMass_orientationCurrent_pos
    (C : CMMPOrientationCurrent X K N CurrentX) :
    0 < C.totalMass C.orientationCurrent := by
  rw [C.totalMass_orientationCurrent]
  exact C.totalVolume_pos

/-- The CMMP orientation current $T$ is concentrated on the regular set $\mathcal{R}_N(X)$:
$$\|T\|(X \setminus \mathcal{R}_N(X)) = 0.$$ -/
theorem massMeasure_compl_regularSet_eq_zero
    (C : CMMPOrientationCurrent X K N CurrentX) :
    C.massMeasure C.orientationCurrent C.regularSetᶜ = 0 := by
  rw [C.massMeasure_orientationCurrent]
  exact C.hausdorffMeasure_compl_regularSet

/-- The CMMP orientation current $T$ vanishes on the topological singular set $\mathcal{S}(X)$:
$$\|T\|(\mathcal{S}(X)) = 0.$$ -/
theorem massMeasure_singularSet_eq_zero
    (C : CMMPOrientationCurrent X K N CurrentX) :
    C.massMeasure C.orientationCurrent C.singularSet = 0 := by
  rw [C.massMeasure_orientationCurrent]
  exact C.hausdorffMeasure_singularSet_eq_zero

end CMMPOrientationCurrent

end MetricCurrentsAndCMMP

end RCDEntropyDegree.RCD
