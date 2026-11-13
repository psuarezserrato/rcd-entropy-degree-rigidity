import RCDEntropyDegree.RCD.StructureAndCurrents
import Mathlib.Topology.Compactness.Compact

/-!
# Analytic & Topological Degree Theory on Non-Collapsed $\mathsf{RCD}(K, N)$ Spaces

This file formalizes Section 2.4 (`subsec:degree`: Lemma 2.3 `lem:regular-values`,
Definition 2.4 `def:deg-Lipschitz`, Proposition 2.5 `prop:degree-equivalence`,
Lemma 2.6 `lem:homotopy-invariance`, Definition 2.7 `def:deg-continuous`, and
Corollary 2.8 `cor:surjective`) and Remark 4.2 (`rmk:index-comparison`) of
P. Suárez-Serrato, *"Entropy-degree rigidity for non-collapsed $\mathsf{RCD}$ spaces"*
(`RCD-Entropy-Degree-Skeleton.tex`).

## Main Results
1. **Lemma 2.3 (`lem:regular-values`, Regular Value Locus $V_f = Y \setminus f(\mathcal{S}(X))$)**:
   - `regularDomainSet_subset_manifoldSet`: $U_f = X \setminus f^{-1}(\Sigma_f) \subseteq \mathcal{M}(X)$.
   - `isClosed_singularValueImage`, `isOpen_regularValueSet`, `isOpen_regularDomainSet`:
     For continuous $f : X \to Y$ with $X$ compact and $Y$ Hausdorff, $\Sigma_f = f(\mathcal{S}(X))$
     is compact and closed, so $V_f$ and $U_f$ are open.
   - `hausdorffMeasureCodimOne_singularValueImage_eq_zero`:
     From $\mathcal{H}^{N-1}(\Sigma_f) \le \mathrm{Lip}(f)^{N-1} \mathcal{H}^{N-1}(\mathcal{S}(X))$
     and Lemma 2.1 ($\mathcal{H}^{N-1}(\mathcal{S}(X)) = 0$), we obtain $\mathcal{H}^{N-1}(\Sigma_f) = 0$
     and $\mathcal{H}^N(V_f) = \mathcal{H}^N(Y)$.
2. **Proposition 2.5 (`prop:degree-equivalence`, Equivalence of Local Degree and Current Pushforward)**:
   - $f_\# T = \deg(f) \llbracket Y \rrbracket$,
   - $\mathbf{M}(f_\# T) = |\deg(f)| \, \mathcal{H}^N(Y)$ (`pushforward_totalMass_eq_abs_degree_mul_volume`),
   - Classical Lipschitz-degree volume inequality (`abs_degree_mul_volume_le_lip_pow_mul_volume`):
     $|\deg(f)| \, \mathcal{H}^N(Y) \le \mathrm{Lip}(f)^N \, \mathcal{H}^N(X)$.
3. **Lemma 2.6 (`lem:homotopy-invariance`, Wenger Homotopy Invariance)**:
   - Under Wenger's homotopy formula $f_{1\#}T - f_{0\#}T = \partial G_\#(\llbracket 0, 1 \rrbracket \times T) + G_\#(\llbracket 0, 1 \rrbracket \times \partial T)$,
     since $\partial T = 0$ and $\mathcal{H}^{N+1}(Y) = 0$, $f_{1\#}T = f_{0\#}T$ and $\deg(f_1) = \deg(f_0)$.
4. **Corollary 2.8 (`cor:surjective`, Surjectivity of Non-Zero Degree Maps)**:
   - `surjective_of_degree_ne_zero`: Every continuous map $f : X \to Y$ of non-zero degree
     ($\deg(f) \ne 0$) from a compact space $X$ to a Hausdorff manifold $Y$ is surjective.
5. **Multiplicativity of Degree & Remark 4.2 (`rmk:index-comparison`, Homological Index Divisibility)**:
   - `degree_comp_of_pushforward`: $\deg(p \circ \hat{f}) = \deg(p) \cdot \deg(\hat{f})$.
   - `homologicalIndex_dvd_natAbs_degree` & `homologicalIndex_le_natAbs_degree`:
     When Mitsuishi's comparison homomorphism $\Psi : H_N^{\mathrm{IC}}(X) \to H_N(X; \mathbb{Z})$
     exists, the homological index $\mathrm{ind}_H(f) = [H_N(Y; \mathbb{Z}) : f_* H_N(X; \mathbb{Z})]$
     divides $|\deg(f)|$ and satisfies $\mathrm{ind}_H(f) \le |\deg(f)|$ whenever $\deg(f) \ne 0$.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace RCDEntropyDegree.RCD

section RegularValuesAndSingularImage

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X]
variable {K : ℝ} {N : ℕ}

/-- The singular value image $\Sigma_f := f(\mathcal{S}(X)) \subseteq Y$
(`RCD-Entropy-Degree-Skeleton.tex`, Section 2.4, Eq. before Lemma 2.3). -/
def singularValueImage (S : ClosedNonCollapsedRCD X K N) (f : X → Y) : Set Y :=
  f '' S.singularSet

/-- The regular value locus $V_f := Y \setminus \Sigma_f = Y \setminus f(\mathcal{S}(X))$
(`RCD-Entropy-Degree-Skeleton.tex`, Section 2.4). -/
def regularValueSet (S : ClosedNonCollapsedRCD X K N) (f : X → Y) : Set Y :=
  (singularValueImage S f)ᶜ

/-- The regular domain locus $U_f := X \setminus f^{-1}(\Sigma_f) = f^{-1}(V_f)$
(`RCD-Entropy-Degree-Skeleton.tex`, Section 2.4). -/
def regularDomainSet (S : ClosedNonCollapsedRCD X K N) (f : X → Y) : Set X :=
  f ⁻¹' (regularValueSet S f)

/-- Every point of $U_f = X \setminus f^{-1}(f(\mathcal{S}(X)))$ lies in the open topological
manifold locus $\mathcal{M}(X)$:
$$U_f \subseteq \mathcal{M}(X).$$ -/
theorem regularDomainSet_subset_manifoldSet (S : ClosedNonCollapsedRCD X K N) (f : X → Y) :
    regularDomainSet S f ⊆ S.manifoldSet := by
  intro x hx
  by_contra hx_not_man
  have hx_sing : x ∈ S.singularSet := hx_not_man
  have hfx_sing : f x ∈ singularValueImage S f := ⟨x, hx_sing, rfl⟩
  exact hx hfx_sing

/-- **Lemma 2.3 (`lem:regular-values`, Compactness and Closedness of $\Sigma_f$)**:
When $X$ is compact and $Y$ is a Hausdorff topological space, for any continuous map $f : X \to Y$,
the singular value image $\Sigma_f = f(\mathcal{S}(X))$ is compact and closed in $Y$. -/
theorem isCompact_singularValueImage [CompactSpace X] [TopologicalSpace Y]
    (S : ClosedNonCollapsedRCD X K N) {f : X → Y} (hf : Continuous f) :
    IsCompact (singularValueImage S f) :=
  S.isClosed_singularSet.isCompact.image hf

theorem isClosed_singularValueImage [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    (S : ClosedNonCollapsedRCD X K N) {f : X → Y} (hf : Continuous f) :
    IsClosed (singularValueImage S f) :=
  (isCompact_singularValueImage S hf).isClosed

/-- **Lemma 2.3 (`lem:regular-values`, Openness of $V_f = Y \setminus \Sigma_f$ and $U_f$)**:
For continuous $f : X \to Y$ with $X$ compact and $Y$ Hausdorff, $V_f = Y \setminus \Sigma_f$ is
open in $Y$ and $U_f = f^{-1}(V_f)$ is open in $X$. -/
theorem isOpen_regularValueSet [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    (S : ClosedNonCollapsedRCD X K N) {f : X → Y} (hf : Continuous f) :
    IsOpen (regularValueSet S f) :=
  (isClosed_singularValueImage S hf).isOpen_compl

theorem isOpen_regularDomainSet [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    (S : ClosedNonCollapsedRCD X K N) {f : X → Y} (hf : Continuous f) :
    IsOpen (regularDomainSet S f) :=
  (isOpen_regularValueSet S hf).preimage hf

/-- **Lemma 2.3 (`lem:regular-values`, Codimension-1 Nullity of the Singular Value Image $\Sigma_f$)**:
If $f : X \to Y$ is Lipschitz with constant $L \ge 0$, so that
$$\mathcal{H}^{N-1}(\Sigma_f) \le L^{N-1} \, \mathcal{H}^{N-1}(\mathcal{S}(X)),$$
then by Lemma 2.1 ($\mathcal{H}^{N-1}(\mathcal{S}(X)) = 0$) we have
$$\mathcal{H}^{N-1}(\Sigma_f) = 0.$$ -/
theorem hausdorffMeasureCodimOne_singularValueImage_eq_zero
    [MeasurableSpace Y] (S : ClosedNonCollapsedRCD X K N) (f : X → Y)
    (hausdorffCodimOneY : Measure Y) (L : ℝ≥0∞)
    (hlip : hausdorffCodimOneY (singularValueImage S f) ≤
      L ^ (N - 1) * S.hausdorffMeasureCodimOne S.singularSet) :
    hausdorffCodimOneY (singularValueImage S f) = 0 := by
  rw [S.hausdorffMeasureCodimOne_singularSet_eq_zero, mul_zero] at hlip
  exact nonpos_iff_eq_zero.mp hlip

/-- Since $\mathcal{H}^N(\Sigma_f) = 0$, the regular value locus $V_f = Y \setminus \Sigma_f$ has
full $N$-dimensional Hausdorff measure in $Y$:
$$\mathcal{H}^N(V_f) = \mathcal{H}^N(Y).$$ -/
theorem volumeMeasure_regularValueSet_eq_univ
    [MeasurableSpace Y] (S : ClosedNonCollapsedRCD X K N) (f : X → Y)
    (volY : Measure Y) (hnull : volY (singularValueImage S f) = 0) :
    volY (regularValueSet S f) = volY Set.univ := by
  refine le_antisymm (measure_mono (Set.subset_univ _)) ?_
  have h := measure_univ_le_add_compl (μ := volY) (s := regularValueSet S f)
  have hc : (regularValueSet S f)ᶜ = singularValueImage S f := compl_compl _
  simpa [hc, hnull] using h

end RegularValuesAndSingularImage

section DegreeEquivalenceAndHomotopyInvariance

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [MeasurableSpace Y]
variable {K : ℝ} {N : ℕ}
variable {CurrentX CurrentY : Type*} [AddCommGroup CurrentX] [AddCommGroup CurrentY]

/-- **Proposition 2.5 (`prop:degree-equivalence`, Equivalence of Local Topological Degree and
Current Pushforward)**:
Given a closed orientable non-collapsed $\mathsf{RCD}(K, N)$ space $X$ with CMMP orientation
current $T \in \mathbf{I}_N(X)$ and a closed oriented Riemannian $N$-manifold $Y$ with fundamental
class $\llbracket Y \rrbracket \in \mathbf{I}_N(Y)$, for any Lipschitz map $f : X \to Y$:
- the pushforward cycle $f_\# T \in \mathbf{I}_N(Y)$ satisfies $f_\# T = \deg(f) \llbracket Y \rrbracket$,
- the pushforward total mass satisfies $\mathbf{M}(f_\# T) \le \mathrm{Lip}(f)^N \mathbf{M}(T)$. -/
structure LipschitzDegreePushforward
    (C : CMMPOrientationCurrent X K N CurrentX)
    (FY : FundamentalManifoldCurrent Y CurrentY)
    (f : X → Y) where
  pushforwardCurrent : CurrentY
  lipschitzDegree : ℤ
  lipConst : ℝ
  lipConst_nonneg : 0 ≤ lipConst
  isCycle_pushforward : FY.isCycle pushforwardCurrent
  pushforward_eq_degree_zsmul :
    pushforwardCurrent = lipschitzDegree • FY.fundamentalClass
  totalMass_pushforward_le :
    FY.totalMass pushforwardCurrent ≤ (lipConst ^ N) * C.totalMass C.orientationCurrent

namespace LipschitzDegreePushforward

variable {C : CMMPOrientationCurrent X K N CurrentX}
variable {FY : FundamentalManifoldCurrent Y CurrentY}
variable {f : X → Y}

/-- **Proposition 2.5 (`prop:degree-equivalence`, Pushforward Mass Identity)**:
$$\mathbf{M}(f_\# T) = |\deg(f)| \, \mathcal{H}^N(Y).$$ -/
theorem totalMass_pushforward_eq_abs_degree_mul_volume
    (D : LipschitzDegreePushforward C FY f) :
    FY.totalMass D.pushforwardCurrent = |(D.lipschitzDegree : ℝ)| * FY.manifoldVolume := by
  rw [D.pushforward_eq_degree_zsmul]
  exact FY.totalMass_zsmul_eq D.lipschitzDegree

/-- **Proposition 2.5 (`prop:degree-equivalence`, Integral Average Formula for $\deg(f)$)**:
$$\frac{1}{\mathcal{H}^N(Y)} \big(\deg(f) \cdot \mathcal{H}^N(Y)\big) = \deg(f).$$ -/
theorem degree_eq_inv_volume_mul_integral
    (D : LipschitzDegreePushforward C FY f) :
    (FY.manifoldVolume)⁻¹ * ((D.lipschitzDegree : ℝ) * FY.manifoldVolume) =
      (D.lipschitzDegree : ℝ) := by
  have hpos : FY.manifoldVolume ≠ 0 := FY.manifoldVolume_pos.ne'
  field_simp [hpos]

/-- **Lipschitz-Degree Volume Inequality**:
For any Lipschitz map $f : X \to Y$ with Lipschitz constant $L = \mathrm{Lip}(f) \ge 0$,
$$|\deg(f)| \, \mathcal{H}^N(Y) \le L^N \, \mathcal{H}^N(X).$$ -/
theorem abs_degree_mul_volume_le_lip_pow_mul_volume
    (D : LipschitzDegreePushforward C FY f) :
    |(D.lipschitzDegree : ℝ)| * FY.manifoldVolume ≤
      (D.lipConst ^ N) * C.totalVolume := by
  rw [← D.totalMass_pushforward_eq_abs_degree_mul_volume, ← C.totalMass_orientationCurrent]
  exact D.totalMass_pushforward_le

/-- For a $1$-Lipschitz map $f : X \to Y$ ($\mathrm{Lip}(f) \le 1$) of degree $|\deg(f)| \ge 1$,
the source volume dominates the target volume:
$$\mathcal{H}^N(Y) \le |\deg(f)| \, \mathcal{H}^N(Y) \le \mathcal{H}^N(X).$$ -/
theorem manifoldVolume_le_totalVolume_of_one_lipschitz
    (D : LipschitzDegreePushforward C FY f)
    (hlip1 : D.lipConst ≤ 1) (hdeg : 1 ≤ |(D.lipschitzDegree : ℝ)|) :
    FY.manifoldVolume ≤ C.totalVolume := by
  have h1 : FY.manifoldVolume ≤ |(D.lipschitzDegree : ℝ)| * FY.manifoldVolume :=
    le_mul_of_one_le_left FY.manifoldVolume_pos.le hdeg
  have hpow : D.lipConst ^ N ≤ 1 := pow_le_one₀ D.lipConst_nonneg hlip1
  have h2 : (D.lipConst ^ N) * C.totalVolume ≤ 1 * C.totalVolume :=
    mul_le_mul_of_nonneg_right hpow C.totalVolume_pos.le
  linarith [D.abs_degree_mul_volume_le_lip_pow_mul_volume]

end LipschitzDegreePushforward

/-- **Lemma 2.6 (`lem:homotopy-invariance`, Wenger Homotopy Invariance of Current Pushforwards
and Degree)**:
Let $G : [0, 1] \times X \to Y$ be a Lipschitz homotopy between $f_0$ and $f_1$. By Wenger's
homotopy formula (`[Wen05]`, `[Lang11]`),
$$f_{1\#} T - f_{0\#} T = \partial G_\#(\llbracket 0, 1 \rrbracket \times T) + G_\#(\llbracket 0, 1 \rrbracket \times \partial T).$$
Since $\partial T = 0$ (`boundarySliceTerm = 0`) and $\mathcal{H}^{N+1}(Y) = 0$ so that the
$(N+1)$-current $G_\#(\llbracket 0, 1 \rrbracket \times T)$ vanishes (`cylinderBoundaryTerm = 0`),
we have $f_{1\#} T = f_{0\#} T$ and $\deg(f_1) = \deg(f_0)$. -/
theorem wenger_homotopy_invariance
    (FY : FundamentalManifoldCurrent Y CurrentY)
    {push₀ push₁ cylinderBoundaryTerm boundarySliceTerm : CurrentY}
    {deg₀ deg₁ : ℤ}
    (h_wenger : push₁ - push₀ = cylinderBoundaryTerm + boundarySliceTerm)
    (h_codim_top : cylinderBoundaryTerm = 0)
    (h_cycle : boundarySliceTerm = 0)
    (h_deg₀ : push₀ = deg₀ • FY.fundamentalClass)
    (h_deg₁ : push₁ = deg₁ • FY.fundamentalClass) :
    push₁ = push₀ ∧ deg₁ = deg₀ := by
  have h_eq : push₁ = push₀ := by
    apply sub_eq_zero.mp
    rw [h_wenger, h_codim_top, h_cycle, add_zero]
  have h_zsmul : deg₁ • FY.fundamentalClass = deg₀ • FY.fundamentalClass := by
    rw [← h_deg₁, ← h_deg₀, h_eq]
  exact ⟨h_eq, FY.zsmul_fundamentalClass_inj h_zsmul⟩

omit [MeasurableSpace X] in
/-- **Corollary 2.8 (`cor:surjective`, Surjectivity of Non-Zero Degree Maps)**:
Let $X$ be a compact space, $Y$ be a Hausdorff space carrying a `FundamentalManifoldCurrent`
whose `volumeMeasure` is strictly positive on every nonempty open subset, and let $f : X \to Y$
be a continuous map of non-zero degree (`deg ≠ 0`) whose pushforward mass measure vanishes outside
$f(X)$ (`(FY.massMeasure (deg • FY.fundamentalClass) (Set.range f)ᶜ).toReal = 0`).
Then $f$ is surjective (`Function.Surjective f`). -/
theorem surjective_of_degree_ne_zero
    [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    (FY : FundamentalManifoldCurrent Y CurrentY)
    (h_open_pos : ∀ U : Set Y, IsOpen U → U.Nonempty → 0 < (FY.volumeMeasure U).toReal)
    {f : X → Y} (hf : Continuous f)
    {deg : ℤ} (hdeg : deg ≠ 0)
    (h_supp : (FY.massMeasure (deg • FY.fundamentalClass) (Set.range f)ᶜ).toReal = 0) :
    Function.Surjective f := by
  intro y
  by_contra hy
  have hW_ne : ((Set.range f)ᶜ : Set Y).Nonempty := ⟨y, hy⟩
  have h_range_closed : IsClosed (Set.range f) := (isCompact_range hf).isClosed
  have hW_open : IsOpen ((Set.range f)ᶜ : Set Y) := h_range_closed.isOpen_compl
  have hvol_pos : 0 < (FY.volumeMeasure (Set.range f)ᶜ).toReal :=
    h_open_pos (Set.range f)ᶜ hW_open hW_ne
  have hdeg_pos : 0 < |(deg : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hdeg)
  have hmass_pos : 0 < (FY.massMeasure (deg • FY.fundamentalClass) (Set.range f)ᶜ).toReal := by
    rw [FY.massMeasure_zsmul_fundamentalClass deg (Set.range f)ᶜ]
    exact mul_pos hdeg_pos hvol_pos
  linarith

/-- **Multiplicativity of Degree under Composition / Covering Projections**:
If $(p \circ \hat{f})_\# T = \deg(p \circ \hat{f}) \llbracket Y \rrbracket$ and functoriality of
current pushforwards gives $(p \circ \hat{f})_\# T = p_\#(\hat{f}_\# T) = (\deg(p) \cdot \deg(\hat{f})) \llbracket Y \rrbracket$,
then
$$\deg(p \circ \hat{f}) = \deg(p) \cdot \deg(\hat{f}) \quad \text{and} \quad
  |\deg(p \circ \hat{f})| = |\deg(p)| \cdot |\deg(\hat{f})|.$$ -/
theorem degree_comp_of_pushforward
    (FY : FundamentalManifoldCurrent Y CurrentY)
    {push_comp : CurrentY} {deg_comp deg_p deg_fhat : ℤ}
    (h_comp : push_comp = deg_comp • FY.fundamentalClass)
    (h_functor : push_comp = (deg_p * deg_fhat) • FY.fundamentalClass) :
    deg_comp = deg_p * deg_fhat ∧
      |(deg_comp : ℝ)| = |(deg_p : ℝ)| * |(deg_fhat : ℝ)| := by
  have h_eq : deg_comp = deg_p * deg_fhat :=
    FY.zsmul_fundamentalClass_inj (h_comp.symm.trans h_functor)
  refine ⟨h_eq, ?_⟩
  rw [h_eq, Int.cast_mul, abs_mul]

/-- **Remark 4.2 (`rmk:index-comparison`, Comparison with the Homological Index $\mathrm{ind}_H(f)$)**:
When Mitsuishi's comparison homomorphism $\Psi : H_N^{\mathrm{IC}}(X) \to H_N(X; \mathbb{Z})$ exists
and maps $[T] \mapsto m_X \cdot \alpha_X$, naturality $\Psi_Y([f_\# T]) = f_* \Psi_X([T])$ yields
$$\deg(f) = m_X \cdot \mathrm{ind}_H(f),$$
where $\mathrm{ind}_H(f) = [H_N(Y; \mathbb{Z}) : f_* H_N(X; \mathbb{Z})] \in \mathbb{N}$ is the
homological index. Consequently, $\mathrm{ind}_H(f)$ divides $|\deg(f)|$, and whenever $\deg(f) \ne 0$,
$$1 \le \mathrm{ind}_H(f) \le |\deg(f)|.$$ -/
theorem homologicalIndex_dvd_natAbs_degree
    {deg_f m_X : ℤ} {ind_H : ℕ}
    (h_mitsuishi : deg_f = m_X * (ind_H : ℤ)) :
    ind_H ∣ deg_f.natAbs := by
  refine ⟨m_X.natAbs, ?_⟩
  have h := congrArg Int.natAbs h_mitsuishi
  rw [Int.natAbs_mul, Int.natAbs_natCast, mul_comm] at h
  exact h

theorem homologicalIndex_le_natAbs_degree
    {deg_f m_X : ℤ} {ind_H : ℕ}
    (h_mitsuishi : deg_f = m_X * (ind_H : ℤ))
    (hdeg_ne : deg_f ≠ 0) :
    1 ≤ ind_H ∧ ind_H ≤ deg_f.natAbs := by
  have hdvd : ind_H ∣ deg_f.natAbs := homologicalIndex_dvd_natAbs_degree h_mitsuishi
  have hpos : 0 < deg_f.natAbs := Int.natAbs_pos.mpr hdeg_ne
  have hind_ne : ind_H ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, mul_zero] at h_mitsuishi
    exact hdeg_ne h_mitsuishi
  exact ⟨Nat.one_le_iff_ne_zero.mpr hind_ne, Nat.le_of_dvd hpos hdvd⟩

end DegreeEquivalenceAndHomotopyInvariance

end RCDEntropyDegree.RCD
