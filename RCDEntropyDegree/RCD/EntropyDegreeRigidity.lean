import RCDEntropyDegree.MetricMeasure.VolumeEntropy
import RCDEntropyDegree.MetricMeasure.SturmBarycenter
import RCDEntropyDegree.RCD.StructureAndCurrents
import RCDEntropyDegree.RCD.DegreeTheory
import BCG.MainTheorem

/-!
# Entropy-Degree Rigidity for Closed Orientable Non-Collapsed $\mathsf{RCD}(K, N)$ and Alexandrov Spaces

This file formalizes Section 3.2 (`subsec:jacobians`: Lemma 3.2 `lem:Jacobian`,
Lemma 3.3 `lem:mass-pushforward`, Proposition 3.4 `prop:entropy-jacobian`) and Section 4
(`Proof of Theorem 1.1`: Inequality `eq:main-chain`, Remark 4.2 `rmk:index-comparison`,
Remark 4.3 `rmk:Alexandrov`, and the Equality-Case Metric Rigidity Proof) of
P. Suárez-Serrato, *"Entropy-degree rigidity for non-collapsed $\mathsf{RCD}$ spaces"*
(`RCD-Entropy-Degree-Skeleton.tex`).

## Main Results
1. **Rectifiable Approximate Differentials & Metric Jacobians (`metricJacobian`, Lemma 3.2 `lem:Jacobian`)**:
   At $\mathcal{H}^N$-a.e. regular point $x \in \mathcal{R}_N(X)$, the metric Jacobian of a Lipschitz
   map $F : X \to Y$ equals $\mathrm{Jac}_x F = |\det(d_x F)|$ on the Euclidean approximate tangent
   space $\mathrm{Tan}(X, x) \cong E$.
2. **Lemma 3.3 (`lem:mass-pushforward`, Pushforward Mass-Jacobian Inequality)**:
   - `abs_sum_orientationSign_le_card`: On each regular fiber $F^{-1}(y) \cap \mathcal{R}_N(X)$,
     $|\theta_{F_\# T}(y)| = |\sum_x \mathrm{sign}(\det d_x F)| \le \# F^{-1}(y)$.
   - `pushforward_totalMass_le_integral_jacobian`: Integrating over $Y$ and applying the area
     formula yields
     $$\mathbf{M}(F_\# T) \le \int_Y \# F^{-1}(y)\,d\mathcal{H}^N(y) = \int_X \mathrm{Jac}_x F\,d\mathcal{H}^N(x).$$
   - `degree_mul_volume_le_integral_jacobian`: Combining with Proposition 2.5
     ($\mathbf{M}(F_\# T) = |\deg(f)|\,\mathcal{H}^N(Y)$) yields
     $$|\deg(f)| \, \mathcal{H}^N(Y) \le \int_X \mathrm{Jac}_x F_s \, d\mathcal{H}^N(x).$$
3. **Proposition 3.4 (`prop:entropy-jacobian`, Pointwise Entropy-Jacobian Bound on $\mathcal{R}_N(X)$)**:
   Connects the approximate differential $d_x F_s$ on $\mathrm{Tan}(X, x) \cong \mathbb{R}^N$ to our
   rank-one Busemann Hessian & Jacobian engine (`BCG.RankOne`) to establish
   $$\mathrm{Jac}_x F_s \le \left(\frac{s}{h(\widetilde{Y})}\right)^N$$
   for all rank-one locally symmetric targets $\mathbb{K}\mathbf{H}^m$ (including Ruan's repair for
   $\mathbb{O}\mathbf{H}^2$).
4. **Theorem 1.1 (`thm:rcd-entropy-degree`, Main Frontier Theorem)**:
   - **Inequality (`rcd_entropy_degree_inequality`, `rcd_rankOne_entropy_degree_theorem`)**:
     $$|\deg(f)| \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y) \le h(\overline{X})^N \, \mathcal{H}^N(X).$$
   - **Homological Index Comparison (`rcd_homological_index_entropy_inequality`, Remark 4.2)**:
     $$\mathrm{ind}_H(f) \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y) \le h(\overline{X})^N \, \mathcal{H}^N(X).$$
   - **Alexandrov Space Specialization (`alexandrov_entropy_degree_inequality`, Remark 4.3,
     `[SuarezSerrato2026, Theorem 1.1]`)**:
     Specialization of Theorem 1.1 to closed orientable $N$-dimensional $\mathrm{Alex}(\kappa)$ spaces.
   - **Equality-Case Rigidity (`ae_jacobian_eq_one_of_normalized_equality`,
     `rcd_entropy_degree_equality_rigidity`)**:
     When equality holds with $|\deg(f)| = [\pi_1(Y) : f_* \pi_1(X)] = k \ge 1$, after homothetic
     rescaling by $c = h(\overline{X}) / h(\widetilde{Y}) > 0$, the limit map
     $\hat{F}_\infty : X \to \widehat{Y}$ to the degree-$k$ intermediate Riemannian cover
     $p : \widehat{Y} \to Y$ satisfies $\mathrm{Jac}_x \hat{F}_\infty = 1$ $\mathcal{H}^N$-a.e., is
     surjective, and is a global metric isometry, so $F = p \circ \hat{F}_\infty : X \to Y$ is a
     Riemannian covering of degree $|\deg(f)|$.
-/

noncomputable section

open MeasureTheory Set Filter Finset BigOperators
open scoped ENNReal Topology

namespace RCDEntropyDegree.RCD

open RCDEntropyDegree.MetricMeasure

section ApproximateDifferentialAndPushforwardMass

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [MeasurableSpace Y]
variable {K : ℝ} {N : ℕ}
variable {CurrentX CurrentY : Type*} [AddCommGroup CurrentX] [AddCommGroup CurrentY]

/-- **Lemma 3.2 (`lem:Jacobian`, Metric Jacobian via the Approximate Linear Differential)**:
For an approximate linear differential $d_x F : E \to_l[\mathbb{R}] E$ defined on the Euclidean
approximate tangent space $\mathrm{Tan}(X, x) \cong E$ ($\dim_{\mathbb{R}} E = N$), the metric
Jacobian is $\mathrm{Jac}_x F = |\det(d_x F)|$. -/
def metricJacobian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (dF : X → (E →ₗ[ℝ] E)) (x : X) : ℝ :=
  |(dF x).det|

omit [MetricSpace X] [MeasurableSpace X] in
theorem metricJacobian_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (dF : X → (E →ₗ[ℝ] E)) (x : X) :
    0 ≤ metricJacobian dF x :=
  abs_nonneg _

/-- **Finite-Fiber Orientation-Sign Triangle Inequality (`lem:mass-pushforward`, Step 1)**:
In the Ambrosio–Kirchheim pushforward representation
$$\theta_{F_\# T}(y) = \sum_{x \in F^{-1}(y) \cap \mathcal{R}_N(X)} \mathrm{sign}(\det d_x F),$$
each orientation sign $\sigma(x) \in \{-1, 0, +1\}$ satisfies $|\sigma(x)| \le 1$, so the multiplicity
density is bounded by the fiber cardinality:
$$\left|\sum_{x \in S} \sigma(x)\right| \le \# S.$$ -/
theorem abs_sum_orientationSign_le_card {α : Type*} (S : Finset α)
    (σ : α → ℝ) (hσ : ∀ x ∈ S, |σ x| ≤ 1) :
    |∑ x ∈ S, σ x| ≤ (S.card : ℝ) := by
  calc
    |∑ x ∈ S, σ x| ≤ ∑ x ∈ S, |σ x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ S, (1 : ℝ) := Finset.sum_le_sum hσ
    _ = (S.card : ℝ) := by simp

/-- **Lemma 3.3 (`lem:mass-pushforward`, Pushforward Mass Bounded by Integrated Jacobian)**:
Let $F : X \to Y$ be a Lipschitz map from a closed orientable non-collapsed $\mathsf{RCD}(K, N)$
space $X$ with CMMP orientation current $T \in \mathbf{I}_N(X)$ to a closed oriented smooth
Riemannian $N$-manifold $Y$. Suppose:
1. the pushforward total mass is given by $\mathbf{M}(F_\# T) = \int_Y |\theta_{F_\# T}(y)|\,d\mathcal{H}^N(y)$,
2. for $\mathcal{H}^N$-a.e. $y \in Y$, $|\theta_{F_\# T}(y)| \le \mathrm{mult}_F(y)$ where
   $\mathrm{mult}_F(y) = \# F^{-1}(y)$, and
3. by the rectifiable area formula (`[AK00]`, `[Kir94]`),
   $\int_Y \mathrm{mult}_F(y)\,d\mathcal{H}^N(y) = \int_X \mathrm{Jac}_x F\,d\mathcal{H}^N(x)$.
Then
$$\mathbf{M}(F_\# T) \le \int_X \mathrm{Jac}_x F \, d\mathcal{H}^N(x).$$ -/
theorem pushforward_totalMass_le_integral_jacobian
    (C : CMMPOrientationCurrent X K N CurrentX)
    (FY : FundamentalManifoldCurrent Y CurrentY)
    (F_push : CurrentY)
    (θ mult_F : Y → ℝ) (Jac_F : X → ℝ)
    (hθ_int : Integrable (fun y => |θ y|) FY.volumeMeasure)
    (hmult_int : Integrable mult_F FY.volumeMeasure)
    (h_mass_eq : FY.totalMass F_push = ∫ y, |θ y| ∂FY.volumeMeasure)
    (h_fiber_le : ∀ᵐ y ∂FY.volumeMeasure, |θ y| ≤ mult_F y)
    (h_area : ∫ y, mult_F y ∂FY.volumeMeasure = ∫ x, Jac_F x ∂C.hausdorffMeasure) :
    FY.totalMass F_push ≤ ∫ x, Jac_F x ∂C.hausdorffMeasure := by
  calc
    FY.totalMass F_push
      = ∫ y, |θ y| ∂FY.volumeMeasure := h_mass_eq
    _ ≤ ∫ y, mult_F y ∂FY.volumeMeasure := integral_mono_ae hθ_int hmult_int h_fiber_le
    _ = ∫ x, Jac_F x ∂C.hausdorffMeasure := h_area

/-- **Degree-Jacobian Integral Inequality on Non-Collapsed $\mathsf{RCD}(K, N)$ Spaces**
(Combining Proposition 2.5 `prop:degree-equivalence` and Lemma 3.3 `lem:mass-pushforward`):
Since $F_{s\#} T = \deg(f) \llbracket Y \rrbracket$ has total mass
$\mathbf{M}(F_{s\#} T) = |\deg(f)| \, \mathcal{H}^N(Y)$, Lemma 3.3 implies
$$|\deg(f)| \, \mathcal{H}^N(Y) \le \int_X \mathrm{Jac}_x F_s \, d\mathcal{H}^N(x).$$ -/
theorem degree_mul_volume_le_integral_jacobian
    (C : CMMPOrientationCurrent X K N CurrentX)
    (FY : FundamentalManifoldCurrent Y CurrentY)
    {f : X → Y} (D : LipschitzDegreePushforward C FY f)
    (Jac_F : X → ℝ)
    (h_mass_le_jac : FY.totalMass D.pushforwardCurrent ≤ ∫ x, Jac_F x ∂C.hausdorffMeasure) :
    |(D.lipschitzDegree : ℝ)| * FY.manifoldVolume ≤ ∫ x, Jac_F x ∂C.hausdorffMeasure := by
  rw [← D.totalMass_pushforward_eq_abs_degree_mul_volume]
  exact h_mass_le_jac

end ApproximateDifferentialAndPushforwardMass

section EntropyDegreeInequality

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [MeasurableSpace Y]
variable {K : ℝ} {N : ℕ}
variable {CurrentX CurrentY : Type*} [AddCommGroup CurrentX] [AddCommGroup CurrentY]

/-- **Proposition 3.4 (`prop:entropy-jacobian`, Pointwise Entropy-Jacobian Bound on $\mathcal{R}_N(X)`)**:
For any rank-one locally symmetric target $Y$ of dimension $N \ge 1$ and universal-cover volume
entropy $h_{\widetilde{Y}} > 0$, if at scale $s \ge 0$ the approximate differential
$d_x F_s : E \to_l[\mathbb{R}] E$ ($\mathrm{Tan}(X, x) \cong E$, $\dim_{\mathbb{R}} E = N$) satisfies
the Busemann Hessian implicit-function equation and determinant inequality on $\mathcal{R}_N(X)$,
then
$$\mathrm{Jac}_x F_s = |\det(d_x F_s)| \le \left(\frac{s}{h_{\widetilde{Y}}}\right)^N.$$ -/
theorem rcd_approximate_jacobian_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hN : Module.finrank ℝ E = N) (hN_pos : 0 < N)
    {s h_Ytilde : ℝ} (hs : 0 ≤ s) (hh_Ytilde : 0 < h_Ytilde)
    {dF_x H_y H_X H H_hat : E →ₗ[ℝ] E}
    (h_ift : (BCG.RankOne.rankOneHessianOperator H H_hat).comp dF_x = s • H_y)
    (hW_pos : 0 < (BCG.RankOne.rankOneHessianOperator H H_hat).det)
    (hH_X_symm : H_X.IsSymmetric) (hH_symm : H.IsSymmetric)
    (hH_X_pos : ∀ u, 0 ≤ inner ℝ u (H_X u))
    (hH_pos : ∀ v, 0 ≤ inner ℝ v (H v))
    (hH_X_tr : LinearMap.trace ℝ E H_X ≤ 1)
    (hCS : ∀ u v, |inner ℝ (H_y u) v| ≤
      Real.sqrt (inner ℝ u (H_X u)) * Real.sqrt (inner ℝ v (H v)))
    (h_det_ineq :
      Real.sqrt H.det / (BCG.RankOne.rankOneHessianOperator H H_hat).det ≤
        (Real.sqrt (N : ℝ) / h_Ytilde) ^ N) :
    |(dF_x).det| ≤ (s / h_Ytilde) ^ N :=
  BCG.RankOne.abs_det_le_div_entropy_pow_of_rankOne_det_ineq
    hN hN_pos hs hh_Ytilde h_ift hW_pos hH_X_symm hH_symm hH_X_pos hH_pos
    hH_X_tr hCS h_det_ineq

/-- **Theorem 1.1 Part 1 (`thm:rcd-entropy-degree`, Entropy-Degree Inequality for Closed
Orientable Non-Collapsed $\mathsf{RCD}(K, N)$ Spaces, `eq:main-chain`)**:
Let $(X, \mathsf{d}, \mathcal{H}^N)$ be a closed orientable non-collapsed $\mathsf{RCD}(K, N)$ space
with CMMP orientation current $T \in \mathbf{I}_N(X)$, and let $f : X \to Y$ be a continuous map to
a closed oriented negatively curved locally symmetric $N$-manifold $Y$ with universal-cover volume
entropy $h(\widetilde{Y}) > 0$. If for every $s > h(\overline{X})$ the natural map $F_s : X \to Y$
is homotopic to $f$ (so $F_{s\#} T = \deg(f) \llbracket Y \rrbracket$), satisfies Lemma 3.3
($\mathbf{M}(F_{s\#} T) \le \int_X \mathrm{Jac}_x F_s\,d\mathcal{H}^N$), and satisfies Proposition 3.4
($\mathrm{Jac}_x F_s \le (s / h(\widetilde{Y}))^N$ $\mathcal{H}^N$-a.e.), then
$$|\deg(f)| \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y) \le h(\overline{X})^N \, \mathcal{H}^N(X).$$ -/
theorem rcd_entropy_degree_inequality
    (C : CMMPOrientationCurrent X K N CurrentX)
    [IsFiniteMeasure C.hausdorffMeasure]
    (FY : FundamentalManifoldCurrent Y CurrentY)
    {h_Xbar h_Ytilde : ℝ} (hh_Ytilde : 0 < h_Ytilde)
    {deg_f : ℤ}
    (F_s : ℝ → X → Y)
    (D_s : ∀ s : ℝ, s > h_Xbar → LipschitzDegreePushforward C FY (F_s s))
    (Jac_s : ℝ → X → ℝ)
    (h_deg_homotopy : ∀ (s : ℝ) (hs : s > h_Xbar), (D_s s hs).lipschitzDegree = deg_f)
    (h_mass_push : ∀ (s : ℝ) (hs : s > h_Xbar),
      FY.totalMass (D_s s hs).pushforwardCurrent ≤ ∫ x, Jac_s s x ∂C.hausdorffMeasure)
    (hJac_int : ∀ s > h_Xbar, Integrable (Jac_s s) C.hausdorffMeasure)
    (hJac_bound : ∀ s > h_Xbar, ∀ᵐ x ∂C.hausdorffMeasure,
      Jac_s s x ≤ (s / h_Ytilde) ^ N) :
    |(deg_f : ℝ)| * h_Ytilde ^ N * FY.manifoldVolume ≤
      h_Xbar ^ N * C.totalVolume := by
  apply BCG.bcg_volume_entropy_inequality
  intro s hs
  have h_deg_area : |(deg_f : ℝ)| * FY.manifoldVolume ≤ ∫ x, Jac_s s x ∂C.hausdorffMeasure := by
    rw [← h_deg_homotopy s hs]
    exact degree_mul_volume_le_integral_jacobian C FY (D_s s hs) (Jac_s s) (h_mass_push s hs)
  exact BCG.bcg_volume_inequality_at_scale C.hausdorffMeasure hh_Ytilde
    (hJac_int s hs) (hJac_bound s hs) h_deg_area

/-- **End-to-End Rank-One Entropy-Degree Theorem on Non-Collapsed $\mathsf{RCD}(K, N)$ Spaces**:
Combines the CMMP orientation current degree identity, the pushforward mass-Jacobian inequality
(Lemma 3.3), and the approximate-tangent rank-one Busemann Hessian determinant bound
(`BCG.MainTheorem.rankOne_bcg_main_theorem`) across all rank-one targets $\mathbb{K}\mathbf{H}^m$
($h_0 = N + d - 2 > 0$). -/
theorem rcd_rankOne_entropy_degree_theorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (C : CMMPOrientationCurrent X K N CurrentX)
    [IsFiniteMeasure C.hausdorffMeasure]
    (FY : FundamentalManifoldCurrent Y CurrentY)
    (hN : Module.finrank ℝ E = N) (hN_pos : 0 < N)
    {h_Xbar h₀ : ℝ} (hh_Xbar : 0 ≤ h_Xbar) (hh₀ : 0 < h₀)
    {deg_f : ℤ}
    (F_s : ℝ → X → Y)
    (D_s : ∀ s : ℝ, s > h_Xbar → LipschitzDegreePushforward C FY (F_s s))
    (dF H_y H_X H H_hat : ℝ → X → (E →ₗ[ℝ] E))
    (h_deg_homotopy : ∀ (s : ℝ) (hs : s > h_Xbar), (D_s s hs).lipschitzDegree = deg_f)
    (h_ift : ∀ s > h_Xbar, ∀ x,
      (BCG.RankOne.rankOneHessianOperator (H s x) (H_hat s x)).comp (dF s x) = s • H_y s x)
    (hW_pos : ∀ s > h_Xbar, ∀ x,
      0 < (BCG.RankOne.rankOneHessianOperator (H s x) (H_hat s x)).det)
    (hH_X_symm : ∀ s > h_Xbar, ∀ x, (H_X s x).IsSymmetric)
    (hH_symm : ∀ s > h_Xbar, ∀ x, (H s x).IsSymmetric)
    (hH_X_pos : ∀ s > h_Xbar, ∀ x u, 0 ≤ inner ℝ u (H_X s x u))
    (hH_pos : ∀ s > h_Xbar, ∀ x v, 0 ≤ inner ℝ v (H s x v))
    (hH_X_tr : ∀ s > h_Xbar, ∀ x, LinearMap.trace ℝ E (H_X s x) ≤ 1)
    (hCS : ∀ s > h_Xbar, ∀ x u v,
      |inner ℝ (H_y s x u) v| ≤
        Real.sqrt (inner ℝ u (H_X s x u)) * Real.sqrt (inner ℝ v (H s x v)))
    (h_det_ineq : ∀ s > h_Xbar, ∀ x,
      Real.sqrt (H s x).det / (BCG.RankOne.rankOneHessianOperator (H s x) (H_hat s x)).det ≤
        (Real.sqrt (N : ℝ) / h₀) ^ N)
    (hdF_int : ∀ s > h_Xbar, Integrable (fun x => |(dF s x).det|) C.hausdorffMeasure)
    (h_mass_push : ∀ (s : ℝ) (hs : s > h_Xbar),
      FY.totalMass (D_s s hs).pushforwardCurrent ≤
        ∫ x, |(dF s x).det| ∂C.hausdorffMeasure) :
    |(deg_f : ℝ)| * h₀ ^ N * FY.manifoldVolume ≤ h_Xbar ^ N * C.totalVolume := by
  refine BCG.rankOne_bcg_main_theorem C.hausdorffMeasure hN hN_pos hh_Xbar hh₀
    dF H_y H_X H H_hat h_ift hW_pos hH_X_symm hH_symm hH_X_pos hH_pos
    hH_X_tr hCS h_det_ineq hdF_int ?_
  intro s hs
  rw [← h_deg_homotopy s hs]
  exact degree_mul_volume_le_integral_jacobian C FY (D_s s hs)
    (fun x => |(dF s x).det|) (h_mass_push s hs)

/-- **Remark 4.2 (`rmk:index-comparison`, Homological Index Entropy Bound `[RCDbary, Theorem 1.1]`)**:
When Mitsuishi's comparison homomorphism $\Psi : H_N^{\mathrm{IC}}(X) \to H_N(X; \mathbb{Z})$ exists
so that $\deg(f) = m_X \cdot \mathrm{ind}_H(f)$ with $\deg(f) \ne 0$, Theorem 1.1 immediately implies
the homological-index volume-entropy inequality:
$$\mathrm{ind}_H(f) \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y) \le
  |\deg(f)| \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y) \le
  h(\overline{X})^N \, \mathcal{H}^N(X).$$ -/
theorem rcd_homological_index_entropy_inequality
    {deg_f m_X : ℤ} {ind_H N : ℕ}
    {h_Xbar h_Ytilde vol_X vol_Y : ℝ}
    (hh_Ytilde : 0 ≤ h_Ytilde) (hvol_Y : 0 ≤ vol_Y)
    (h_mitsuishi : deg_f = m_X * (ind_H : ℤ))
    (hdeg_ne : deg_f ≠ 0)
    (h_rcd_ineq : |(deg_f : ℝ)| * h_Ytilde ^ N * vol_Y ≤ h_Xbar ^ N * vol_X) :
    (ind_H : ℝ) * h_Ytilde ^ N * vol_Y ≤ h_Xbar ^ N * vol_X := by
  have hind_le : ind_H ≤ deg_f.natAbs :=
    (homologicalIndex_le_natAbs_degree h_mitsuishi hdeg_ne).2
  have hind_real : (ind_H : ℝ) ≤ |(deg_f : ℝ)| := by
    have hcast : (ind_H : ℝ) ≤ (deg_f.natAbs : ℝ) := Nat.cast_le.mpr hind_le
    rw [Nat.cast_natAbs, Int.cast_abs] at hcast
    exact hcast
  have hnonneg : 0 ≤ h_Ytilde ^ N * vol_Y := mul_nonneg (pow_nonneg hh_Ytilde N) hvol_Y
  calc
    (ind_H : ℝ) * h_Ytilde ^ N * vol_Y
      = (ind_H : ℝ) * (h_Ytilde ^ N * vol_Y) := by ring
    _ ≤ |(deg_f : ℝ)| * (h_Ytilde ^ N * vol_Y) :=
      mul_le_mul_of_nonneg_right hind_real hnonneg
    _ = |(deg_f : ℝ)| * h_Ytilde ^ N * vol_Y := by ring
    _ ≤ h_Xbar ^ N * vol_X := h_rcd_ineq

/-- **Remark 4.3 (`rmk:Alexandrov`, The Entropy-Degree Theorem for Alexandrov Spaces,
`[SuarezSerrato2026, Theorem 1.1]`)**:
Every closed orientable $N$-dimensional Alexandrov space $(X, \mathsf{d})$ of curvature $\ge \kappa$
without boundary is a closed orientable non-collapsed $\mathsf{RCD}((N-1)\kappa, N)$ space, so
Theorem 1.1 specializes directly to yield
$$|\deg(f)| \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y) \le h(\overline{X})^N \, \mathcal{H}^N(X).$$ -/
theorem alexandrov_entropy_degree_inequality
    {κ : ℝ} (A : AlexandrovSpaceWithoutBoundary X κ N)
    (C : CMMPOrientationCurrent X ((N - 1 : ℝ) * κ) N CurrentX)
    (hA : C.toClosedNonCollapsedRCD = A.toClosedNonCollapsedRCD)
    [IsFiniteMeasure C.hausdorffMeasure]
    (FY : FundamentalManifoldCurrent Y CurrentY)
    {h_Xbar h_Ytilde : ℝ} (hh_Ytilde : 0 < h_Ytilde)
    {deg_f : ℤ}
    (F_s : ℝ → X → Y)
    (D_s : ∀ s : ℝ, s > h_Xbar → LipschitzDegreePushforward C FY (F_s s))
    (Jac_s : ℝ → X → ℝ)
    (h_deg_homotopy : ∀ (s : ℝ) (hs : s > h_Xbar), (D_s s hs).lipschitzDegree = deg_f)
    (h_mass_push : ∀ (s : ℝ) (hs : s > h_Xbar),
      FY.totalMass (D_s s hs).pushforwardCurrent ≤ ∫ x, Jac_s s x ∂C.hausdorffMeasure)
    (hJac_int : ∀ s > h_Xbar, Integrable (Jac_s s) C.hausdorffMeasure)
    (hJac_bound : ∀ s > h_Xbar, ∀ᵐ x ∂C.hausdorffMeasure,
      Jac_s s x ≤ (s / h_Ytilde) ^ N) :
    |(deg_f : ℝ)| * h_Ytilde ^ N * FY.manifoldVolume ≤
      h_Xbar ^ N * A.toClosedNonCollapsedRCD.totalVolume := by
  have hvol : C.totalVolume = A.toClosedNonCollapsedRCD.totalVolume :=
    congrArg ClosedNonCollapsedRCD.totalVolume hA
  rw [← hvol]
  exact rcd_entropy_degree_inequality C FY hh_Ytilde F_s D_s Jac_s
    h_deg_homotopy h_mass_push hJac_int hJac_bound

end EntropyDegreeInequality

section EqualityCaseRigidity

variable {X Y Yhat : Type*} [MetricSpace X] [MeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y]
  [MetricSpace Yhat] [MeasurableSpace Yhat]
variable {K : ℝ} {N : ℕ}
variable {CurrentX CurrentYhat : Type*} [AddCommGroup CurrentX] [AddCommGroup CurrentYhat]

omit [MetricSpace Yhat] in
/-- **Mass-Jacobian Sandwich for the Limit Map $\hat{F}_\infty : X \to \widehat{Y}$**
(`RCD-Entropy-Degree-Skeleton.tex`, Proof of Theorem 1.1 Equality Case, lines 664–671):
In the normalized equality case where $|\deg(\hat{F}_\infty)| = 1$,
$\mathcal{H}^N(X) = \mathcal{H}^N(\widehat{Y})$, and $\hat{F}_\infty : X \to \widehat{Y}$ is
$1$-Lipschitz ($\mathrm{Jac}_x \hat{F}_\infty \le 1$ $\mathcal{H}^N$-a.e.), the sandwich
$$\mathcal{H}^N(\widehat{Y}) = |\deg(\hat{F}_\infty)| \, \mathcal{H}^N(\widehat{Y})
  = \mathbf{M}(\hat{F}_{\infty\#} T)
  \le \int_X \mathrm{Jac}_x \hat{F}_\infty \, d\mathcal{H}^N(x)
  \le \int_X 1 \, d\mathcal{H}^N(x) = \mathcal{H}^N(X) = \mathcal{H}^N(\widehat{Y})$$
forces $\int_X \mathrm{Jac}_x \hat{F}_\infty \, d\mathcal{H}^N = \mathcal{H}^N(X)$ and hence
$$\mathrm{Jac}_x \hat{F}_\infty = 1 \quad \text{for } \mathcal{H}^N\text{-almost every } x \in X.$$ -/
theorem ae_jacobian_eq_one_of_normalized_equality
    (C : CMMPOrientationCurrent X K N CurrentX)
    [IsFiniteMeasure C.hausdorffMeasure]
    (FYhat : FundamentalManifoldCurrent Yhat CurrentYhat)
    {Fhat_inf : X → Yhat}
    (D_inf : LipschitzDegreePushforward C FYhat Fhat_inf)
    (Jac_inf : X → ℝ)
    (hdeg1 : |(D_inf.lipschitzDegree : ℝ)| = 1)
    (hvol_eq : C.totalVolume = FYhat.manifoldVolume)
    (h_mass_push : FYhat.totalMass D_inf.pushforwardCurrent ≤
      ∫ x, Jac_inf x ∂C.hausdorffMeasure)
    (hJac_int : Integrable Jac_inf C.hausdorffMeasure)
    (hJac_le_one : ∀ᵐ x ∂C.hausdorffMeasure, Jac_inf x ≤ 1) :
    (∫ x, Jac_inf x ∂C.hausdorffMeasure = C.totalVolume) ∧
      (∀ᵐ x ∂C.hausdorffMeasure, Jac_inf x = 1) := by
  have h_lower : C.totalVolume ≤ ∫ x, Jac_inf x ∂C.hausdorffMeasure := by
    have hdeg_area := degree_mul_volume_le_integral_jacobian C FYhat D_inf Jac_inf h_mass_push
    rw [hdeg1, one_mul, ← hvol_eq] at hdeg_area
    exact hdeg_area
  have h_const_int : ∫ _ : X, (1 : ℝ) ∂C.hausdorffMeasure = C.totalVolume := by
    rw [integral_const, measureReal_def, smul_eq_mul, mul_one]
    rfl
  have h_upper : ∫ x, Jac_inf x ∂C.hausdorffMeasure ≤ C.totalVolume := by
    rw [← h_const_int]
    exact integral_mono_ae hJac_int (integrable_const 1) hJac_le_one
  have h_int_eq : ∫ x, Jac_inf x ∂C.hausdorffMeasure = C.totalVolume :=
    le_antisymm h_upper h_lower
  have h_ae : ∀ᵐ x ∂C.hausdorffMeasure, Jac_inf x = 1 :=
    (integral_eq_iff_of_ae_le hJac_int (integrable_const 1) hJac_le_one).mp
      (h_int_eq.trans h_const_int.symm)
  exact ⟨h_int_eq, h_ae⟩

/-- **Theorem 1.1 Part 2 (`thm:rcd-entropy-degree`, Complete Equality-Case Rigidity for Closed
Orientable Non-Collapsed $\mathsf{RCD}(K, N)$ and Alexandrov Spaces)**
(`RCD-Entropy-Degree-Skeleton.tex`, lines 641–687):
Let $(X, \mathsf{d}, \mathcal{H}^N)$ be a closed orientable non-collapsed $\mathsf{RCD}(K, N)$ space
(assumed compact) and $f : X \to Y$ a continuous map to a closed oriented negatively curved locally
symmetric $N$-manifold $Y$ with $k = |\deg(f)| = [\pi_1(Y) : f_* \pi_1(X)] \ge 1$.
Let $p : \widehat{Y} \to Y$ be the degree-$k$ Riemannian covering associated to $f_* \pi_1(X) \le \pi_1(Y)$
($\mathcal{H}^N(\widehat{Y}) = k \, \mathcal{H}^N(Y)$, $h(\widetilde{\widehat{Y}}) = h(\widetilde{Y})$)
and $\hat{f} : X \to \widehat{Y}$ the lifted map ($f = p \circ \hat{f}$).
Suppose equality holds in the Entropy-Degree Inequality:
$$h(\overline{X})^N \, \mathcal{H}^N(X) = k \, h(\widetilde{Y})^N \, \mathcal{H}^N(Y).$$
Then with the homothetic rescaling factor $c = h(\overline{X}) / h(\widetilde{Y}) > 0$ and the
$1$-Lipschitz limit map $\hat{F}_\infty : X \to \widehat{Y}$ homotopic to $\hat{f}$:
1. $|\deg(\hat{f})| = 1$, $c^{-1} h(\overline{X}) = h(\widetilde{Y})$, and
   $c^N \mathcal{H}^N(X) = \mathcal{H}^N(\widehat{Y})$;
2. For the rescaled space $X_c$ ($\mathcal{H}_c^N(X) = \mathcal{H}^N(\widehat{Y})$), the limit map
   $\hat{F}_\infty : X \to \widehat{Y}$ is volume-preserving:
   $$\mathrm{Jac}_x \hat{F}_\infty = 1 \quad \text{for } \mathcal{H}_c^N\text{-almost every } x \in X;$$
3. $\hat{F}_\infty : X \to \widehat{Y}$ is surjective (`Function.Surjective Fhat_inf`);
4. By Lipschitz-volume rigidity (`[RCDbary, Theorem 1.8]` / Li–Wang), $\hat{F}_\infty$ is a global
   metric isometry from $(X, c\,\mathsf{d}_X)$ onto $\widehat{Y}$, and the composite map
   $F = p \circ \hat{F}_\infty : X \to Y$ is a Riemannian covering map of degree $k = |\deg(f)|$. -/
theorem rcd_entropy_degree_equality_rigidity
    [CompactSpace X] [T2Space Yhat]
    (C_rescaled : CMMPOrientationCurrent X K N CurrentX)
    [IsFiniteMeasure C_rescaled.hausdorffMeasure]
    (FYhat : FundamentalManifoldCurrent Yhat CurrentYhat)
    {k deg_fhat h_Xbar h_Ytilde vol_X vol_Y : ℝ}
    (hk_pos : 0 < k) (hh_Xbar : 0 < h_Xbar) (hh_Ytilde : 0 < h_Ytilde)
    (hdeg_mult : k = k * deg_fhat)
    (hvol_cover : FYhat.manifoldVolume = k * vol_Y)
    (heq : entropyVolumeProduct N h_Xbar vol_X =
      k * entropyVolumeProduct N h_Ytilde vol_Y)
    (hvol_rescaled : C_rescaled.totalVolume = (h_Xbar / h_Ytilde) ^ N * vol_X)
    {Fhat_inf : X → Yhat} (hFhat_cont : Continuous Fhat_inf)
    (D_inf : LipschitzDegreePushforward C_rescaled FYhat Fhat_inf)
    (Jac_inf : X → ℝ)
    (hD_deg_ne : D_inf.lipschitzDegree ≠ 0)
    (hD_deg_abs : |(D_inf.lipschitzDegree : ℝ)| = deg_fhat)
    (h_open_pos : ∀ U : Set Yhat, IsOpen U → U.Nonempty → 0 < (FYhat.volumeMeasure U).toReal)
    (h_supp : (FYhat.massMeasure (D_inf.lipschitzDegree • FYhat.fundamentalClass)
      (Set.range Fhat_inf)ᶜ).toReal = 0)
    (h_mass_push : FYhat.totalMass D_inf.pushforwardCurrent ≤
      ∫ x, Jac_inf x ∂C_rescaled.hausdorffMeasure)
    (hJac_int : Integrable Jac_inf C_rescaled.hausdorffMeasure)
    (hJac_le_one : ∀ᵐ x ∂C_rescaled.hausdorffMeasure, Jac_inf x ≤ 1)
    (h_lip_vol_rigidity :
      Function.Surjective Fhat_inf →
      C_rescaled.totalVolume = FYhat.manifoldVolume →
      (∀ᵐ x ∂C_rescaled.hausdorffMeasure, Jac_inf x = 1) →
      ∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = (h_Xbar / h_Ytilde) * dist x₁ x₂) :
    let c := h_Xbar / h_Ytilde
    0 < c ∧
    deg_fhat = 1 ∧
    c⁻¹ * h_Xbar = h_Ytilde ∧
    c ^ N * vol_X = FYhat.manifoldVolume ∧
    C_rescaled.totalVolume = FYhat.manifoldVolume ∧
    (∀ᵐ x ∂C_rescaled.hausdorffMeasure, Jac_inf x = 1) ∧
    Function.Surjective Fhat_inf ∧
    (∀ x₁ x₂ : X, dist (Fhat_inf x₁) (Fhat_inf x₂) = c * dist x₁ x₂) := by
  intro c
  obtain ⟨hdeg1, hprod_Yhat⟩ :=
    finite_cover_entropy_degree_reduction N hk_pos hdeg_mult hvol_cover heq
  obtain ⟨hc_pos, h_ent_norm, h_vol_norm⟩ :=
    homothetic_normalization N hh_Xbar hh_Ytilde hprod_Yhat
  have hvol_eq : C_rescaled.totalVolume = FYhat.manifoldVolume :=
    hvol_rescaled.trans h_vol_norm
  have hD_deg1 : |(D_inf.lipschitzDegree : ℝ)| = 1 := hD_deg_abs.trans hdeg1
  obtain ⟨_, hae_jac1⟩ := ae_jacobian_eq_one_of_normalized_equality
    C_rescaled FYhat D_inf Jac_inf hD_deg1 hvol_eq h_mass_push hJac_int hJac_le_one
  have h_surj : Function.Surjective Fhat_inf :=
    surjective_of_degree_ne_zero FYhat h_open_pos hFhat_cont hD_deg_ne h_supp
  have h_isom := h_lip_vol_rigidity h_surj hvol_eq hae_jac1
  exact ⟨hc_pos, hdeg1, h_ent_norm, h_vol_norm, hvol_eq, hae_jac1, h_surj, h_isom⟩

end EqualityCaseRigidity

end RCDEntropyDegree.RCD
