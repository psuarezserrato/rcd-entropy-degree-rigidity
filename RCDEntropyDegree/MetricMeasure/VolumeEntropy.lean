import BCG.Entropy.VolumeEntropy
import DifferentialGeometry.Geometry.Comparison.Volume.HyperbolicModel

/-!
# Metric-Measure Volume Entropy, Intermediate Covers, and Homothetic Scaling Laws

This file formalizes the metric-measure volume entropy infrastructure from Section 3.1 and
Section 4 of P. Suárez-Serrato, *"Entropy-degree rigidity for non-collapsed $\mathsf{RCD}$ spaces"*
(`RCD-Entropy-Degree-Skeleton.tex`):

1. **Logarithmic Ball-Volume Growth & Exponential Volume Growth** (`ballVolumeLogRate`,
   `HasExponentialVolumeGrowth`):
   For a metric-measure space $(Z, \mathsf{d}, \mathfrak{m})$, the logarithmic ball-volume growth rate
   $$\frac{1}{R} \log \mathfrak{m}(B(x_0, R))$$
   is controlled uniformly across basepoints $x_0, x_1 \in Z$ via the triangle inclusion
   $B(x_0, R) \subseteq B(x_1, R + \mathsf{d}(x_0, x_1))$. Under Bishop–Gromov exponential growth
   ($\mathfrak{m}(B(x_0, R)) \le C e^{h R}$), we establish basepoint transfer and upper bounds on
   the asymptotic logarithmic growth rate.

2. **Isometric Equivariance of Exponential Weights (`μ_x^s`)**:
   Under an isometric group action $\Gamma \curvearrowright Z$, the exponential weight
   $w_x^s(z) = e^{-s\,\mathsf{d}(x, z)}$ satisfies $w_{\gamma x}^s(\gamma z) = w_x^s(z)$, ensuring
   that the normalized probability weights on an orbit / sample are $\Gamma$-equivariant.

3. **Homothetic Scaling Invariance and Normalization in the Equality Case**
   (`entropyVolumeProduct`, `entropyVolumeProduct_homothetic_invariance`,
   `homothetic_normalization`, `finite_cover_entropy_degree_reduction`):
   Rescaling the metric by $c > 0$ scales $\mathcal{H}^N(X)$ by $c^N$ and the volume entropy
   $h(\overline{X})$ by $c^{-1}$, leaving $h(\overline{X})^N \mathcal{H}^N(X)$ invariant.
   In the equality case of the Entropy-Degree Theorem (`thm:rcd-entropy-degree`) with a finite
   degree-$k$ cover $p : \widehat{Y} \to Y$ ($k = |\deg(f)|$), choosing $c = h(\overline{X}) / h(\widetilde{Y})$
   normalizes $h(\overline{X}) = h(\widetilde{Y})$ and $\mathcal{H}^N(X) = \mathcal{H}^N(\widehat{Y})$.
-/

noncomputable section

open MeasureTheory Set Filter Finset BigOperators
open scoped ENNReal Topology

namespace RCDEntropyDegree.MetricMeasure

open BCG.Entropy

section BallVolumeGrowth

variable {Z : Type*} [PseudoMetricSpace Z] [MeasurableSpace Z]

/-- The logarithmic ball-volume growth rate at radius $R > 0$ and basepoint $x_0 \in Z$:
$$\frac{1}{R} \log \mathfrak{m}(B(x_0, R)).$$ -/
def ballVolumeLogRate (m : Measure Z) (x₀ : Z) (R : ℝ) : ℝ :=
  R⁻¹ * Real.log (m (Metric.ball x₀ R)).toReal

/-- Triangle inequality inclusion of metric balls under a change of basepoint:
$$B(x_0, R) \subseteq B(x_1, R + \mathsf{d}(x_0, x_1)).$$ -/
theorem ball_subset_ball_add_dist (x₀ x₁ : Z) (R : ℝ) :
    Metric.ball x₀ R ⊆ Metric.ball x₁ (R + dist x₀ x₁) := by
  intro z hz
  rw [Metric.mem_ball] at hz ⊢
  linarith [dist_triangle z x₀ x₁]

/-- Monotonicity of finite ball measures under a basepoint shift:
$$\mathfrak{m}(B(x_0, R)) \le \mathfrak{m}(B(x_1, R + \mathsf{d}(x_0, x_1))).$$ -/
theorem measure_ball_le_measure_ball_add_dist (m : Measure Z) (x₀ x₁ : Z) (R : ℝ) :
    m (Metric.ball x₀ R) ≤ m (Metric.ball x₁ (R + dist x₀ x₁)) :=
  measure_mono (ball_subset_ball_add_dist x₀ x₁ R)

/-- Real-valued ball volume comparison under a basepoint shift when the larger ball has finite measure. -/
theorem toReal_measure_ball_le_add_dist (m : Measure Z) (x₀ x₁ : Z) (R : ℝ)
    (hfin : m (Metric.ball x₁ (R + dist x₀ x₁)) ≠ ⊤) :
    (m (Metric.ball x₀ R)).toReal ≤ (m (Metric.ball x₁ (R + dist x₀ x₁))).toReal :=
  ENNReal.toReal_mono hfin (measure_ball_le_measure_ball_add_dist m x₀ x₁ R)

/-- **Exponential Volume Growth Condition** (`HasExponentialVolumeGrowth m x₀ C h`):
A metric-measure space $(Z, \mathsf{d}, \mathfrak{m})$ has exponential ball-volume growth with
constant $C > 0$ and exponent $h \ge 0$ at $x_0 \in Z$ if
$$\forall R > 0, \quad \mathfrak{m}(B(x_0, R)) \le C e^{h R}.$$
By Bishop–Gromov volume comparison (`DifferentialGeometry.Geometry.Riemannian.VolumeComparison`),
every non-collapsed $\mathsf{RCD}(K, N)$ space or intermediate cover $\overline{X}$ satisfies this
condition. -/
structure HasExponentialVolumeGrowth (m : Measure Z) (x₀ : Z) (C h : ℝ) : Prop where
  C_pos : 0 < C
  h_nonneg : 0 ≤ h
  ball_le : ∀ R : ℝ, 0 < R →
    (m (Metric.ball x₀ R)).toReal ≤ C * Real.exp (h * R)

/-- **Basepoint Independence of Exponential Volume Growth**:
If $(Z, \mathsf{d}, \mathfrak{m})$ has exponential volume growth with exponent $h$ and constant $C$
at $x_1$, and balls centered at $x_1$ have finite measure, then $(Z, \mathsf{d}, \mathfrak{m})$ has
exponential volume growth at any other basepoint $x_0 \in Z$ with the *same* exponent $h$ and
shifted constant $C e^{h\,\mathsf{d}(x_0, x_1)}$. -/
theorem HasExponentialVolumeGrowth.of_basepoint {m : Measure Z} {x₁ : Z} {C h : ℝ}
    (hg : HasExponentialVolumeGrowth m x₁ C h) (x₀ : Z)
    (hfin : ∀ R : ℝ, 0 < R → m (Metric.ball x₁ (R + dist x₀ x₁)) ≠ ⊤) :
    HasExponentialVolumeGrowth m x₀ (C * Real.exp (h * dist x₀ x₁)) h where
  C_pos := mul_pos hg.C_pos (Real.exp_pos _)
  h_nonneg := hg.h_nonneg
  ball_le := by
    intro R hR
    have hR' : 0 < R + dist x₀ x₁ := add_pos_of_pos_of_nonneg hR dist_nonneg
    calc
      (m (Metric.ball x₀ R)).toReal
        ≤ (m (Metric.ball x₁ (R + dist x₀ x₁))).toReal :=
          toReal_measure_ball_le_add_dist m x₀ x₁ R (hfin R hR)
      _ ≤ C * Real.exp (h * (R + dist x₀ x₁)) := hg.ball_le (R + dist x₀ x₁) hR'
      _ = C * Real.exp (h * dist x₀ x₁) * Real.exp (h * R) := by
          rw [mul_add, Real.exp_add]
          ring

/-- Under `HasExponentialVolumeGrowth m x₀ C h`, for every radius $R > 0$ with positive ball measure,
the logarithmic growth rate satisfies
$$\frac{1}{R} \log \mathfrak{m}(B(x_0, R)) \le h + \frac{\log C}{R}.$$ -/
theorem HasExponentialVolumeGrowth.ballVolumeLogRate_le {m : Measure Z} {x₀ : Z} {C h : ℝ}
    (hg : HasExponentialVolumeGrowth m x₀ C h) {R : ℝ} (hR : 0 < R)
    (hpos : 0 < (m (Metric.ball x₀ R)).toReal) :
    ballVolumeLogRate m x₀ R ≤ h + R⁻¹ * Real.log C := by
  unfold ballVolumeLogRate
  have hlog : Real.log (m (Metric.ball x₀ R)).toReal ≤ Real.log C + h * R := by
    calc
      Real.log (m (Metric.ball x₀ R)).toReal
        ≤ Real.log (C * Real.exp (h * R)) :=
          Real.log_le_log hpos (hg.ball_le R hR)
      _ = Real.log C + h * R := by
          rw [Real.log_mul hg.C_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hinv_pos : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  calc
    R⁻¹ * Real.log (m (Metric.ball x₀ R)).toReal
      ≤ R⁻¹ * (Real.log C + h * R) := mul_le_mul_of_nonneg_left hlog hinv_pos
    _ = h + R⁻¹ * Real.log C := by
      have hR_ne : R ≠ 0 := hR.ne'
      field_simp [hR_ne]
      ring

/-- **Exponential Upper Bound for the Hyperbolic Model Warping Function `hyperbolicSn`**
(`DifferentialGeometry.Geometry.Riemannian.VolumeComparison`):
For all $q \ge 0$ and $R \in \mathbb{R}$,
$$\mathrm{sn}_{-q^2}(R) \le R \, e^{q R}.$$ -/
theorem hyperbolicSn_le_mul_exp {q : ℝ} (hq : 0 ≤ q) (R : ℝ) :
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicSn q R ≤
      R * Real.exp (q * R) := by
  unfold DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicSn
  split_ifs with hq0
  · subst hq0
    simp
  · have hq_pos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    rw [div_le_iff₀ hq_pos]
    set u := q * R
    have h_exp : 1 - 2 * u ≤ Real.exp (-2 * u) := by
      simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-2 * u)
    have h_prod : Real.exp u * Real.exp (-2 * u) = Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h_sinh : Real.sinh u ≤ u * Real.exp u := by
      rw [Real.sinh_eq]
      have h_mul := mul_le_mul_of_nonneg_left h_exp (Real.exp_pos u).le
      linarith [h_prod]
    calc
      Real.sinh u ≤ u * Real.exp u := h_sinh
      _ = R * Real.exp u * q := by ring

/-- **Exponential Upper Bound for the Bishop–Gromov Model Density `hyperbolicDensity`**:
For any dimension $d \in \mathbb{N}$, $q \ge 0$, and $R \ge 0$,
$$\mathrm{sn}_{-q^2}(R)^d \le R^d \, e^{q d R}.$$ -/
theorem hyperbolicDensity_le_pow_mul_exp (d : ℕ) {q R : ℝ} (hq : 0 ≤ q) (hR : 0 ≤ R) :
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicDensity q d R ≤
      R ^ d * Real.exp (q * (d : ℝ) * R) := by
  unfold DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicDensity
  have hsn_nonneg : 0 ≤
      DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicSn q R := by
    rcases eq_or_lt_of_le hR with rfl | hR_pos
    · simp [DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicSn]
    · exact (DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicSn_pos hq hR_pos).le
  calc
    DifferentialGeometry.Geometry.Riemannian.VolumeComparison.hyperbolicSn q R ^ d
      ≤ (R * Real.exp (q * R)) ^ d :=
        pow_le_pow_left₀ hsn_nonneg (hyperbolicSn_le_mul_exp hq R) d
    _ = R ^ d * Real.exp (q * (d : ℝ) * R) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring

end BallVolumeGrowth

section ExponentialWeightEquivariance

variable {Z : Type*} [PseudoMetricSpace Z]

/-- **Isometric Invariance of the Exponential Distance Weight**:
If $\gamma : Z \to Z$ preserves distances ($\mathsf{d}(\gamma x, \gamma z) = \mathsf{d}(x, z)$),
then $e^{-s\,\mathsf{d}(\gamma x, \gamma z)} = e^{-s\,\mathsf{d}(x, z)}$. -/
theorem exponentialWeight_isometry (s : ℝ) {γ : Z → Z}
    (hγ : ∀ a b : Z, dist (γ a) (γ b) = dist a b) (x z : Z) :
    exponentialWeight s (γ x) (γ z) = exponentialWeight s x z := by
  simp [exponentialWeight, hγ x z]

/-- Normalized finite-sample exponential probability weight at $x \in Z$:
$$\bar{w}_x^s(i) = \frac{e^{-s\,\mathsf{d}(x, z_i)}}{\sum_{j \in \iota} e^{-s\,\mathsf{d}(x, z_j)}}.$$ -/
def normalizedExponentialWeight {ι : Type*} [Fintype ι]
    (s : ℝ) (pts : ι → Z) (x : Z) (i : ι) : ℝ :=
  exponentialWeight s x (pts i) / ∑ j : ι, exponentialWeight s x (pts j)

theorem normalizedExponentialWeight_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ℝ) (pts : ι → Z) (x : Z) (i : ι) :
    0 < normalizedExponentialWeight s pts x i := by
  unfold normalizedExponentialWeight
  refine div_pos (exponentialWeight_pos s x (pts i)) ?_
  exact Finset.sum_pos (fun j _ => exponentialWeight_pos s x (pts j)) Finset.univ_nonempty

theorem normalizedExponentialWeight_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ℝ) (pts : ι → Z) (x : Z) (i : ι) :
    0 ≤ normalizedExponentialWeight s pts x i :=
  (normalizedExponentialWeight_pos s pts x i).le

/-- The normalized exponential weights sum to $1$:
$$\sum_{i \in \iota} \bar{w}_x^s(i) = 1.$$ -/
theorem sum_normalizedExponentialWeight_eq_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (s : ℝ) (pts : ι → Z) (x : Z) :
    ∑ i : ι, normalizedExponentialWeight s pts x i = 1 := by
  unfold normalizedExponentialWeight
  rw [← Finset.sum_div]
  have hpos : 0 < ∑ j : ι, exponentialWeight s x (pts j) :=
    Finset.sum_pos (fun j _ => exponentialWeight_pos s x (pts j)) Finset.univ_nonempty
  exact div_self hpos.ne'

/-- **$\Gamma$-Equivariance of Normalized Exponential Probability Weights**:
If $\gamma : Z \to Z$ is an isometry permuting the sample points via $e : \iota \simeq \iota$
($\gamma(\mathrm{pts}(i)) = \mathrm{pts}(e(i))$), then
$$\bar{w}_{\gamma(x)}^s(e(i)) = \bar{w}_x^s(i).$$ -/
theorem normalizedExponentialWeight_equivariant {ι : Type*} [Fintype ι]
    (s : ℝ) (pts : ι → Z) (γ : Z → Z) (e : ι ≃ ι)
    (hγ : ∀ a b : Z, dist (γ a) (γ b) = dist a b)
    (hpts : ∀ i : ι, γ (pts i) = pts (e i)) (x : Z) (i : ι) :
    normalizedExponentialWeight s pts (γ x) (e i) =
      normalizedExponentialWeight s pts x i := by
  unfold normalizedExponentialWeight
  have hnum : exponentialWeight s (γ x) (pts (e i)) = exponentialWeight s x (pts i) := by
    rw [← hpts i, exponentialWeight_isometry s hγ x (pts i)]
  have hden : (∑ j : ι, exponentialWeight s (γ x) (pts j)) =
      ∑ j : ι, exponentialWeight s x (pts j) := by
    rw [← Equiv.sum_comp e (fun j => exponentialWeight s (γ x) (pts j))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hpts j, exponentialWeight_isometry s hγ x (pts j)]
  rw [hnum, hden]

end ExponentialWeightEquivariance

section HomotheticScalingAndCoveringReduction

/-- The scale-invariant entropy-volume product functional
$$\mathcal{E}_N(h, V) = h^N \, V$$
appearing on both sides of the Entropy-Degree Inequality (`thm:rcd-entropy-degree`):
$$h(\overline{X})^N \mathcal{H}^N(X) \ge |\deg(f)| \, h(\widetilde{Y})^N \mathcal{H}^N(Y).$$ -/
def entropyVolumeProduct (N : ℕ) (h vol : ℝ) : ℝ :=
  h ^ N * vol

/-- Under a homothetic metric rescaling $\mathsf{d}_c = c\,\mathsf{d}$ ($c > 0$), the exponential
distance weight at parameter $s / c$ coincides with the unscaled weight at parameter $s$:
$$\exp\!\big(-(s / c) \cdot (c \, d)\big) = \exp(-s \, d).$$ -/
theorem exp_rescaled_dist_eq {c : ℝ} (hc : c ≠ 0) (s d : ℝ) :
    Real.exp (-(s / c) * (c * d)) = Real.exp (-s * d) := by
  congr 1
  field_simp [hc]

/-- Under a homothetic metric rescaling $\mathsf{d}_c = c\,\mathsf{d}$ ($c > 0$), the volume
entropy scales by $c^{-1}$:
$$\frac{1}{c R} \log V = c^{-1} \cdot \left(\frac{1}{R} \log V\right).$$ -/
theorem logRate_homothetic_scaling (c R logV : ℝ) :
    (c * R)⁻¹ * logV = c⁻¹ * (R⁻¹ * logV) := by
  rw [mul_inv, mul_assoc]

/-- **Homothetic Scaling Invariance of $h(\overline{X})^N \mathcal{H}^N(X)$**
(`RCD-Entropy-Degree-Skeleton.tex`, proof of Theorem 1.1, lines 655–657):
Rescaling the metric of an $N$-dimensional space $X$ by a factor $c > 0$ scales the Hausdorff
volume $\mathcal{H}^N(X)$ by $c^N$ and the volume entropy $h(\overline{X})$ by $c^{-1}$, leaving
$h(\overline{X})^N \mathcal{H}^N(X)$ strictly invariant:
$$(c^{-1} h)^N \cdot (c^N V) = h^N V.$$ -/
theorem entropyVolumeProduct_homothetic_invariance
    (N : ℕ) {c : ℝ} (hc : c ≠ 0) (h vol : ℝ) :
    entropyVolumeProduct N (c⁻¹ * h) (c ^ N * vol) = entropyVolumeProduct N h vol := by
  unfold entropyVolumeProduct
  rw [mul_pow, inv_pow]
  have hcN : c ^ N ≠ 0 := pow_ne_zero N hc
  calc
    (c ^ N)⁻¹ * h ^ N * (c ^ N * vol)
      = ((c ^ N)⁻¹ * c ^ N) * (h ^ N * vol) := by ring
    _ = h ^ N * vol := by rw [inv_mul_cancel₀ hcN, one_mul]

/-- **Homothetic Normalization in the Equality Case of Theorem 1.1**
(`RCD-Entropy-Degree-Skeleton.tex`, lines 656–660):
Suppose $h_X > 0$, $h_Y > 0$, and the equality $h_X^N V_X = h_Y^N V_{\widehat{Y}}$ holds.
Then choosing the homothetic rescaling factor $c = h_X / h_Y > 0$ yields both:
1. $c^{-1} h_X = h_Y$ (normalized volume entropy equality), and
2. $c^N V_X = V_{\widehat{Y}}$ (normalized Hausdorff volume equality). -/
theorem homothetic_normalization
    (N : ℕ) {h_X h_Y vol_X vol_Yhat : ℝ}
    (hhX : 0 < h_X) (hhY : 0 < h_Y)
    (heq : entropyVolumeProduct N h_X vol_X = entropyVolumeProduct N h_Y vol_Yhat) :
    let c := h_X / h_Y
    0 < c ∧ c⁻¹ * h_X = h_Y ∧ c ^ N * vol_X = vol_Yhat := by
  intro c
  have hc_pos : 0 < c := div_pos hhX hhY
  have h_ent : c⁻¹ * h_X = h_Y := by
    dsimp [c]
    rw [inv_div]
    exact div_mul_cancel₀ h_Y hhX.ne'
  have h_vol : c ^ N * vol_X = vol_Yhat := by
    have hinv := entropyVolumeProduct_homothetic_invariance N hc_pos.ne' h_X vol_X
    rw [h_ent, heq] at hinv
    unfold entropyVolumeProduct at hinv
    have hhYN : h_Y ^ N ≠ 0 := pow_ne_zero N hhY.ne'
    exact mul_left_cancel₀ hhYN hinv
  exact ⟨hc_pos, h_ent, h_vol⟩

/-- **Finite Degree-$k$ Intermediate Covering Reduction**
(`RCD-Entropy-Degree-Skeleton.tex`, Proof of Theorem 1.1, lines 645–654):
Let $p : \widehat{Y} \to Y$ be the finite Riemannian covering of degree $k = |\deg(f)| \ge 1$
associated to $f_* \pi_1(X) \le \pi_1(Y)$, and let $\hat{f} : X \to \widehat{Y}$ be the lift of $f$
satisfying $f = p \circ \hat{f}$. Then:
1. From multiplicative degree $|\deg(f)| = k \cdot |\deg(\hat{f})|$ and $k = |\deg(f)| > 0$, the lift
   has degree $|\deg(\hat{f})| = 1$.
2. Since $\mathcal{H}^N(\widehat{Y}) = k \, \mathcal{H}^N(Y)$ and $h(\widetilde{\widehat{Y}}) = h(\widetilde{Y})$,
   the equality $h(\overline{X})^N \mathcal{H}^N(X) = |\deg(f)| \, h(\widetilde{Y})^N \mathcal{H}^N(Y)$
   rewrites as the degree-$1$ equality
   $$h(\overline{X})^N \mathcal{H}^N(X) = h(\widetilde{Y})^N \mathcal{H}^N(\widehat{Y}).$$ -/
theorem finite_cover_entropy_degree_reduction
    (N : ℕ) {k deg_fhat h_X h_Y vol_X vol_Y vol_Yhat : ℝ}
    (hk_pos : 0 < k)
    (hdeg_mult : k = k * deg_fhat)
    (hvol_cover : vol_Yhat = k * vol_Y)
    (heq : entropyVolumeProduct N h_X vol_X = k * entropyVolumeProduct N h_Y vol_Y) :
    deg_fhat = 1 ∧
      entropyVolumeProduct N h_X vol_X = entropyVolumeProduct N h_Y vol_Yhat := by
  have hdeg1 : deg_fhat = 1 := by
    apply mul_left_cancel₀ hk_pos.ne'
    linarith
  have hprod : entropyVolumeProduct N h_X vol_X = entropyVolumeProduct N h_Y vol_Yhat := by
    rw [heq, hvol_cover]
    unfold entropyVolumeProduct
    ring
  exact ⟨hdeg1, hprod⟩

end HomotheticScalingAndCoveringReduction

end RCDEntropyDegree.MetricMeasure
