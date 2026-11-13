import RCDEntropyDegree.MetricMeasure.VolumeEntropy
import BCG.Hyperbolic.NaturalMap
import DifferentialGeometry.Geometry.CenterOfMass.Basic

/-!
# Sturm's $\mathsf{CAT}(0)$ $d^2$-Barycenter, Equivariant Natural Maps, and Geodesic Homotopy

This file formalizes Section 3.1 (`subsec:natural-maps` and Lemma 3.1 `lem:natural-maps`) of
P. Suárez-Serrato, *"Entropy-degree rigidity for non-collapsed $\mathsf{RCD}$ spaces"*
(`RCD-Entropy-Degree-Skeleton.tex`), building on Sturm's theory of probability measures on metric
spaces of nonpositive curvature (`[Sturm03, Proposition 4.3]`) and the metric center-of-mass
infrastructure in `DifferentialGeometry.Geometry.Riemannian.CenterOfMass`.

## Main Results
1. **Sturm's Renormalized $d^2$-Barycenter Functional (`sturmFunctional`)**:
   $$\mathcal{S}_{w, y, o}(z) = \sum_{i \in \iota} w_i \big(\mathsf{d}(y_i, z)^2 - \mathsf{d}(o, y_i)^2\big).$$
   - **First-Moment Linear Growth Bound (`abs_sturmSummand_le`, `abs_sturmFunctional_le`)**:
     $$\big|\mathsf{d}(y, z)^2 - \mathsf{d}(o, y)^2\big| \le \mathsf{d}(o, z)\big(\mathsf{d}(o, z) + 2\,\mathsf{d}(o, y)\big),$$
     explaining why $\mathcal{S}_{w, y, o}$ only requires a finite first moment rather than second moment.
   - **Basepoint Independence (`sturmFunctional_sub_basepoint`, `sturmFunctional_min_iff_basepoint`)**:
     Changing the reference point $o_1 \mapsto o_2$ shifts $\mathcal{S}_{w, y, o}(z)$ by a constant
     independent of $z$, so global minimizers are independent of the basepoint $o$ and coincide
     with minimizers of `metricEnergy`.
2. **$\mathsf{CAT}(0)$ Semi-Parallelogram Law & Sturm's Variance Inequality (`IsCATZeroMidpoint`,
   `sturmFunctional_midpoint_le`, `sturm_variance_inequality`, `sturmFunctional_unique_min`)**:
   Under the $\mathsf{CAT}(0)$ midpoint inequality
   $$\mathsf{d}(y, m)^2 \le \frac{1}{2}\mathsf{d}(y, a)^2 + \frac{1}{2}\mathsf{d}(y, b)^2 - \frac{1}{4}\mathsf{d}(a, b)^2,$$
   every minimizer $q = \mathrm{bar}(\nu)$ of $\mathcal{S}_{w, y, o}$ satisfies Sturm's variance
   inequality
   $$\frac{1}{2}\mathsf{d}(q, z)^2 \le \mathcal{S}_{w, y, o}(z) - \mathcal{S}_{w, y, o}(q)$$
   and is therefore the **unique** global minimizer.
3. **$\Gamma$-Equivariance, Natural Maps $\overline{F}_s$, Quotient Descent $F_s$, and Geodesic Homotopy**
   (`sturmBarycenter_equivariant`, `sturmNaturalMap_equivariant`, `geodesicHomotopyLift`,
   `geodesicHomotopyQuotient`, `geodesicHomotopyQuotient_zero`, `geodesicHomotopyQuotient_one`):
   Formalizes Lemma 3.1 (`lem:natural-maps`) of `RCD-Entropy-Degree-Skeleton.tex`: the natural map
   $\overline{F}_s(x) = \mathrm{bar}(\overline{f}_* \mu_x^s / \mu_x^s(\overline{X}))$ is
   $\Gamma$-equivariant, descends to a quotient map $F_s : X \to Y$, and is homotopic to $f$ via
   the $\Gamma$-equivariant geodesic homotopy $\overline{H}_s(x, t) = \gamma_{\overline{f}(x), \overline{F}_s(x)}(t)$.
-/

noncomputable section

open Finset BigOperators Set Filter
open scoped Topology

namespace RCDEntropyDegree.MetricMeasure

open DifferentialGeometry.Geometry.Riemannian.CenterOfMass
open BCG.Hyperbolic

section SturmFunctional

variable {Y : Type*} [MetricSpace Y]
variable {ι : Type*} [Fintype ι]

/-- The renormalized squared-distance integrand of Sturm's $d^2$-barycenter functional
(`[Sturm03, Prop. 4.3]`, `RCD-Entropy-Degree-Skeleton.tex` Sec. 3.1):
$$\psi_o(y, z) = \mathsf{d}(y, z)^2 - \mathsf{d}(o, y)^2.$$ -/
def sturmSummand (o y z : Y) : ℝ :=
  dist y z ^ 2 - dist o y ^ 2

@[simp]
theorem sturmSummand_basepoint_self (o y : Y) :
    sturmSummand o y o = 0 := by
  simp [sturmSummand, dist_comm]

/-- Shifting the basepoint $o_1 \mapsto o_2$ in `sturmSummand` changes it by a quantity
independent of $z$:
$$\psi_{o_1}(y, z) - \psi_{o_2}(y, z) = \mathsf{d}(o_2, y)^2 - \mathsf{d}(o_1, y)^2.$$ -/
theorem sturmSummand_sub_sturmSummand (o₁ o₂ y z : Y) :
    sturmSummand o₁ y z - sturmSummand o₂ y z = dist o₂ y ^ 2 - dist o₁ y ^ 2 := by
  unfold sturmSummand
  ring

/-- **First-Moment Linear Growth Bound for `sturmSummand`**:
For any basepoint $o \in Y$ and points $y, z \in Y$,
$$\big|\mathsf{d}(y, z)^2 - \mathsf{d}(o, y)^2\big| \le \mathsf{d}(o, z)\big(\mathsf{d}(o, z) + 2\,\mathsf{d}(o, y)\big).$$
This guarantees integrability of $y \mapsto \mathsf{d}(y, z)^2 - \mathsf{d}(o, y)^2$ against any
probability measure with finite first moment $\int \mathsf{d}(o, y)\,d\nu(y) < \infty$. -/
theorem abs_sturmSummand_le (o y z : Y) :
    |sturmSummand o y z| ≤ dist o z * (dist o z + 2 * dist o y) := by
  unfold sturmSummand
  have hfac : dist y z ^ 2 - dist o y ^ 2 = (dist y z - dist o y) * (dist y z + dist o y) := by
    ring
  have htri1 : dist y z ≤ dist o y + dist o z := by
    simpa [dist_comm y o] using dist_triangle y o z
  have htri2 : dist o y ≤ dist o z + dist y z := by
    simpa [dist_comm z y] using dist_triangle o z y
  have habs_diff : |dist y z - dist o y| ≤ dist o z :=
    abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hsum_nonneg : 0 ≤ dist y z + dist o y := add_nonneg dist_nonneg dist_nonneg
  have hsum_le : dist y z + dist o y ≤ dist o z + 2 * dist o y := by linarith
  rw [hfac, abs_mul, abs_of_nonneg hsum_nonneg]
  exact mul_le_mul habs_diff hsum_le hsum_nonneg dist_nonneg

/-- **Sturm's Renormalized $d^2$-Barycenter Functional** (`RCD-Entropy-Degree-Skeleton.tex` Sec. 3.1):
$$\mathcal{S}_{w, y, o}(z) = \sum_{i \in \iota} w_i \big(\mathsf{d}(y_i, z)^2 - \mathsf{d}(o, y_i)^2\big).$$ -/
def sturmFunctional (w : ι → ℝ) (y : ι → Y) (o : Y) (z : Y) : ℝ :=
  ∑ i : ι, w i * sturmSummand o (y i) z

@[simp]
theorem sturmFunctional_basepoint_self (w : ι → ℝ) (y : ι → Y) (o : Y) :
    sturmFunctional w y o o = 0 := by
  simp [sturmFunctional]

/-- Relation between `sturmFunctional` and `metricEnergy` from
`DifferentialGeometry.Geometry.Riemannian.CenterOfMass`:
$$\mathcal{S}_{w, y, o}(z) = 2 \, \mathrm{metricEnergy}(w, y, z) - \sum_{i \in \iota} w_i \, \mathsf{d}(o, y_i)^2.$$ -/
theorem sturmFunctional_eq_two_mul_metricEnergy_sub
    (w : ι → ℝ) (y : ι → Y) (o z : Y) :
    sturmFunctional w y o z =
      2 * metricEnergy w y z - ∑ i : ι, w i * dist o (y i) ^ 2 := by
  unfold sturmFunctional sturmSummand metricEnergy
  rw [← mul_assoc]
  norm_num
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dist_comm z (y i)]
  ring

/-- Shifting the basepoint $o_1 \mapsto o_2$ in `sturmFunctional` adds a constant independent of $z$. -/
theorem sturmFunctional_sub_basepoint
    (w : ι → ℝ) (y : ι → Y) (o₁ o₂ z : Y) :
    sturmFunctional w y o₁ z - sturmFunctional w y o₂ z =
      ∑ i : ι, w i * (dist o₂ (y i) ^ 2 - dist o₁ (y i) ^ 2) := by
  unfold sturmFunctional
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← mul_sub, sturmSummand_sub_sturmSummand]

/-- **Basepoint Independence of Global Minimizers of `sturmFunctional`**:
A point $q \in Y$ minimizes $\mathcal{S}_{w, y, o_1}$ if and only if it minimizes $\mathcal{S}_{w, y, o_2}$. -/
theorem sturmFunctional_min_iff_basepoint
    (w : ι → ℝ) (y : ι → Y) (o₁ o₂ q : Y) :
    (∀ z : Y, sturmFunctional w y o₁ q ≤ sturmFunctional w y o₁ z) ↔
      (∀ z : Y, sturmFunctional w y o₂ q ≤ sturmFunctional w y o₂ z) := by
  constructor
  · intro h z
    have hq := sturmFunctional_sub_basepoint w y o₁ o₂ q
    have hz := sturmFunctional_sub_basepoint w y o₁ o₂ z
    linarith [h z]
  · intro h z
    have hq := sturmFunctional_sub_basepoint w y o₁ o₂ q
    have hz := sturmFunctional_sub_basepoint w y o₁ o₂ z
    linarith [h z]

/-- Equivalence between minimizing `sturmFunctional` and minimizing `metricEnergy`. -/
theorem sturmFunctional_min_iff_metricEnergy
    (w : ι → ℝ) (y : ι → Y) (o q : Y) :
    (∀ z : Y, sturmFunctional w y o q ≤ sturmFunctional w y o z) ↔
      (∀ z : Y, metricEnergy w y q ≤ metricEnergy w y z) := by
  constructor
  · intro h z
    have hq := sturmFunctional_eq_two_mul_metricEnergy_sub w y o q
    have hz := sturmFunctional_eq_two_mul_metricEnergy_sub w y o z
    linarith [h z]
  · intro h z
    have hq := sturmFunctional_eq_two_mul_metricEnergy_sub w y o q
    have hz := sturmFunctional_eq_two_mul_metricEnergy_sub w y o z
    linarith [h z]

/-- Continuity of Sturm's $d^2$-barycenter functional $z \mapsto \mathcal{S}_{w, y, o}(z)$. -/
theorem continuous_sturmFunctional (w : ι → ℝ) (y : ι → Y) (o : Y) :
    Continuous (sturmFunctional w y o) := by
  have h_eq : sturmFunctional w y o =
      fun z => 2 * metricEnergy w y z - ∑ i : ι, w i * dist o (y i) ^ 2 := by
    funext z
    exact sturmFunctional_eq_two_mul_metricEnergy_sub w y o z
  rw [h_eq]
  exact (continuous_const.mul (metricEnergy_cont w y)).sub continuous_const

/-- **First-Moment Bound for Sturm's Functional**:
For probability weights ($w_i \ge 0$, $\sum_i w_i = 1$),
$$\big|\mathcal{S}_{w, y, o}(z)\big| \le \mathsf{d}(o, z)^2 + 2\,\mathsf{d}(o, z) \sum_{i \in \iota} w_i\,\mathsf{d}(o, y_i).$$ -/
theorem abs_sturmFunctional_le
    {w : ι → ℝ} (hw_nn : ∀ i : ι, 0 ≤ w i) (hw_sum : ∑ i : ι, w i = 1)
    (y : ι → Y) (o z : Y) :
    |sturmFunctional w y o z| ≤
      dist o z ^ 2 + 2 * dist o z * ∑ i : ι, w i * dist o (y i) := by
  unfold sturmFunctional
  calc
    |∑ i : ι, w i * sturmSummand o (y i) z|
      ≤ ∑ i : ι, |w i * sturmSummand o (y i) z| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : ι, w i * |sturmSummand o (y i) z| := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [abs_mul, abs_of_nonneg (hw_nn i)]
    _ ≤ ∑ i : ι, w i * (dist o z * (dist o z + 2 * dist o (y i))) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_of_nonneg_left (abs_sturmSummand_le o (y i) z) (hw_nn i)
    _ = (∑ i : ι, w i) * dist o z ^ 2 +
          2 * dist o z * ∑ i : ι, w i * dist o (y i) := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ = dist o z ^ 2 + 2 * dist o z * ∑ i : ι, w i * dist o (y i) := by
        rw [hw_sum, one_mul]

end SturmFunctional

section CATZeroBarycenter

variable {Y : Type*} [MetricSpace Y]
variable {ι : Type*} [Fintype ι]

/-- **$\mathsf{CAT}(0)$ Geodesic Join & Midpoint Semi-Parallelogram Law**
(Bruhat–Tits / Alexandrov $\kappa \le 0$ / Sturm `[Sturm03]`):
A geodesic join `join : Y → Y → ℝ → Y` satisfies the $\mathsf{CAT}(0)$ midpoint inequality if
$\mathrm{join}(a, b, 0) = a$, $\mathrm{join}(a, b, 1) = b$, and for every reference point $y \in Y$
and endpoints $a, b \in Y$, the midpoint $m = \mathrm{join}(a, b, 1/2)$ satisfies
$$\mathsf{d}(y, m)^2 \le \frac{\mathsf{d}(y, a)^2 + \mathsf{d}(y, b)^2}{2} - \frac{1}{4}\mathsf{d}(a, b)^2.$$ -/
structure IsCATZeroMidpoint (join : Y → Y → ℝ → Y) : Prop where
  join_zero : ∀ a b : Y, join a b 0 = a
  join_one : ∀ a b : Y, join a b 1 = b
  midpoint_sq_dist_le : ∀ y a b : Y,
    dist y (join a b (1 / 2 : ℝ)) ^ 2 ≤
      (dist y a ^ 2 + dist y b ^ 2) / 2 - (1 / 4 : ℝ) * dist a b ^ 2

/-- Every $\mathsf{CAT}(0)$ midpoint structure satisfies `StrictMidJensenOn join univ (halfSqDist y)`
from `DifferentialGeometry.Geometry.Riemannian.CenterOfMass`. -/
theorem IsCATZeroMidpoint.strictMidJensenOn_halfSqDist
    {join : Y → Y → ℝ → Y} (hcat : IsCATZeroMidpoint join) (y : Y) :
    StrictMidJensenOn join Set.univ (halfSqDist y) := by
  intro a _ b _ hne
  refine ⟨ trivial, ?_ ⟩
  unfold halfSqDist
  have hpos : 0 < dist a b ^ 2 := sq_pos_of_pos (dist_pos.mpr hne)
  have hmid := hcat.midpoint_sq_dist_le y a b
  rw [dist_comm (join a b (1 / 2 : ℝ)) y, dist_comm a y, dist_comm b y]
  linarith

/-- **Quantitative Strong Midpoint Convexity of `sturmFunctional` on $\mathsf{CAT}(0)$ Spaces**:
For any probability weights ($w_i \ge 0$, $\sum_i w_i = 1$) and points $a, b \in Y$,
$$\mathcal{S}_{w, y, o}\!\big(\mathrm{join}(a, b, 1/2)\big) \le
  \frac{\mathcal{S}_{w, y, o}(a) + \mathcal{S}_{w, y, o}(b)}{2} - \frac{1}{4}\mathsf{d}(a, b)^2.$$ -/
theorem sturmFunctional_midpoint_le
    {join : Y → Y → ℝ → Y} (hcat : IsCATZeroMidpoint join)
    {w : ι → ℝ} (hw_nn : ∀ i : ι, 0 ≤ w i) (hw_sum : ∑ i : ι, w i = 1)
    (y : ι → Y) (o a b : Y) :
    sturmFunctional w y o (join a b (1 / 2 : ℝ)) ≤
      (sturmFunctional w y o a + sturmFunctional w y o b) / 2 -
        (1 / 4 : ℝ) * dist a b ^ 2 := by
  unfold sturmFunctional sturmSummand
  have hterm : ∀ i : ι,
      w i * (dist (y i) (join a b (1 / 2 : ℝ)) ^ 2 - dist o (y i) ^ 2) ≤
        w i * ((dist (y i) a ^ 2 - dist o (y i) ^ 2 +
          (dist (y i) b ^ 2 - dist o (y i) ^ 2)) / 2 - (1 / 4 : ℝ) * dist a b ^ 2) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (hw_nn i)
    linarith [hcat.midpoint_sq_dist_le (y i) a b]
  calc
    ∑ i : ι, w i * (dist (y i) (join a b (1 / 2 : ℝ)) ^ 2 - dist o (y i) ^ 2)
      ≤ ∑ i : ι, w i * ((dist (y i) a ^ 2 - dist o (y i) ^ 2 +
          (dist (y i) b ^ 2 - dist o (y i) ^ 2)) / 2 - (1 / 4 : ℝ) * dist a b ^ 2) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((∑ i : ι, w i * (dist (y i) a ^ 2 - dist o (y i) ^ 2)) +
          ∑ i : ι, w i * (dist (y i) b ^ 2 - dist o (y i) ^ 2)) / 2 -
          (∑ i : ι, w i) * ((1 / 4 : ℝ) * dist a b ^ 2) := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ = ((∑ i : ι, w i * (dist (y i) a ^ 2 - dist o (y i) ^ 2)) +
          ∑ i : ι, w i * (dist (y i) b ^ 2 - dist o (y i) ^ 2)) / 2 -
          (1 / 4 : ℝ) * dist a b ^ 2 := by
        rw [hw_sum, one_mul]

/-- **Sturm's Variance Inequality (`[Sturm03, Proposition 4.3]`)**:
On a $\mathsf{CAT}(0)$ space $(Y, \mathsf{d}, \mathrm{join})$, if $q \in Y$ is a global minimizer
of $\mathcal{S}_{w, y, o}$ for probability weights ($w_i \ge 0$, $\sum_i w_i = 1$), then for every
$z \in Y$,
$$\frac{1}{2}\mathsf{d}(q, z)^2 \le \mathcal{S}_{w, y, o}(z) - \mathcal{S}_{w, y, o}(q).$$ -/
theorem sturm_variance_inequality
    {join : Y → Y → ℝ → Y} (hcat : IsCATZeroMidpoint join)
    {w : ι → ℝ} (hw_nn : ∀ i : ι, 0 ≤ w i) (hw_sum : ∑ i : ι, w i = 1)
    (y : ι → Y) (o : Y) {q : Y}
    (hq : ∀ z : Y, sturmFunctional w y o q ≤ sturmFunctional w y o z) (z : Y) :
    (1 / 2 : ℝ) * dist q z ^ 2 ≤ sturmFunctional w y o z - sturmFunctional w y o q := by
  have hmid := sturmFunctional_midpoint_le hcat hw_nn hw_sum y o q z
  have hmin := hq (join q z (1 / 2 : ℝ))
  linarith

/-- **Uniqueness of Sturm's $d^2$-Barycenter on $\mathsf{CAT}(0)$ Spaces**:
Any two global minimizers $q_1, q_2 \in Y$ of $\mathcal{S}_{w, y, o}$ coincide ($q_1 = q_2$). -/
theorem sturmFunctional_unique_min
    {join : Y → Y → ℝ → Y} (hcat : IsCATZeroMidpoint join)
    {w : ι → ℝ} (hw_nn : ∀ i : ι, 0 ≤ w i) (hw_sum : ∑ i : ι, w i = 1)
    (y : ι → Y) (o : Y) {q₁ q₂ : Y}
    (hq₁ : ∀ z : Y, sturmFunctional w y o q₁ ≤ sturmFunctional w y o z)
    (hq₂ : ∀ z : Y, sturmFunctional w y o q₂ ≤ sturmFunctional w y o z) :
    q₁ = q₂ := by
  have hvar := sturm_variance_inequality hcat hw_nn hw_sum y o hq₁ q₂
  have hle : sturmFunctional w y o q₂ ≤ sturmFunctional w y o q₁ := hq₂ q₁
  have hsq : dist q₁ q₂ ^ 2 ≤ 0 := by linarith
  have hzero : dist q₁ q₂ ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
  exact dist_eq_zero.mp (sq_eq_zero_iff.mp hzero)

end CATZeroBarycenter

section EquivarianceAndGeodesicHomotopy

variable {Y : Type*} [MetricSpace Y]
variable {ι : Type*} [Fintype ι]

/-- **Isometry Equivariance of Sturm's $d^2$-Barycenter Functional**:
If $T : Y \to Y$ is a distance-preserving map and $e : \iota \simeq \iota$ permutes the points
so that $w_2(e(i)) = w_1(i)$ and $T(y(i)) = y(e(i))$, then
$$\mathcal{S}_{w_2, y, T(o)}(T(z)) = \mathcal{S}_{w_1, y, o}(z).$$ -/
theorem sturmFunctional_isometry
    (w₁ w₂ : ι → ℝ) (y : ι → Y) (T : Y → Y) (e : ι ≃ ι)
    (hw : ∀ i : ι, w₂ (e i) = w₁ i)
    (hy : ∀ i : ι, T (y i) = y (e i))
    (hT : ∀ a b : Y, dist (T a) (T b) = dist a b)
    (o z : Y) :
    sturmFunctional w₂ y (T o) (T z) = sturmFunctional w₁ y o z := by
  unfold sturmFunctional sturmSummand
  rw [← Equiv.sum_comp e (fun j => w₂ j * (dist (y j) (T z) ^ 2 - dist (T o) (y j) ^ 2))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hw i, ← hy i, hT (y i) z, hT o (y i)]

/-- **Isometry Equivariance of Sturm's $d^2$-Barycenter (`lem:natural-maps` (1))**:
On a $\mathsf{CAT}(0)$ space $(Y, \mathsf{d}, \mathrm{join})$, if $T : Y \to Y$ is a surjective
isometry, $c_1$ minimizes $\mathcal{S}_{w_1, y, o}$, $c_2$ minimizes $\mathcal{S}_{w_2, y, o}$,
$w_2(e(i)) = w_1(i)$, and $T(y(i)) = y(e(i))$, then
$$T(c_1) = c_2.$$ -/
theorem sturmBarycenter_equivariant
    {join : Y → Y → ℝ → Y} (hcat : IsCATZeroMidpoint join)
    {w₁ w₂ : ι → ℝ} (hw₂_nn : ∀ i : ι, 0 ≤ w₂ i) (hw₂_sum : ∑ i : ι, w₂ i = 1)
    (y : ι → Y) (T : Y → Y) (e : ι ≃ ι)
    (hT_surj : Function.Surjective T)
    (hw : ∀ i : ι, w₂ (e i) = w₁ i)
    (hy : ∀ i : ι, T (y i) = y (e i))
    (hT : ∀ a b : Y, dist (T a) (T b) = dist a b)
    (o : Y) {c₁ c₂ : Y}
    (hc₁ : ∀ z : Y, sturmFunctional w₁ y o c₁ ≤ sturmFunctional w₁ y o z)
    (hc₂ : ∀ z : Y, sturmFunctional w₂ y o c₂ ≤ sturmFunctional w₂ y o z) :
    T c₁ = c₂ := by
  have hTc₁_To : ∀ z : Y, sturmFunctional w₂ y (T o) (T c₁) ≤ sturmFunctional w₂ y (T o) z := by
    intro z
    obtain ⟨z₀, rfl⟩ := hT_surj z
    rw [sturmFunctional_isometry w₁ w₂ y T e hw hy hT o c₁,
      sturmFunctional_isometry w₁ w₂ y T e hw hy hT o z₀]
    exact hc₁ z₀
  have hTc₁_o : ∀ z : Y, sturmFunctional w₂ y o (T c₁) ≤ sturmFunctional w₂ y o z :=
    (sturmFunctional_min_iff_basepoint w₂ y (T o) o (T c₁)).mp hTc₁_To
  exact sturmFunctional_unique_min hcat hw₂_nn hw₂_sum y o hTc₁_o hc₂

/-- **$\Gamma$-Equivariance of the Natural Map $\overline{F}_s : \overline{X} \to \widetilde{Y}$**
(`RCD-Entropy-Degree-Skeleton.tex`, Lemma 3.1 `lem:natural-maps` (1)):
Let $\overline{f} : \overline{X} \to \widetilde{Y}$ be $\Gamma$-equivariant, let
$\mathrm{pts} : \iota \to \overline{X}$ be a $\Gamma$-invariant sample ($\gamma(\mathrm{pts}(i)) = \mathrm{pts}(e(i))$),
and let $\overline{F}_s(x) \in \widetilde{Y}$ be the Sturm $d^2$-barycenter of the pushed-forward
normalized exponential weights $\bar{w}_x^s$. Then $\overline{F}_s(\gamma_X(x)) = \gamma_Y(\overline{F}_s(x))$. -/
theorem sturmNaturalMap_equivariant [Nonempty ι]
    {X_bar : Type*} [PseudoMetricSpace X_bar]
    {join : Y → Y → ℝ → Y} (hcat : IsCATZeroMidpoint join)
    (s : ℝ) (pts : ι → X_bar) (f_bar : X_bar → Y)
    (γ_X : X_bar → X_bar) (γ_Y : Y → Y) (e : ι ≃ ι)
    (hγ_X : ∀ a b : X_bar, dist (γ_X a) (γ_X b) = dist a b)
    (hγ_Y : ∀ a b : Y, dist (γ_Y a) (γ_Y b) = dist a b)
    (hγ_Y_surj : Function.Surjective γ_Y)
    (hpts : ∀ i : ι, γ_X (pts i) = pts (e i))
    (hf_equiv : ∀ x : X_bar, f_bar (γ_X x) = γ_Y (f_bar x))
    (o : Y) (F_bar : X_bar → Y)
    (hF_min : ∀ (x : X_bar) (z : Y),
      sturmFunctional (normalizedExponentialWeight s pts x) (f_bar ∘ pts) o (F_bar x) ≤
        sturmFunctional (normalizedExponentialWeight s pts x) (f_bar ∘ pts) o z)
    (x : X_bar) :
    γ_Y (F_bar x) = F_bar (γ_X x) := by
  refine sturmBarycenter_equivariant hcat
    (normalizedExponentialWeight_nonneg s pts (γ_X x))
    (sum_normalizedExponentialWeight_eq_one s pts (γ_X x))
    (f_bar ∘ pts) γ_Y e hγ_Y_surj
    (normalizedExponentialWeight_equivariant s pts γ_X e hγ_X hpts x)
    (fun i => by simp only [Function.comp_apply, ← hpts i, hf_equiv (pts i)])
    hγ_Y o (hF_min x) (hF_min (γ_X x))

/-- **Equivariant Geodesic Homotopy $\overline{H}_s : \overline{X} \times \mathbb{R} \to \widetilde{Y}$**
(`RCD-Entropy-Degree-Skeleton.tex`, Proof of Lemma 3.1 `lem:natural-maps` (2)):
Given a geodesic join `join : Y_tilde → Y_tilde → ℝ → Y_tilde` on $\widetilde{Y}$, the map
$$\overline{H}_s(x, t) = \mathrm{join}\big(\overline{f}(x), \, \overline{F}_s(x), \, t\big)$$
interpolates along unique minimizing geodesics between $\overline{f}$ and $\overline{F}_s$. -/
def geodesicHomotopyLift
    {X_bar Y_tilde : Type*} (join : Y_tilde → Y_tilde → ℝ → Y_tilde)
    (f_bar F_bar : X_bar → Y_tilde) (x : X_bar) (t : ℝ) : Y_tilde :=
  join (f_bar x) (F_bar x) t

@[simp]
theorem geodesicHomotopyLift_zero
    {X_bar Y_tilde : Type*} {join : Y_tilde → Y_tilde → ℝ → Y_tilde}
    (hzero : ∀ a b : Y_tilde, join a b 0 = a)
    (f_bar F_bar : X_bar → Y_tilde) (x : X_bar) :
    geodesicHomotopyLift join f_bar F_bar x 0 = f_bar x :=
  hzero (f_bar x) (F_bar x)

@[simp]
theorem geodesicHomotopyLift_one
    {X_bar Y_tilde : Type*} {join : Y_tilde → Y_tilde → ℝ → Y_tilde}
    (hone : ∀ a b : Y_tilde, join a b 1 = b)
    (f_bar F_bar : X_bar → Y_tilde) (x : X_bar) :
    geodesicHomotopyLift join f_bar F_bar x 1 = F_bar x :=
  hone (f_bar x) (F_bar x)

/-- **$\Gamma$-Equivariance of the Geodesic Homotopy**:
Since unique geodesics in $\widetilde{Y}$ are preserved by isometries
($\gamma \cdot \mathrm{join}(a, b, t) = \mathrm{join}(\gamma \cdot a, \gamma \cdot b, t)$),
if $\overline{f}$ and $\overline{F}_s$ are $\Gamma$-equivariant, then so is $\overline{H}_s(\cdot, t)$
for every $t \in \mathbb{R}$. -/
theorem geodesicHomotopyLift_equivariant
    {Γ : Type*} [Group Γ] {X_bar Y_tilde : Type*}
    [MulAction Γ X_bar] [MulAction Γ Y_tilde]
    {join : Y_tilde → Y_tilde → ℝ → Y_tilde}
    (hjoin_equiv : ∀ (γ : Γ) (a b : Y_tilde) (t : ℝ),
      join (γ • a) (γ • b) t = γ • join a b t)
    {f_bar F_bar : X_bar → Y_tilde}
    (hf : ∀ (γ : Γ) (x : X_bar), f_bar (γ • x) = γ • f_bar x)
    (hF : ∀ (γ : Γ) (x : X_bar), F_bar (γ • x) = γ • F_bar x)
    (t : ℝ) (γ : Γ) (x : X_bar) :
    geodesicHomotopyLift join f_bar F_bar (γ • x) t =
      γ • geodesicHomotopyLift join f_bar F_bar x t := by
  unfold geodesicHomotopyLift
  rw [hf γ x, hF γ x, hjoin_equiv γ (f_bar x) (F_bar x) t]

/-- **Quotient Geodesic Homotopy $H_s : (\Gamma \backslash \overline{X}) \times \mathbb{R} \to \Gamma \backslash \widetilde{Y}$**
(`RCD-Entropy-Degree-Skeleton.tex`, Lemma 3.1 `lem:natural-maps` (2)):
For each $t \in \mathbb{R}$, $\overline{H}_s(\cdot, t)$ descends via `equivariantQuotientMap` to the
quotient spaces $X = \Gamma \backslash \overline{X} \to Y = \Gamma \backslash \widetilde{Y}$,
providing an explicit homotopy between the descended map $f$ at $t = 0$ and the natural map $F_s$
at $t = 1$. -/
def geodesicHomotopyQuotient
    {Γ : Type*} [Group Γ] {X_bar Y_tilde : Type*}
    [MulAction Γ X_bar] [MulAction Γ Y_tilde]
    {join : Y_tilde → Y_tilde → ℝ → Y_tilde}
    (hjoin_equiv : ∀ (γ : Γ) (a b : Y_tilde) (t : ℝ),
      join (γ • a) (γ • b) t = γ • join a b t)
    (f_bar F_bar : X_bar → Y_tilde)
    (hf : ∀ (γ : Γ) (x : X_bar), f_bar (γ • x) = γ • f_bar x)
    (hF : ∀ (γ : Γ) (x : X_bar), F_bar (γ • x) = γ • F_bar x)
    (t : ℝ) :
    MulAction.orbitRel.Quotient Γ X_bar → MulAction.orbitRel.Quotient Γ Y_tilde :=
  equivariantQuotientMap (fun x => geodesicHomotopyLift join f_bar F_bar x t)
    (geodesicHomotopyLift_equivariant hjoin_equiv hf hF t)

/-- At $t = 0$, the quotient geodesic homotopy equals the descended map $f$. -/
theorem geodesicHomotopyQuotient_zero
    {Γ : Type*} [Group Γ] {X_bar Y_tilde : Type*}
    [MulAction Γ X_bar] [MulAction Γ Y_tilde]
    {join : Y_tilde → Y_tilde → ℝ → Y_tilde}
    (hzero : ∀ a b : Y_tilde, join a b 0 = a)
    (hjoin_equiv : ∀ (γ : Γ) (a b : Y_tilde) (t : ℝ),
      join (γ • a) (γ • b) t = γ • join a b t)
    (f_bar F_bar : X_bar → Y_tilde)
    (hf : ∀ (γ : Γ) (x : X_bar), f_bar (γ • x) = γ • f_bar x)
    (hF : ∀ (γ : Γ) (x : X_bar), F_bar (γ • x) = γ • F_bar x)
    (q : MulAction.orbitRel.Quotient Γ X_bar) :
    geodesicHomotopyQuotient hjoin_equiv f_bar F_bar hf hF 0 q =
      equivariantQuotientMap f_bar hf q := by
  induction q using Quotient.inductionOn with
  | h x =>
    simp [geodesicHomotopyQuotient, hzero]

/-- At $t = 1$, the quotient geodesic homotopy equals the descended natural map $F_s$. -/
theorem geodesicHomotopyQuotient_one
    {Γ : Type*} [Group Γ] {X_bar Y_tilde : Type*}
    [MulAction Γ X_bar] [MulAction Γ Y_tilde]
    {join : Y_tilde → Y_tilde → ℝ → Y_tilde}
    (hone : ∀ a b : Y_tilde, join a b 1 = b)
    (hjoin_equiv : ∀ (γ : Γ) (a b : Y_tilde) (t : ℝ),
      join (γ • a) (γ • b) t = γ • join a b t)
    (f_bar F_bar : X_bar → Y_tilde)
    (hf : ∀ (γ : Γ) (x : X_bar), f_bar (γ • x) = γ • f_bar x)
    (hF : ∀ (γ : Γ) (x : X_bar), F_bar (γ • x) = γ • F_bar x)
    (q : MulAction.orbitRel.Quotient Γ X_bar) :
    geodesicHomotopyQuotient hjoin_equiv f_bar F_bar hf hF 1 q =
      equivariantQuotientMap F_bar hF q := by
  induction q using Quotient.inductionOn with
  | h x =>
    simp [geodesicHomotopyQuotient, hone]

end EquivarianceAndGeodesicHomotopy

end RCDEntropyDegree.MetricMeasure
