import BCG
import RCDEntropyDegree.MetricMeasure.VolumeEntropy
import RCDEntropyDegree.MetricMeasure.SturmBarycenter
import RCDEntropyDegree.RCD.StructureAndCurrents
import RCDEntropyDegree.RCD.DegreeTheory
import RCDEntropyDegree.RCD.EntropyDegreeRigidity

/-!
# Entropy-Degree Rigidity for Closed Orientable Non-Collapsed $\mathsf{RCD}(K, N)$ Spaces (`RCDEntropyDegree`)

Root module for the Lean 4 formalization of P. Suárez-Serrato,
*"Entropy-degree rigidity for non-collapsed $\mathsf{RCD}$ spaces"*, extending the
Besson–Courtois–Gallot barycenter method (`BCG`) to closed orientable non-collapsed
$\mathsf{RCD}(K, N)$ and Alexandrov spaces via:

1. Metric-measure volume entropy, Bishop–Gromov exponential volume comparison, and homothetic/covering
   scaling laws (`RCDEntropyDegree.MetricMeasure.VolumeEntropy`),
2. Sturm's renormalized $\mathsf{CAT}(0)$ $d^2$-barycenter, $\pi_1(X)$-equivariant natural maps,
   and quotient geodesic homotopies (`RCDEntropyDegree.MetricMeasure.SturmBarycenter`),
3. De Philippis–Gigli regular/singular stratification and the Cavallucci–Marti–Mondino–Perales
   (CMMP) orientation current $T \in \mathbf{I}_N(X)$ (`RCDEntropyDegree.RCD.StructureAndCurrents`),
4. Regular values, Lipschitz current pushforward degree $f_\# T = \deg(f)\llbracket Y \rrbracket$,
   and Wenger homotopy invariance (`RCDEntropyDegree.RCD.DegreeTheory`), and
5. Rectifiable approximate Jacobians, the mass-Jacobian pushforward bound, and the main
   entropy-degree inequality and isometric/smoothness rigidity theorem (`RCDEntropyDegree.RCD.EntropyDegreeRigidity`).
-/
