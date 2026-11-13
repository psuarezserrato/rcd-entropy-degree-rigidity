# Entropy-Degree Rigidity for Closed Orientable Non-Collapsed $\mathsf{RCD}(K, N)$ and Alexandrov Spaces (Lean 4)

Machine-checked Lean 4 (`leanprover/lean4:v4.35.0`) formalization accompanying:

> **P. Suárez-Serrato**, *"Entropy-degree rigidity for non-collapsed $\mathsf{RCD}$ spaces"* (2026).

This repository extends the Besson–Courtois–Gallot barycenter method formalized in [`formalized-barycenter-methods`](https://github.com/psuarezserrato/formalized-barycenter-methods) (`BCG`) to closed orientable non-collapsed $\mathsf{RCD}(K, N)$ metric-measure spaces and closed orientable $N$-dimensional Alexandrov spaces without boundary.

---

## Verification Summary

- **Toolchain:** `leanprover/lean4:v4.35.0` (Mathlib `v4.35.0`)
- **Upstream Dependency:** [`BCG`](https://github.com/psuarezserrato/formalized-barycenter-methods)
- **Modules & Scale:** 6 library modules (`RCDEntropyDegree`), 1,971 lines of Lean code, 109 tracked blueprint declarations
- **Kernel & Axiom Audit:** **`0` `sorryAx`**, **`0` custom axioms** (standard Lean axioms only: `propext`, `Classical.choice`, `Quot.sound`)
- **Blueprint DAG:** 21 nodes (`blueprint/dep_graph.dot`) — **100% green** (15 `#1CAC78` proved theorem nodes, 6 `#B0ECA3` definition nodes), `0` `plasTeX` errors
- **Executive Audit Report:** [`report/rcd_entropy_degree_report.pdf`](report/rcd_entropy_degree_report.pdf) (5 pages, `0` LaTeX errors, `0` overfull boxes)

---

## Module Overview (`RCDEntropyDegree`)

| Module | Mathematical Contents & Principal Declarations |
| :--- | :--- |
| [`RCDEntropyDegree.lean`](RCDEntropyDegree.lean) | Root aggregator importing `BCG` and all five submodules |
| [`RCDEntropyDegree/MetricMeasure/VolumeEntropy.lean`](RCDEntropyDegree/MetricMeasure/VolumeEntropy.lean) | Metric-measure volume entropy `ballVolumeLogRate`, Bishop–Gromov exponential growth bounds, $\pi_1$-equivariant normalized weights, homothetic invariance, finite-cover reduction `finite_cover_entropy_degree_reduction` |
| [`RCDEntropyDegree/MetricMeasure/SturmBarycenter.lean`](RCDEntropyDegree/MetricMeasure/SturmBarycenter.lean) | Sturm's renormalized $\mathsf{CAT}(0)$ $d^2$-barycenter functional, `sturm_variance_inequality`, unique minimizer, $\pi_1$-equivariant natural maps, geodesic homotopy descent (`geodesicHomotopyQuotient`) |
| [`RCDEntropyDegree/RCD/StructureAndCurrents.lean`](RCDEntropyDegree/RCD/StructureAndCurrents.lean) | De Philippis–Gigli regular/singular stratification (`NonCollapsedRCDStructure`), Alexandrov specialization `AlexandrovSpaceWithoutBoundary`, and Cavallucci–Marti–Mondino–Perales (CMMP) orientation currents `CMMPOrientationCurrent` |
| [`RCDEntropyDegree/RCD/DegreeTheory.lean`](RCDEntropyDegree/RCD/DegreeTheory.lean) | Regular-value locus $V_f = Y \setminus f(\mathcal{S}(X))$, Lipschitz current pushforward degree `LipschitzDegreePushforward`, Wenger homotopy invariance, degree surjectivity, Mitsuishi homological index divisibility |
| [`RCDEntropyDegree/RCD/EntropyDegreeRigidity.lean`](RCDEntropyDegree/RCD/EntropyDegreeRigidity.lean) | Pointwise entropy-Jacobian bound `rcd_approximate_jacobian_bound`, Theorem 1.1 Part 1 (`rcd_entropy_degree_inequality`, `rcd_rankOne_entropy_degree_theorem`, `alexandrov_entropy_degree_inequality`, `rcd_homological_index_entropy_inequality`), and Theorem 1.1 Part 2 (`ae_jacobian_eq_one_of_normalized_equality`, `rcd_entropy_degree_equality_rigidity`) |

---

## Blueprint, Print PDF, and Executive Report

- **Interactive Dependency Graph:** [`blueprint/web/dep_graph_document.html`](blueprint/web/dep_graph_document.html) (rendered HTML & inline SVG from [`blueprint/src/content.tex`](blueprint/src/content.tex))
- **Blueprint Print PDF:** [`blueprint/print/print.pdf`](blueprint/print/print.pdf)
- **Executive Audit Report:** [`report/rcd_entropy_degree_report.pdf`](report/rcd_entropy_degree_report.pdf)
- **Architectural Boundary:** Geometric-measure theorems not yet in Mathlib~4 (CMMP orientation currents, Kirchheim area/mass-Jacobian pushforward, Wenger flat convergence, Li–Wang Lipschitz-volume rigidity) are captured explicitly as typed structure fields/theorem hypotheses without any `axiom` declarations, while the rank-one Busemann Hessian determinant estimate is proved unconditionally via `BCG`.

---

## Reproducing the Build & Audit Locally

This repository requires access to the upstream `BCG` package ([`psuarezserrato/formalized-barycenter-methods`](https://github.com/psuarezserrato/formalized-barycenter-methods)): if both are cloned as private repositories, ensure Git credentials (SSH or HTTPS PAT) are configured before fetching dependencies. When cloned as a submodule inside `formalized-barycenter-methods`, run from this directory:

```bash
# Build all Lean modules (requires Mathlib v4.35.0 & BCG caches/access)
lake build

# Regenerate the blueprint web & PDF dependency graph
./blueprint/export_dep_graph.sh
```

Downstream geometric applications of the Alexandrov entropy-degree theorem (`arXiv:2606.30403`) live in [`alexandrov-entropy-degree-applications`](https://github.com/psuarezserrato/alexandrov-entropy-degree-applications).

## License & Citation

Licensed under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use — see [LICENSE.md](https://github.com/psuarezserrato/gromov-genus0-compactness/blob/main/LICENSE.md) for details:
This project is licensed under non-commercial use. If you wish to use this software in a commercial product, service, or enterprise environment, please contact the developer to purchase a commercial license or negotiate royalty terms.
Authored by Pablo Suárez-Serrato (November 2026).
