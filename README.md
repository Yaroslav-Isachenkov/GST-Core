# GST Core — Mathematical Foundations of Guided Symbiosis Theory

**Author:** Yaroslav Isachenkov  
**Paper:** [GST: Coherent Core V2](https://doi.org/10.5281/zenodo.23296683) · [English PDF](docs/GST_Coherent_Core_V2_EN_Lean4_Apache2.pdf)  
**License:** [Apache-2.0](LICENSE), with [scope and third-party exclusions](LICENSING_SCOPE.txt)

This repository contains the Lean formalization of a deterministic, infinite-horizon optimal control problem with two states and a bounded scalar control. It includes 190 original source modules through `GSTStage191` (there is no Stage03), a theorem-to-source map, and evidence from the author's fresh sequential rebuild on 23 November 2026.

The sources are byte-for-byte identical to the closed Stage191 archive identified in the paper. This release reorganizes the files and adds documentation and a portable verification driver; it does not change the mathematical proofs.

## Mathematical problem

The state equations are

$$\dot\Omega=-a\Omega+c\varphi u,\qquad \dot\varphi=B-\eta\varphi u,\qquad B=bn,\qquad 0\leq u\leq U.$$

The objective is

$$J_n(u)=-\int_0^\infty e^{-\rho t}\bigl[q(\Omega(t)-\Omega_\star)^2+ru(t)^2\bigr]dt,\qquad V_n=\sup_u J_n(u).$$

The coefficients specified in Section 1 of the paper are positive; initial states and the external parameter `n` are nonnegative. Individual results have additional hypotheses. The principal results cover attainment, canonical costates and necessary conditions, conditional global sufficiency and uniqueness, zero-source decay, an exact criterion for preserving positive state/resource bounds, and strict improvement `V_n > V_0` for every `n > 0` with other data fixed.

Start with [THEOREMS.md](THEOREMS.md) for the precise declaration names and scope. The interpretation of the source as human contribution motivates the model; these mathematical results do not establish empirical validity or safety of a deployed intelligent system.

## Verification status

The included [rebuild report](evidence/rebuild_20261123/report.json) records successful compilation of all 190 modules on the author's Linux x86_64 WSL machine. The recorded `#print axioms` inventories match the original closure report and contain only subsets of `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, warnings or errors were found in those logs.

This is saved author-run evidence, not a claim of an independently reproduced build on every platform. Integrity checks can be run without Lean; a fresh Lean rebuild is a separate command. The distributed `verify.py` also completed a fresh end-to-end rebuild of all 190 modules on the same pinned WSL environment. The [portable-driver report](evidence/portable_rebuild_20261123/report.json) and its 190 logs record the run started at 20:17:23 UTC on 23 November 2026. Its source hashes, verifier hash, exit codes and axiom inventories were checked against this release and the earlier evidence. The driver and proof sources are unchanged from that successful run.

## Quick check — no Lean required

From the repository directory, using Python 3.9 or later:

```bash
python3 verify.py
```

This verifies the release manifest, all source hashes against the original manifest, and the saved report/log/axiom inventories. It does **not** compile Lean. Checksums detect changes relative to the supplied manifests; they are not digital signatures or a substitute for reviewing theorem statements.

## Fresh Lean rebuild

The supported procedure uses an **external, pinned Mathlib Lake project**. This repository deliberately retains the build method used for the author-run checks: `lake env lean` is invoked in that Mathlib checkout, while new GST artifacts go into a new isolated directory. There is no root `lakefile` and plain `lake build` in this repository is not the supported command. `environment/lake-manifest.json` is Mathlib's lockfile, not a standalone GST lockfile.

Required environment:

| Component | Pinned value |
| --- | --- |
| Lean | `leanprover/lean4:v4.28.0` |
| Lean commit | `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b` |
| Mathlib commit | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Platform checked by the driver | Linux x86_64, including WSL |
| Python | 3.9 or later, standard library only |

Install Lean/elan using the [official installation instructions](https://leanprover-community.github.io/install/project.html). For a **new** Mathlib checkout, after installing elan and making `lake` available:

```bash
elan toolchain install leanprover/lean4:v4.28.0
git clone https://github.com/leanprover-community/mathlib4.git gst-mathlib-pinned
cd gst-mathlib-pinned
git checkout --detach 8f9d9cff6bd728b17a24e163c9402775d9e6a365
lake exe cache get
```

Do not run `lake update` or change the pinned versions for this release. Dependency downloads/cache preparation require internet access and sufficient storage. Lean, Mathlib and their caches are not bundled. The repository's archived Mathlib patch is empty. The verifier checks the Mathlib commit, tracked changes and lockfiles; it does not independently rebuild or audit all Mathlib dependency caches.

Return to the GST repository. Replace the example paths below with your actual paths:

```bash
python3 verify.py --check-env --mathlib /absolute/path/to/gst-mathlib-pinned --lake /absolute/path/to/lake
python3 -u verify.py --rebuild --mathlib /absolute/path/to/gst-mathlib-pinned --lake /absolute/path/to/lake
```

For a custom elan installation, add `--elan-home /absolute/path/to/elan`. An existing prepared checkout may be used if the preflight checks pass. Elan/Lake may prepare missing toolchain/dependency components when invoked; prepare them before expecting an offline run.

Each run creates `verification/<UTC timestamp>/` with source snapshots, new `.olean` files, one log per module and a report. It does not reuse old GST build artifacts. Modules are compiled sequentially. Failures stop the run; interruption leaves the saved report and logs. Do not edit sources during verification. A new invocation starts a new full run rather than resuming old artifacts.

## Layout

| Path | Contents |
| --- | --- |
| `src/` | 190 unchanged proof modules |
| `docs/` | Unchanged English paper, editorial revision 11 October 2026 |
| `THEOREMS.md` | Paper-to-Lean declaration map and assumptions |
| `verify.py` | Integrity, saved-evidence, environment and fresh-build checks |
| `MANIFEST.json` | SHA256 and size of every distributed file except this manifest |
| `SOURCE_PROVENANCE.json` | Mapping from current source paths to original archive paths |
| `environment/` | Original Mathlib environment lockfiles and empty patch |
| `evidence/` | Original manifest, semantic coverage records, November rebuild report/logs |
| `verification/` | New local build output; excluded from Git |

Historical JSON records retain their original paths and dates. The old coverage reports refer to the Ukrainian edition; the English PDF includes its own correspondence table. These records document a semantic comparison; the Lean kernel does not verify a PDF or its interpretation. Earlier `full_core_verified=false` fields in intermediate reports describe their historical stage-local scope.

The original archive remains unchanged and is not bundled here:

`GST_Coherent_Core_V2_CLOSED_stage191_20261007T152232866335Z.zip`

SHA256: `a7410946c63104c1eee67c945791dcd58c6684a7ef743bc0e401920ceca86ff3`

The earlier November evidence ZIP supplied by the author has SHA256:
`097bf6ae294a8ce954a167da4226b70d8accdb2f8763bf99c8bcb7b19596282c`.

The subsequent portable-driver evidence ZIP has SHA256:
`3b98332fcf1209d70cea8d913c00e3f68ad95e28a832b88163aa237c8776cb20`.

The default integrity check verifies the earlier report semantically and covers the added portable-driver evidence through the release manifest. The latter evidence was also cross-checked during final packaging; a fresh build generates its own checked report.

## Research context and citation

- [The Theory of Guided Symbiosis: A New Paradigm for Human Evolution in the Age of Superintelligence](https://doi.org/10.5281/zenodo.17195102) — conceptual origins.
- [Earlier mathematical core, 10 September 2026](https://doi.org/10.5281/zenodo.22704652).
- [GST: Coherent Core V2](https://doi.org/10.5281/zenodo.23296683) — the mathematical paper corresponding to this release.

Please cite the paper and specify the repository commit used for a reproduction. Citation is requested, not an additional Apache-2.0 condition. Lean, Mathlib and third-party dependencies retain their own licenses.
