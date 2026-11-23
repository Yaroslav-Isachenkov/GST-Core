# Packaging checks — 23 November 2026

## Inputs and unchanged content

- Original Stage191 ZIP SHA256: `a7410946c63104c1eee67c945791dcd58c6684a7ef743bc0e401920ceca86ff3`.
- Author's November rebuild ZIP SHA256: `097bf6ae294a8ce954a167da4226b70d8accdb2f8763bf99c8bcb7b19596282c`.
- All 926 entries in the original payload manifest were checked.
- All 190 release source files match the original archive and November rebuild snapshots byte-for-byte.
- The English PDF matches the supplied Apache-2.0 publication package byte-for-byte.
- The Apache LICENSE text is copied unchanged from that package.
- No old compiled GST artifacts or dependency caches are shipped in this repository package.

## Saved evidence

The November author-run report and 190 logs were checked for unique, complete module coverage, successful recorded exit codes, matching source/log hashes, matching pinned environment and agreement with the closure report's axiom inventory. Recorded axiom dependencies are subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, warnings or errors were found in the logs.

This validates the supplied evidence. Packaging did not perform a new Lean compilation or an independent semantic audit of every theorem.

## Portable verifier checks

`python3 verify.py` passed on the assembled release. The following 10 deliberate corruptions were rejected in isolated test copies or parser inputs:

1. `sorryAx` in a log.
2. A warning in a log.
3. Missing axiom output.
4. An unexpected axiom.
5. Duplicate axiom output.
6. A changed source file.
7. An incomplete saved report.
8. A missing module record.
9. A failed recorded compiler exit.
10. An axiom mismatch between report and log.

The complete 190-module driver control flow was exercised with simulated compiler output. That test checks orchestration only and is **not** a Lean rebuild. The author subsequently completed the actual end-to-end portable-driver rebuild on the pinned WSL environment (run `20261123T201723064244Z`): all 190 modules passed. The supplied report and logs are included in `evidence/portable_rebuild_20261123/`. The verifier is byte-for-byte identical to the one used in that run; its SHA256 is `a49079b39c8585ce999a04efa35a2abea6eda5fc46fca3860d86e12aed91f2b3`. All 190 source hashes, log hashes, recorded successful exits, and axiom inventories were cross-checked. No `sorryAx`, warnings or errors were found. The earlier successful November rebuild used the inline predecessor.

All declaration names linked in THEOREMS.md were found in the recorded axiom inventories and corresponding source files. Local Markdown links were checked.

`SOURCE_PROVENANCE.json` is preserved from the initial extraction, so its `fresh_build_performed: false` describes that extraction step. The later successful build is documented separately in `evidence/rebuild_20261123/report.json`. `EDITORIAL_CHECKS.txt` records the earlier PDF editorial work, not this packaging action.

## Finalization

The final package adds the portable-driver report and logs, updates README and this checklist, and regenerates the release manifest. All previously distributed proof sources, PDF, license and verifier bytes are unchanged. The author-run evidence archive SHA256 is `3b98332fcf1209d70cea8d913c00e3f68ad95e28a832b88163aa237c8776cb20`. No additional Lean compilation was performed during packaging.
