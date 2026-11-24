# Operations, Data Integrity, and Offsite Mirrors

`pauli-contextuality-lab` is a static scientific repository with no persistent database or backend service. Operational hygiene focuses on dataset integrity, immutable releases, and offsite archival mirrors.

## Data Checksums (`B39`)

- All witness hex masks and flat-state datasets in `data/` are hashed in `data/MANIFEST.sha256`.
- All vendored third-party components in `third_party/` are hashed in `third_party/SHA256SUMS.json`.
- Verification: `python scripts/verify_all.py` and `pytest tests/test_repo_integrity.py` verify every hash automatically.

## Offsite Repository Mirrors & Archival (`A35`)

1. **Primary remote:** `https://github.com/0thernes/pauli-contextuality-lab`
2. **Master Archive submodule mirror:** Registered as a pinned Git submodule with frozen PDF SHA-256 digests in `https://github.com/0thernes/0thernes-research-archive`.
3. **Software Heritage preservation:** Public commits and release tags are archived to `https://archive.softwareheritage.org` via Save Code Now, producing immutable ISO/IEC 18670 SWHIDs.
4. **Offline Git bundle backup:** Create a self-contained verifiable mirror anytime with:
   ```bash
   git bundle create pauli-contextuality-lab-backup.bundle --all
   git bundle verify pauli-contextuality-lab-backup.bundle
   ```
