# ADR 0004: Open Dual Licensing (Apache-2.0 + CC-BY-4.0) and Independent Affiliation

- **Status:** Accepted (2026-11-24)
- **Context:** Earlier repositories carried a restrictive verification-only ("All rights reserved") license and cited `0thernes LLC` before legal entity formation. This blocked Mathlib upstreaming, JOSS eligibility, and external reuse, and created an accuracy defect flagged in the Defensible Independent AI Research Playbook (Findings #1-#4).
- **Decision:** Re-license all code in the consolidated repository under `Apache-2.0` (`LICENSE`, matching Mathlib) and all manuscripts, figures, and documentation under `CC-BY-4.0` (`LICENSE-DOCS`), retaining MIT licenses for vendored `third_party/` components (`NOTICE`). Attribute all work accurately to `Alexander S. Donahue (independent researcher, ORCID 0009-0006-8168-9648)` with transparent CRediT and AI-contribution statements.
- **Consequences:** Full compatibility with Mathlib PRs, JOSS, open academic reuse, and honest provenance.
