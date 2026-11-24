# Contributing to pauli-contextuality-lab

Thanks for your interest. This is a one-person project run lean.

## Workflow

- Work goes straight to `main`. There are no pull-request gates, required checks, hooks or signing requirements, and none will be added.
- CI runs on every push and is informational: a red run is a finding to fix in a follow-up commit, never a barrier.
- Outside contributions: open an issue first (bug, feature or question form). Small fixes can be sent as a patch or fork link in the issue.

## Setup and commands

```bash
just setup   # install toolchain and dependencies
just test    # run tests
just lint    # linters and type checks, report-only
just audit   # score the repo against the Build Standard
```

Without `just`, run `bash scripts/dev.sh <setup|build|test|lint>` directly.

## Expectations

- Every behavior change comes with a test; every fixed bug gets a regression test named after its issue.
- Every number or claim in the README has a row in [CLAIMS.md](CLAIMS.md).
- Update [CHANGELOG.md](CHANGELOG.md) under Unreleased in the same commit.
- Commit messages are short and imperative (for example `fix: reject empty config`).
- Classify each finding as exactly one of bug, error, issue, problem, dilemma or conflict (definitions in [AGENTS.md](AGENTS.md)).

AI agents: read [AGENTS.md](AGENTS.md) first.
