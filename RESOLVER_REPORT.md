# RESOLVER REPORT — Formalization Phase (Attempt 11)

## Diagnosis

**Error:** `git worktree add -b worktree/chunk-0-1 .worktrees/chunk-0-1` → exit status 255

**Root cause:** Stale worktrees (11th consecutive occurrence). The previous formalization run was interrupted before it could tear down its 43 git worktrees. On retry, `git worktree add -b` fails immediately because the branches (`worktree/chunk-*`) and directories (`.worktrees/chunk-*`) already exist.

**Notable state this run:** Three worktree branches had commits ahead of the base (`chunk-2-1`: 2b61b5e, `chunk-2-10`: a6b5ebb, `chunk-infra-minkowski-embedding`: ba359b3, `chunk-infra-prime-ideals`: 5ad9ca6) — all of these commits were already merged into main (`fe48258`).

## Cleanup Performed

- Removed all 43 stale git worktrees via `git worktree remove --force`
- Deleted all 43 `worktree/*` branches via `git branch -D`
- No `.lean` source files were modified

## Post-Cleanup State

- Main worktree only: `fe48258 [main]`
- No `worktree/*` branches
- No `.worktrees/` directories
- All 43 chunks already `status: "pending"` in `dag.json`

## Phase to Resume

**`formalization`** — environment is clean for fresh worktree creation.

## ⚠️ Recurring Pattern (11th consecutive failure)

The formalization orchestrator **must** add a pre-flight cleanup guard at the very start of every run:

```bash
git worktree list --porcelain | grep 'worktree ' | grep '.worktrees' | awk '{print $2}' | xargs -I{} git worktree remove --force {} 2>/dev/null || true
git branch -l 'worktree/*' | tr -d '+ ' | xargs -I{} git branch -D {} 2>/dev/null || true
git worktree prune
```

This makes worktree setup idempotent and prevents this class of failure entirely.
