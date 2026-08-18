# INCIDENT: shared Mathlib checkout destroyed (2026-08-18 ~07:20)

WHAT: lake's "URL has changed → delete and re-clone" remedy fired in
the r4-wave2 worktree and deleted `.lake/packages/mathlib` — which is
the MAIN TREE's checkout (worktrees symlink the packages dir). The
re-clone then failed (github not in the sandbox allowlist). No lake
build anywhere in the repo can run until Mathlib is restored.

ROOT CAUSE (evidenced): `~/.gitconfig` became unreadable to the
sandbox at 07:15:45 (owner shows as an unmapped uid); every git run
since warns `unable to access '/home/dev/.gitconfig': Permission
denied` and some fail outright. Lake's URL-change check runs git
against the checkout; with git broken it misreads the state and
takes the delete-and-reclone remedy. NOT caused by anything in the
source tree.

CONTAINMENT (in-sandbox, verified): `export
GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1` makes git fully
functional. DO NOT run lake before Mathlib is restored — with the
override set, lake should no longer misread, but there is nothing
left for it to destroy either way.

RECOVERY (needs network — outside the sandbox):
  cd /home/dev/projects/ACL2Lean
  GIT_CONFIG_GLOBAL=/dev/null git clone \
    https://github.com/leanprover-community/mathlib4.git .lake/packages/mathlib
  GIT_CONFIG_GLOBAL=/dev/null git -C .lake/packages/mathlib \
    checkout 8f9d9cff6bd728b17a24e163c9402775d9e6a365   # lake-manifest.json pin
  lake exe cache get   # ~/.cache/mathlib (405M .ltar) is intact — fast

ALSO WORTH FIXING AT THE ROOT: whatever changed ~/.gitconfig's
ownership at 07:15:45, and exporting the two GIT_CONFIG_* vars for
all sandbox lake/git invocations permanently.

STATE AT PAUSE: wave-2d item 1 committed in the worktree (partial,
labeled); items 2-7 not started; both arcs otherwise intact and
committed; main is at ff77c89 and untouched by the incident except
the shared packages dir.
