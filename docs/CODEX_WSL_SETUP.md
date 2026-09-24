# Codex setup for the Lean port

Use Codex CLI inside WSL2 in a separate Linux Git checkout. The setup below
creates a migration branch while preserving the accepted Lean 4.32.2 source and
the existing PCats dependency installations. It does not start the port.

The paths supplied by the maintainer are:

| Role | WSL path |
| --- | --- |
| Maintained source checkout | `/mnt/c/Users/fleng/Zettelkasten/Projects/FailureOfComposition` |
| Existing execution environment | `/home/flengyel/src/FailureOfComposition` |
| New isolated port checkout | `/home/flengyel/src/FailureOfComposition-port` |

Preserve the existing execution environment and its build state. Inspect its
current sync ownership before any future synchronization; a directory name alone does not establish
which source checkout owns it. The setup below does not synchronize or modify it.

## 1. Check Codex inside WSL

Run these commands in the WSL shell, not PowerShell:

```bash
command -v codex git python3 elan lean lake
codex --version
elan toolchain list
```

Use the Linux Codex executable. If Codex is missing, the official WSL
installation command is:

```bash
curl -fsSL https://chatgpt.com/codex/install.sh | sh
```

Open a new WSL shell if the installer requests it. On Ubuntu/Debian, install
`bubblewrap` if it is missing and the Codex sandbox requires it:

```bash
sudo apt install bubblewrap
```

Run `codex` and complete its interactive sign-in if it has not been configured.
Use the existing account and model selection; this repository does not set a
model, install global configuration, or store credentials. Keep Codex's normal
permission controls. Permit the task's required downloads through that workflow
if prompted; disabling the sandbox is not part of this setup.

References checked on 2026-09-24: [Codex CLI](https://learn.chatgpt.com/docs/codex/cli),
[WSL](https://learn.chatgpt.com/docs/windows/wsl), and
[sandboxing](https://learn.chatgpt.com/docs/sandboxing).
The [AGENTS.md documentation](https://learn.chatgpt.com/docs/agent-configuration/agents-md)
describes how Codex loads the repository instructions.

## 2. Create the dedicated port checkout

From the maintained Windows checkout in WSL:

```bash
cd /mnt/c/Users/fleng/Zettelkasten/Projects/FailureOfComposition
git pull --ff-only
bash scripts/setup-codex-wsl.sh
```

The helper clones `flengyel/FailureOfComposition` from `main` into
`$HOME/src/FailureOfComposition-port` and creates branch
`codex/lean-4.35.0-rc2`. It refuses an existing destination, including an empty
directory or symlink. It does not erase or repurpose any existing mirror. For
another fresh destination, pass its absolute Linux path as the sole argument.

Only the Git repository is downloaded. The helper does not install Lean, clone
Foundation or Mathlib, run Lake, build proofs, or change global settings. If a
clone fails, inspect the directory left behind and choose a fresh destination
for another attempt. Do not remove an existing directory without checking it.

The existing `/home/flengyel/src/FailureOfComposition` execution environment is
not the port checkout. Do not point `syncfailcomp.sh` at the port checkout or run
synchronization over Codex's edits. Git carries changes between the independent
checkouts.

## 3. Launch Codex

```bash
cd "$HOME/src/FailureOfComposition-port"
mkdir -p .codex-work/logs .codex-work/tmp
export TMPDIR="$PWD/.codex-work/tmp"
export LEAN_NUM_THREADS=1
export FAILCOMP_STYLE_JOBS=1
codex "Read AGENTS.md and docs/CODEX_PORT_TASK.md. Carry out the first porting milestone described there."
```

Codex reads the root `AGENTS.md` instructions. On later sessions, return to this
checkout and repeat the environment exports before starting or resuming Codex.
Use `/status` to inspect the session and `/permissions` if a required operation
is blocked. Do not start a second Lean build concurrently.

## 4. The first task and its acceptance conditions

[CODEX_PORT_TASK.md](CODEX_PORT_TASK.md) is the complete first task. It begins
with a no-Lake environment check of the accepted baseline, then ports the
development and its verifier to the recorded candidate toolchain and dependency
revisions. New dependency sources and compiled output stay inside the port
checkout's `Lean/.lake/` tree. Existing shared package checkouts are used only
for the baseline check and are not updated.

The default baseline package location is `~/src/PCats/.lake/packages`. Set
`PCATS_DST` to another PCats checkout only if that is the actual installation.
An existing `CRS_LAKE_PACKAGES` override takes precedence; Codex must record and
inspect it before deciding whether it describes the baseline or the port.
Do not reuse that baseline mapping for the newer dependency revisions.

The task includes focused source repairs and one final full verification. It
does not include redesigning the Palomar Challenge or editing the manuscript.
Completion requires passing verification with the newer toolchain, preserved
mathematical statements, and a recorded source/provenance comparison. If blocked,
Codex must report the first concrete failing obligation and retain the log.

The prompt authorizes local commits on the migration branch. It does not ask
Codex to merge or push the port to `main`. This setup commit on `main` leaves the
accepted Lean files and pins unchanged. Review the port's report and diff before
merging it. A successful port still leaves the permitted Challenge interface and
actual Palomar verification outstanding.
