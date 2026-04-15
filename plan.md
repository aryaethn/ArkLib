# AI Optimization Plan

This document captures the initial plan for making ArkLib easier to use with:

- human contributors working with AI assistants
- AI contributors operating locally in the repo
- GitHub workflows that summarize, review, or validate changes with AI support

## Goals

- Reduce setup and navigation friction for new contributors and agentic tooling.
- Make the repo's rules easier to consume programmatically, not just by reading prose.
- Separate actionable regressions from expected background warning noise.
- Tighten the trust model around AI-triggered GitHub workflows.
- Improve task intake so humans and AI systems receive consistent change requests.

## Current Shortcomings

The initial audit identified these gaps:

1. Contributor intake is mostly free-form.
   PRs and issues do not yet have structured templates for scope, validation, generated files, or
   paper/reference impact.
2. AI guidance is present but spread across several docs.
   `AGENTS.md`, `docs/wiki/`, and script help are good, but there is no single short page aimed at
   AI-assisted contribution.
3. Bootstrap is documented but not packaged as a first-class workflow.
   A cold environment still requires contributors to know when to run `lake exe cache get`.
4. Build output contains substantial non-failing warning noise.
   This makes it harder for contributors and AI systems to identify new regressions.
5. AI GitHub workflows need clearer trust boundaries.
   The repo uses external AI workflows, but the triggering model, permissions, and safety
   assumptions should be documented and tightened.
6. Repo metadata is mostly human-readable.
   There is no small machine-readable manifest describing commands, generated paths, and repo
   constraints.
7. Some repo hygiene still leaves avoidable friction.
   Example: agent scratch files such as `.codex` are not ignored.

## Workstreams

### 1. Structured Intake

Deliverables:

- `.github/PULL_REQUEST_TEMPLATE.md`
- `.github/ISSUE_TEMPLATE/` forms for formalization, cleanup, and docs tasks
- optional `CODEOWNERS` for key review surfaces

Purpose:

- standardize task statements
- capture validation expectations up front
- expose repo-specific constraints to humans and bots

Acceptance criteria:

- every new PR records affected areas, validation run, generated-file impact, and docs/citation
  impact
- issue templates make it easy to open scoped, actionable tasks

### 2. AI Contributor Guide

Deliverables:

- `docs/wiki/ai-contributing.md`

Purpose:

- give one short path for AI-assisted work
- collect the rules that agents repeatedly need during execution

Suggested contents:

- first commands to run
- how to bootstrap a cold clone
- which paths are generated and must not be edited directly
- which validation command to use by default
- when to escalate to blueprint/citation updates
- how to distinguish existing `sorry`/warning debt from new regressions

Acceptance criteria:

- a new contributor can start from one page and reach the correct command flow without searching
  across multiple docs

### 3. Bootstrap and Validation UX

Deliverables:

- `scripts/bootstrap.sh`
- linked documentation updates in `AGENTS.md` or `docs/wiki/quickstart.md`

Purpose:

- make environment setup explicit and reproducible
- reduce hidden assumptions in local and automated workflows

Suggested behavior:

- verify toolchain presence
- run `lake exe cache get`
- print recommended next-step commands
- fail with actionable messages when prerequisites are missing

Acceptance criteria:

- cold-start setup becomes a documented one-command path
- contributors do not need to infer when dependency bootstrap is required

### 4. Warning and Signal Management

Deliverables:

- a documented warning policy
- optionally a checked-in warning baseline or scoped warning filters
- CI changes only if they improve signal without blocking active development

Purpose:

- make regressions obvious
- preserve room for ongoing formalization work with existing `sorry` blocks

Possible approaches:

- keep the current hard checks, but classify the rest of the output as advisory
- add a warning-delta check for selected linter classes
- record current known warning debt and fail only on increases in priority categories

Acceptance criteria:

- contributors can tell whether a warning is expected debt or a new problem
- PR review output highlights deltas instead of replaying the entire ambient warning stream

### 5. GitHub AI Workflow Hardening

Deliverables:

- documentation for existing AI workflows under `.github/workflows/`
- pinned action SHAs where appropriate
- a short repo policy describing who may trigger AI review and under what conditions

Purpose:

- reduce trust ambiguity
- make permissions and safety assumptions explicit

Topics to cover:

- use of `pull_request` vs `pull_request_target`
- who can trigger `/review`
- what secrets are exposed to which workflows
- how external action updates are reviewed

Acceptance criteria:

- maintainers can explain the security model of each AI-related workflow in one place
- action upgrades become deliberate rather than implicit

### 6. Machine-Readable Repo Manifest

Deliverables:

- a small root-level manifest such as `ai-context.yaml` or `repo-context.yaml`

Purpose:

- encode stable repo facts in a form that local tools, GitHub Actions, and assistants can reuse

Suggested contents:

- default validation command
- bootstrap command
- optional validation commands
- generated/derived paths
- major work areas
- docs that are canonical for style, repo map, and citations

Acceptance criteria:

- automation can discover the main repo rules without scraping multiple markdown files

### 7. Repo Hygiene for AI Tooling

Deliverables:

- `.gitignore` update for `.codex` and any other agreed agent scratch files
- optional `.editorconfig` or lightweight markdown lint config if maintainers want stricter doc
  consistency

Purpose:

- reduce noisy diffs
- avoid accidental commits from local assistant tools

Acceptance criteria:

- common assistant scratch artifacts no longer appear in routine `git status`

## Sequencing

### Phase 1: Fast, Low-Risk Wins

- add `plan.md`
- add `.gitignore` cleanup for agent scratch files
- add PR template
- add issue templates
- add `docs/wiki/ai-contributing.md`

### Phase 2: Bootstrap and Metadata

- add `scripts/bootstrap.sh`
- update quickstart docs to reference bootstrap explicitly
- add machine-readable repo manifest

### Phase 3: Warning Policy and CI Signal

- choose warning classification strategy
- prototype warning-baseline or warning-delta checks
- update CI only after the local workflow is clear

### Phase 4: AI Workflow Hardening

- document current AI workflows
- pin third-party actions
- refine trigger and permission policy

## Success Metrics

- A new AI-assisted contributor can reach a valid first build from one short doc and one bootstrap
  command.
- PRs carry enough structured context that review automation needs less manual prompting.
- Common local assistant artifacts stop appearing as untracked files.
- CI and local validation make new warning regressions easier to spot.
- Maintainers have a documented security model for AI-enabled workflows.

## Out of Scope for the First Pass

- changing the mathematical roadmap of the project
- eliminating all existing `sorry` blocks
- redesigning the full CI matrix
- replacing existing AI review workflows outright

## Immediate Next Steps

1. Land the low-risk documentation and intake improvements first.
2. Add bootstrap plus machine-readable repo metadata.
3. Decide whether warning management should use a baseline file, scoped filters, or advisory-only
   reporting.
4. Review AI GitHub workflows for permissions, triggers, and pinned versions.
