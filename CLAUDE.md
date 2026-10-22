# CLAUDE.md

Thales is a proof tool: the `thales` executable (`lake build thales`). It runs `@lakatos/lemma` (the TypeScript front end, pinned in `package.json`) as a subprocess, renders each file's emission as plain Lean 4, runs Lean on it, and prints one SZS verdict per `@ensures` annotation as a JSON envelope. The same package holds the JS semantics (`Js/`) and an evaluator over them (`Tarski/`, the `tarski` and `tarski-test262` executables).

- `Thales/` — the tool: admit lemma's documents, mirror, render + run each artifact, join verdicts, print the envelope. Start at `Thales/Prove.lean` and `Thales/Cli.lean`.
- `ThalesDsl/` — what artifacts import: `#thales_prove` (the tactic ladder) and `#thales_validate` (model correspondence). Start at `ThalesDsl/Prove.lean`.
- `ThalesEmit/` — the renderer: lemma's emission JSON → a readable `.lean` artifact, in process. Start at `ThalesEmit/Render.lean`.
- `Js/` — the JS semantics: `JsM`, `JsVal`, `JsString`, binary64 ops and theory, the `js_norm` simp set. Start at `Js/Runtime.lean`.
- `Tarski/` — a definitional interpreter whose primitives are `Js`'s, plus the test262 runner. Start at `Tarski/Eval.lean`'s header.

Every module opens with a header doc explaining its design; read it before editing the module. `CONTEXT.md` holds the engine's vocabulary. Annotation parsing, discovery, and the emitter itself (tsc AST → per-declaration JSON) are lemma's; this repo starts from its JSON documents.

Docs under `docs/adr/`, `docs/specs/`, `docs/beyond-typescript.md`, and `CHANGELOG.md` describe a removed whole-file compiler (TH-code diagnostics, refinement types). Trust the code over them.

Issues: GitHub (`docs/agents/issue-tracker.md`, `docs/agents/triage-labels.md`).

## Commands

```bash
npm ci                           # first: installs the pinned lemma the Lean tests parse with
lake build                       # everything
lake build Test                  # every Lean test
timeout 600 lake env lean Test/ThalesDsl/BindersTest.lean   # one test file
npx vitest run                   # TS suites; bin suites skip without LAKATOS_PROVE_E2E=1
LAKATOS_PROVE_E2E=1 npx vitest run tests/e2e.test.ts
LAKATOS_TARSKI_E2E=1 npx vitest run tests/tarski --no-file-parallelism
npm run check:verdict-channel    # verdict-line contract over tests/fixtures/*.lean
npm run check:envelopes          # envelopes vs tests/fixtures/envelopes.expected.json
UPDATE_ENVELOPES=1 LAKATOS_PROVE_E2E=1 npm run check:envelopes   # regenerate (full manifest only)
sh scripts/check-boundary.sh && sh scripts/check-imports.sh
```

- **Always wrap `lake env lean` in a `timeout`**: a bad artifact can grind indefinitely.
- **After changing `ThalesDsl` or `ThalesEmit`, run `lake build thales`.** A run's own `lake build` builds only the default target, so the binary would stay stale.
- Run the binary from a project directory (where `tsconfig.json` is): `timeout 600 .../.lake/build/bin/thales <file.ts>`. `LAKATOS_LEMMA=<built lemma checkout>` runs an unreleased lemma instead of the pin.
- The check scripts go through the real binary (`scripts/harness.js`), never a copy of its logic.

## Contracts

### Pipeline

`Thales.prove` is admit → mirror (`.lakatos/<UTC time>/thales/`) → render + `lake env lean` per artifact → join → print. Exit 2 for a refused run, input error, engine `Error`, unhealthy join, or interruption; 1 when the worst verdict is `CounterSatisfiable`; 0 otherwise.

- **Interruption is child death only.** A child exiting 130/143/129 that thales didn't kill reports `User`. Thales installs no signal handler.
- **Failure containment over abortion.** An unhandled construct degrades that declaration, annotation, or artifact, never the run; healthy verdicts still ship.
- Annotations lemma already classified (`InputError`, `Inappropriate`, `NotTried`) never reach Lean; the join adds them from lemma's document.

### Emitter invariants (lemma emits, `ThalesEmit` renders)

- Anything that can settle an annotation's fate is settled in lemma, before Lean. Classified annotations never reach Lean.
- **Classification travels**: a use of a failed declaration reports that declaration's reason. Registries are keyed by module and name together.
- **A body degrades only at its first out-of-slice statement.** An unmodelable _expression_ becomes a residual site (`noncomputable opaque` in `JsM`, refusal text as docstring), and everything reaching one is tainted `noncomputable`. Writes and formulas never residualize.
- **Rendering is `TSyntax` quotations only**, never string concatenation (the one override is `ThalesEmit/Format.lean`). Each obligation is parsed back and checked against the IR (`ThalesEmit/RoundTrip.lean`).
- **Names never collide by construction**: models under `TsModel`, dependency paths as a guillemet component, binders that clash with artifact vocabulary are primed.
- **Truthiness has no model**: conditions and `!`/`&&`/`||` operands must be boolean-shaped.
- **The `ast` field is the bridge's output, never authored by the emitter**; a closure that won't close carries no field.
- Artifacts pin `set_option autoImplicit false`.
- **A new emission shape adds a syntax guard in `Test/ThalesEmit/RenderTest.lean`, not a golden.** The `*.emitted.lean.expected` goldens are readability pins only.

### Verdict and model channels

- Each `#thales_prove` prints **exactly one** `thales-verdict:` line, even on failure; each `#thales_validate` prints exactly one `thales-model:` line. Only sentinel-framed stdout lines are contract. An empty `reason` is a contract violation.
- Missing, duplicate, surplus, or unrepresentable lines make the run unhealthy (exit 2).
- `Error` means the engine broke; `Inappropriate` means outside the model. A rung blowing `maxRecDepth` falls through to the next rung.
- **An unvalidated model never moves a verdict.**
- Budgets: `LAKATOS_PROVE_HEARTBEATS`, `LAKATOS_PROVE_VALIDATE_HEARTBEATS` (0 is ignored). The e2e suites and the corpus slices set the validate budget to 1 to stay fast.
- `tests/verdict-contract.test.ts` checks each `Szs` constructor (`ThalesDsl/Verdict.lean`) goes on the wire under its own name.

## Semantics and evaluator (`Js/`, `Tarski/`)

- **Boundary rule:** nothing under `Js/` or `Tarski/` imports `ThalesDsl`, `ThalesEmit`, or `Thales`, or mentions emission. `scripts/check-imports.sh` enforces it.
- **Computability is the invariant** in `Js/`: `decide` must evaluate models over bounded domains. Float ops are built from `Float.Model`, never `extern`. `Float.toString` is never called.
- **Arithmetic boundary:** under `Tarski/`, `Float.`-namespace calls and method-syntax Float ops are banned (`scripts/check-boundary.sh`); use the infix spellings or `Js` definitions. This is why `NativeFn` constructors are prefixed (`mathAbs`) and some are guillemet-quoted.
- **A string is a `JsString`** (UTF-16 code units, `List UInt16`), not a Lean `String`. Property keys are still Lean `String`s via the lossy `JsString.toKey` (#519).
- **`tarski_eval` membership** (`Tarski/Simp.lean`): recursion on syntax is a member; recursion on loops or lists (`evalWhile`, `evalFor`, `callBound`, …) is never a member and is unfolded with `rw`; recursion on the heap joins as a guarded simproc. `Test/Tarski/SimpSetTest.lean` pins it. `callNative` is too large for equation lemmas, which is why native groups are split out (`callReflectNative`, `callStringNative`, …).
- **The realm is at fixed heap references** (`Tarski/Realm.lean`, pinned by `Test/Tarski/RealmTest.lean`). Adding an intrinsic means appending refs and updating the test.
- The messages the evaluator raises are one table in `Tarski/Eval.lean`'s header; reuse one rather than inventing a new one.
- `Test/Tarski/fixtures/*.json` are copies of lemma's parser output; regenerate with `node node_modules/@lakatos/lemma/dist/cli.js parse <f.js>` when the bridge changes. CI runs `tarski` on each.
- Test location follows ownership: a `ThalesDsl` import under `Test/Js/` is a boundary violation.

### test262

The PR-gated slice is `test262/slice.txt`, scored against `test262/expected.json`; every failure is hand-classified in `test262/failures.md`. **To ratchet:** run `.lake/build/bin/tarski-test262 --slice-file test262/slice.txt --write test262/expected.json`, reclassify what moved in `failures.md`, and commit both (`tests/tarski/test262-failures.test.ts` checks the sums). Strict mode only. `results.md` is linked by URL from outside this repo, so don't rename it.

## Conventions

- `autoImplicit` is off; bind implicit and universe variables explicitly.
- `package.json` pins the exact lemma release that `Tarski/Lemma.lean`'s `version` names; bump the two together.
- Shell scripts are outside every typecheck: run `sh -n` after editing one.
