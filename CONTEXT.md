# Thales vocabulary

The terms the engine's code, comments, and issues use. Older docs (`docs/adr/`, `docs/specs/`, `CHANGELOG.md`) use a removed compiler's vocabulary — refinement types, prelude library types, TH#### diagnostics — and are historical.

## Pipeline

**Emission**:
lemma's per-declaration JSON for a source file, which `ThalesEmit` renders as ordinary Lean: a `def` per function, a `#thales_prove` per obligation. It carries only declarations with a model; what lemma cannot map, it classifies instead.

**Classification**:
lemma's own verdict on an annotation it will not emit: `Inappropriate` (outside the model: an unmapped construct, a refused operator), `NotTried` (a safe-integer clamp is the sole blocker), or `Error` (the engine is at fault). A classified annotation never reaches Lean; the join adds it to the envelope.

**Failed declaration**:
A declaration the emitter could not model, recorded with the construct that stopped it. A use of it reports that same reason, so a caller of an unmapped import is `Inappropriate`, not `Error`.

**Artifact**:
The generated `.lean` file for one source file, at `<run>/thales/<source path>.lean` (`a.ts` → `a.ts.lean`). Regenerated every run, never hand-edited; a source with no annotations gets none.

**Model**:
The Lean `def` a declaration becomes, under `TsModel` and tagged `@[js_norm, grind]` so the symbolic rungs can unfold it. A class becomes a structure with a `construct` and one def per getter and method. Numbers are `Float` (binary64, what a TypeScript `number` holds) in the `JsM` monad; unions and optionals are a `JsVal`. `int`/`nat` binders quantify over the mathematical integers and coerce at the call, which is why an interval past the safe-integer range is refused: there the coercion stops being injective.

**Residual**:
The stand-in for an unmodelable expression inside an otherwise-modeled body: a per-site `noncomputable opaque` over the modeled variables in scope, valued in `JsM`, with the refusal text as its docstring. It assumes the unmodeled code is a deterministic, possibly throwing function of that scope that does not mutate it, so an expression that assigns is refused outright. Two sites are never identified. A proof that never forces a site succeeds as usual; a goal whose every failing leaf forces one is `Inappropriate`, naming the constructs. `noncomputable` is load-bearing: a valueless opaque compiles to `pure`, which compiled evaluation would prove straight through.
_Avoid_: "stub", "placeholder" (a residual asserts nothing about the value).

**JsM**:
The semantic domain of models, `Except JsError`. Its load-bearing property is computability: the decide rungs evaluate models over bounded domains, and with no binary64 theory in Lean that is often the only route to a proof.

**`ballIco`**:
The half-open-interval ∀ that binder guards elaborate to, with its own `Decidable` instance; the reason bounded properties are decidable at all.

## Verdicts

**Verdict channel**:
The stdout contract between `#thales_prove` and the tool: one `thales-verdict:`-framed compact-JSON line per annotation. Unframed stdout is Lean diagnostics and never contract.

**Model line**:
The `thales-model:` line each `#thales_validate` prints, saying whether the model was shown to agree with the evaluator (`validated`) or not, and why (`unvalidated`). It never changes a verdict.

**Identity**:
The `[file, function, property]` triple keying each annotation. Function names are qualified: `fn`, `Class#method`, `Class.method`.

**SZS statuses**:
The `Szs` inductive in `ThalesDsl/Verdict.lean`. `Theorem` (proved; `axioms` lists the non-standard axioms it rests on, empty when kernel-checked), `CounterSatisfiable` (false on the bounded domain, with a `counterexample`), `GaveUp` (the ladder ran out, including falsity with no witness to ship), `Inappropriate` (outside the model), `Error` (the engine broke), `NotTried` (no structured property), `Timeout` (the heartbeat budget ran out). The envelope adds `InputError` and `User`, which no Lean command emits.

**Verdict vs envelope entry**:
A verdict is a line Lean prints; an envelope entry is the per-annotation record after the join, which also carries lemma's classifications. Lean emits verdicts, never envelopes.

**Failure containment**:
The degradation ladder: a bad construct fails one declaration, a bad property one annotation, a bad artifact one file. Once admitted, a run completes and healthy verdicts ship; only a refused admission or a failed `lake build` ends it early.

**Structured property**:
A property expressible as a plain `Prop`: `ballIco` or `∀` binders, guards as `= pure true` hypotheses, an equation or boolean conclusion. An obligation without one verdicts `NotTried`.

**Verdict corpus**:
`tests/conformance/`: `.ts` fixtures bucketed by SZS status, where the bucket is the whole specification — every annotation in a fixture must get its bucket's status. A capability gain is a `git mv` between buckets, never an expectation edit.

**Emitter vs prover**:
The emitter is lemma's front-end pass; the prover is the Lean side (`ThalesDsl`). "Compiler" is loose usage for either.
