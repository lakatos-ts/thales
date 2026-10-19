import { describe, expect, test } from "vitest";
import * as fs from "node:fs";
import * as path from "node:path";
import { admittedDocument, type Emission } from "@lakatos/lemma";
import { schemaValidator } from "./helpers/schema-validator.js";

// lemma's emitter over thales's own corpus: the fixtures the envelope
// check proves, the conformance corpus, and the emission goldens the Lean
// tests under `Test/ThalesEmit/` render. The emitter's unit tests are
// lemma's; these pin what thales consumes, through lemma's barrel.

/** lemma ships its schemas beside its entry point. */
const lemmaSchemas = new URL(
  "../schemas/",
  import.meta.resolve("@lakatos/lemma"),
);

const expectValidEmission = schemaValidator(
  new URL("thales-emission.schema.json", lemmaSchemas),
  "emission",
  [new URL("tarski-estree.schema.json", lemmaSchemas)],
);

/** The emission lemma documents `file` with, as thales writes it. */
function emissionOf(file: string): Emission {
  return admittedDocument(file, new Map()).emitted.emission;
}

describe("the emission over thales's fixtures", () => {
  test.each([
    ["tests/fixtures/tracer.ts"],
    ["tests/fixtures/statements.ts"],
    ["tests/fixtures/binders.ts"],
    ["tests/fixtures/degradations.ts"],
    ["tests/fixtures/classes.ts"],
    ["tests/fixtures/class-params.ts"],
    ["tests/fixtures/module-consts.ts"],
    ["tests/fixtures/nested-class-binder.ts"],
    ["tests/fixtures/unions.ts"],
    ["tests/fixtures/optionals.ts"],
    ["tests/fixtures/defaults.ts"],
    ["tests/fixtures/ctor-defaults.ts"],
    ["tests/fixtures/instance-defaults.ts"],
    ["tests/fixtures/object-is-tagged.ts"],
    ["tests/fixtures/fields.ts"],
    ["tests/conformance/theorem/class-binder-equality-guards.ts"],
    ["tests/conformance/theorem/boolean-classes.ts"],
  ])("the emission for %s validates against the schema", (fixture) => {
    expectValidEmission(emissionOf(fixture));
  });

  test.each([
    ["tests/fixtures/tracer.ts", "tracer.emission.json"],
    ["tests/fixtures/operators.ts", "operators.emission.json"],
    ["tests/fixtures/statements.ts", "statements.emission.json"],
    ["tests/fixtures/binders.ts", "binders.emission.json"],
    ["tests/fixtures/degradations.ts", "degradations.emission.json"],
    ["tests/fixtures/classes.ts", "classes.emission.json"],
    ["tests/fixtures/class-params.ts", "class-params.emission.json"],
    ["tests/fixtures/module-consts.ts", "module-consts.emission.json"],
    [
      "tests/fixtures/nested-class-binder.ts",
      "nested-class-binder.emission.json",
    ],
    ["tests/fixtures/unions.ts", "unions.emission.json"],
    ["tests/fixtures/optionals.ts", "optionals.emission.json"],
    ["tests/fixtures/defaults.ts", "defaults.emission.json"],
    ["tests/fixtures/ctor-defaults.ts", "ctor-defaults.emission.json"],
    ["tests/fixtures/instance-defaults.ts", "instance-defaults.emission.json"],
    ["tests/fixtures/object-is-tagged.ts", "object-is-tagged.emission.json"],
    ["tests/fixtures/fields.ts", "fields.emission.json"],
    [
      "tests/conformance/theorem/class-binder-equality-guards.ts",
      "class-binder-equality-guards.emission.json",
    ],
    [
      "tests/conformance/theorem/boolean-classes.ts",
      "boolean-classes.emission.json",
    ],
  ])(
    "the pinned emission for %s is exactly what lemma emits",
    (fixture, pin) => {
      const pinned = JSON.parse(
        fs.readFileSync(`tests/fixtures/${pin}`, "utf8"),
      );
      expect(emissionOf(fixture)).toEqual(pinned);
    },
  );

  test("every stacked JSDoc block's @ensures becomes its own obligation", () => {
    const fixture = "tests/conformance/theorem/stacked-blocks.ts";
    expect(emissionOf(fixture).obligations.map((o) => o.property)).toEqual([
      "nonNegative",
      "atLeastOne",
    ]);
  });
});

/** The declarations of the store's inputs that carry no ast by design, by
 * file: each closure binds a name to a differently spelled declaration,
 * and a script would need a renaming the emitter never writes. Naming
 * each one keeps any other exception visible. */
const WITHOUT_AST: Record<string, string[]> = {
  // #570: the importer's `b` is dep's `inner`.
  "tests/conformance/theorem/aliased-export/main.ts": ["top"],
};

/** Every `.ts` the emission store is built from: acceptance criterion 1's
 * frontend half, every emitted declaration carries an ast, but for the
 * exceptions `WITHOUT_AST` names. */
function storeInputs(): string[] {
  const roots = ["tests/fixtures", "tests/conformance"];
  const out: string[] = [];
  const walk = (dir: string): void => {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      const full = path.join(dir, entry.name);
      if (entry.isDirectory()) walk(full);
      // A declaration file is never an entry: it has no runtime statements
      // at all, which is why `tsc` declines to transpile one.
      else if (entry.name.endsWith(".ts") && !entry.name.endsWith(".d.ts"))
        out.push(full);
    }
  };
  for (const root of roots) walk(root);
  return out.sort();
}

describe("every emitted declaration carries its AST", () => {
  test.each(storeInputs())("%s", (file) => {
    const without = emissionOf(file)
      .declarations.filter((d) => d.kind !== "residual" && d.ast === undefined)
      .map((d) => (d.kind === "residual" ? "" : d.name));
    expect(without).toEqual(WITHOUT_AST[file] ?? []);
  });
});
