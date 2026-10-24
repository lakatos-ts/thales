import Tarski.Test262.Frontmatter

open Tarski.Test262

/-- A test file around a front-matter body, as the suite writes one. -/
def wrap (body : String) : String :=
  s!"// Copyright (C) 2026\n/*---\n{body}---*/\nvar x = 1;\n"

-- reads a flow list
#guard (parseFrontMatter (wrap "includes: [propertyHelper.js, compareArray.js]\n")).includes ==
  #["propertyHelper.js", "compareArray.js"]
-- reads a flow list written without spaces
#guard (parseFrontMatter (wrap "includes: [a.js,b.js]\n")).includes == #["a.js", "b.js"]
-- reads a block list
#guard (parseFrontMatter (wrap "includes:\n  - a.js\n  - b.js\nflags: [onlyStrict]\n")).includes ==
  #["a.js", "b.js"]
#guard (parseFrontMatter (wrap "includes:\n  - a.js\n  - b.js\nflags: [onlyStrict]\n")).flags ==
  #["onlyStrict"]
-- reads the negative map
#guard (parseFrontMatter (wrap "negative:\n  phase: parse\n  type: SyntaxError\n")).negative ==
  some { phase := "parse", type := "SyntaxError" }
-- has no negative when the block is absent
#guard (parseFrontMatter (wrap "flags: [async]\n")).negative == none
-- stops a block list at the first line that is not an item
#guard (parseFrontMatter (wrap "includes:\n  - a.js\n  note: not an item\n  - b.js\nflags: [async]\n")).includes ==
  #["a.js"]
#guard (parseFrontMatter (wrap "includes:\n  - a.js\n  note: not an item\n  - b.js\nflags: [async]\n")).flags ==
  #["async"]
-- ignores a negative block missing the phase
#guard (parseFrontMatter (wrap "negative:\n  type: SyntaxError\n")).negative == none
-- ignores a line under negative that is not an entry
#guard (parseFrontMatter (wrap "negative:\n  - phase\n  phase: parse\n  type: SyntaxError\n")).negative ==
  some { phase := "parse", type := "SyntaxError" }
-- ignores a negative block missing a key
#guard (parseFrontMatter (wrap "negative:\n  phase: parse\n")).negative == none
-- skips block scalars, even one holding something that looks like a key
#guard (parseFrontMatter (wrap "description: >\n  A description that wraps\n  onto a second line\ninfo: |\n  flags: [raw]\n  includes: [nope.js]\nincludes: [real.js]\n")).includes ==
  #["real.js"]
#guard (parseFrontMatter (wrap "description: >\n  A description that wraps\n  onto a second line\ninfo: |\n  flags: [raw]\n  includes: [nope.js]\nincludes: [real.js]\n")).flags ==
  #[]
-- drops a trailing comment
#guard (parseFrontMatter (wrap "flags: [async] # not run here\nincludes:\n  - a.js # helper\n")).flags == #["async"]
#guard (parseFrontMatter (wrap "flags: [async] # not run here\nincludes:\n  - a.js # helper\n")).includes == #["a.js"]
-- reads an empty flow list as empty
#guard (parseFrontMatter (wrap "flags: []\n")).flags == #[]
-- answers empty for a file with no front matter
#guard parseFrontMatter "var x = 1;\n" == {}
-- answers empty for an unterminated block
#guard parseFrontMatter "/*---\nflags: [async]\n" == {}
-- reads only the three keys; `features` is one of the ones it does not
#guard parseFrontMatter (wrap "esid: sec-assert\ndescription: a test\nauthor: someone\nfeatures: [Symbol]\nincludes: [a.js]\n") ==
  { includes := #["a.js"] }

-- The regular expressions' own edges: a CRLF line is no key with a value,
-- `\s` is wider than ASCII, and a later key wins.
#guard (parseFrontMatter (wrap "flags: [raw]\r\nincludes: [a.js]\n")).flags == #[]
#guard (parseFrontMatter (wrap "includes:\n  - a.js\n")).includes == #["a.js"]
#guard (parseFrontMatter (wrap "flags: [raw]\nflags: [async]\n")).flags == #["async"]
#guard trim "  a b \t\r\n" == "a b"
