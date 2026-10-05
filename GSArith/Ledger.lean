/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public meta import Lean.Attributes
public import Lean.Attributes

/-!
# The obligations ledger and the `gs_public` attribute

`GSArith` formalizes the paper *modulo* an explicit list of assumed statements (results of the
Stacks Project and the literature).  This file holds the two mechanisms that keep that list
honest.

## The `@[gs_public]` attribute

Marks a theorem as a headline result.  CI (`lake exe axioms`, see `scripts/Axioms.lean`)
checks that every `gs_public` declaration depends only on the three standard axioms
`propext`, `Classical.choice`, `Quot.sound` — in particular on no `sorry`.  Oracle
*structures* are hypotheses, not axioms, so they never appear.

## The `OBLIGATION` tag grammar

Every unproved statement — a `sorry` in a real statement, or a field of an oracle class —
carries, on the line immediately above it, a comment of the form

```text
-- OBLIGATION[<source>][tier:<A|B|C>][crit:<yes|no>][prop:<paper numbering>] <description>
```

where `<source>` is exactly one of

* `stacks:<TAG>` — a Stacks Project tag, four upper-case alphanumerics; several tags may be
  comma-separated, e.g. `stacks:0BGP,07QS`;
* `lit:<reference>` — an external reference, e.g. `lit:NSW-3.9.5`;
* `paper:<numbering>` — a debt internal to the paper, e.g. `paper:2.14`.

`tier` is `A` (formalizable now, no oracle), `B` (formalizable given the cohomology
interface) or `C` (must be assumed).  `crit` records whether the statement is on the critical
path to Theorems 1.1–1.3.  `prop` is the paper's numbering of the result being assumed.  The
description is free text and must be non-empty.

A discharged obligation keeps its tag with the keyword `DISCHARGED` in place of `OBLIGATION`.

Two worked examples:

```text
-- OBLIGATION[stacks:0BGP,07QS][tier:C][crit:yes][prop:2.4] Lipman resolution of arithmetic surfaces
-- DISCHARGED[lit:NSW-3.9.5][tier:A][crit:yes][prop:2.33] H² of a free pro-2 group vanishes
```

`scripts/ledger.py` scans `GSArith/` for these tags and regenerates `LEDGER.md`; a malformed
tag fails the scan, and CI fails if `LEDGER.md` is stale.
-/

public meta section

/-- Marks a headline theorem of `GSArith`.  `lake exe axioms` verifies that every declaration
carrying this attribute depends only on `propext`, `Classical.choice` and `Quot.sound`. -/
initialize gsPublicAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `gs_public
    "headline theorem of GSArith; audited to depend only on the standard axioms"

end
