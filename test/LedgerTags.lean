/-! Fixture for `scripts/ledger.py --selftest`: exactly one well-formed and one malformed tag.
Not part of any build target. -/

-- OBLIGATION[stacks:0BGP,07QS][tier:C][crit:yes][prop:2.4] Lipman resolution of arithmetic surfaces
theorem well_formed_example : True := trivial

-- OBLIGATION[stacks:0BGP][tier:D] malformed: bad tier, missing crit and prop
theorem malformed_example : True := trivial
