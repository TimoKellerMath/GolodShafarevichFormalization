# Audit (LEAN-PLAN.md P29)

Adversarial review of the formalization as of milestone M9.  Regenerate the numbers with `lake exe axioms` and `scripts/ledger.py`.

## 1. Critical path

Re-derived from the proofs of Theorem 3.18 and Corollaries 3.19–3.24 as written in the draft of
2026-09-09.  The closure is the one recorded in LEAN-PLAN.md §2; nothing has moved.  Off the
critical path, as predicted: 2.15, 2.30, 2.31, 3.5, 3.6, 3.7, 3.8, 3.9.  Of these, 2.30 (its
second half, the torsor of lifts), 2.31 and 3.8 are formalized anyway (`Profinite/FieldEmbedding`,
`Profinite/LiftDescent`, `LinearAlgebra/Telescope`); 2.15, 3.5, 3.6, 3.7, 3.9 are not.  Also
formalized beside the path: the square-class half of 2.16 and the function-field content of 3.1
(`Arithmetic/BranchClasses`, `Arithmetic/MultiquadraticCover`), and 2.6/2.7 in their
étale-algebra form (`Arithmetic/UnramifiedZ`).

The formal critical path is exactly: M1 (`b_lt_quarter_sq`) → M7
(`ObstructionSituation.hG2_lt_quarter_sq`) → 2.29 (`ComparisonSituation.finrank_H2_le`, composed
in `PaperSetup.finrank_H2_lt_quarter_sq`) → M2 (`exists_tower`) → `exists_level_tower` →
`theorem_3_18` → `theorem_1_1`, `theorem_1_2`, `theorem_1_3`.  Theorem 2.33 is a hypothesis of
every theorem from M2 onwards (`GolodShafarevichHypothesis`), by decision.

## 2. The assumed statements

Every assumed statement is a field of one of the records/classes below (or the one `sorry` in
`Arithmetic/UnramifiedZ.lean`) and carries an `OBLIGATION` tag; `LEDGER.md` is the authoritative list.
For each, the review asked (a) is it cited, (b) is the Lean statement recognizably the citation,
(c) is it strictly weaker than any conclusion of the paper.

| Record / class | Fields | Review |
|---|---|---|
| `OddLocalSituation N` | 3.11 (three counts), 2.18 (two), 2.19 (three), 2.27 (two), 2.25 | (a) yes. (b) The fields are the *specializations* of 2.18/2.19/2.25/2.27 to the situation of 3.12, with the constructible-sheaf ranks `r ≤ 2, 3` already substituted; the general statements are not formalized. (c) yes: the paper's 3.12 (`42N, 120N, 162N`) is *derived* from them. |
| `DyadicLocalSituation g m` | 3.13 (`n₂ = 2^(m-1)-1`, `h ≤ 5n₂+4g+4`), 3.14 (`s ≤ 2g`), 3.15 (two), 2.25 | (a) yes. (b) yes, in the numerical form the paper states them. (c) yes: `h²_G ≤ 5 (2^(m-1) - 1) + 14g + 4` (the paper's rounded `10gm + 14g + 4` a fortiori) is derived. The count `n₂ ≤ 2gm` is *discharged* from `Combinatorics.dyadic_component_le`. |
| `GoodLocusSituation g t` | 2.21 (two), 2.22 (Leray) | (b) the Leray field is the three-term filtration bound with `h⁰(U, R²) = 1` and `R¹ ≅ 𝔽₂^{2g}` substituted (2.24 and the monodromy argument of 3.3 are inside it). (c) yes: `(2g+1)(t+2)` is derived. |
| `GenericOverlapSituation g p` | 2.23 | (b) the Kummer/Picard exact sequence with `Pic(C)[2] ≅ 𝔽₂^{2g}` substituted; `dim K_p^×/K_p^{×2}` is *computed* (`finrank_squareClassGroup_padic`), not assumed. (c) yes. |
| `ObstructionSituation g m` | 2.26 (excision) | (b) 2.26 is the inequality (2), not the exact sequence. (c) yes: 3.17's bound `h²_G(T) ≤ b'(g, m) ≤ b(g, m)` and `h²_G(T) < g²/4` for `m ≥ 10529` are derived. |
| `ComparisonSituation Γ h2` | 2.29 (two): `e_transition`, `e_eq_zero` | (a) yes. (b) They are the two facts the paper's proof establishes about the edge maps `e_M : H²(H_M, 𝔽₂) → H²_G(T)` of the bar spectral sequence: compatibility under inflation (descent along the kernel torsor, Stacks `03AG`, `03RV`, `025P`) and that a class in `ker e_M` — the image of the transgression, represented by a torsor — dies at a deeper admissible level. The edge maps `e`, the space `V = H²_G(T)` and `N₀ = ker(Π → G)` are data; `finrank_V` identifies `dim V` with the numeric record's `h²_G(T)`. The levels are the open normal `U ≤ N₀`, exactly the paper's `M ⊇ L`. (c) yes: the injection in dimensions `dim H²_cts(Γ, 𝔽₂) ≤ h²_G(T)` and the finite-dimensionality of `H²_cts(Γ, 𝔽₂)` are *derived* (`finrank_H2_le`, `finite_H2`) from TauCeti's degree-two descent and the compatibility of inflation with the finite-level transitions; the injectivity half of the colimit is not needed. |
| `PaperSetup m` | 3.1 (four), 3.16, 2.3, 2.5 (two), 3.4 (six), 2.7 (two), 2.17 | (a) yes. (b) These are the propositions the proof of 3.18 invokes, packaged per level; `realHom_*` is Proposition 3.4 together with 2.5 (base change to the regular model) and 2.4 (resolution). `Γ` is assumed profinite (instance fields, not obligations). The former fields `finiteH2` (3.17) and `dimH2_eq` (2.29) are now theorems, from the `cmp : ComparisonSituation` field. (c) **the point to watch**: the record asserts, for *every* geometric finite quotient, a regular projective surface with the listed properties. That is not a conclusion of the paper (3.18 needs the *tower* and its orders, which come from M2), but it is the whole of Sections 3.2 and 3.6's geometry. Non-vacuity of the record type is not proved; see §3. |
| `PaperConstruction` | `IsProjective`, `IsGaloisCover` (opaque), `setup` | The two predicates occur in the *statements* of Theorems 1.1/1.2 and Corollaries 3.19/3.20. Everything else in those statements is Mathlib vocabulary. |
| `ConductorData P`, `ConductorOracle` | 3.24 (good reduction outside Σ), 3.23 (`a_p ≤ 2(1+B_p)g`), data | (b) yes, the two inputs the proof of 3.24 uses. (c) yes: 3.24 is derived. |
| `UnramifiedZ.lean` | 2.6 (`stacks:0BVH`: unit discriminant; `stacks:02GH,025P,0357`: a finite étale `ℤ`-algebra is a product of rings of integers of number fields, each étale over `ℤ`) | the two `sorry`s; (b) yes: the second is the scheme-theoretic reduction of the paper's proof (connected components, étale over normal is normal, normal and finite over `ℤ` is `𝓞_K`); (c) yes: `finite_etale_over_int` (`A ≃ₐ[ℤ] ℤ^d`) and `card_ringHom_int_eq` (exactly `d` sections, Proposition 2.7) are derived. |

### 2.1 Ledger, grouped by paper numbering

| Paper | Count | Tags |
|---|---|---|
| 2.3 | 1 | `stacks:0BX5,0BX6` |
| 2.5 | 3 | `stacks:0BGP,025N,0567,0357`, `stacks:0BGP,025N`, `stacks:02GH` |
| 2.6 | 2 | `stacks:0BVH`, `stacks:02GH,025P,0357` |
| 2.7 | 2 | `stacks:02GH` |
| 2.17 | 1 | `stacks:0C1A,0C1B` |
| 2.18 | 2 | `stacks:03QP,03RQ` |
| 2.19 | 3 | `stacks:03RY,03S2` |
| 2.21 | 2 | `stacks:03PK,03P8`, `stacks:03Q9,03Q5` |
| 2.22 | 1 | `stacks:03QC,095T,0EYU` |
| 2.23 | 1 | `stacks:03PK,03RN,04GE` |
| 2.25 | 2 | `stacks:095T,03QO,03QQ` |
| 2.26 | 1 | `stacks:08GS,09YQ` |
| 2.27 | 2 | `stacks:015J,04GK,03QO` |
| 2.29 | 3 | `stacks:03AG,03RV,025P`, `stacks:03AG,03RV` |
| 3.1 | 5 | `paper:3.1`, `stacks:0BQ8`, `stacks:0C1B,0BXX` |
| 3.4 | 6 | `paper:3.4`, `stacks:02GH,02GW`, `stacks:0BN0,0BQ8` |
| 3.11 | 3 | `paper:3.11` |
| 3.13 | 4 | `paper:3.13`, `stacks:0A3J,0A3L,03OY,02UU` |
| 3.14 | 1 | `stacks:0AG0,04GK,0BSD` |
| 3.15 | 2 | `stacks:03SI,015J` |
| 3.16 | 2 | `stacks:01W7,0B44,0B3I`, `paper:3.16` |
| 3.17 | 1 | `paper:3.17` |
| 3.23 | 1 | `stacks:0CDN,0CDB,0BMB` |
| 3.24 | 2 | `stacks:095T,0EYU`, `lit:Serre-LocalFields-IV-VI` |

Counts include the discharged entries (3.13, 3.17 and one of 2.29).

## 3. Vacuity and consistency

* The situation records of `Oracle/EtaleCohomology.lean` are hypotheses, not axioms.  Each is
  inhabited (all dimension functions zero, counts zero, `dimH2 = 0`), so they cannot be a source
  of inconsistency; their content is entirely that the paper's models satisfy them.
* `PaperSetup m` is a hypothesis too.  Its record type contains no field of the form `False` and
  no two fields that contradict each other on inspection: the only equations between numbers
  are `card_L₀`, `rank_L₀`, `dimH2_eq`, `realHom_finrank`, `genus_L₀`, `genus_formula`, and
  they are mutually consistent for the paper's values (`|H| = 2^g`, `d(H) = g`, degrees the
  indices).  A genuine inhabitant would require the schemes of Section 3; none is exhibited.
  Thirty minutes of trying to derive `False` from the record produced nothing.
* `ComparisonSituation Γ h2` is a hypothesis as well, and a genuine constraint on `Γ` (it
  implies `dim H²_cts(Γ, 𝔽₂) ≤ h2`); it is consistent (for trivial `Γ` take `V = 𝔽₂^{h2}`,
  `e = 0`: every level is `⊤` and `H²(1, 𝔽₂) = 0`).
* No global `axiom` is declared anywhere (`lake exe axioms`: every declaration uses only
  `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` in exactly five declarations of
  `UnramifiedZ.lean`, all downstream of its two ledgered `sorry`s `isUnit_discr_of_etale` and
  `exists_algEquiv_pi_ringOfIntegers`).

## 4. Statement-level faithfulness

* Theorems 1.1 and 1.2 are stated with Mathlib's `Scheme`, `IsIntegral`, `IsProper`, `Flat`,
  `IsFinite`, `Etale`, `Scheme.Hom.finrank`, `pullback`, `∐`, and the definitions
  `IsRegularScheme` (regular local rings at all points) and `IsArithmeticSurface` (fibres of Krull
  dimension one — the paper asks for *pure* dimension one, which is stronger).  The two opaque
  predicates are the only oracle notions in the statements.
* "π₁ is infinite" is stated as the tower (LEAN-PLAN.md §3.3); `π₁^ét` of a scheme is not
  defined.
* Theorem 1.2 and Corollaries 3.20/3.21 are stated on regular models: the genus is the
  interface's `genus` of the generic fibre and the rational points of `Cₙ` are the sections of
  `Sₙ → Spec ℤ` (Proposition 2.3).
* Theorem 1.3 is stated for the interface's conductor function.

## 5. Known gaps (beyond the ledger)

1. Theorem 2.33 is the named hypothesis `GolodShafarevichHypothesis` (user decision, M3 skipped).
2. P15 (Proposition 2.16 / 3.1) is complete on the square-class side: parity core, squares in
   `k(x)(√F)`, kernel `{∅, ℬ}` of the branch map, the `2g` count, and Proposition 3.1's
   independence of the `uᵢ` with the degree `2^g` (`Arithmetic/BranchClasses.lean`,
   `Arithmetic/MultiquadraticCover.lean`).  What remains is Tier C and lives in the interface:
   the Kummer identification of these classes with `J(C)[2]` (Stacks `03RQ`) and the
   identification of the Galois group of the *curve* cover `C₀ → C` with this field extension
   (the fields `card_L₀`, `rank_L₀`, `delta_L₀` of `PaperSetup`).
3. Proposition 2.6 is stated in full (`finite_etale_over_int`) and derived from two ledgered
   inputs; the scheme-theoretic decomposition `exists_algEquiv_pi_ringOfIntegers` is the one
   that Mathlib is furthest from (étale over normal is normal, finitely many idempotents of a
   noetherian ring).
4. Proposition 2.29: the Tier-A half is proved (`Oracle/Comparison.lean`) and wired into
   `PaperSetup`; the Tier-C half is the two fields `e_transition` and `e_eq_zero` of
   `ComparisonSituation`.  TauCeti's degree-two descent (surjectivity of inflation from finite
   levels) suffices; the injectivity half of the colimit, which TauCeti does not provide in
   degree two at the pinned revision, is not used.
5. `PaperSetup.Γ` is assumed profinite; the paper's `Π_m` is a Galois group, so this is a
   faithful strengthening of the earlier interface, not a new assumption of substance.

