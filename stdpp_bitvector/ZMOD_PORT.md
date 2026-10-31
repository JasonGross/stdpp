# Port of `stdpp.bitvector` to the standard library's `Zmod`/`bits`

This branch makes `bv n` the Rocq standard library type `bits (Z.of_N n)`
(that is, `Zmod (2 ^ Z.of_N n)` from `Stdlib.Zmod`) and turns the std++
operations into aliases of, or thin wrappers around, the `Zmod` operations.
All std++ names keep their statements. Built with Rocq 9.2 and rocq-stdlib
9.1. Only `stdpp_bitvector/definitions.v` and `stdpp_bitvector/tactics.v`
changed; `tests/bitvector_definitions.ref` and `tests/bitvector_tactics.ref`
are unchanged and still match.

## The type

| std++ name | now |
|---|---|
| `bv n` | `Definition bv (n : N) : Set := bits (Z.of_N n)`. A definition, not a notation, so `Bind Scope bv_scope with bv` and instance keys stay as they were. `bv n` and `bits (Z.of_N n)` are convertible, so a `bv 64` can be passed where a `bits 64` is expected and the other way round. |
| `BV n z` (with `BvWf n z`) | `Definition BV n z {H : BvWf n z} : bv n := Zmod.of_small_Z (2 ^ Z.of_N n) z` (`simpl never`). |
| `bv_unsigned` | `Definition bv_unsigned {n} (b : bv n) : Z := Zmod.unsigned b` (`simpl never`). A wrapper, not a notation, so `@bv_unsigned n b` keeps `n : N`. |
| `bv_signed` | unchanged definition `bv_swrap n (bv_unsigned b)`; equal to `Zmod.signed b` by `bv_signed_Zmod_signed`. Kept so that `unfold bv_signed` in user tactics still gives a `bv_wrap` term that `lia` understands. |
| `bv_is_wf` | a lemma `bv_is_wf {n} (b : bv n) : BvWf n (bv_unsigned b)` instead of a record field. |
| `Z_to_bv n z` | `Zmod.of_Z (2 ^ Z.of_N n) z`. |
| `bv_swrap n z` | unchanged; equal to `Z.smodulo z (bv_modulus n)` by `bv_swrap_smodulo`. |
| `EqDecision (bv n)` | `decide (bv_unsigned b1 = bv_unsigned b2)` plus `Zmod.unsigned_inj`. |
| `Countable`, `Finite`, `Inhabited`, `bvn`, notations, number notation | unchanged. |

## Aliases (same meaning as the stdlib operation)

| std++ | stdlib | how |
|---|---|---|
| `bv_add`, `bv_sub`, `bv_opp`, `bv_mul` | `Zmod.add`, `Zmod.sub`, `Zmod.opp`, `Zmod.mul` | abbreviation |
| `bv_modu` | `Zmod.umod` (both give `x` for `x mod 0`) | abbreviation |
| `bv_rems` | `Zmod.srem` | abbreviation |
| `bv_or`, `bv_and`, `bv_xor`, `bv_not` | `Zmod.or`, `Zmod.and`, `Zmod.xor`, `Zmod.not` | abbreviation |
| `bv_0 n` | `Zmod.zero` | definition (`n` is an explicit argument) |
| `bv_shiftl x y`, `bv_shiftr x y`, `bv_ashiftr x y` | `Zmod.slu x (bv_unsigned y)`, `Zmod.sru x (bv_unsigned y)`, `Zmod.srs x (bv_unsigned y)` | definition (stdlib takes the shift amount as a `Z`) |
| `bv_zero_extend z b` | `Zmod.firstn (Z.of_N z) b` | definition (`Z.of_N`) |

The ten abbreviations (`Abbreviation bv_add := Zmod.add.` and so on) make
`bv_add x y` and `Zmod.add x y` the same term, so stdlib lemmas such as
`bits.unsigned_add` rewrite directly, `Search bv_add` finds them, and
`unfold bv_add` unfolds `Zmod.add`. The rest stay definitions: their
arguments are not just bitvectors (a width, a shift amount read through
`bv_unsigned`), so an abbreviation would need parameters and could not be
used unapplied (`Infix`, `Assoc (=) bv_shiftl`, `fmap`).

### What the abbreviations cost (all measured; see "Abbreviations" below)

- The implicit argument of an abbreviated operation is the modulus, not the
  width: `@bv_add n x y` must become `@bv_add (bv_modulus n) x y`. Neither
  downstream project writes `@bv_add`.
- They cannot be opaque: `Global Opaque bv_add` would make `Zmod.add` opaque
  for every stdlib user. They are `simpl never` instead (also a global
  setting on the `Zmod` constants, but weaker). `cbv`/`lazy`/`unfold` now go
  through them where they did not before.
- `bv n` is now `Zmod (bv_modulus n)` with `bv_modulus` marked `simpl never`,
  because `simpl`/`cbn` rewrote the hidden modulus `2 ^ Z.of_N 64` to
  `2 ^ 64` in the goal but not in a term the user typed, and
  `destruct (a + 1)` then found nothing (rocq-linux-process-semantics
  `State.v`). `rewrite bv_modulus_add` still works in goals that contain
  operations at that width.
- Their arguments have type `Zmod _`, which is bound to `Zmod_scope` only
  in files that import `Stdlib.Zmod`; in a file that imports only
  `stdpp.bitvector`, `bv_add x 5` and `bv_and (x ≪ 2) y` did not parse
  unless `bv_scope` was open. `Bind Scope bv_scope with Zmod` in
  `definitions.v` fixes that; the binding is visible to importers of
  `definitions.v` and then also applies to arguments of a plain `Zmod m`
  (where `+`, `-`, `*` mean the same, but `^` and the `0%Zmod` style
  literals of `Zmod_scope` are not available).
- The type of `bv_add x y` is `Zmod (bv_modulus n)`, not syntactically
  `bv n`; `bv_simplify` now also accepts equalities at type `Zmod _`, and
  `bv_unfold_db` treats `bv` as transparent.
- Printing: `Zmod.add a b` prints as `(a + b)%bv` (or `a + b` with
  `bv_scope` open) for anyone who imports `definitions.v`, since the std++
  notation was declared last; stdlib lemmas display with the std++ names
  (`Search bv_add` shows `bits.unsigned_add` as
  `bv_unsigned (bv_add x y) = ...`).

## Wrappers whose meaning differs from the stdlib operation

| std++ | stdlib | difference | bridge lemma |
|---|---|---|---|
| `bv_divu x y` | `Zmod.udiv` | `bv_divu x 0 = 0` (like `Z.div`); `Zmod.udiv x 0 = -1` (all ones, like SMT-LIB `bvudiv`) | `bv_divu_udiv : bv_unsigned y ≠ 0 → bv_divu x y = Zmod.udiv x y` |
| `bv_quots x y` | `Zmod.squot` | `bv_quots x 0 = 0`; `Zmod.squot x 0 = -1` | `bv_quots_squot : bv_signed y ≠ 0 → bv_quots x y = Zmod.squot x y` |
| `bv_divs`, `bv_mods` | none | floor division and modulo on signed values; stdlib only has truncating `squot`/`srem` | - |
| `bv_concat n b1 b2` | `Zmod.app` | `bv_concat` puts `b1` in the high bits and takes the result width `n` as an argument; `Zmod.app a b` puts `a` in the low bits and has type `bits (n1 + n2)` | `bv_concat_app : bv_concat n b1 b2 = Zmod.firstn (Z.of_N n) (Zmod.app b2 b1)` |
| `bv_extract s l b` | `Zmod.slice` | std++ takes start and length, stdlib takes start and end and has type `bits (pastend - start)` | `bv_extract_slice : bv_extract s l b = Zmod.firstn (Z.of_N l) (Zmod.skipn (Z.of_N s) b)` |
| `bv_sign_extend z b` | none | `Z_to_bv z (bv_signed b)` | - |
| `bv_succ`, `bv_pred`, `bv_add_Z`, `bv_sub_Z`, `bv_mul_Z`, `bool_to_bv`, `bv_to_bits`, `bv_to_little_endian`, `little_endian_to_bv`, `bv_seq` | none | unchanged, defined through `Z_to_bv` (= `Zmod.of_Z`) | - |

## Lemmas

The `_unsigned` unfolding lemmas that used to hold by conversion are now
proved from the stdlib lemmas (`Zmod.unsigned_add`, `Zmod.unsigned_sub`,
`Zmod.unsigned_opp`, `Zmod.unsigned_mul`, `Zmod.unsigned_umod`,
`Zmod.unsigned_slu`, `Zmod.unsigned_sru`, `Zmod.unsigned_srs`,
`bits.unsigned_or`, `bits.unsigned_and`, `bits.unsigned_xor`,
`Zmod.unsigned_of_Z`, `Zmod.unsigned_0`, `Zmod.unsigned_pos_bound`,
`Zmod.unsigned_inj_iff`, `Zmod.smod_unsigned`), and `bv_sub_add_opp`,
`bv_add_assoc`, `bv_mul_assoc` come from `Zmod.add_opp_r`, `Zmod.add_assoc`,
`Zmod.mul_assoc`. All other proofs are kept, adapted to rewrite with the
unfolding lemmas instead of relying on conversion. New lemmas:
`bv_wrap_modulo`, `bv_swrap_smodulo`, `bv_signed_Zmod_signed`,
`bv_signed_unsigned_wrap`, `bv_unsigned_BV` (now a real lemma),
`bv_divu_udiv`, `bv_quots_squot`, `bv_extract_slice`, `bv_concat_app`.

`definitions.v` and `tactics.v` do `From Stdlib Require Import Zmod Bits`
(Import, not Export): users do not get the `Zmod.unsigned` coercion, the
`bits` notation, or `Zmod_scope` unless they require `Stdlib.Zmod` themselves.

## Abbreviations: what was tried

Tried for each pure alias, with the std++ `.ref` tests, coq-sail and
rocq-linux-process-semantics (rlps) as the yardstick.

| name | result |
|---|---|
| `bv_add`, `bv_sub`, `bv_opp`, `bv_mul`, `bv_modu`, `bv_rems`, `bv_or`, `bv_and`, `bv_xor`, `bv_not` | abbreviations, kept (commit `f7ac58a` + `65d0583`). `.ref` outputs unchanged; coq-sail builds; rlps builds with the same source edits as before (none new). Three std++-internal fixes were needed (`Hint Transparent bv : bv_unfold_db`, `bv_simplify` on `=@{Zmod _}`, `bv n := Zmod (bv_modulus n)` with `bv_modulus` `simpl never`) plus `Bind Scope bv_scope with Zmod`. Before the `bv_modulus` change rlps broke in `State.v` (`cbn` changed the hidden modulus, `destruct (a + 1)` found nothing); before the `simpl never` and scope changes nothing in the two projects broke, but `bv_add x 5` without `bv_scope` open did. |
| `bv_unsigned` (`Abbreviation bv_unsigned := Zmod.unsigned`) | not kept; the diff is in the lead's scratch copy (`b2-bv_unsigned-abbreviation.patch`). It needs `Global Arguments Zmod.unsigned : simpl never` and the `@bv_unsigned (bv_modulus ?n) ?b` pattern in `bv_unfold`; breaks `@bv_unsigned n` (two uses in rlps `MeasureLib.v`, `FileGeometricPrefixOver.v`); `rewrite bv_modulus_0 in H` fails with "abstracting over bv_modulus 0 leads to an ill-typed term" because the modulus is also the hidden argument of `bv_unsigned b`; `rewrite <-(length_fmap bv_unsigned bs)` no longer finds its pattern; and `Zmod.unsigned x` would print as `bv_unsigned x` (the abbreviation beats the coercion) for every stdlib user who imports the file. Stopped after the fourth std++-internal proof needed a rewrite. |
| `Z_to_bv`, `bv_zero_extend`, shifts, `bv_0` | not pure aliases (`Z.of_N`, `bv_unsigned y`, explicit width); an abbreviation with parameters cannot be used unapplied (`Infix "≪" := bv_shiftl`, `Z_to_bv n <$> l`, the number notation needs `Z_to_bv` to be a constant). Not tried. |
| `bv` (`Abbreviation bv n := bits (Z.of_N n)`) | not tried: `Bind Scope bv_scope with bv`, `Inj (=) (=) (@bv_to_bvn n)` and every instance keyed on `bv n` would need the `Zmod` form, and `Set` placement could not be forced. The definition form already makes `bv 64` and `bits 64` convertible. |

Things an abbreviation keeps working: `unfold bv_add` (unfolds `Zmod.add`),
`Arguments bv_add : simpl never`, `Opaque bv_add` (both act on `Zmod.add`
globally), `Search`/`About` (`About bv_add` shows `Notation bv_add :=
@Zmod.add`), `Infix "+" := bv_add`, the typeclass hint keys.
Things it does not: `@bv_add n` (the implicit is the modulus),
`b.(bv_unsigned)` (an abbreviation of a non-projection in `t.(f)` syntax
raises an anomaly `Uncaught exception Not_found` in Rocq 9.2; of a primitive
projection it works), record-syntax in general.

## Reducing breakage: what was tried

| breakage | fix | status |
|---|---|---|
| `destruct b as [z Hwf]` / `induction b` on a `bv` | `bv_rect`, `bv_rec`, `bv_ind` eliminators built from `bv_BV_unsigned : BV n (bv_unsigned b) (bv_is_wf b) = b`; `destruct b as [z Hwf] using bv_rect` gives the old shape | in `definitions.v` (commit `7e11d46`). For proofs only: a *definition* that matches on `BV` does not compute through `bv_rect` (the equality is opaque); such a definition must use `bv_unsigned b` instead, which is what the match meant. Neither downstream project matches on `BV` in a definition (0 hits for `match ... BV`, `Program`, `Equations`). |
| `vm_compute` output prints `Zmod.mk 18446744073709551616 8 I` | number notation also maps `ZmodDef.Zmod.mk`, printing only | in `definitions.v` (commit `7e11d46`); `Eval vm_compute in Z_to_bv 64 8` prints `8%bv` again. Side effect: a `Zmod.mk` of any modulus prints with `%bv` for importers. Ltac matching `@BV _ _ _` on normalized terms still misses; a user Ltac must also match `Zmod.mk _ _ _` (rlps `StepTac.v`, `WalkTac.v`, `AsanNodesAux.v` have such matches; they did not fire in the build, so no failure). |
| `b.(bv_unsigned)`, `b.(bv_is_wf)` | none found. `bv_unsigned` cannot be a projection; an abbreviation of `Private_to_Z` would work with `t.(f)` but uses the private field, breaks `@bv_unsigned n`, and stdlib lemmas about `Zmod.unsigned` would no longer match syntactically. Neither downstream project uses the syntax. | user-side: `bv_unsigned b` |
| `firstorder using L` with `L` quantified over `bv` leaves the goal open | none in std++: it happens for any primitive record, with or without parameters (checked with a parameter-free one). Rocq bug to report; dropping primitive projections from `Zmod` would cost its efficiency. | user-side: `pose proof (L _ b)` (one site in coq-sail) |
| `split`/`constructor`/`reflexivity` on `check_syscall ... = literal` 17x slower | measured with a synthetic chain of 1500 operations: primitive projections do not matter (6.0 s vs 6.3 s with a plain record); the `if small z m then z else 0` guard plus the `Is_true` proof field cost 2.3x on a field-level equality and 3.5x on a record-level one; `Global Opaque BV` does not help (the rlps probe still did not finish in 590 s). The 17x in rlps is not reproduced by these; it stays open. `Strategy` was not tried because the slow path is `constructor`'s unification, which only respects opacity. | user-side: `repeat (apply conj \|\| apply Forall_cons \|\| apply Forall_nil); check_eq` (83 sites in rlps, then 40x faster than on std++ master) |
| `bv n` in `Set` | `Definition bv (n : N) : Set := ...` | in (commit `bde6745`) |
| `cbn` changes the hidden modulus | `bv n := Zmod (bv_modulus n)`, `bv_modulus` `simpl never` | in (commit `f7ac58a`) |

User definitions that could break were looked for in both projects
(`Fixpoint`/`Definition` matching on `BV`, `Program`, `Equations`,
`Record` fields of type `bv` in `Set`, `destruct` on a `bv`): only the `Set`
case occurred (coq-sail `MachineWord.v`, fixed in `bde6745`).

## What does not stay compatible

1. `BV` is a function, not a constructor. `match b with BV z H => ...` does
   not work; `destruct b as [z Hwf] using bv_rect` does. In a definition use
   `bv_unsigned b` and `bv_is_wf b`.
2. `b.(bv_unsigned)` and `b.(bv_is_wf)` (record projection syntax) do not
   parse any more because neither is a projection. Workaround:
   `bv_unsigned b`, `bv_is_wf b`.
3. `vm_compute`, `native_compute` and `compute` normalize a closed bitvector to
   `Zmod.mk 18446744073709551616 8 I`, not to `BV 64 8 I`. It prints as
   `8%bv` (the number notation maps `Zmod.mk` for printing), but Ltac that
   matches `@BV _ _ _` on normalized terms misses it.
   `bv_simplify`/`bv_unfold` handle the `Zmod.mk` shape (`bv_unfold_mk`).
   Workaround in user Ltac: also match `Zmod.mk _ _ _`.
4. `firstorder using L` with a lemma `L` quantified over a `bv n` succeeds
   without proving anything: `firstorder` cannot instantiate a quantifier
   whose domain is a primitive record (this is a Rocq limitation; it happens
   with any `#[projections(primitive)]` record, even one without parameters).
   Workaround: `pose proof (L _ b)`, or `lia`/`firstorder (L _ b)`. Hit once in
   coq-sail (`MachineWord.v`, `word_to_bools_nth_Some`).
5. Equations that held by conversion are now lemmas: `bv_unsigned (Z_to_bv n z)`
   does not reduce to `bv_wrap n z` for symbolic `z`, `bv_unsigned (b1 + b2)` does
   not reduce to `bv_wrap n (...)`, `bv_unsigned (BV n z H)` reduces to `z` only
   when `n` and `z` are closed. Use `Z_to_bv_unsigned`, `bv_add_unsigned`,
   `bv_unsigned_BV`, etc. (`rewrite`, not `done`). None of the two downstream
   projects needed a change for this.
6. Conversely, `exact eq_refl`/`reflexivity` between two closed bitvectors
   built by different computations now succeeds where it used to fail: the
   range proofs are built with `transparent_Is_true` and reduce to `I`, while
   `BvWf` obligations were opaque. More goals are provable, no goal is lost.
7. Lazy conversion (`constructor`, `split`, `reflexivity`, `exact eq_refl`,
   `apply` with unification, `Qed` without `vm_cast`) over large closed
   bitvector computations is much slower: 17x or more (see below). The
   `vm_compute` route is as fast as before. Workaround: `vm_compute` first
   (`check_eq`-style), and do not let `split`/`constructor` close `eq` goals
   on big terms. This was the only change rocq-linux-process-semantics needed
   (83 proof scripts in 18 files, all the same mechanical edit), and those
   files then compile 40x faster than on std++ master, because that lazy
   conversion was the slow part there too.
8. `lazy`/`cbv` on terms with many literals (`3%bv`, `0xffff`) unfold `BV` into
   `Zmod.of_small_Z (2 ^ Z.of_N n) z` and recompute `2 ^ Z.of_N n` per literal
   (300 literals: 0.002 s before, 0.4 s now). `Global Opaque BV` removes this,
   but then `reflexivity` no longer proves `bv_unsigned (BV 64 3) = 3`, so `BV`
   stays transparent.
9. `bv_solve` no longer unfolds `bv_unsigned` (an internal change): `simpl`
   would rewrite the hidden modulus argument of `Zmod.unsigned` in the goal
   but not in hypotheses and `lia` would see different atoms. `bv_unsigned
   (BV n z H)` is rewritten with `bv_unsigned_BV` instead.
10. The `EqDecision` instance has a different proof term (no `Program`); it
    still computes with `vm_compute` and `cbv`.
11. The `Number Notation` declaration warns (`via-type-remapping`,
    `via-type-mismatch`) because `bv n` unfolds to `Zmod _`; the warnings are
    disabled locally. Parsing and printing of `3%bv` are unchanged.
12. With the abbreviations: `@bv_add n` is `@bv_add (bv_modulus n)`; the ten
    abbreviated operations are `simpl never` but not opaque; a user file that
    imports `definitions.v` has `bv_scope` bound to `Zmod`.

## Test results

- `make -j8` of the whole std++ clone on the `rocq-9.2` switch: ok.
- `tests/bitvector_definitions.v` and `tests/bitvector_tactics.v`: output
  identical to the `.ref` files (checked with `COQ_REF=1`, since the switch's
  `9.2+rc2` version string makes the Makefile skip ref comparison).

## Downstream results

Both projects were built with dune in a workspace that contains a copy of
std++ (master `14c0bc5` for the baseline, this branch for the port), so the
local std++ shadows the installed one. `stdpp.bitvector` had to be added to
the `(theories ...)` list of the rocq-linux-process-semantics dune files in
both workspaces (an installed std++ provides it implicitly; a workspace copy
does not).

### rems-project/coq-sail (0.20.3, `src-stdpp`, 29 files plus `MachineWordTest`)

- std++ master: builds (49 s including std++).
- port: one error, `MachineWord.v:234`, `word_to_bools_nth_Some`:
  `firstorder using bv_unsigned_in_range` leaves the goal
  `0 <= bv_unsigned w` open (item 4 above). With that line replaced by
  `pose proof (bv_unsigned_in_range _ w); Lia.lia.` everything builds,
  including the test file.

### theorem-labs/rocq-linux-process-semantics (`68ccc39`, core theory `LinuxProcessSemantics`, 200 files; `Common` and `Examples` not built)

- std++ master: builds, about 30 minutes wall clock.
- port, unchanged sources: 172 of 200 files build. The other 28 are
  `LinuxProcessSem/Checks/Cases/*` and the files that import them. They stall
  on proofs of the form `repeat split; check_eq` / `repeat constructor;
  check_eq` whose goals are equalities between a `check_syscall ...` run and
  a literal model: `split`/`constructor` proves them by `eq_refl`, i.e. lazy
  conversion of the whole run. One such element takes 33 s on master and did
  not finish in 10 minutes on the port (item 7). With the mechanical edit
  `repeat split; check_eq` -> `repeat (apply conj || apply Forall_cons ||
  apply Forall_nil); check_eq` (83 places in 18 files, so that `check_eq`'s
  `vm_compute` does the work) all 200 files build. The edited files are much
  faster than on master: `Cases/Prelude.v` 258 s -> 7 s, `Cases/Fs/ReadWrite.v`
  407 s -> 6.5 s.

## Speed

Measured on the same machine, `rocq top -batch`, std++ master vs this branch.

Tactics (`tests/bitvector_tactics.v` goals): `bv_simplify_arith` 0.019 s vs
0.018 s, `bv_solve` 0.054 s vs 0.051 s and 0.053 s vs 0.050 s,
`bv_simplify; bitblast` 0.196 s vs 0.178 s, `compute_done` on
`(-1 =@{bv 5} 31)%bv` 0.000 s both, `reduce_closed; bv_simplify` 0.003 s both,
`bv_solve` on a signed goal 0.019 s vs 0.016 s. No change.

`vm_compute` on closed chains of 20000 operations on `bv 64` (master vs port):
`x * x + 1` 5.8 s vs 5.2 s; `bv_xor (x ≪ 3) (bv_or x 5)` 0.75 s vs 2.3 s;
`bv_extract 8 64 (bv_concat 128 x (x + 1))` 3.7 s vs 3.8 s;
`x `divu` 3 + x `modu` 7 + bv_sign_extend 64 (bv_extract 0 32 (x `ashiftr` 1))`
2.6 s vs 1.7 s; `if decide (x = 3) then x + 1 else x + 2` 0.19 s vs 0.36 s;
2000 steps of `x * x + 1` on `bv 512` then `bv_to_bits` 32.6 s vs 27.8 s.
Same order of magnitude; `xor`/`or` and `decide` are 2-3x slower, the rest
is equal or faster.

Lazy conversion that must evaluate every operation (100 operations, all
definitions transparent, `exact eq_refl` of `bv_unsigned (...) = <Z value>`):
`x * 3 + 1` 0.68 s vs 0.47 s; `bv_and (x ≪ 3) 0xffff + 1` 0.06 s vs 0.15 s;
`bv_extract 4 64 (bv_zero_extend 128 x) + 7` 0.03 s vs 0.07 s;
`x `divu` 3 + x `modu` 7 + 100` 0.15 s vs 0.19 s;
`bv_sign_extend 64 (bv_extract 0 32 (x `ashiftr` 1)) + 5` 2.7 s vs 2.3 s;
`decide (x = 3)` 0.01 s vs 0.03 s. So 1-3x per operation, but the
rocq-linux-process-semantics case above (a whole syscall checker run compared
to a literal model by `eq_refl`) is 17x slower or worse (33 s -> more than
590 s per element). The cause was not pinned down; the candidates are the
`if small z m then z else 0` guard and the range proof that
`Zmod.of_small_Z` attaches to every value, which the lazy machine evaluates
again each time a value is compared or unfolded.

`cbv` (full call-by-value normalization, including proof terms) of 20 steps
of `x * x + 1`: 34 s on master, more than 540 s on the port. `cbv` on
bitvectors was already impractical.

## Recommendations

- Division by zero: std++ follows `Z.div`/`Z.quot` (`x / 0 = 0`); the stdlib
  follows SMT-LIB (`bvudiv x 0 = all ones`, `bvsdiv x 0 = -1`). Since std++
  documents these operations as the SMT-LIB ones, the cleaner end state is for
  std++ to adopt the stdlib (SMT-LIB) meaning and alias `bv_divu := Zmod.udiv`,
  `bv_quots := Zmod.squot`; until then the wrappers and `bv_divu_udiv`,
  `bv_quots_squot` bridge the two. `bv_divs`/`bv_mods` (floor division) have no
  stdlib counterpart; they can stay wrappers.
- `bv_concat`/`bv_extract`/`bv_sign_extend`: the wrappers are one-liners over
  `Zmod.of_Z`; no stdlib change is needed, though a sign extension
  (`of_Z _ (signed x)`) and a high-first concatenation would be natural stdlib
  additions.
- `firstorder` and primitive records: report upstream to Rocq; it is
  independent of std++ and the stdlib, and primitive projections are what
  make `Zmod` cheap, so the stdlib should not drop them.
- Lazy conversion speed: investigate on the stdlib side (`of_small_Z`'s guard
  and proof) with the rocq-linux-process-semantics `check_syscall` example as
  the benchmark. Users of either library should prove closed computations with
  `vm_compute` rather than `constructor`/`split`/`reflexivity`.
- `BV`, `bv_is_wf`, record syntax, `@BV _ _ _` matching on normalized terms:
  user-side edits, no library fix; the port keeps the names so the edits are
  local.
- Next steps for the port: make `bv_signed` an alias of `Zmod.signed` (needs
  the `bv_wrap_simplify` and `bv_solve` tactics to rewrite with
  `bv_signed_Zmod_signed` instead of unfolding), then consider turning the
  wrapper definitions into notations once it is decided how `bv_scope` and
  `Zmod_scope` printing should interact, and move the remaining std++ lemmas
  that have stdlib counterparts (`bits.unsigned_range`, `signed_range'`, ...)
  to aliases.

## Strategy `bits`: `bv n := bits (Z.of_N n)` with the abbreviations (branch `zmod-bitvector-bits`)

Same as `zmod-bitvector` (abbreviations for the ten pure aliases) but `bv n`
is literally `bits (Z.of_N n)`, so the hidden modulus is `2 ^ Z.of_N n` and
the type of `bv_add x y` prints as `bits (Z.of_N 64)`.

- std++ `make` and both `.ref` outputs: unchanged.
- `rewrite bits.unsigned_add` on `Zmod.unsigned (bv_add x y)`: works directly
  (the only strategy where the specialized `bits.*` lemmas rewrite without
  `unfold bv_modulus`); `rewrite Zmod.unsigned_add`: works. Under
  `bv_unsigned` (a definition) neither rewrites, as in every strategy.
- Prints: `(x + y)%bv : bits (Z.of_N 64)`; `vm_compute` gives `7%bv`.
- Downstream checks for this strategy (same workspaces and the same user-side edits as before: 1 line in coq-sail, 83 `check_eq` sites in rocq-linux-process-semantics; casemate and the sail-tiny-arm snapshot unmodified): coq-sail: builds. sail-tiny-arm: builds. casemate: fails
  (`@bv_add _64`, the implicit is the modulus). rocq-linux-process-semantics:
  fails in `LinuxProcessSem/State.v` (`cbn` turns the hidden
  `2 ^ Z.of_N 64` into `2 ^ 64` in the goal, `destruct (a + 1)` finds
  nothing). With `Global Arguments Z.of_N : simpl never` (tried, not kept)
  `State.v` passes but `Sys/Net/Socket.v` fails, where a proof needs
  `Z.of_N 64` to simplify. So the width-shaped modulus needs its own constant
  (`bv_modulus`, as on `zmod-bitvector`), or the `bv_modulus`/`2 ^ Z.of_N`
  mismatch has to be accepted.
