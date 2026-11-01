# Prototype: std++ `Pmap` as a wrapper around the standard library's `Trie`

Branch `trie-pmap` on master `14c0bc5`. `Trie.v` is the rocq-stdlib port of
rocq/rocq#17044 (JasonGross/rocq-stdlib, branch `fable/emaps-trie`, commit
`5b5b6e3`), vendored here under `stdpp_trie/` with the logical name `Trie.Trie`
only because the released Rocq 9.2 standard library does not have it yet.

## Feature comparison (std++ `Pmap` vs `Trie`)

| | std++ `Pmap` (master) | `Trie` |
|---|---|---|
| representation | `Pmap_ne` with `PNode001..PNode111`, `Pmap := PEmpty \| PNodes` | `branch` with `Node001..Node111`, `trie A := option (branch A)` |
| canonical / Leibniz-extensional | yes (`Pmap_eq`) | yes (`extensionality`) |
| nested positivity (`Inductive t := T : Pmap t → t`) | yes | yes (`option` of an inductive) |
| lookup | `Pmap_ne_lookup` (fix) | `get` (CPS form over `get'`) |
| insert / delete | one `partial_alter` traversal | `set`, `remove` (two traversals for `partial_alter`) |
| fmap / omap | own | `map_filter` |
| merge | own, needs `diag_None` | `combine` (law needs `f None None = None`) |
| fold | structural `map_fold` (`map_fold_fmap_ind` law) | `keys`/`values`/`to_list` and the `FMapInterface` fold through `elements`; no structural fold with the std++ law |
| decidable equality, countable | yes | derivable (same inductive) |
| `simpl`-inert on `∅` | by construction (`match` on the map first) | not by itself; the wrapper matches on the map first |

So `Trie` is the same data structure; it can replace `Pmap` with a thin
wrapper. It cannot replace `gmap`: `gmap_dep_ne A P` carries a key-validity
predicate in its type, which `Trie` does not have, and `gmap` does not use
`Pmap` except for the conversion functions `gmap_to_pmap`/`pmap_to_gmap`.

## The wrapper

`Pmap_ne := branch`, `Pmap A := trie A`, `PEmpty`/`PNodes` are `None`/`Some`
(only-parsing notations), the seven constructors are notations; `lookup`,
`partial_alter`, `fmap`, `omap`, `merge` are `get`, `set`/`remove`,
`map_filter`, `combine (diag_None f)`; `map_fold` is std++'s structural fold
on the shared type. The `FinMap` instance is proved from the `Trie` lemmas.

## What changed for users of std++

- `Pmap A` is `option (Pmap_ne A)`: `destruct m as [|t]` now names the `Some`
  case first (one such `destruct` in `gmap.v`); `Pmap` had to be
  `Typeclasses Opaque`, otherwise `m1 ∪ m2` picked `option_union`.
- `Pmap_ne` lookup is `Trie.get'`; `simpl` exposes it in a goal but not in an
  induction hypothesis (two proofs in `gmap.v` needed `unfold lookup,
  Pmap_ne_lookup in *`).
- `partial_alter` does two traversals instead of one.
- All 28 std++ test outputs are unchanged, including `Fail progress simpl`
  on concrete maps, the `reflexivity` tests on 500/1000-element maps and the
  128000-element `vm_compute` tests.

## Downstream

coq-sail, rocq-linux-process-semantics core (199 files, with the same
`check_eq` edits as for the bitvector port), casemate, iris (145 files of
`iris/`) and `iris_heap_lang` (32 files) build unchanged against this branch.

## Speed (master vs this branch, same machine)

`reflexivity` on `pmap_insert_positives 1 1 500 = ..._rev 500 1 500`: 0.138 s vs
0.075 s; the 1000 version: 0.50 s vs 0.16 s. `vm_compute` on 16000-element maps:
insert-and-compare 0.004 s both; union 0.057 s vs 0.035 s; filter 0.10 s vs
0.034 s; `map_fold` 0.049 s vs 0.050 s; lookup 0.14 s vs 0.15 s. Nothing is
slower.
