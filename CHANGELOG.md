# Changelog

## 0.1.8 — 2026-10-24

- Refresh Grip to v0.4.1, in both Lake projects. Proofs that unfolded `seqR`, `seqL` or `map2`
  rewrite with Grip's new `seqR_run`, `seqL_run` and `map2_run`.
- An unpaired surrogate escape decodes to U+FFFD instead of being dropped, decoding to NUL, or
  being merged into the next `\u` escape (`"\uD834\u0041"` used to lose the `A`).
- Move the library's `#guard` checks to the test library, so importing `GripJson` no longer
  elaborates them, and drop the test library's copy of Grip's own guards.
- Prove the `escEnd`, `scanStr` and `bodyFwd` bounds lemmas by functional induction; statements
  and axioms are unchanged.
- Correct the parser docstrings and the README install snippet.
- The property suite builds without warnings and follows the declaration layout.

## 0.1.7 — 2026-09-09

- Refresh Grip and document the contribution policy and package problem.

## 0.1.6 — 2026-09-08

- Support Lean v4.33.1 and refresh Grip to v0.3.5.
- Update the Mathlib-backed property suite to v4.33.1.
- Clarify AI-assisted development.

## 0.1.5 — 2026-08-13

- Document OATP as a related consumer.

## 0.1.4 — 2026-08-13

- Add the standard review guidance to the README.
- Pin the newest released Grip dependency in both Lake projects.

## 0.1.3 — 2026-08-13

- Adopt precommit-lean v0.1.6.

## 0.1.2 — 2026-08-12

- Adopt Lean v4.33.0 and precommit-lean v0.1.5.

## 0.1.1 — 2026-08-12

- Move to grip v0.3.0, whose `GParser` carries a `fwit` failure-position proof. The four
  parser literals here and `oscBody` in the properties package supply it.
- Add `escEnd_le`, `scanStr_err`, and `bodyFwd_err`, the bounds needed to discharge those
  proofs. `scanStr_err` bounds a failure below by the opening quote rather than the current
  scan position, since a body that fails UTF-8 validation is reported back at the quote.
- No change to the parser's behavior: the JSONTestSuite conformance figures and the axiom
  set of `GripProps.Container.parse_render` are unchanged.

## 0.1.0 — 2026-08-07

- Extract the RFC-8259 JSON value parser, renderer, conformance corpus, and benchmark from Grip.
