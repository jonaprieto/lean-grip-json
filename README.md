# grip-json

[![CI](https://github.com/jonaprieto/lean-grip-json/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/lean-grip-json/actions/workflows/ci.yml)
[![Lean 4](https://img.shields.io/badge/Lean%204-library-5f5f5f)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-green)](LICENSE)

An exact, RFC-8259 JSON value parser and renderer for Lean 4, built on
[`grip`](https://github.com/jonaprieto/lean-grip). It is pure and byte-oriented: it performs no
IO and does not depend on a terminal or a JSON-specific runtime.

## Quick start

```lean
import GripJson

#eval Grip.Json.parseString "{\"answer\": 42}"
-- .ok (obj #[("answer", num 42 0)])
```

Numbers are represented exactly as a mantissa and decimal exponent; parsing never rounds through
`Float`. Strings validate UTF-8 and decode JSON escapes, including surrogate pairs. The parser
returns positioned `Grip.ParseError` values on failure.

## Install

```lean
require «grip-json» from git
  "https://github.com/jonaprieto/lean-grip-json.git" @ "v0.1.0"
```

## Build and verification

```sh
lake build GripJson GripJsonTest Examples tests demo readme conformance bench
lake exe conformance
```

The checked-in JSONTestSuite corpus gates grammar behavior. The benchmark keeps separate rows for
Grip's allocation-light validator, the Grip DOM parser, Lean's standard DOM parser, and the
cross-language reference harnesses.

## License

Apache-2.0.
