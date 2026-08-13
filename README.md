# grip-json

[![CI](https://github.com/jonaprieto/lean-grip-json/actions/workflows/ci.yml/badge.svg)](https://github.com/jonaprieto/lean-grip-json/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/jonaprieto/lean-grip-json?display_name=tag&sort=semver)](https://github.com/jonaprieto/lean-grip-json/releases)
[![Lean 4](https://img.shields.io/badge/Lean%204-v4.33.0-6f42c1)](lean-toolchain)
[![Docs](https://img.shields.io/badge/docs-GitHub%20Pages-4c8bf5)](https://jonaprieto.github.io/lean-grip-json/)
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
  "https://github.com/jonaprieto/lean-grip-json.git" @ "v0.1.2"
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
