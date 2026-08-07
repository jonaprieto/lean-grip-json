use nom::{
    branch::alt,
    bytes::complete::{tag, take_while, take_while1, take_while_m_n},
    combinator::{opt, recognize},
    multi::fold_many0,
    sequence::{delimited, preceded, separated_pair, tuple},
    IResult,
};
use std::hint::black_box;
use std::time::Instant;

// ---------------------------------------------------------------------------
// Whitespace (JSON whitespace: 0x20, 0x09, 0x0A, 0x0D)
// ---------------------------------------------------------------------------

#[inline]
fn is_ws(b: u8) -> bool {
    matches!(b, b' ' | b'\t' | b'\n' | b'\r')
}

#[inline]
fn ws(input: &[u8]) -> IResult<&[u8], &[u8]> {
    take_while(is_ws)(input)
}

// ---------------------------------------------------------------------------
// String: strict RFC-8259
//   Each character is either:
//     - an unescaped byte >= 0x20 that is not `"` or `\`
//     - an escape: `\` followed by one of `" \ / b f n r t`
//     - a unicode escape: `\u` followed by exactly 4 hex digits
//   Reject: bytes < 0x20, unknown escapes, short \u sequences.
// ---------------------------------------------------------------------------

fn string_body(mut input: &[u8]) -> IResult<&[u8], ()> {
    loop {
        // consume a run of safe unescaped bytes (>= 0x20, not " or \)
        let (rest, _) = take_while(|b: u8| b >= 0x20 && b != b'"' && b != b'\\')(input)?;
        input = rest;

        match input.first() {
            // end of string
            Some(b'"') => return Ok((input, ())),
            // escape sequence
            Some(b'\\') => {
                let rest = &input[1..];
                match rest.first() {
                    Some(b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't') => {
                        input = &rest[1..];
                    }
                    Some(b'u') => {
                        // need exactly 4 hex digits
                        let (rest2, _) =
                            take_while_m_n(4, 4, |b: u8| b.is_ascii_hexdigit())(&rest[1..])?;
                        input = rest2;
                    }
                    _ => {
                        // unknown escape or EOF inside escape
                        return Err(nom::Err::Error(nom::error::Error::new(
                            input,
                            nom::error::ErrorKind::Tag,
                        )));
                    }
                }
            }
            // control byte < 0x20 (includes None/EOF inside string)
            _ => {
                return Err(nom::Err::Error(nom::error::Error::new(
                    input,
                    nom::error::ErrorKind::Char,
                )));
            }
        }
    }
}

/// Parses a JSON string and returns nothing (key or value body discarded).
#[inline]
fn json_string(input: &[u8]) -> IResult<&[u8], ()> {
    let (input, _) = tag(b"\"" as &[u8])(input)?;
    let (input, _) = string_body(input)?;
    let (input, _) = tag(b"\"" as &[u8])(input)?;
    Ok((input, ()))
}

// ---------------------------------------------------------------------------
// Number: strict RFC-8259
//   -? ( 0 | [1-9][0-9]* ) ( . [0-9]+ )? ( [eE] [+-]? [0-9]+ )?
//   Rejects: 00, 1., 1e, +1, lone -
// ---------------------------------------------------------------------------

fn json_number(input: &[u8]) -> IResult<&[u8], &[u8]> {
    recognize(tuple((
        // optional minus
        opt(tag(b"-" as &[u8])),
        // integer: 0 | [1-9][0-9]*
        alt((
            // exactly "0", but not "00..." (the alt tries this first)
            tag(b"0" as &[u8]),
            // [1-9] followed by zero or more digits
            recognize(tuple((
                take_while1(|b: u8| b.is_ascii_digit() && b != b'0'),
                take_while(|b: u8| b.is_ascii_digit()),
            ))),
        )),
        // optional fraction: "." [0-9]+   (rejects "1.")
        opt(recognize(tuple((
            tag(b"." as &[u8]),
            take_while1(|b: u8| b.is_ascii_digit()),
        )))),
        // optional exponent: [eE] [+-]? [0-9]+   (rejects "1e")
        opt(recognize(tuple((
            alt((tag(b"e" as &[u8]), tag(b"E" as &[u8]))),
            opt(alt((tag(b"+" as &[u8]), tag(b"-" as &[u8])))),
            take_while1(|b: u8| b.is_ascii_digit()),
        )))),
    )))(input)
}

// ---------------------------------------------------------------------------
// Value — returns leaf count
// ---------------------------------------------------------------------------

fn json_value(input: &[u8]) -> IResult<&[u8], usize> {
    let (input, _) = ws(input)?;
    alt((
        json_object,
        json_array,
        |i| {
            let (i, _) = json_string(i)?;
            Ok((i, 1usize))
        },
        |i| {
            let (i, _) = json_number(i)?;
            Ok((i, 1usize))
        },
        |i| {
            let (i, _) = tag(b"true" as &[u8])(i)?;
            Ok((i, 1usize))
        },
        |i| {
            let (i, _) = tag(b"false" as &[u8])(i)?;
            Ok((i, 1usize))
        },
        |i| {
            let (i, _) = tag(b"null" as &[u8])(i)?;
            Ok((i, 1usize))
        },
    ))(input)
}

// ---------------------------------------------------------------------------
// Object: { "key": value, ... }  — keys NOT counted
// ---------------------------------------------------------------------------

fn json_object(input: &[u8]) -> IResult<&[u8], usize> {
    let (input, _) = tag(b"{" as &[u8])(input)?;
    let (input, _) = ws(input)?;

    if input.first() == Some(&b'}') {
        return Ok((&input[1..], 0));
    }

    let (input, first) = json_kv(input)?;
    let (input, rest) = fold_many0(
        preceded(tuple((ws, tag(b"," as &[u8]), ws)), json_kv),
        || 0usize,
        |acc, c| acc + c,
    )(input)?;
    let (input, _) = ws(input)?;
    let (input, _) = tag(b"}" as &[u8])(input)?;

    Ok((input, first + rest))
}

fn json_kv(input: &[u8]) -> IResult<&[u8], usize> {
    // ws already consumed by caller before json_kv; but handle key ws too
    let (input, _) = ws(input)?;
    let (input, (_, count)) = separated_pair(
        json_string,
        delimited(ws, tag(b":" as &[u8]), ws),
        json_value,
    )(input)?;
    Ok((input, count))
}

// ---------------------------------------------------------------------------
// Array: [ value, ... ]
// ---------------------------------------------------------------------------

fn json_array(input: &[u8]) -> IResult<&[u8], usize> {
    let (input, _) = tag(b"[" as &[u8])(input)?;
    let (input, _) = ws(input)?;

    if input.first() == Some(&b']') {
        return Ok((&input[1..], 0));
    }

    let (input, first) = json_value(input)?;
    let (input, rest) = fold_many0(
        preceded(tuple((ws, tag(b"," as &[u8]))), json_value),
        || 0usize,
        |acc, c| acc + c,
    )(input)?;
    let (input, _) = ws(input)?;
    let (input, _) = tag(b"]" as &[u8])(input)?;

    Ok((input, first + rest))
}

// ---------------------------------------------------------------------------
// Top-level parse: one value, optional trailing ws, then EOF
// ---------------------------------------------------------------------------

fn parse_count(input: &[u8]) -> Result<usize, String> {
    let (remaining, count) = json_value(input).map_err(|e| format!("parse error: {:?}", e))?;
    let (remaining, _) = ws(remaining).map_err(|e| format!("ws error: {:?}", e))?;
    if !remaining.is_empty() {
        return Err(format!(
            "trailing garbage: {:?}",
            &remaining[..remaining.len().min(20)]
        ));
    }
    Ok(count)
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: nom-bench <path-to-json>");
        std::process::exit(1);
    }
    let path = &args[1];
    let basename = std::path::Path::new(path)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(path.as_str());

    let data = std::fs::read(path).unwrap_or_else(|e| {
        eprintln!("cannot read {}: {}", path, e);
        std::process::exit(1);
    });

    // Warmup + correctness gate (untimed).
    let final_count = parse_count(black_box(&data)).unwrap_or_else(|e| {
        eprintln!("parse failed: {}", e);
        std::process::exit(1);
    });

    const RUNS: usize = 20;
    let mut samples = Vec::with_capacity(RUNS);

    for _ in 0..RUNS {
        let t0 = Instant::now();
        let count = parse_count(black_box(&data)).unwrap_or_else(|e| {
            eprintln!("parse failed: {}", e);
            std::process::exit(1);
        });
        let ms = t0.elapsed().as_secs_f64() * 1000.0;
        samples.push(ms);
        black_box(count);
    }

    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let best_ms = samples[0];
    let med_ms = samples[samples.len() / 2];

    println!(
        "nom {} count={} best_ms={:.3} med_ms={:.3}",
        basename, final_count, best_ms, med_ms
    );
}
