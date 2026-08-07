# grip as a JSONTestSuite parser

`test_grip.sh <file>` follows the JSONTestSuite protocol: exit `0` = valid,
`1` = invalid, anything else = crash. Build the binary first:

    lake build conformance

## Register in the official run_tests.py

Add this entry to the `programs` dict in a *copy* of upstream `run_tests.py`
(do not edit the upstream checkout in place):

    "grip (Lean)": {
        "url": "https://github.com/jonaprieto/lean-grip-json",
        "commands": ["/absolute/path/to/lean-grip-json/parsers/test_grip.sh"]
    }

Then run the driver as usual; grip appears as a column in `results/parsing.html`.
`test/run-jsontestsuite.sh` automates a grip-only run against a fresh clone.
