# WLP Verification Tool

Uses a combination of program path unrolling, WLP and predicate logic to
automatically generate test cases for verifying GCL programs. For more details,
see `report/report.tex`.

## Using the tool

This program requires the [Haskell Stack](https://haskellstack.org) to build,
run and test.

Using the functions in the `Syntax` module, you can build a `Program` that
includes assertions and assumptions, and use `wlpCheck` from the `Lib` module
to automatically test this program.

## Testing the tool

You can run the included test suite using the command `stack test`. This will
run a set of QuickCheck test cases for verification of specific components,
before testing the full program on various examples. The first set of examples
should be failures (as indicated by the line "The following programs should fail:")
and the second set of examples should be successes (as indicated by the line
"The following programs should work:").
