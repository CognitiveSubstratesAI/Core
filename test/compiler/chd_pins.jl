# chd_pins.jl — GENERATED from an actual run of `workflows/compiled_head_differential.jl`
# over `test/standard/conformance`, NOT hand-transcribed. Regenerate deliberately when a
# divergence is FIXED; never to make a red run green.
#
# Each entry is (file, directive, interpreted answers, compiled answers). The gate asserts the
# divergence set is EXACTLY this: a new divergence fails, and a PINNED ONE CHANGING VALUE fails
# too — which is the half a bare count would miss.
const CHD_TOTALS = (files = 24, directives = 234, answered = 234)
const CHD_PINS = [
    ("d5_auto_types.metta",
     "(pragma! type-check auto)",
     ["()"],
     ["(())"]),
    ("g1_docs.metta",
     "(help! (some-func arg1 arg2))",
     ["()"],
     ["(())"]),
    ("g1_docs.metta",
     "(help! NoSuchAtom)",
     ["()"],
     ["(())"]),
    ("g1_docs.metta",
     "(help! SomeSymbol)",
     ["()"],
     ["(())"]),
    ("g1_docs.metta",
     "(help! some-func)",
     ["()"],
     ["(())"]),
    ("g1_docs.metta",
     "(help! some-gnd-atom)",
     ["()"],
     ["(())"]),
]
