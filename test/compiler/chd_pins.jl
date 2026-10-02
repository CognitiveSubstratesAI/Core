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
     "(assertEqual\n   (get-doc NoSuchAtom)\n   Empty)",
     ["()"],
     ["(Error (assertEqual (get-doc NoSuchAtom) Empty) AssertionFailed)"]),
    ("g1_docs.metta",
     "(assertEqual\n   (get-doc SomeSymbol)\n   (@doc-formal (@item SomeSymbol) (@kind atom) (@type SomeType)\n               (@desc \"Test symbol atom having specific type\")))",
     ["()"],
     ["(Error (assertEqual (get-doc SomeSymbol) (@doc-formal (@item SomeSymbol) (@kind atom) (@type SomeType) (@desc Test symbol atom having specific type))) AssertionFailed)"]),
    ("g1_docs.metta",
     "(assertEqual\n   (get-doc some-func)\n   (@doc-formal (@item some-func) (@kind function)\n               (@type (-> Arg1Type Arg2Type ReturnType))\n               (@desc \"Test function\")\n               (@params (\n                        (@param (@type Arg1Type) (@desc \"First argument\"))\n                        (@param (@type Arg2Type) (@desc \"Second argument\"))))\n               (@return (@type ReturnType) (@desc \"Return value\"))))",
     ["()"],
     ["(Error (assertEqual (get-doc some-func) (@doc-formal (@item some-func) (@kind function) (@type (-> Arg1Type Arg2Type ReturnType)) (@desc Test function) (@params ((@param (@type Arg1Type) (@desc First argument)) (@param (@type Arg2Type) (@desc Second argument)))) (@return (@type ReturnType) (@desc Return value)))) AssertionFailed)"]),
    ("g1_docs.metta",
     "(assertEqual\n   (get-doc some-gnd-atom)\n   (@doc-formal (@item some-gnd-atom) (@kind function)\n               (@type %Undefined%)\n               (@desc \"Test function\")\n               (@params (\n                        (@param (@type %Undefined%) (@desc \"First argument\"))\n                        (@param (@type %Undefined%) (@desc \"Second argument\"))))\n               (@return (@type %Undefined%) (@desc \"Return value\"))))",
     ["()"],
     ["(Error (assertEqual (get-doc some-gnd-atom) (@doc-formal (@item some-gnd-atom) (@kind function) (@type %Undefined%) (@desc Test function) (@params ((@param (@type %Undefined%) (@desc First argument)) (@param (@type %Undefined%) (@desc Second argument)))) (@return (@type %Undefined%) (@desc Return value)))) AssertionFailed)"]),
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
