;;;; unit/math.metta — hyperon UNIT-test corpus for numeric/math grounded ops.
;;;; EXTRACTED + TRANSLATED VERBATIM (not redeveloped) from
;;;;   hyperon-experimental/lib/src/metta/runner/stdlib/math.rs  (test mod, lines 447-740)
;;;; Method: each `run_program("PROG")` + `assert_eq!(.., Ok(vec![vec![EXPECTED]]))` becomes
;;;;   one self-checking directive. expr! → MeTTa surface: "X"→symbol X, bare x→$x (variable),
;;;;   {Number::Integer n}→n (Int), {Number::Float f}→f (Float) — numeric TYPE preserved exactly.
;;;;   Bool(true)→True, Bool(false)→False. GROUND expected → (assertEqual …).
;;;;   assertAlphaEqual is NOT in Minimal (only assertEqual / assertEqualToResult /
;;;;   assertAlphaEqualToResult); all math expecteds here are GROUND → assertEqual throughout.
;;;;
;;;; NOTE ON Int/Float COERCION (the point of this module): several Float-producing ops are
;;;;   asserted to return an INTEGER literal in upstream (e.g. (sqrt-math 4) → 2 not 2.0,
;;;;   (cos-math 0) → 1 not 1.0). A known Minimal coercion bug rides on this distinction, so the
;;;;   exact Rust literal (with/without decimal point) is copied verbatim — DO NOT normalize.
;;;;   `5.5_f64.powf(2.3)` evaluates to 50.44686540422945 (shortest round-trip f64).
;;;;
;;;; EXTRACTION COMPLETENESS (counted, not silently dropped):
;;;;   math.rs test fns = 32 total.
;;;;   run_program-based (TRANSLATED here) = 16 fns:
;;;;     metta_pow_math, metta_sqrt_math, metta_abs_math, metta_log_math, metta_trunc_math,
;;;;     metta_ceil_math, metta_floor_math, metta_round_math, metta_sin_math, metta_asin_math,
;;;;     metta_cos_math, metta_acos_math, metta_tan_math, metta_atan_math, metta_isnan_math,
;;;;     metta_isinf_math.
;;;;   RESIDUE — Rust-op-direct `OpName{}.execute(...)` + assert_eq!/assert! with NO MeTTa
;;;;     program = 16 fns (NOT portable; they call the Rust grounded op directly, and several use
;;;;     `assert!(x.is_nan())` / `assert!(abs_difference < 1e-10)` which have no MeTTa-program form):
;;;;     pow_math_op, sqrt_math_op, abs_math_op, log_math_op, trunc_math_op, ceil_math_op,
;;;;     floor_math_op, round_math_op, sin_math_op, asin_math_op, cos_math_op, acos_math_op,
;;;;     tan_math_op, atan_math_op, isnan_math_op, isinf_math_op. These largely duplicate the
;;;;     MeTTa-level coverage above (same inputs/outputs) or test approximate trig via tolerance.

; ── pow-math (math.rs:452-458) ───────────────────────────────────────────────
!(assertEqual (pow-math 5 2) 25)
!(assertEqual (pow-math 5 200000000000000) (Error (pow-math 5 200000000000000) "power argument is too big, try using float value"))
!(assertEqual (pow-math 5.5 2.3) 50.44686540422945)
!(assertEqual (pow-math A 2) (Error (pow-math A 2) "pow-math expects two arguments: number (base) and number (power)"))
!(assertEqual (pow-math 2 -1) 0.5)   ; negative Integer power is VALID — Rust does base.powi(i32::try_from(n))

; ── sqrt-math (math.rs:460-465) ──────────────────────────────────────────────
!(assertEqual (sqrt-math 4) 2)
!(assertEqual (let $sqrt (sqrt-math -4) (isnan-math $sqrt)) True)
!(assertEqual (sqrt-math A) (Error (sqrt-math A) "sqrt-math expects one argument: number"))

; ── abs-math (math.rs:467-472) ───────────────────────────────────────────────
!(assertEqual (abs-math 4) 4)
!(assertEqual (abs-math -5) 5)
!(assertEqual (abs-math A) (Error (abs-math A) "abs-math expects one argument: number"))

; ── log-math (math.rs:474-479) ───────────────────────────────────────────────
!(assertEqual (log-math 2 4) 2)
!(assertEqual (let $log (log-math 0 0) (isnan-math $log)) True)
!(assertEqual (let $log (log-math 5 0) (isinf-math $log)) True)

; ── trunc-math (math.rs:481-485) ─────────────────────────────────────────────
!(assertEqual (trunc-math 2.4) 2)
!(assertEqual (trunc-math A) (Error (trunc-math A) "trunc-math expects one argument: input number"))

; ── ceil-math (math.rs:487-492) ──────────────────────────────────────────────
!(assertEqual (ceil-math 2.4) 3)
!(assertEqual (ceil-math -2.4) -2)
!(assertEqual (ceil-math A) (Error (ceil-math A) "ceil-math expects one argument: input number"))

; ── floor-math (math.rs:494-499) ─────────────────────────────────────────────
!(assertEqual (floor-math 2.4) 2)
!(assertEqual (floor-math -2.4) -3)
!(assertEqual (floor-math A) (Error (floor-math A) "floor-math expects one argument: input number"))

; ── round-math (math.rs:501-506) ─────────────────────────────────────────────
!(assertEqual (round-math 2.4) 2)
!(assertEqual (round-math -2.7) -3)
; half-integers — Rust f64::round is half-AWAY-from-zero (NOT banker's/half-even): .5 rounds outward
!(assertEqual (round-math 0.5) 1)
!(assertEqual (round-math 2.5) 3)
!(assertEqual (round-math -2.5) -3)
!(assertEqual (round-math A) (Error (round-math A) "round-math expects one argument: input number"))

; ── sin-math (math.rs:508-513) ───────────────────────────────────────────────
!(assertEqual (sin-math 0) 0)
!(assertEqual (let $sin (sin-math 1.570796327) (< (- $sin 1.0) 1e-10)) True)
!(assertEqual (sin-math A) (Error (sin-math A) "sin-math expects one argument: input number"))

; ── asin-math (math.rs:515-520) ──────────────────────────────────────────────
!(assertEqual (asin-math 0) 0)
!(assertEqual (let $sin (sin-math 1) (< (- (asin-math $sin) 1.0) 1e-10)) True)
!(assertEqual (asin-math A) (Error (asin-math A) "asin-math expects one argument: input number"))

; ── cos-math (math.rs:522-527) ───────────────────────────────────────────────
!(assertEqual (cos-math 0) 1)
!(assertEqual (let $cos (cos-math 1.570796327) (< (- $cos 0.0) 1e-10)) True)
!(assertEqual (cos-math A) (Error (cos-math A) "cos-math expects one argument: input number"))

; ── acos-math (math.rs:529-534) ──────────────────────────────────────────────
!(assertEqual (acos-math 1) 0)
!(assertEqual (let $cos (cos-math 1) (< (- (acos-math $cos) 1.0) 1e-10)) True)
!(assertEqual (acos-math A) (Error (acos-math A) "acos-math expects one argument: input number"))

; ── tan-math (math.rs:536-541) ───────────────────────────────────────────────
!(assertEqual (tan-math 0) 0)
!(assertEqual (let $tan (tan-math 0.78539816339) (< (- $tan 1.0) 1e-10)) True)
!(assertEqual (tan-math A) (Error (tan-math A) "tan-math expects one argument: input number"))

; ── atan-math (math.rs:543-548) ──────────────────────────────────────────────
!(assertEqual (atan-math 0) 0)
!(assertEqual (let $atan (atan-math 1) (< (- $atan 0.78539816339) 1e-10)) True)
!(assertEqual (atan-math A) (Error (atan-math A) "atan-math expects one argument: input number"))

; ── isnan-math (math.rs:550-555) ─────────────────────────────────────────────
!(assertEqual (isnan-math 0) False)
!(assertEqual (let $log (log-math 0 0) (isnan-math $log)) True)
!(assertEqual (isnan-math A) (Error (isnan-math A) "isnan-math expects one argument: input number"))

; ── isinf-math (math.rs:557-562) ─────────────────────────────────────────────
!(assertEqual (isinf-math 0) False)
!(assertEqual (let $log (log-math 5 0) (isinf-math $log)) True)
!(assertEqual (isinf-math A) (Error (isinf-math A) "isinf-math expects one argument: input number"))
