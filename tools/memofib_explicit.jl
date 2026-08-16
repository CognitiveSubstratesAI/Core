using MeTTaCore
const IV = MeTTaCore.Eval
# Triska's assertz pattern, in MeTTa: check the store, else compute AND store.
P = raw"""
(= (fib $n) (if (< $n 2) $n (fib-memo $n)))
(= (fib-memo $n)
   (let $hit (collapse (match &self (fib-cache $n $v) $v))
     (if (== $hit ())
         (let $r (+ (fib (- $n 1)) (fib (- $n 2)))
           (let $_ (add-atom &self (fib-cache $n $r)) $r))
         (car-atom $hit))))
"""
for n in (15, 20, 25, 30)
    sp = IV.Space(); IV.load_core_stdlib!(sp); IV.load_metta!(sp, P)
    t = time_ns()
    r = try IV.load_metta!(sp, "!(fib $n)\n") catch e; "ERR " * first(sprint(showerror,e),60) end
    println("  explicit-memo fib(", n, ") = ", r, "   [", round((time_ns()-t)/1e6, digits=1), " ms]")
    flush(stdout)
end
