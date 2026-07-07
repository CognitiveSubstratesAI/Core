# WFS `tnot` differential oracle — SWI-Prolog 9.0.4

Ground-truth for `Core/test/standard/test_tnot_wfs.jl`. Each program uses `:- table` + `tnot/1`;
run with `swipl -q <file>.pl`. Values (true / false / **undefined**) are the well-founded semantics
answers Core's tabled `tnot` must reproduce.

- `A_win_game.pl` — win/move game: WON=true, LOST=false, DRAW-cycle=undefined (self-classifying via `call_delays/2`).
- `A_bare.pl` — same moves; `printf 'win(c).\n' | swipl -q A_bare.pl` prints the `% WFS residual program`.
- `B_paradox.pl` / `B_bare.pl` — `p :- tnot(p).` ⇒ p undefined.
- `C_stratified.pl` — reachable/unreachable; MUST be strictly 2-valued (no negative cycle ⇒ no undefined).
- `RUN.sh` — runs all three and prints the classification table.
