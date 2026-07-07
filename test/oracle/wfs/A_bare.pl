% Bare Program A (no driver) — for native toplevel inspection.
:- table win/1.
win(X) :- move(X, Y), tnot(win(Y)).
move(a, b).
move(g, h).
move(f, g).
move(c, c).
move(d, e).
move(e, d).
