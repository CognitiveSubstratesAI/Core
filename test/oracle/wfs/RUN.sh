#!/usr/bin/env bash
# WFS/tnot differential oracle — SWI-Prolog. Runs all 3 programs + native reporting.
set -euo pipefail
cd "$(dirname "$0")"
echo "swipl: $(swipl --version)"
echo; echo "########## A: win/move game (classifier) ##########"
swipl -q A_win_game.pl
echo; echo "########## B: p :- tnot(p) (classifier) ##########"
swipl -q B_paradox.pl
echo; echo "########## C: stratified negation (classifier) ##########"
swipl -q C_stratified.pl
echo; echo "########## Native toplevel reporting of UNDEFINED ##########"
echo "--- B: query p ---";     printf 'p.\n'      | swipl -q B_bare.pl
echo "--- A: query win(c) ---"; printf 'win(c).\n' | swipl -q A_bare.pl
echo "--- A: query win(a) TRUE ---"; printf 'win(a).\n' | swipl -q A_bare.pl
echo "--- A: query win(b) FALSE ---"; printf 'win(b).\n' | swipl -q A_bare.pl
