% Constructing state diagrams (as DOT files) for 3+3 protocols

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(si)).
:- use_module(library(lambda)).
:- use_module(library(pairs)).
:- use_module(library(assoc)).
:- use_module(library(time)).
:- use_module(library(format)).
:- use_module(library(debug)).
:- use_module(library(tabling)).
:- use_module(library(iso_ext)).

:- use_module(rcpearl).

clpz:monotonic.

% Translate from DCG's (list-pair) states to _state-machine_ states 'M':
dcgstate_machinestate(Ls-_, M) :- length(Ls, X), phrase(format_("e~d", [X]), M).
dcgstate_machinestate(recommend_dose(X), M) :- phrase(format_("r~d", [X]), M).

%?- dcgstate_machinestate([0/0,0/3]-[0/0], M).
%@    M = "e2".
%?- dcgstate_machinestate(recommend_dose(2), M).
%@    M = "r2".
%?- dcgstate_machinestate(S, "r2"). % (Doesn't work both ways, but needn't for now.)
%@    error('$interrupt_thrown',repl/0).

% For D-dose 3+3 trial, there is a transition M0 --Q--> M
% from state M0 to state M, labeled (induced) by tally Q.
d_transition(D, M0, Qs, M) :-
    d_path(D, Path),
    phrase((..., [S0,E,S], ...), Path),
    E \== sta, % we omit self-arrows as part of overall 'dimension reduction'
    state_tallies(S0, Qs),
    dcgstate_machinestate(S0, M0),
    dcgstate_machinestate(S, M).

%?- d_transition(2, M0, Qs, M).
%@    M0 = "e1", Qs = [0/3,0/0], M = "e2"
%@ ;  M0 = "e2", Qs = [0/3,0/6], M = "r2"
%@ ;  M0 = "e1", Qs = [0/3,0/0], M = "e2"
%@ ;  M0 = "e2", Qs = [0/3,1/6], M = "r2"
%@ ;  M0 = "e1", Qs = [0/3,0/0], M = "e2"
%@ ;  M0 = "e2", Qs = [0/3,2/6], M = "e1"
%@ ;  M0 = "e1", Qs = [0/6,2/6], M = "r1"
%@ ;  M0 = "e1", Qs = [0/3,0/0], M = "e2"
%@ ;  M0 = "e2", Qs = [0/3,2/6], M = "e1"
%@ ;  M0 = "e1", Qs = [1/6,2/6], M = "r1"
%@ ;  M0 = "e1", Qs = [0/3,0/0], M = "e2"
%@ ;  ... .
% The above is correct (as far as reviewed), but
% duplicates many state-machine arrows, of course,
% since each such arrow generally appears on _many_
% distinct paths.

% We must therefore collect _sets_ of these transitions.
%?- D=2, setof([M0, Qs, M], d_transition(D, M0, Qs, M), Txs), maplist(portray_clause, Txs).
%@ ["e1",[0/3,0/0],"e2"].
%@ ["e1",[0/6,2/3],"r1"]. % -
%@ ["e1",[0/6,2/6],"r1"].
%@ ["e1",[0/6,3/3],"r1"].
%@ ["e1",[0/6,3/6],"r1"]. % ↑
%@ ["e1",[0/6,4/6],"r1"]. % above are 5 arrows {0/6}x{2+/3,2-4/6}
%@ ["e1",[1/6,0/0],"e2"].
%@ ["e1",[1/6,2/3],"r1"]. % -
%@ ["e1",[1/6,2/6],"r1"].
%@ ["e1",[1/6,3/3],"r1"].
%@ ["e1",[1/6,3/6],"r1"]. % ↑
%@ ["e1",[1/6,4/6],"r1"]. % another 5 arrows, {1/6}x{2+/3,2-4/6}
%@ ["e1",[2/3,0/0],"r0"]. % -
%@ ["e1",[2/6,0/0],"r0"].
%@ ["e1",[2/6,2/3],"r0"].
%@ ["e1",[2/6,2/6],"r0"].
%@ ["e1",[2/6,3/3],"r0"].
%@ ["e1",[2/6,3/6],"r0"].
%@ ["e1",[2/6,4/6],"r0"].
%@ ["e1",[3/3,0/0],"r0"].
%@ ["e1",[3/6,0/0],"r0"].
%@ ["e1",[3/6,2/3],"r0"].
%@ ["e1",[3/6,2/6],"r0"].
%@ ["e1",[3/6,3/3],"r0"].
%@ ["e1",[3/6,3/6],"r0"].
%@ ["e1",[3/6,4/6],"r0"]. % ↑
%@ ["e1",[4/6,0/0],"r0"]. % 15 arrows {2+/3,2-4/6}x{0/0} U {2/6,3/6}x{2+/3,2-4/6}
%@ ["e2",[0/3,0/6],"r2"]. % \ 2 arrows ~> r2
%@ ["e2",[0/3,1/6],"r2"]. % /  {0/3}x{0/6,1/6}
%@ ["e2",[0/3,2/3],"e1"].
%@ ["e2",[0/3,2/6],"e1"].
%@ ["e2",[0/3,3/3],"e1"]. % 5 de-escalations {0/3}x{2+/3,2-4/6}
%@ ["e2",[0/3,3/6],"e1"].
%@ ["e2",[0/3,4/6],"e1"].
%@ ["e2",[1/6,0/6],"r2"]. % \ 2 more arrows ~> r2
%@ ["e2",[1/6,1/6],"r2"]. % /  {1/6}x{0/6,1/6}
%@ ["e2",[1/6,2/3],"r1"].
%@ ["e2",[1/6,2/6],"r1"].
%@ ["e2",[1/6,3/3],"r1"]. % 5 tox-outs from DL2 {1/6}x{2+/3,2-4/6}
%@ ["e2",[1/6,3/6],"r1"].
%@ ["e2",[1/6,4/6],"r1"].
%@    D = 2, Txs = [["e1",[0/3,0/0],"e2"],["e1",[0/6,2/3],"r1"],["e1",[0/6,2/6],"r1"],["e1",[0/6,3/3],"r1"],["e1",[0/6,3/6],"r1"],["e1",[0/6,4/6],"r1"],["e1",[1/6,0/0],"e2"],["e1",[1/6,2/3],"r1"],["e1",[1/6,2/6],"r1"],["e1",[1/6,3/3],"r1"],["e1",[1/6,3/6],"r1"],["e1",[1/6,4/6],"r1"],["e1",[2/3,0/0],"r0"],["e1",[2/6,0/0],"r0"],["e1",[2/6,2/3],"r0"],["e1",[2/6,2/6],"r0 ..."],["e1",[2/6,3/3],"r ..."],["e1 ...",[2/6,... / ...],"r0"],["e ...",[... / ...|...]|...],["e1"|...]|...].

% Above listing agrees with my diagram as typed out 'by hand':
% - 15 transitions to r0
% - 15 transitions to r1
% - 4 transitions to r2
% - 2 escalations {0/3,1/6}x{0/0}
% - 5 de-escalations {0/3}x{2+/3,2-4/6}

d_path(D, Path) :-
    length(Init, D), maplist(=(0/0), Init), Init = [I|Is],
    phrase(path([I]-Is), Path).

%?- d_path(2, Path).
%@    Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[0/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[1/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[0/6]-[2/6],stop,recommend_dose(1)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[1/6]-[2/6],stop,recommend_dose(1)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[2/6]-[2/6],stop,recommend_dose(0)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[3/6]-[2/6],stop,recommend_dose(0)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[3/6,0/3]-[],des,[0/6]-[3/6],stop,recommend_dose(1)]
%@ ;  ... .
