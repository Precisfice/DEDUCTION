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
:- use_module(catform).

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

% For D-dose 3+3 trial, there is a transition M0 -{Q}-> M
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

% A crucial further element of the needed dimension-reduction
% will be obtained through _summarizing_ whole sets of tallies
% generating the transitions, so that a single arrow bearing a
% concise label may be drawn between each connected state-pair.

% Our now well-developed partial order ≼ on Qᴰ could be the key
% to achieving a concise and _generalizable_ summary of tallies
% labeling each transition.  But this seems likely to require
% knowing *all* possible tallies that may arise within each
% enrolling state.  I would be looking, in particular, for
% simple conditions (in forms like '≼'(Q), etc.) that split off
% exactly the labeling set of each transition M0 --Qss--> M
% from the set of all tallies that could possibly arise in M0.

% So let's next collect all tallies arising in each enrolling state.
%?- M0 = "e2", setof(Q, d_transition(2, M0, Q, M), Qs).
%@    M0 = "e2", M = "e1", Qs = [[0/3,2/3],[0/3,2/6],[0/3,3/3],[0/3,3/6],[0/3,4/6]]
%@ ;  M0 = "e2", M = "r1", Qs = [[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]]
%@ ;  M0 = "e2", M = "r2", Qs = [[0/3,0/6],[0/3,1/6],[1/6,0/6],[1/6,1/6]].
%?- M0 = "e1", setof(Q, d_transition(2, M0, Q, M), Qs).
%@    M0 = "e1", M = "e2", Qs = [[0/3,0/0],[1/6,0/0]]
%@ ;  M0 = "e1", M = "r0", Qs = [[2/3,0/0],[2/6,0/0],[2/6,2/3],[2/6,2/6],[2/6,3/3],[2/6,3/6],[2/6,4/6],[3/3,0/0],[3/6,0/0],[3/6,2/3],[3/6,2/6],[3/6,3/3],[3/6,3/6],[3/6,4/6],[4/6,0/0]]
%@ ;  M0 = "e1", M = "r1", Qs = [[0/6,2/3],[0/6,2/6],[0/6,3/3],[0/6,3/6],[0/6,4/6],[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]].

% Can we use catform:'≼'/2 and catform:meet_/3 now?
%?- meet_([0/0,0/0], [1/1,0/1], Meet).
%@    Meet = [1/1,0/1].
%?- [1/1,0/1] '≼' [1/1,0/1].
%@    true.
% So convenient!  In the absence of formal module exports,
% we apparently gain access to all predicates in the file.
% This means I can do a lot more development in here.

%?- setof(Q, d_transition(2, "e2", Q, "r2"), Qs), reduce(meet_, Qs, M).
%@    Qs = [[0/3,0/6],[0/3,1/6],[1/6,0/6],[1/6,1/6]], M = [1/5,1/6].
%?- maplist('≼'([1/5,1/6]), [[0/3,0/6],[0/3,1/6],[1/6,0/6],[1/6,1/6]]).
%@    true.
% Accordingly, we might label the arrow e2--{↑[1/5,1/6])}-->r2.

%?- setof(Q, d_transition(2, "e2", Q, "r1"), Qs), reduce(meet_, Qs, M).
%@    Qs = [[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]], M = [1/6,4/5].
%?- maplist('≼'([1/6,4/5]), [[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]]).
%@    true.
% Thus, so long as the e2-->r2 arrow's test gets applied *first*,
% we could label e2-->r1 as  e2--{↑[1/6,4/5])}-->r1.

% ------------------------------------------------------------

% I'm getting an inkling that I haven't yet found quite the right
% way of partitioning these diagrams into what is seen and what
% gets submerged as implicit.
%
% What if I really should be depicting only the enrolling states,
% leaving the entire question of termination as implicit?

% Let's look for transition 'guards' in the form -∈↑sₖ for eScalation
% into enrolling-state k, and -∈↓rₖ for de-escalation (dose Reduction)
% from state k.
d_e(D, X, Q) :-
    #D #> 1, indomain(D),
    X in 1..D,
    #X0 #= #X - 1,
    phrase(format_("e~d", [X0]), M0),
    phrase(format_("e~d", [X]), M),
    phrase(format_("r~d", [X]), R),
    setof(Qx, (   d_transition(D, M0, Qx, M)
              ;   d_transition(D, M0, Qx, R)
             ), Qxs),
    reduce(meet_, Qxs, Q).

%?- d_e(2, 2, S2).
%@    S2 = [1/5,0/0].
%?- d_e(2, 1, S1).
%@    false. % As expected, since we declared no "e0" state to start from.
%              (This special case may require trial-and-error exploration.)

d_r(D, X, Q) :-
    #D #> 1, indomain(D),
    X in 1..D,
    #X_ #= #X - 1,
    phrase(format_("e~d", [X]), M),
    phrase(format_("e~d", [X_]), M_),
    phrase(format_("r~d", [X_]), R),
    setof(Qx, (   d_transition(D, M, Qx, M_)
              ;   d_transition(D, M, Qx, R)
             ), Qxs),
    reduce(join_, Qxs, Q).

%?- d_r(2, 2, R2).
%@    R2 = [0/4,2/6].
%?- d_r(2, 1, R1).
%@    R1 = [2/6,0/2].
