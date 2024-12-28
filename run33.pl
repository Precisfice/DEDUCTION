% run33.pl
% Utilities for _running_ 3+3 trials defined by library(rcpearl)

:- module(run33, [
              d_init/2,
              d_path/2,
              d_tally_nextdose_final/4,
              d_tally_next/3,
              d_tally_dose/3,
              d_endtally_rec/3
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(dcgs)).

:- use_module(rcpearl).

clpz:monotonic. % The error occurs with or without this declaration.

d_init(D, Init) :-
    #D #> 0, length(Init, D),
    maplist(=(0/0), Init).

%?- d_init(3, Init).
%@    Init = [0/0,0/0,0/0].

d_path(D, Path) :-
    d_init(D, [I|Is]),
    phrase(path([I]-Is), Path).

%?- d_path(2, Path).
%@    Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[0/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[1/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[0/6]-[2/6],stop,recommend_dose(1)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[1/6]-[2/6],stop,recommend_dose(1)]
%@ ;  ... .

%?- J+\(findall(Path, user:d_path(2, Path), Paths), lists:length(Paths, J)).
%@    J = 46.

%% d_tally_nextdose_final(+D, ?Q, ?X, ?Final) is nondet
%
% Describes the interim [Final=false] and final [Final=true] tallies
% and subsequent next-dose recommendations which terminate the paths
% of the D-dose 3+3 design as described by our DCG.
% Memoizing it via *tabling* achieves a _complete_ description at the
% cost of only a single, one-off comprehensive elaboration of the DCG.
:- table d_tally_nextdose_final/3.
d_tally_nextdose_final(D, Q, X, Final) :-
    d_path(D, Path),
    (   Final = false,
        phrase((..., [State0,E,Ls-_], ...), Path),
        member(E, [esc,des,sta]),
        state_tallies(State0, Q),
        length(Ls, X)
    ;   Final = true,
        phrase((..., [Endstate,stop,recommend_dose(X)]), Path),
        state_tallies(Endstate, Q)
    ).
d_tally_nextdose_final(D, Q, 1, false) :- d_init(D, Q). % (**)

% Let's enable checking all the interim tallies and dose recs
d_tally_next(D, Tally, Next) :-
    d_tally_nextdose_final(D, Tally, Next, false).

d_tally_dose(D, Tally, X) :-
    d_tally_nextdose_final(D, Tally, X, _).

%?- d_tally_dose(3, [0/0,0/0,0/0], X).
%@    false. % before adding (**) clause of d_tally_nextdose_final/4
%@    X = 1. % with (**) clause

d_endtally_rec(D, FinalTally, Rec) :-
    d_tally_nextdose_final(D, FinalTally, Rec, true).

%?- d_endtally_rec(2, Q, D).
%@    Q = [0/3,0/6], D = 2
%@ ;  Q = [0/3,1/6], D = 2
%@ ;  Q = [0/6,2/3], D = 1
%@ ;  Q = [0/6,2/6], D = 1
%@ ;  Q = [0/6,3/3], D = 1
%@ ;  Q = [0/6,3/6], D = 1
%@ ;  Q = [0/6,4/6], D = 1
%@ ;  Q = [1/6,0/6], D = 2
%@ ;  Q = [1/6,1/6], D = 2
%@ ;  Q = [1/6,2/3], D = 1
%@ ;  Q = [1/6,2/6], D = 1
%@ ;  Q = [1/6,3/3], D = 1
%@ ;  Q = [1/6,3/6], D = 1
%@ ;  Q = [1/6,4/6], D = 1
%@ ;  Q = [2/3,0/0], D = 0
%@ ;  Q = [2/6,0/0], D = 0
%@ ;  Q = [2/6,2/3], D = 0
%@ ;  Q = [2/6,2/6], D = 0
%@ ;  Q = [2/6,3/3], D = 0
%@ ;  Q = [2/6,3/6], D = 0
%@ ;  Q = [2/6,4/6], D = 0
%@ ;  Q = [3/3,0/0], D = 0
%@ ;  Q = [3/6,0/0], D = 0
%@ ;  Q = [3/6,2/3], D = 0
%@ ;  Q = [3/6,2/6], D = 0
%@ ;  Q = [3/6,3/3], D = 0
%@ ;  Q = [3/6,3/6], D = 0
%@ ;  Q = [3/6,4/6], D = 0
%@ ;  Q = [4/6,0/0], D = 0
%@ ;  false.

% Now we readily "check the functoriality" of the dose recommendations
/*
?- d_endtally_rec(2, Q1, D1),
   d_endtally_rec(2, Q2, D2),
   Q1 '≼' Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% A different way to put this would be:
/*
?- d_endtally_rec(2, Q1, D1),
   d_endtally_rec(2, Q2, D2),
      Q1 '≼' Q2,  % Q1 is evidently no safer than Q2,
   #\(D1 #=< D2). % yet D1 is NOT likewise related to D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% That initial listing in Section 4.1 ought to have been done with
% this predicate too!
/*
?- N+\(setof(Q-Rec, d_endtally_rec(2, Q, Rec), QRecs),
       maplist(portray_clause, QRecs),
       length(QRecs, N)).
%@ [0/3,0/6]-2.
%@ [0/3,1/6]-2.
%@ [0/6,2/3]-1.
%@ [0/6,2/6]-1.
%@ [0/6,3/3]-1.
%@ [0/6,3/6]-1.
%@ [0/6,4/6]-1.
%@ [1/6,0/6]-2.
%@ [1/6,1/6]-2.
%@ [1/6,2/3]-1.
%@ [1/6,2/6]-1.
%@ [1/6,3/3]-1.
%@ [1/6,3/6]-1.
%@ [1/6,4/6]-1.
%@ [2/3,0/0]-0.
%@ [2/6,0/0]-0.
%@ [2/6,2/3]-0.
%@ [2/6,2/6]-0.
%@ [2/6,3/3]-0.
%@ [2/6,3/6]-0.
%@ [2/6,4/6]-0.
%@ [3/3,0/0]-0.
%@ [3/6,0/0]-0.
%@ [3/6,2/3]-0.
%@ [3/6,2/6]-0.
%@ [3/6,3/3]-0.
%@ [3/6,3/6]-0.
%@ [3/6,4/6]-0.
%@ [4/6,0/0]-0.
%@    N = 29.
*/

% Clearly, some of these 29 final tallies must be shared
% between several of the 46 distinct trial paths.
% Let's demonstrate how!

