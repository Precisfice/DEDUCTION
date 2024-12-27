% intlist.pl
% Utilities for integer lists

:- module(intlist, [
              intlist_sum/2,
              intlist_negated/2,
              intlist_partsums/2,
              maxs/3,
              mins/3
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).

clpz:monotonic.

intlist_sum([X|Xs], Sum) :- intlist_sum_([X|Xs], Sum).
intlist_sum_([X|Xs], Sum) :-
    intlist_sum_(Xs, _Sum),
    #Sum #= #X + #_Sum.
intlist_sum_([], 0).

%?- intlist_sum([], Nope).
%@    false. % As desired.

%?- findall(N, (N in 1..100, indomain(N)), Ns), time(intlist_sum(Ns, Sum)).
%@    % CPU time: 0.000s, 379 inferences
%@    Ns = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20|...], Sum = 5050.

intlist_negated([X|Xs], [N|Ns]) :-
    same_length(Xs, Ns),
    #X #= -(#N),
    intlist_negated(Xs, Ns).
intlist_negated([], []).

%?- intlist_negated(Xs, [-1,-2,-3]).
%@    Xs = [1,2,3].

%?- intlist_negated(Xs, Ns).
%@    Xs = [_A], Ns = [_B], clpz:(#_A+ #_B#=0)
%@ ;  Xs = [_A,_C], Ns = [_B,_D], clpz:(#_A+ #_B#=0), clpz:(#_C+ #_D#=0)
%@ ;  Xs = [_A,_C,_E], Ns = [_B,_D,_F], clpz:(#_A+ #_B#=0), clpz:(#_C+ #_D#=0), clpz:(#_E+ #_F#=0)
%@ ;  ... .

intlist_partsums([X|Xs], [X|Σs]) :-
    same_length(Xs, Σs), % eliminate unnecessary choice point
    intlist_partsums_acc(Xs, Σs, X).

intlist_partsums_acc([], [], _).
intlist_partsums_acc([X|Xs], [Σ|Σs], A) :-
    #Σ #= #X + #A,
    intlist_partsums_acc(Xs, Σs, Σ).

maxs(N1s, N2s, Ns) :- maplist(max_, N1s, N2s, Ns).
mins(N1s, N2s, Ns) :- maplist(min_, N1s, N2s, Ns).

max_(E, M0, M) :- #M #= max(E, M0). % Copied from library(clpz),
min_(E, M0, M) :- #M #= min(E, M0). % which does not export them.

%?- maxs([1,2,6], [3,4,5], Maxs).
%@    Maxs = [3,4,6].
%?- mins([1,2,6], [3,4,5], Mins).
%@    Mins = [1,2,5].

% Unused, so not exported; retained 'on spec' only:

intlist_rolled([X|Xs], G_3, [X|Zs]) :-
    same_length(Xs, Zs),
    intlist_rolled_(Xs, G_3, Zs, X).

intlist_rolled_([X|Xs], G_3, [Z|Zs], R) :-
    call(G_3, X, R, Z),
    intlist_rolled_(Xs, G_3, Zs, Z).
intlist_rolled_([], _, [], _).

intlist_rollmin(Xs, As) :- intlist_rolled(Xs, min_, As).

%?- intlist_rollmin([5,3,56,4,9], Ms).
%@    Ms = [5,3,3,3,3].

intlist_rollmax(Xs, Vs) :- intlist_rolled(Xs, max_, Vs).

%?- intlist_rollmax([5,3,56,4,9], Ms).
%@    Ms = [5,5,56,56,56].

intlist_inverse(Xs, NegXs) :-
    same_length(Xs, NegXs), % avoid choicepoint when used (-Xs, +NegXs)
    maplist(\X^N^(#N #= - #X), Xs, NegXs).

%?- intlist_inverse([5,3,56,4,9], Ns).
%@    Ns = [-5,-3,-56,-4,-9].

%?- intlist_inverse(Xs, [5,3,56,4,9]).
%@    Xs = [-5,-3,-56,-4,-9].
