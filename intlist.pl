% intlist.pl
% Utilities for integer lists

:- module(intlist, [
              intlist_sum/2,
              intlist_negated/2,
              intlist_partsums/2,
              maxs/3,
              mins/3,
              intlist_from_upto/3,
              posints_bins/2
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(pairs)).
:- use_module(library(dcgs)).
:- use_module(library(dif)).
:- use_module(library(reif)).
:- use_module(library(lambda)).

clpz:monotonic.

intlist_sum([X|Xs], Sum) :- intlist_sum_([X|Xs], Sum).
intlist_sum_([X|Xs], Sum) :-
    intlist_sum_(Xs, _Sum),
    #Sum #= #X + #_Sum.
intlist_sum_([], 0).

?- intlist_sum([], Nope).
   false.

?- findall(N, (N in 1..100, indomain(N)), Ns), intlist_sum(Ns, Sum).
   Ns = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20|...], Sum = 5050.

intlist_negated([X|Xs], [N|Ns]) :-
    same_length(Xs, Ns),
    #X #= -(#N),
    intlist_negated(Xs, Ns).
intlist_negated([], []).

?- intlist_negated(Xs, [-1,-2,-3]).
   Xs = [1,2,3].

?- intlist_negated(Xs, Ns).
   Xs = [_A], Ns = [_B], clpz:(#_A+ #_B#=0)
;  Xs = [_A,_C], Ns = [_B,_D], clpz:(#_A+ #_B#=0), clpz:(#_C+ #_D#=0)
;  Xs = [_A,_C,_E], Ns = [_B,_D,_F], clpz:(#_A+ #_B#=0), clpz:(#_C+ #_D#=0), clpz:(#_E+ #_F#=0)
;  ... .

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

?- maxs([1,2,6], [3,4,5], Maxs).
   Maxs = [3,4,6].
?- mins([1,2,6], [3,4,5], Mins).
   Mins = [1,2,5].

% Unused, so not exported; retained 'on spec' only:

intlist_rolled([X|Xs], G_3, [X|Zs]) :-
    same_length(Xs, Zs),
    intlist_rolled_(Xs, G_3, Zs, X).

intlist_rolled_([X|Xs], G_3, [Z|Zs], R) :-
    call(G_3, X, R, Z),
    intlist_rolled_(Xs, G_3, Zs, Z).
intlist_rolled_([], _, [], _).

intlist_rollmin(Xs, As) :- intlist_rolled(Xs, min_, As).

?- intlist_rollmin([5,3,56,4,9], Ms).
   Ms = [5,3,3,3,3].

intlist_rollmax(Xs, Vs) :- intlist_rolled(Xs, max_, Vs).

?- intlist_rollmax([5,3,56,4,9], Ms).
   Ms = [5,5,56,56,56].

intlist_inverse(Xs, NegXs) :-
    same_length(Xs, NegXs), % avoid choicepoint when used (-Xs, +NegXs)
    maplist(\X^N^(#N #= - #X), Xs, NegXs).

?- intlist_inverse([5,3,56,4,9], Ns).
   Ns = [-5,-3,-56,-4,-9].

?- intlist_inverse(Xs, [5,3,56,4,9]).
   Xs = [-5,-3,-56,-4,-9].

%% intlist_from_upto(?Zs, ?A, ?B)
%
% Zs lists the integers from A ≤ B up to B, inclusive.
% (Zs is therefore a list of length B-A+1.)
%
% The aim of this predicate is to avoid all-solutions predicates, à la
% findall(X, (X in A..B, indomain(X)), Xs).  But perhaps in light of
% https://github.com/mthom/scryer-prolog/discussions/2722#discussioncomment-11657471
% this is not so important a goal?  (With the current Scryer engine,
% this implementation leaves a choice-point which findall/3 does not.)
intlist_from_upto([A|_As], A, B) :-
    #A #< #B,
    #A1 #= #A + 1,
    intlist_from_upto(_As, A1, B).
intlist_from_upto([A], A, A).

?- findall(N, (N in 1..5, indomain(N)), Ns).
   Ns = [1,2,3,4,5].

?- intlist_from_upto(Ns, 1, 5).
   Ns = [1,2,3,4,5]
;  false.

?- intlist_from_upto([1,2,3], A, B).
   A = 1, B = 3
;  false.

?- intlist_from_upto([3,2,1], A, B).
   false.

%% posints_bins(+Ns, -Bins)
%
% Ns is a list of positive integers, and Bins is a 1-indexed list
% such that nth1(N, Bins, F) iff N appears exactly F times in Ns.
% That is, Bins lists the _frequency_ in Ns for each number 1..L,
% where length(Bins, L).
%
% Generally, this predicate will be invoked with the length of Bins
% fixed, but its elements uninstantiated.
posints_bins(Ns, Bins) :-
    length(Bins, L),
    findall(B, (B in 1..L, indomain(B)), Bs),
    append(Ns, Bs, N1s),  % each B ∈ 1..L occurs at least once in N1s
    samsort(N1s, SN1s),
    list_rle(SN1s, NC1s), % NC1s now overcounts each bin by +1
    pairs_values(NC1s, Bins1),
    maplist(\F1^F^(#F1 #= #F + 1), Bins1, Bins).

?- length(Bins, 7), posints_bins([5,2,7,5,3,5,7,5,6,7], Bins).
   Bins = [0,1,1,0,4,1,3]
;  false.

?- nth1(2, [a,b,c,d,e], C, R).
   C = b, R = "acde".

%% samsort(+Ls0, Ls)
%
% See https://github.com/mthom/scryer-prolog/issues/1163#issuecomment-1006135163
% HT @triska
samsort(Ls0, Ls) :-
        same_length(Ls0, Pairs0), % https://github.com/mthom/scryer-prolog/issues/192
        pairs_keys(Pairs0, Ls0),
        keysort(Pairs0, Pairs),
        pairs_keys(Pairs, Ls).

?- samsort([4,2,4,2,3,5], SXs).
   SXs = [2,2,3,4,4,5].

%% list_rle(?Xs, ?XNs)
%
% The list XNs is a run-length decoding of list Xs.
list_rle(Xs, XNs) :- phrase(rle(XNs), Xs).

?- list_rle("Bwwaaahaaahaaaa!", RLE).
   RLE = ['B'-1,w-2,a-3,h-1,a-3,h-1,a-4,!-1]
;  false.

?- list_rle(Bwahaha, ['B'-1,w-2,a-3,h-1,a-3,h-1,a-4,!-1]).
   Bwahaha = "Bwwaaahaaahaaaa!"
;  false.

%% rle//1
%
% Describes a list by run-length encoding.
rle([X-N|XNs]) --> { #N #> 1, #N_ #= #N - 1 },
                   [X],
                   rle([X-N_|XNs]).
rle([X-1,Y-N|XNs]) --> { dif(X,Y) },
                       [X],
                       rle([Y-N|XNs]).
rle([X-1]) --> [X].
rle([]) --> [].

?- phrase(rle([a-2,b-3,z-1]), List).
   List = "aabbbz"
;  false.
?- phrase(rle(RLE), "aabbbz").
   RLE = [a-2,b-3,z-1]
;  false.

