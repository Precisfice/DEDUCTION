% Experiments toward 'less impure' all-solutions predicates

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

clpz:monotonic.

reduce(P_3, [X|Xs], R) :- foldl(P_3, Xs, X, R).

sum_(X, Y, Z) :- #Z #= #X + #Y.

%?- reduce(sum_, [1,2,3], R).
%@    R = 6.

%?- reduce(sum_, [-1], R).
%@    R = -1. % as desired

%?- reduce(sum_, [], R).
%@    false. % as desired

sum_all(X, Goal, R) :-
    asserta('$reducing'([])),
    (   sum_all_(X, Goal, R)
    ;   call('$reducing'([R])),
        retract('$reducing'([R]))
    ).

sum_all_(X, Goal, R) :-
    call(Goal),
    (   retract('$reducing'([R0])), % succeeds on 2nd & subsequent instantiations of Goal
        sum_(R0, X, R),
        asserta('$reducing'([R]))
    ;   retract('$reducing'([])), % succeeds only on the 1st instantiation of Goal
        asserta('$reducing'([X]))
    ),
    fail.

%?- sum_all(X, (X in 1..10, indomain(X)), R).
%@    R = 55.

:- meta_predicate reduce_all(3, ?, 0, ?).
:- meta_predicate reduce_all_(3, ?, 0, ?).

% Akin to reduce(P_3, {X : Goal(X)}, R), and operationally
% equivalent to (findall(X, Goal, Xs), reduce(P_3, Xs, R)),
% where X is a free variable in Goal.
reduce_all(P_3, X, Goal, R) :-
    asserta('$reducing'([])),
    (   reduce_all_(P_3, X, Goal, R)
    ;   call('$reducing'([R])),
        retract('$reducing'([R]))
    ).

reduce_all_(P_3, X, Goal, R) :-
    call(Goal),
    (   retract('$reducing'([R0])), % succeeds on 2nd & subsequent instantiations of Goal
        call(P_3, R0, X, R),
        asserta('$reducing'([R]))
    ;   retract('$reducing'([])), % succeeds on the 1st instantiation of Goal only
        asserta('$reducing'([X]))
    ),
    fail.

%?- reduce_all(sum_, X, (X in 1..10, indomain(X)), R).
%@    R = 55.
