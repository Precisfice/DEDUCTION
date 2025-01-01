% comprehension.pl
% Utilities variously invoking the Principle of Comprehension

:- module(comprehension, [
              reduce/3
              ,reduce/4
              ,binsof/3
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(lambda)).
:- use_module(library(pairs)).

clpz:monotonic.

:- meta_predicate(reduce(3, ?, ?)).
:- meta_predicate(reduce(3, ?, 0, ?)).

reduce(P_3, [X|Xs], R) :- foldl(P_3, Xs, X, R).
reduce(P_3, X, Goal, R) :-
    setof(X, Goal, Xs),
    reduce(P_3, Xs, R).

%?- reduce(\X^Y^X^(#Z #= #X + #Y), [1,2,3,4], R).
%@    R = 4.
%?- reduce(clpz:max_, [2,1,4,3], R).
%@    R = 4.

:- meta_predicate(binsof(?, 0, ?)).

%% binsof(-(K-V), +Goal_2, -Bins) is det
%
% Given Goal_2 with free variables K-V, unifies Bins with
% the K-sorted list of sets of the form {V : Goal(K,V)}.
% In the special case where K in 0..(N-1), Bins will be
% a length-N list-of-lists such that nth0(K, Bins, Vs)
% iff setof(V, Goal_2(K), Vs).
% TODO: Given that this implementation ultimately depends
%       on !/0 (via same_key/4 via group_pairs_by_key/2),
%       and that my intended use at the moment is precisely
%       the special case documented above, consider a more
%       specialized and _purer_ recursive implementation.
binsof(K-V, Goal, Bins) :-
    setof(K-V, Goal, KVs),
    group_pairs_by_key(KVs, Ps), % uses same_key/4, which has a !/0
    pairs_values(Ps, Bins).

:- use_module(run33).

%?- D = 2, binsof(X-Q, d_tally_dose(D, Q, X), Bins).
%@    D = 2, Bins = [[[2/3,0/0],[2/6,0/0],[2/6,2/3],[2/6,2/6],[2/6,3/3],[2/6,3/6],
%                     [2/6,4/6],[3/3,0/0],[3/6,0/0],[3/6,2/3],[3/6,2/6],[3/6,3/3],
%                     [3/6,3/6],[3/6,4/6],[4/6,0/0]],
%                    [[0/0,0/0],[0/3,2/3],[0/3,2/6],[0/3,3/3],[0/3,3/6],[0/3,4/6],
%                     [0/6,2/3],[0/6,2/6],[0/6,3/3],[0/6,3/6],[0/6,4/6],[1/3,0/0],
%                     [1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]],
%                    [[0/3,0/0],[0/3,0/3],[0/3,0/6],[0/3,1/3],[0/3,1/6],[1/6,0/0],
%                     [1/6,0/3],[1/6,0/6],[1/6,1/3],[1/6,1/6]]].
