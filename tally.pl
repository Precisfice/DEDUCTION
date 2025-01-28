% tally.pl
% Basic utilities for tally generation, esp. fair enumeration,
% also tally construction and the monoidal operation on 𝒬.

:- module(tally, [
              qs_ts_ns/3,
              qs_ts_us/3,
              tally_netn/2,
              qsum_/3,
              tallyo/3,
              tallyx/3,
              qs_d_nmax/3
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(lambda)).
:- use_module(library(time)).
:- use_module(library(reif)).
:- use_module(intlist).
:- use_module(fairenum).

clpz:monotonic.

qs_ts_ns([T/N|Qs], [T|Ts], [N|Ns]) :- qs_ts_ns(Qs, Ts, Ns).
qs_ts_ns([], [], []).

qs_ts_us(Qs, Ts, Us) :-
    maplist(\Q^T^U^(Q = T/N, #U #= N - T), Qs, Ts, Us).

tally_netn(Qs, ΣN) :- % net enrollment
    qs_ts_ns(Qs, _, Ns),
    sum(Ns, #=, #ΣN).

?- tally_netn([1/6,2/3], N).
   N = 9.
   N = 9.

%% qsum_(?Q0s, ?ΔQs, ?Qs)
%
% Akin to clpz:max_, but taking Q0s, ΔQs, Qs ∈ 𝒬 as arguments, so that
% Qs = Q0s + ΔQs, '+' here being the 𝒬's symmetric monoidal operation.
%
% TODO: Since this aims to extend declarative integer arithmetic to 𝒬,
%       we might do well to pursue this more vigorously, including to
%       the full MGQ, with attention to fair enumeration, etc.
qsum_(Q0s, ΔQs, Qs) :-
    same_length(Q0s, ΔQs), % Needed for
    same_length(Q0s, Qs),  % termination
    qs_ts_ns(Q0s, T0s, N0s),
    qs_ts_ns(ΔQs, ΔTs, ΔNs),
    qs_ts_ns(Qs, Ts, Ns),
    maplist(sum_, T0s, ΔTs, Ts),
    maplist(sum_, N0s, ΔNs, Ns).

sum_(X, Y, Z) :- #Z #= #X + #Y.

?- qsum_([0/1,1/1], [0/0,0/1], Qs).
   Qs = [0/1,1/2].

%% d_x_qs(+D, +X, -Qs)
%
% X in 1..D and Qs = <1/1>ₓ per Notation 2.5 of the monograph.  That
% is, Qs is a length-D list of 0/0 *except* that nth1(X, Qs, 1/1).
d_x_qs(D, X, Qs) :-
    0 #< #X, #X #=< #D,
    length(Qs, D),
    qs_ts_ns(Qs, Ns, Ns),
    d_unitvec_x(D, X, Ns),
    % Now we just need Ns as a 'unit vector' in X direction
    false.

% TODO: This utility may belong in module(intlist).
d_unitvec_x(D, O1s, X) :-
    length(O1s, D),
    0 #< #X, #X #=< D,
    intlist_from_upto(Ix, 1, D),
    maplist(=(X), Ix, TFs), % NB: this is reif:(=)/3
    maplist(clpz:zo_t, O1s, TFs).

?- d_unitvec_x(5, O1s, 2).
   O1s = [0,1,0,0,0]
;  false.

?- d_unitvec_x(5, O1s, 5).
   O1s = [0,0,0,0,1]
;  false.

?- d_unitvec_x(D, U, X).
   D = 1, U = [1], X = 1
;  D = 2, U = [1,0], X = 1
;  D = 2, U = [0,1], X = 2
;  D = 2, U = [0,0], clpz:(X in 1..2), dif:dif(X,1), dif:dif(X,2)
;  D = 3, U = [1,0,0], X = 1
;  D = 3, U = [0,1,0], X = 2
;  D = 3, U = [0,0,1], X = 3
;  D = 3, U = [0,0,0], clpz:(X in 1..3), dif:dif(X,1), dif:dif(X,2), dif:dif(X,3)
;  D = 4, U = [1,0,0,0], X = 1
;  ... .

%% tallyx(Q, X, Q1)
%
% Q1 - Q = <1/1>ₓ
tallyx(Q, Dose, Q1) :-
    length(Q, D),
    d_unitvec_x(D, Ns, Dose),
    qs_ts_ns(ΔQ, Ns, Ns),
    qsum_(Q, ΔQ, Q1).

%% tallyo(Q, X, Q1)
%
% Q1 - Q = <0/1>ₓ
tallyo(Q, Dose, Q1) :-
    length(Q, D),
    d_unitvec_x(D, Ns, Dose),
    same_length(Q, Ts),
    maplist(=(0), Ts),
    qs_ts_ns(ΔQ, Ts, Ns),
    qsum_(Q, ΔQ, Q1).

?- Q = [0/3,0/3,2/3], tallyo(Q, 2, Qo), tallyx(Q, 2, Qx). 
   Q = [0/3,0/3,2/3], Qo = [0/3,0/4,2/3], Qx = [0/3,1/4,2/3]
;  false.

qs_d_nmax(Qs, D, Nmax) :-
    n_d_max(Ns, D, Nmax),
    label(Ns),
    maplist(\T^N^(T in 0..N), Ts, Ns),
    label(Ts),
    maplist(\Q^T^N^(Q = T/N), Qs, Ts, Ns).

?- L+\(findall(Qs, (Max in 0..3, qs_d_nmax(Qs, 2, Max)), Qss), length(Qss, L)).
   L = 100. % Correct: (4+3+2+1)^2

?- qs_d_nmax(Qs, D, Nmax). % MGQ
   Qs = [0/0], D = 1, Nmax = 0
;  Qs = [0/1], D = 1, Nmax = 1
;  Qs = [1/1], D = 1, Nmax = 1
;  Qs = [0/0,0/0], D = 2, Nmax = 0
;  Qs = [0/2], D = 1, Nmax = 2
;  Qs = [1/2], D = 1, Nmax = 2
;  Qs = [2/2], D = 1, Nmax = 2
;  Qs = [0/0,0/1], D = 2, Nmax = 1
;  Qs = [0/0,1/1], D = 2, Nmax = 1
;  Qs = [0/1,0/0], D = 2, Nmax = 1
;  Qs = [1/1,0/0], D = 2, Nmax = 1
;  Qs = [0/1,0/1], D = 2, Nmax = 1
;  Qs = [0/1,1/1], D = 2, Nmax = 1
;  Qs = [1/1,0/1], D = 2, Nmax = 1
;  Qs = [1/1,1/1], D = 2, Nmax = 1
;  Qs = [0/0,0/0,0/0], D = 3, Nmax = 0
;  Qs = [0/3], D = 1, Nmax = 3
;  Qs = [1/3], D = 1, Nmax = 3
;  Qs = [2/3], D = 1, Nmax = 3
;  Qs = [3/3], D = 1, Nmax = 3
;  Qs = [0/0,0/2], D = 2, Nmax = 2
;  Qs = [0/0,1/2], D = 2, Nmax = 2
;  Qs = [0/0,2/2], D = 2, Nmax = 2
;  Qs = [0/1,0/2], D = 2, Nmax = 2
;  Qs = [0/1,1/2], D = 2, Nmax = 2
;  Qs = [0/1,2/2], D = 2, Nmax = 2
;  Qs = [1/1,0/2], D = 2, Nmax = 2
;  Qs = [1/1,1/2], D = 2, Nmax = 2
;  Qs = [1/1,2/2], D = 2, Nmax = 2
;  Qs = [0/2,0/0], D = 2, Nmax = 2
;  Qs = [1/2,0/0], D = 2, Nmax = 2
;  Qs = [2/2,0/0], D = 2, Nmax = 2
;  Qs = [0/2,0/1], D = 2, Nmax = 2
;  Qs = [0/2,1/1], D = 2, Nmax = 2
;  Qs = [1/2,0/1], D = 2, Nmax = 2
;  Qs = [1/2,1/1], D = 2, Nmax = 2
;  Qs = [2/2,0/1], D = 2, Nmax = 2
;  Qs = [2/2,1/1], D = 2, Nmax = 2
;  Qs = [0/2,0/2], D = 2, Nmax = 2
;  Qs = [0/2,1/2], D = 2, Nmax = 2
;  Qs = [0/2,2/2], D = 2, Nmax = 2
;  Qs = [1/2,0/2], D = 2, Nmax = 2
;  Qs = [1/2,1/2], D = 2, Nmax = 2
;  Qs = [1/2,2/2], D = 2, Nmax = 2
;  Qs = [2/2,0/2], D = 2, Nmax = 2
;  Qs = [2/2,1/2], D = 2, Nmax = 2
;  Qs = [2/2,2/2], D = 2, Nmax = 2
;  Qs = [0/0,0/0,0/1], D = 3, Nmax = 1
;  Qs = [0/0,0/0,1/1], D = 3, Nmax = 1
;  ... .
