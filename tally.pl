% tally.pl
% Basic utilities for tally generation, esp. fair enumeration

:- module(tally, [
              qs_d_nmax/3
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(lambda)).
:- use_module(library(time)).
:- use_module(fairenum).

clpz:monotonic.

qs_d_nmax(Qs, D, Nmax) :-
    n_d_max(Ns, D, Nmax),
    length(Ts, D),
    maplist(\T^N^(T in 0..N), Ts, Ns),
    label(Ts),
    maplist(\Q^T^N^(Q = T/N), Qs, Ts, Ns).

%?- L+\(findall(Qs, qs_d_nmax(Qs, 2, 3), Qss), length(Qss, L)).
%@    L = 100. % Correct: (4+3+2+1)^2

%?- qs_d_nmax(Qs, D, Nmax). % MGQ
%@    Qs = [0/0], D = 1, Nmax = 0
%@ ;  Qs = [0/0], D = 1, Nmax = 1
%@ ;  Qs = [0/1], D = 1, Nmax = 1
%@ ;  Qs = [1/1], D = 1, Nmax = 1
%@ ;  Qs = [0/0,0/0], D = 2, Nmax = 0
%@ ;  Qs = [0/0], D = 1, Nmax = 2
%@ ;  Qs = [0/1], D = 1, Nmax = 2
%@ ;  Qs = [1/1], D = 1, Nmax = 2
%@ ;  Qs = [0/2], D = 1, Nmax = 2
%@ ;  Qs = [1/2], D = 1, Nmax = 2
%@ ;  Qs = [2/2], D = 1, Nmax = 2
%@ ;  Qs = [0/0,0/0], D = 2, Nmax = 1
%@ ;  Qs = [0/0,0/1], D = 2, Nmax = 1
%@ ;  Qs = [0/0,1/1], D = 2, Nmax = 1
%@ ;  Qs = [0/1,0/0], D = 2, Nmax = 1
%@ ;  Qs = [1/1,0/0], D = 2, Nmax = 1
%@ ;  Qs = [0/1,0/1], D = 2, Nmax = 1
%@ ;  Qs = [0/1,1/1], D = 2, Nmax = 1
%@ ;  Qs = [1/1,0/1], D = 2, Nmax = 1
%@ ;  Qs = [1/1,1/1], D = 2, Nmax = 1
%@ ;  Qs = [0/0,0/0,0/0], D = 3, Nmax = 0
%@ ;  Qs = [0/0], D = 1, Nmax = 3
%@ ;  Qs = [0/1], D = 1, Nmax = 3
%@ ;  Qs = [1/1], D = 1, Nmax = 3
%@ ;  Qs = [0/2], D = 1, Nmax = 3
%@ ;  Qs = [1/2], D = 1, Nmax = 3
%@ ;  Qs = [2/2], D = 1, Nmax = 3
%@ ;  Qs = [0/3], D = 1, Nmax = 3
%@ ;  Qs = [1/3], D = 1, Nmax = 3
%@ ;  Qs = [2/3], D = 1, Nmax = 3
%@ ;  Qs = [3/3], D = 1, Nmax = 3
%@ ;  Qs = [0/0,0/0], D = 2, Nmax = 2
%@ ;  Qs = [0/0,0/1], D = 2, Nmax = 2
%@ ;  ... .
