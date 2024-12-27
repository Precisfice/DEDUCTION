% tally.pl
% Basic utilities for tally generation, esp. fair enumeration

:- module(tally, [
              qs_d_nmax/3
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(lambda)).

clpz:monotonic.

% Regions near the origin
% TODO: Find a name conveying geometrical intutition ('sphere'? 'hypercube'?),
%       or perhaps link this to *accessible* tallies as discussed in Fact 1.27.
% TODO: Also deal with the 'qs' plurality; perhaps in this module, a given tally
%       counts as 'q', and only _lists_ of tallies should be regarded a plural?
%       Alternatively, perhaps there will be 'low-level' predicates that regard
%       a tally as a list, properly called 'Qs', but 'higher-level' predicates
%       that regard a 'Tally' or 'Tallies' at higher levels of abstraction.
%       (Of course, in general these distinct manners of regarding tallies may
%       well argue for distinct modules!)
qs_d_nmax(Qs, D, Nmax) :-
    length(Qs, D),
    maplist(\Q^T^N^(Q = T/N), Qs, Ts, Ns),
    Ns ins 0..Nmax, label(Ns),
    maplist(\T^N^(T in 0..N), Ts, Ns), label(Ts).
