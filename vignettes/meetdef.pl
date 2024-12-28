% meetdef.pl
% Demonstrate calculations of meets 'as defined'

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(lambda)).
:- use_module('../tally.pl').
:- use_module('../enst.pl').

clpz:monotonic.

% Pending https://github.com/mthom/scryer-prolog/issues/2547,
% some pretty operators resist export, and require 'extraction':
:- op(900, xfx, '≽').

'≽'(X,Y,T) :- enst:'≽'(X,Y,T).

% Compare the computation by meet/3 against a brute-force calculation
% that directly implements the _definition_ of meet.

nmax_meet(Nmax, Q1s, Q2s, Qs) :-
    % 1. Generate a list of 'all possible' Qss to test.
    same_length(Q1s, Q2s),
    length(Q1s, D),
    findall(Qs, qs_d_nmax(Qs, D, Nmax), Qss),
    % 2. Filter out elements that are below both Q1s and Q2s.
    tfilter('≽'(Q1s), Qss, Qss1),
    tfilter('≽'(Q2s), Qss1, Qss12),
    % 3. Find the maximal elements of the resulting list.
    qs_maxs(Qss12, Meets),
    member(Qs, Meets).

/*
?- MeetDef^Meet+\(Q1=[0/6,4/6], Q2=[1/6,2/3],
                  nmax_meet(6, Q1, Q2, MeetDef),
                  meet(Q1, Q2, Meet)).
%@    MeetDef = [1/6,3/6], Meet = [1/6,3/6].
*/
