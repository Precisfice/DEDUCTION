% po.pl
% See what I can abstract from run-on catform.pl workbench.

:- module(po, [
              % Pending https://github.com/mthom/scryer-prolog/issues/2547,
              % we cannot export some pretty operators.  Client modules may
              % however access these by explicit qualification, and assign
              % these operators locally.
              %op(900, xfx, 'leq'), % Mutually exclusive infix
              %op(900, xfx, '≰'), % relations defined on ℕᴰ.
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).

clpz:monotonic. % The error occurs with or without this declaration.

:- op(900, xfx, '≤'). % Mutually exclusive infix
:- op(900, xfx, '≰'). % relations defined on ℕᴰ.

'≤'([], [], true). % trivial case makes general clause easier to implement
'≤'([X|Xs], [Y|Ys], Truth) :- % ≤ extended to ℕᴰ, D≥1
    if_(clpz_t(#X #=< #Y),
        '≤'(Xs,Ys,Truth),
        Truth = false
       ).
    
%?- '≤'([], [], Truth).
%@    Truth = true. % A quirk easily excluded from ('≤')/2

%?- '≤'([2], [3], Truth).
%@    Truth = true.

%?- '≤'([2,3], [3,2], Truth).
%@    Truth = false.

%?- '≤'([2], [3], true).
%@    true.

%?- '≤'([2], [3], false).
%@    false.

Xs '≤' Ys :-
    same_length(Xs, Ys),
    length(Xs, D), D #> 0,
    '≤'(Xs, Ys, true).

%?- [] '≤' [].
%@    false. % As desired

%?- [2] '≤' [3].
%@    true.

%?- [3] '≤' [2].
%@    false.

%?- [2,3] '≤' [3,2].
%@    false.

%?- [2,3] '≤' [3,X].
%@    clpz:(X in 3..sup).

%?- [0,0,0] '≤' Xs, Xs '≤' [1,1,1], label(Xs).
%@    Xs = [0,0,0]
%@ ;  Xs = [0,0,1]
%@ ;  Xs = [0,1,0]
%@ ;  Xs = [0,1,1]
%@ ;  Xs = [1,0,0]
%@ ;  Xs = [1,0,1]
%@ ;  Xs = [1,1,0]
%@ ;  Xs = [1,1,1].


Xs '≰' Ys :-
    same_length(Xs, Ys),
    length(Xs, D), D #> 0,
    '≤'(Xs, Ys, false).

%?- [1,1,1] '≰' Xs.
%@    Xs = [_A,_B,_C], clpz:(_A in inf..0)
%@ ;  Xs = [_A,_B,_C], clpz:(_A in 1..sup), clpz:(_B in inf..0)
%@ ;  Xs = [_A,_B,_C], clpz:(_A in 1..sup), clpz:(_B in 1..sup), clpz:(_C in inf..0)
%@ ;  false.

