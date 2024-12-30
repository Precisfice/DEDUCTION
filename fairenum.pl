% fairenum.pl
% Basic utilities for fair enumeration

% TODO: Investigate the systematic approach in:
%
% New MS, Fetscher B, Findler RB, Mccarthy J.
% Fair enumeration combinators. J Funct Prog.
% 2017;27:e19. doi:10.1017/S0956796817000107

:- module(fairenum, [
              n_d_max/3
              ,n_d_sum/3
              % Pending https://github.com/mthom/scryer-prolog/issues/2547,
              % we cannot export some pretty operators.  Client modules may
              % however access these by explicit qualification, and assign
              % these operators locally.
              ,op(900, xfx, '≤') % Mutually exclusive infix
              ,op(900, xfx, '≰') % relations defined on ℕᴰ.
              ,op(900, xfx, '≠') % Generate distinct pairs.
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(lambda)).
:- use_module(library(reif)).
:- use_module(library(debug)).
:- use_module(library(format)).
:- use_module(comprehension).

clpz:monotonic.

:- op(900, xfx, '≤'). % Mutually exclusive infix
:- op(900, xfx, '≰'). % relations defined on ℕᴰ.
:- op(900, xfx, '≠'). % Generate distinct pairs from ℕᴰ.

% ('≤')/3 does NOT attempt fair enumeration
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

% Enumerates fairly, unlike ('≤')/3
% TODO: Fairly enumerate ([0,0,0] '≤' Xs, label(Xs)); see below.
Xs '≤' Ys :-
    same_length(Xs, Ys), Ys \== [],
    n_d_max(Ys, _, _),
    Xs ins 0..1_000_000_000, % '0..sup'
    maplist(\X^Y^(X #=< Y), Xs, Ys).

%?- [] '≤' [].
%@    false. % As desired

%?- [2] '≤' [3].
%@    true.

%?- [3] '≤' [2].
%@    false.

%?- [2,3] '≤' [3,2].
%@    false.

%?- [2,X] '≤' [3,4].
%@    clpz:(X in 0..4).

%?- [2,3] '≤' [3,X].
%@    clpz:(X in 3..1000000000), clpz:(#_A#>= #X), clpz:(#_A#=max(#X,3)), clpz:(_A in 3..1000000000).

%?- [0,0,0] '≤' Xs.
%@    Xs = [_D,_E,_C], clpz:(_A in 0..1000000000), clpz:(#_A#>= #_B), clpz:(#_A#>= #_C), clpz:(#_A#=max(#_C,#_B)), clpz:(_B in 0..1000000000), clpz:(#_B#>= #_D), clpz:(#_B#>= #_E), clpz:(#_B#=max(#_E,#_D)), clpz:(_D in 0..1000000000), clpz:(_E in 0..1000000000), clpz:(_C in 0..1000000000).

%?- [0,0,0] '≤' Xs, label(Xs).
%@    Xs = [0,0,0]
%@ ;  Xs = [0,0,1]
%@ ;  Xs = [0,0,2]
%@ ;  Xs = [0,0,3]
%@ ;  Xs = [0,0,4]
%@ ;  Xs = [0,0,5]
%@ ;  Xs = [0,0,6]
%@ ;  Xs = [0,0,7]
%@ ;  Xs = [0,0,8]
%@ ;  Xs = [0,0,9]
%@ ;  Xs = [0,0,10]
%@ ;  Xs = [0,0,11]
%@ ;  Xs = [0,0,12]
%@ ;  ... . % UNFAIR

%?- Xs '≤' [1,1,1], label(Xs).
%@    Xs = [0,0,0]
%@ ;  Xs = [0,0,1]
%@ ;  Xs = [0,1,0]
%@ ;  Xs = [0,1,1]
%@ ;  Xs = [1,0,0]
%@ ;  Xs = [1,0,1]
%@ ;  Xs = [1,1,0]
%@ ;  Xs = [1,1,1].


%?- [1,1,1] '≤' Xs, Xs '≤' [2,2,2], label(Xs).
%@    Xs = [1,1,1]
%@ ;  Xs = [1,1,2]
%@ ;  Xs = [1,2,1]
%@ ;  Xs = [1,2,2]
%@ ;  Xs = [2,1,1]
%@ ;  Xs = [2,1,2]
%@ ;  Xs = [2,2,1]
%@ ;  Xs = [2,2,2].


% TODO: Implement a fair-enumerating version of ('≰')/2 as well.
Xs '≰' Ys :-
    same_length(Xs, Ys),
    length(Xs, D), D #> 0,
    '≤'(Xs, Ys, false).

% WRONG:
%?- [1,1,1] '≰' Xs.
%@    Xs = [_A,_B,_C], clpz:(_A in inf..0)
%@ ;  Xs = [_A,_B,_C], clpz:(_A in 1..sup), clpz:(_B in inf..0)
%@ ;  Xs = [_A,_B,_C], clpz:(_A in 1..sup), clpz:(_B in 1..sup), clpz:(_C in inf..0)
%@ ;  false.

n_d_sum(Ns, D, Sum) :-
    n_d_norm(Ns, D, Sum),
    sum(Ns, #=, Sum).

n_d_max(Ns, D, Max) :-
    n_d_norm(Ns, D, Max),
    reduce(clpz:max_, Ns, Max).

n_d_norm(Ns, D, Norm) :-
    D    in 1..1_000, % '1..sup'
    Norm in 0..1_000_000_000, % '0..sup'
    (   nonvar(Ns) -> length(Ns, D)
    ;   #I #= #Norm + #D,
        label([I,D]),
        length(Ns, D)
    ),
    maplist(\N^(#N #>= 0), Ns).

% Fair enumeration fails if 1st arg is an improper list:
%?- n_d_sum([3|Xs], D, Sum), label(Xs).
%@    Xs = [], D = 1, Sum = 3
%@ ;  Xs = [0], D = 2, Sum = 3
%@ ;  Xs = [1], D = 2, Sum = 4
%@ ;  Xs = [2], D = 2, Sum = 5
%@ ;  Xs = [3], D = 2, Sum = 6
%@ ;  Xs = [4], D = 2, Sum = 7
%@ ;  ... .

%?- n_d_sum([3,X], D, Sum), label([X]).
%@    X = 0, D = 2, Sum = 3
%@ ;  X = 1, D = 2, Sum = 4
%@ ;  X = 2, D = 2, Sum = 5
%@ ;  X = 3, D = 2, Sum = 6
%@ ;  ... .

%?- n_d_max([3,X], D, Max).
%@    D = 2, clpz:(X in 0..1000000000), clpz:(#Max#>= #X), clpz:(#Max#=max(#X,3)), clpz:(Max in 3..1000000000).

%?- n_d_max(Ns, D, Max).
%@    Ns = [0], D = 1, Max = 0
%@ ;  Ns = [1], D = 1, Max = 1
%@ ;  Ns = [0,0], D = 2, Max = 0
%@ ;  Ns = [2], D = 1, Max = 2
%@ ;  Ns = [_A,_B], D = 2, Max = 1, clpz:(_A in 0..1), clpz:(1#=max(#_B,#_A)), clpz:(_B in 0..1)
%@ ;  Ns = [0,0,0], D = 3, Max = 0
%@ ;  Ns = [3], D = 1, Max = 3
%@ ;  Ns = [_A,_B], D = 2, Max = 2, clpz:(_A in 0..2), clpz:(2#=max(#_B,#_A)), clpz:(_B in 0..2)
%@ ;  Ns = [_A,_C,_D], D = 3, Max = 1, clpz:(_A in 0..1), clpz:(#_B#>= #_A), clpz:(#_B#=max(#_C,#_A)), clpz:(_B in 0..1), clpz:(#_B#>= #_C), clpz:(1#=max(#_D,#_B)), clpz:(_C in 0..1), clpz:(_D in 0..1)
%@ ;  ... .

%?- n_d_max(Ns, D, Max), label(Ns).
%@    Ns = [0], D = 1, Max = 0
%@ ;  Ns = [1], D = 1, Max = 1
%@ ;  Ns = [0,0], D = 2, Max = 0
%@ ;  Ns = [2], D = 1, Max = 2
%@ ;  Ns = [0,1], D = 2, Max = 1
%@ ;  Ns = [1,0], D = 2, Max = 1
%@ ;  Ns = [1,1], D = 2, Max = 1
%@ ;  Ns = [0,0,0], D = 3, Max = 0
%@ ;  Ns = [3], D = 1, Max = 3
%@ ;  Ns = [0,2], D = 2, Max = 2
%@ ;  Ns = [1,2], D = 2, Max = 2
%@ ;  Ns = [2,0], D = 2, Max = 2
%@ ;  Ns = [2,1], D = 2, Max = 2
%@ ;  Ns = [2,2], D = 2, Max = 2
%@ ;  Ns = [0,0,1], D = 3, Max = 1
%@ ;  Ns = [0,1,0], D = 3, Max = 1
%@ ;  ... .

%?- n_d_max([3], D, Max).
%@    D = 1, Max = 3.

/*
?- L+\(findall(Ns, (Max in 0..5,
                    n_d_max(Ns, 2, Max),
                    label(Ns)), Nss),
       length(Nss, L)).
%@    L = 36.
*/

%?- L+\(findall(Ns, (n_d_max(Ns, 2, 5), label(Ns)), Nss), length(Nss, L)).
%@    L = 11.
%?- L+\(setof(Ns, (n_d_max(Ns, 2, 5), label(Ns)), Nss), length(Nss, L)).
%@    L = 11.

%?- L+\(findall(Ns, (n_d_sum(Ns, 2, 5), label(Ns)), Nss), length(Nss, L)).
%@    L = 6.
%?- L+\(setof(Ns, (n_d_sum(Ns, 2, 5), label(Ns)), Nss), length(Nss, L)).
%@    L = 6.

%?- n_d_sum(Ns, 2, 5), label(Ns).
%@    Ns = [0,5]
%@ ;  Ns = [1,4]
%@ ;  Ns = [2,3]
%@ ;  Ns = [3,2]
%@ ;  Ns = [4,1]
%@ ;  Ns = [5,0].

%?- n_d_max(Ns, 2, 5), label(Ns).
%@    Ns = [0,5]
%@ ;  Ns = [1,5]
%@ ;  Ns = [2,5]
%@ ;  Ns = [3,5]
%@ ;  Ns = [4,5]
%@ ;  Ns = [5,0]
%@ ;  Ns = [5,1]
%@ ;  Ns = [5,2]
%@ ;  Ns = [5,3]
%@ ;  Ns = [5,4]
%@ ;  Ns = [5,5].

%?- I^D^Ns+\(#D #=< 3, #I #= #D + #Sum, n_d_sum(Ns, D, Sum)).
%@    I = 1, D = 1, Ns = [0]
%@ ;  I = 2, D = 1, Ns = [1]
%@ ;  I = 2, D = 2, Ns = [0,0]
%@ ;  I = 3, D = 1, Ns = [2]
%@ ;  I = 3, D = 2, Ns = [_A,_B], clpz:(_A in 0..1), clpz:(#_A+ #_B#=1), clpz:(_B in 0..1)
%@ ;  I = 3, D = 3, Ns = [0,0,0]
%@ ;  I = 4, D = 1, Ns = [3]
%@ ;  I = 4, D = 2, Ns = [_A,_B], clpz:(_A in 0..2), clpz:(#_A+ #_B#=2), clpz:(_B in 0..2)
%@ ;  I = 4, D = 3, Ns = [_A,_B,_C], clpz:(_A in 0..1), clpz:(#_A+ #_B+ #_C#=1), clpz:(_B in 0..1), clpz:(_C in 0..1)
%@ ;  ... .

%?- I^D^Ns+\(#I #< 6, #I #= #D + #Sum, n_d_sum(Ns, D, Sum)).
%@    I = 1, D = 1, Ns = [0]
%@ ;  I = 2, D = 1, Ns = [1]
%@ ;  I = 2, D = 2, Ns = [0,0]
%@ ;  I = 3, D = 1, Ns = [2]
%@ ;  I = 3, D = 2, Ns = [_A,_B], clpz:(_A in 0..1), clpz:(#_A+ #_B#=1), clpz:(_B in 0..1)
%@ ;  I = 3, D = 3, Ns = [0,0,0]
%@ ;  I = 4, D = 1, Ns = [3]
%@ ;  I = 4, D = 2, Ns = [_A,_B], clpz:(_A in 0..2), clpz:(#_A+ #_B#=2), clpz:(_B in 0..2)
%@ ;  I = 4, D = 3, Ns = [_A,_B,_C], clpz:(_A in 0..1), clpz:(#_A+ #_B+ #_C#=1), clpz:(_B in 0..1), clpz:(_C in 0..1)
%@ ;  I = 4, D = 4, Ns = [0,0,0,0]
%@ ;  I = 5, D = 1, Ns = [4]
%@ ;  I = 5, D = 2, Ns = [_A,_B], clpz:(_A in 0..3), clpz:(#_A+ #_B#=3), clpz:(_B in 0..3)
%@ ;  I = 5, D = 3, Ns = [_A,_B,_C], clpz:(_A in 0..2), clpz:(#_A+ #_B+ #_C#=2), clpz:(_B in 0..2), clpz:(_C in 0..2)
%@ ;  I = 5, D = 4, Ns = [_A,_B,_C,_D], clpz:(_A in 0..1), clpz:(#_A+ #_B+ #_C+ #_D#=1), clpz:(_B in 0..1), clpz:(_C in 0..1), clpz:(_D in 0..1)
%@ ;  I = 5, D = 5, Ns = [0,0,0,0,0]
%@ ;  false.
