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
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(lambda)).
:- use_module(library(time)).

clpz:monotonic.

n_d_sum(Ns, D, Sum) :-
    n_d_norm(Ns, D, Sum),
    Ns ins 0..Sum,
    sum(Ns, #=, Sum),
    label(Ns).

n_d_max(Ns, D, Max) :-
    n_d_norm(Ns, D, Max),
    Ns ins 0..Max,
    label(Ns).

n_d_norm(Ns, D, Norm) :-
    [I,D] ins 1..1_000, % '1..sup'
    #I #= #Norm + #D, % index I penalizes Norm and D _jointly_
    D #=< I, % sharply curtail growth of *dimension* D
    label([I,D]),
    length(Ns, D).


%?- L+\(findall(Ns, n_d_max(Ns, 2, 5), Nss), length(Nss, L)).
%@    L = 36.

%?- n_d_max(Ns, 2, 3).
%@    Ns = [0,0]
%@ ;  Ns = [0,1]
%@ ;  Ns = [0,2]
%@ ;  Ns = [0,3]
%@ ;  Ns = [1,0]
%@ ;  Ns = [1,1]
%@ ;  Ns = [1,2]
%@ ;  Ns = [1,3]
%@ ;  Ns = [2,0]
%@ ;  Ns = [2,1]
%@ ;  Ns = [2,2]
%@ ;  Ns = [2,3]
%@ ;  Ns = [3,0]
%@ ;  Ns = [3,1]
%@ ;  Ns = [3,2]
%@ ;  Ns = [3,3].


%?- L+\(findall(Ns, n_d_sum(Ns, 2, 5), Nss), length(Nss, L)).
%@    L = 6.

%?- n_d_sum(Ns, 2, 5).
%@    Ns = [0,5]
%@ ;  Ns = [1,4]
%@ ;  Ns = [2,3]
%@ ;  Ns = [3,2]
%@ ;  Ns = [4,1]
%@ ;  Ns = [5,0].

%?- I^D^Ns+\(#D #=< 3, #I #= #D + #Sum, n_d_sum(Ns, D, Sum)).
%@    I = 1, D = 1, Ns = [0]
%@ ;  I = 2, D = 1, Ns = [1]
%@ ;  I = 2, D = 2, Ns = [0,0]
%@ ;  I = 3, D = 1, Ns = [2]
%@ ;  I = 3, D = 2, Ns = [0,1]
%@ ;  I = 3, D = 2, Ns = [1,0]
%@ ;  I = 3, D = 3, Ns = [0,0,0]
%@ ;  I = 4, D = 1, Ns = [3]
%@ ;  I = 4, D = 2, Ns = [0,2]
%@ ;  I = 4, D = 2, Ns = [1,1]
%@ ;  I = 4, D = 2, Ns = [2,0]
%@ ;  I = 4, D = 3, Ns = [0,0,1]
%@ ;  I = 4, D = 3, Ns = [0,1,0]
%@ ;  I = 4, D = 3, Ns = [1,0,0]
%@ ;  I = 5, D = 1, Ns = [4]
%@ ;  I = 5, D = 2, Ns = [0,3]
%@ ;  I = 5, D = 2, Ns = [1,2]
%@ ;  I = 5, D = 2, Ns = [2,1]
%@ ;  I = 5, D = 2, Ns = [3,0]
%@ ;  I = 5, D = 3, Ns = [0,0,2]
%@ ;  I = 5, D = 3, Ns = [0,1,1]
%@ ;  I = 5, D = 3, Ns = [0,2,0]
%@ ;  I = 5, D = 3, Ns = [1,0,1]
%@ ;  I = 5, D = 3, Ns = [1,1,0]
%@ ;  I = 5, D = 3, Ns = [2,0,0]
%@ ;  I = 6, D = 1, Ns = [5]
%@ ;  I = 6, D = 2, Ns = [0,4]
%@ ;  I = 6, D = 2, Ns = [1,3]
%@ ;  I = 6, D = 2, Ns = [2,2]
%@ ;  I = 6, D = 2, Ns = [3,1]
%@ ;  I = 6, D = 2, Ns = [4,0]
%@ ;  I = 6, D = 3, Ns = [0,0,3]
%@ ;  I = 6, D = 3, Ns = [0,1,2]
%@ ;  I = 6, D = 3, Ns = [0,2,1]
%@ ;  I = 6, D = 3, Ns = [0,3,0]
%@ ;  I = 6, D = 3, Ns = [1,0,2]
%@ ;  I = 6, D = 3, Ns = [1,1,1]
%@ ;  I = 6, D = 3, Ns = [1,2,0]
%@ ;  I = 6, D = 3, Ns = [2,0,1]
%@ ;  I = 6, D = 3, Ns = [2,1,0]
%@ ;  I = 6, D = 3, Ns = [3,0,0]
%@ ;  I = 7, D = 1, Ns = [6]
%@ ;  I = 7, D = 2, Ns = [0,5]
%@ ;  ... .

%?- I^D^Ns+\(#I #< 6, #I #= #D + #Sum, n_d_sum(Ns, D, Sum)).
%@    I = 1, D = 1, Ns = [0]
%@ ;  I = 2, D = 1, Ns = [1]
%@ ;  I = 2, D = 2, Ns = [0,0]
%@ ;  I = 3, D = 1, Ns = [2]
%@ ;  I = 3, D = 2, Ns = [0,1]
%@ ;  I = 3, D = 2, Ns = [1,0]
%@ ;  I = 3, D = 3, Ns = [0,0,0]
%@ ;  I = 4, D = 1, Ns = [3]
%@ ;  I = 4, D = 2, Ns = [0,2]
%@ ;  I = 4, D = 2, Ns = [1,1]
%@ ;  I = 4, D = 2, Ns = [2,0]
%@ ;  I = 4, D = 3, Ns = [0,0,1]
%@ ;  I = 4, D = 3, Ns = [0,1,0]
%@ ;  I = 4, D = 3, Ns = [1,0,0]
%@ ;  I = 4, D = 4, Ns = [0,0,0,0]
%@ ;  I = 5, D = 1, Ns = [4]
%@ ;  I = 5, D = 2, Ns = [0,3]
%@ ;  I = 5, D = 2, Ns = [1,2]
%@ ;  I = 5, D = 2, Ns = [2,1]
%@ ;  I = 5, D = 2, Ns = [3,0]
%@ ;  I = 5, D = 3, Ns = [0,0,2]
%@ ;  I = 5, D = 3, Ns = [0,1,1]
%@ ;  I = 5, D = 3, Ns = [0,2,0]
%@ ;  I = 5, D = 3, Ns = [1,0,1]
%@ ;  I = 5, D = 3, Ns = [1,1,0]
%@ ;  I = 5, D = 3, Ns = [2,0,0]
%@ ;  I = 5, D = 4, Ns = [0,0,0,1]
%@ ;  I = 5, D = 4, Ns = [0,0,1,0]
%@ ;  I = 5, D = 4, Ns = [0,1,0,0]
%@ ;  I = 5, D = 4, Ns = [1,0,0,0]
%@ ;  I = 5, D = 5, Ns = [0,0,0,0,0]
%@ ;  false.
