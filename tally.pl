% tally.pl
% Basic utilities for tally generation, esp. fair enumeration
/*
:- module(tally, [
              qs_d_nmax/3
	  ]).
*/
:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(lambda)).
:- use_module(library(time)).

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

% TODO:
% I would really like to dispense with explicit enumeration,
% in favor of basic predicates that work in all directions.
% Ideally, these could even abstract away the 'd_*' prefix
% that sullies so many predicates.

% Thus, to begin, I would like to have a predicate q/1
% that fairly enumerates ALL tallies having ANY VALUE OF D.
% This means fairly enumerating over the [disjoint] union
%
%               Q¹ ⊔ Q² ⊔ ... ⊔ Q⁸ (say).
%
% As needed, this enumeration could be further constrained
% by additional goal(s) preceding q/1, as in
%
%                ?- length(Q,3), q(Q).
%
% The first ingredient for this is fairly enumerating over
%
%                ℕ¹ ⊔ ℕ² ⊔ ... ⊔ ℕ⁸.
%
% Let me accomplish this with a predicate n_d/2.

% Being *by design* non-terminating, this predicate must
% expose 'hooks' allowing client code to force termination.
% The only such 'hooks' in Prolog are of course: _arguments_.
% Besides the obligatory D, the 2 most natural single logical
% variables I could expose would be the ℓ¹ and ℓ⁰ norms --
% respectively the sum and maximum of Ns.
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