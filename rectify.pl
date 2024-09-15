% rectify.pl
% Experiments with 'rectifying' dose-escalation protocols
% so they become *dose-monotonic*.

% Def 2.9, implemented via Fact 2.16
% Def 2.9, implemented via Fact 2.13
%'≼'/2,
:- module(rectify, [
              op(900, xfx, '≼'),
              %('≼')/2, % => syntax_error(invalid_module_declaration)
	      op(900, xfx, =<$),
	      (=<$)/2,
	      (=<$)/3
	  ]).

:- use_module(library(clpz)).
:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(time)).
:- use_module(library(debug)).
:- use_module(library(dif)).
:- use_module(library(reif)).
:- use_module(library(lambda)).
:- use_module(library(error)).
:- use_module(library(pio)).
:- use_module(library(format)).

clpz:monotonic.

:- op(900, xfx, '≤'). % Mutually exclusive infix
:- op(900, xfx, '≰'). % relations defined on ℕᴰ.

Xs '≤' Ys :-
    same_length(Xs, Ys),
    length(Xs, D), D #> 0,
    %maplist(#=<(0), Xs), % I get instantiation_error's here, as if
    %maplist(#=<(0), Ys), % each element demands to be #'ed separately.
    maplist(\X^(#X #>= 0), Xs), % Why must I do these in monotonic mode, instead
    maplist(\Y^(#Y #>= 0), Ys), % of the above?  I thought this used to work!
    maplist(#=<, Xs, Ys). % NB: 0 ≤ Xs ≤ Ys ⟹ 0 ≤ Ys as well

%?- [] '≤' [].
%@    false. % CORRECT

%?- [2] '≤' [3].
%@    true.

%?- [3] '≤' [2].
%@    false.

%?- [2,3] '≤' [3,2].
%@    false.

%?- [2,3] '≤' [3,X].
%@    clpz:(X in 3..sup).

%?- [2,3] '≤' [3,#X]. % NB: This works fine with the maplist(#=<(0), _)'s above.
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


% Note that we must provide a dedicated implementation for ≰
% because we cannot *safely* apply negation-as-failure to ≤.
'≰'([X], [Y]) :- #X #> #Y, #Y #>= 0.
'≰'([X|Xs], [Y|Ys]) :-
    same_length(Xs, Ys),
    length(Xs, D), D #> 0,
    %maplist(#=<(0), Xs), % Same story
    %maplist(#=<(0), Ys), % as above.
    maplist(\Xi^(#Xi #>= 0), [X|Xs]),
    maplist(\Yi^(#Yi #>= 0), [Y|Ys]),
    % (The foregoing ensures both args are in ℕᴰ for some D≥1.)
    (   #X #> #Y
    ;   Xs '≰' Ys % TODO: Render this more efficient with if_/3?
    ).

%?- [1,1,1] '≰' Xs.
%@    Xs = [0,_A,_B], clpz:(_A in 0..sup), clpz:(_B in 0..sup)
%@ ;  Xs = [_A,0,_B], clpz:(_A in 0..sup), clpz:(_B in 0..sup)
%@ ;  Xs = [_A,_B,0], clpz:(_A in 0..sup), clpz:(_B in 0..sup)
%@ ;  false.

% Observe now that, having done this, we obtain a reified version of ≤
'≤'(Xs, Ys, true) :- Xs '≤' Ys.
'≤'(Xs, Ys, false) :- Xs '≰' Ys.

%% 1. Via Fact 2.13, define evident-$afety relation ≼ ⊂ 𝒬✕𝒬:
:- op(900, xfx, =<$).
:- op(900, xfx, =/<$). % negation of above

qs_Ts_Us(Qs, ΣTs, ΣUs) :-
    maplist(\Q^T^U^(q_r(Q, T:U)), Qs, Ts, Us),
    intlist_partsums(Ts, ΣTs),
    intlist_partsums(Us, ΣUs).

%?- qs_Ts_Us([1/6,2/6], Ts, Us).
%@    Ts = [1,3], Us = [5,9].

=<$(Q1s, Q2s) :-
    qs_Ts_Us(Q1s, ST1s, SU1s),
    qs_Ts_Us(Q2s, ST2s, SU2s),
    ST2s '≤' ST1s, %maplist(#>=, ST1s, ST2s),
    SU1s '≤' SU2s. %maplist(#=<, SU1s, SU2s).

=/<$(Q1s, Q2s) :-
    qs_Ts_Us(Q1s, ST1s, SU1s),
    qs_Ts_Us(Q2s, ST2s, SU2s),
    ST2s '≰' ST1s,
    SU1s '≰' SU2s.

% And now, importantly for (e.g.) pure construction of transitive reduction,
% we obtain the reified version (=<$)/3:
=<$(Q1s, Q2s, true) :- Q1s =<$ Q2s.
=<$(Q1s, Q2s, false) :- Q1s =/<$ Q2s.

%% Allow the notational convenience of a 'flippable' preorder symbol:
:- op(900, xfx, $>=).
$>=(Q1, Q2) :- =<$(Q2, Q1).

%% Utility predicates used above:

qs_ts_us(Qs, Ts, Us) :-
    maplist(\Q^T^U^(Q = T/N, #U #= N - T), Qs, Ts, Us),
    maplist(\T^(#T #>= 0), Ts),
    maplist(\U^(#U #>= 0), Us).

intlist_partsums([X|Xs], [X|Ss]) :-
    intlist_partsums_acc(Xs, Ss, X).

intlist_partsums_acc([], [], _).
intlist_partsums_acc([X|Xs], [S|Ss], A) :-
    #S #= #X + #A,
    intlist_partsums_acc(Xs, Ss, S).

%?- [1/3, 1/2] =<$ [0/4, 0/1].
%@    true.
%@    true.

%?- [1/6,1/6] =<$ [0/6,2/6].
%@    true.
%@    true.

%?- [1/6,1/6] =<$ [0/6,2/5].
%@    false.
%@    false.

%?- [1/6,1/6] =<$ [0/6,2/7].
%@    true.
%@    true.

%?- [0/6,2/6] $>= [1/6,1/6].
%@    true.
%@    true.

% 2. Note that a recursive implementation is possible, which might
%    conceivably fail earlier & faster in big searches.
qs_sum1([T1/N1, T2/N2 | Qs], [T12/N12 | Qs]) :-
    #T12 #= #T1 + #T2,
    #N12 #= #N1 + #N2.

lesaf([Q1|Q1s], [Q2|Q2s]) :-
    [Q1] =<$ [Q2],
    lesaf_([Q1|Q1s], [Q2|Q2s]).
lesaf_([_], [_]). % nothing to do!
lesaf_([Q1,Q1b|Q1s], [Q2,Q2b|Q2s]) :-
    qs_sum1([Q1,Q1b|Q1s], Q1s_),
    qs_sum1([Q2,Q2b|Q2s], Q2s_),
    lesaf_(Q1s_, Q2s_).

%?- lesaf_([], []).
%@    false.
%@    false.

%?- [1/6] =<$ [0/6].
%@    true.
%@    true.

%?- lesaf([1/6,1/6], [0/6,2/6]).
%@    true
%@ ;  false.

% 2b. Implement ≼ via Fact 2.16 -- Eq (6)

/* Implementation notes:

We have two nested conditions, whereby we say,

Q1 ≼ Q2 iff ∃ Q, Q' : Q1 ≼_cel Q ≼_dm Q' ≼_cer Q2,

with ≼_cel and ≼_cer being the left- and right-hand sides
of the ≼_ce relation, respectively.

Unlike the ≼_ce relation, ≼_dm regards an *exchange* which
cannot be separated into a LHS and RHS.  (Note how the η's
are inherently *paired* across the 2 sides of ≼_dm.)

(At least at the level of *implementation*, it appears that
the single ≼_ce relation I have thus far written up might
best be thought of as separate ≼_cel and ≼_cer relations.)

*/

:- op(900, xfx, '≼l'). % LHS of Eq (3) in Def 2.2
:- op(900, xfx, '≼r'). % RHS of Eq (3) in Def 2.2

'≼l'(Ql, Q) :- q_r(Ql, Tl:U), q_r(Q, T:U), Tl #>= T.
'≼r'(Q, Qr) :- q_r(Q, T:U), q_r(Qr, T:Ur), Ur #>= U.

:- op(900, xfx, '≼cel'). % λ terms of Eq (6) in Fact 2.16
:- op(900, xfx, '≼cer'). % γ terms of Eq (6) in Fact 2.16

'≼cel'(Q1, Q2) :- same_length(Q1, Q2), maplist('≼l', Q1, Q2).
'≼cer'(Q1, Q2) :- same_length(Q1, Q2), maplist('≼r', Q1, Q2).

:- op(900, xfx, '≼dm'). % Dose-Monotonicity condition of Def 2.7
:- op(900, xfx, '≼'). % Def 2.9, implemented via Fact 2.16

% Now, let's write out the R-representation of Notation 2.8;
% observe that the inherently 2-D 'shape' of this relation
% does not allow for the same maplist/3-based implementation
% we enjoyed with ≼_ce.
'≼dm'(Q1, Q2) :-
    same_length(Q1, Q2),
    maplist(q_r, Q1, [R1|R1s]),
    maplist(q_r, Q2, [R2|R2s]),
    enst_dm_r([R1|R1s], [R2|R2s]).

% Utility predicate in the R-representation, to be used recursively:
enst_dm_r([R], [R]) :- q_r(_, R). % D=1 ==> exchange collapses
    
enst_dm_r([R1|R1s], [R2|R2s]) :-
    length(R1s, Dminus1), Dminus1 #> 0, % exclude D=1 base-case handled above
    same_length(R1s, R2s),
    same_length(R1s, Hs), maplist(\H^(#H #>= 0), Hs), % ∃ η₁ₖ ∈ ℕ, 1<k≤D
    % Post constraints on the d=1 component first..
    q_r(_, R1), R1 = T1:U1,
    q_r(_, R2), R2 = T2:U2,
    sum([T2|Hs], #=, #T1),
    sum([U1|Hs], #=, #U2),
    % ..and then on the 2≤d≤D components:
    maplist(\H^R^Rh^(   R = T:U,
                        Rh= T:Uh,
                        #U #= #Uh + #H
                    ), Hs, R1s, R1hats),
    maplist(\H^R^Rh^(   R = T:U,
                        Rh= Th:U,
                        #T #= #Th + #H
                    ), Hs, R2s, R2hats),
    enst_dm_r(R1hats, R2hats).

% Let's make sure to construct a *true* case of this exchange relation:
% - R = [0/5,1/5]
% - H12 = 1
% - R1 = [0/5,1/5] + [1/1,0/1] = [1/6,1/6]
% - R2 = [0/5,1/5] + [0/1,1/1] = [0/6,2/6].

%?- '≼dm'([1/6, 1/6], [0/6, 2/6]).
%@    true
%@ ;  false. % TODO: Find the choice-point; can I eliminate it?

%?- enst_dm_r([1:5, 1:5], [0:6, 2:4]).
%@    true
%@ ;  false.


% Let's exhibit the *reason* why same_length/2 is needed to ensure termination:
:- op(900, xfx, '≼dm∞').
'≼dm∞'(Q1, Q2) :- % Same as ≼dm above, except for ..
    same_length(Q1, Q2), % .. removal of this goal,
    % and inclusion of some instrumentation:
    length(Q1, L1), length(Q2, L2),
    format("Checking if X ≼dm Y, with length-~d X and length-~d Y..~n", [L1,L2]),
    sleep(1),
    maplist(q_r, Q1, [R1|R1s]),
    maplist(q_r, Q2, [R2|R2s]),
    enst_dm_r([R1|R1s], [R2|R2s]).

%?- [0/6,A/B] '≼dm∞' Q, false. % With same_length/2 goal restored
%@ Checking if X ≼dm Y, with length-2 X and length-2 Y..
%@    false.
%@ Checking if X ≼dm Y, with length-2 X and length-0 Y..
%@ Checking if X ≼dm Y, with length-2 X and length-1 Y..
%@ Checking if X ≼dm Y, with length-2 X and length-2 Y..
%@ Checking if X ≼dm Y, with length-2 X and length-3 Y..
%@ Checking if X ≼dm Y, with length-2 X and length-4 Y..
%@ Checking if X ≼dm Y, with length-2 X and length-5 Y..
%@    error('$interrupt_thrown',repl/0).

% What should the bindings be?  We ought to have:
% - R =  0:5, Rs  = [1:4],
% - R2 = 0:6, R2s = [2:4],
% - R1 = 1:5, R1s = [1:5],
% - Dminus1 = 1,
% - Hs = [1],
% - T  = 0, U = 5 (from R = T:U)
% - T1 = 1, U = 5 (from R1 = T1:U)
% - T  = 0, U2 = 6 (from R2 = T:U2)
% (So far, so good -- and indeed, the predicate does succeed this far.)
% But now what about the hats?  NB in what follows, T,U are *local* vars...
% - R1s = [T:U], R1hats = [T:Uh], U=Uh+H ==> T=1, U=5, Uh=4 ==> R1hats = [1:4]
% - R2s = [T:U], R2hats = [Th,U], T=Th+H ==> T=2, U=4, Th=1 ==> R2hats = [1:4].
% Finally, the recursive condition should give us Rs = R1hats = R2hats = [1:4].

%?- enst_dm_r([1:4], [1:4]).
%@    true
%@ ;  false.

'≼'(Q1, Q2) :-
    Q1 '≼cel' Qa,
    Qa '≼dm' Qb,
    Qb '≼cer' Q2.

%?- [0/6, 2/6] '≼' [1/6, 1/6].
%@    false.

%?- [1/6, 1/6] '≼' [0/6, 2/6].
%@    true
%@ ;  false.

% TODO: Demonstrate, by a non-terminating and fairly-enumerated search,
%       that '≼' (Fact 2.16) is equivalent to =<$ (Fact 2.13).

% Does '≼' do any fair enumeration of its own?
%?- Q = [T1/N1, T2/N2], maplist(q_r, Q, _).
%@    Q = [T1/N1,T2/N2], clpz:(T1 in 0..sup), clpz:(#_A+ #T1#= #N1), clpz:(#N1#>= #T1), clpz:(N1 in 0..sup), clpz:(T2 in 0..sup), clpz:(#_B+ #T2#= #N2), clpz:(#N2#>= #T2), clpz:(N2 in 0..sup).
%?- Q = [T1/N1, T2/N2], maplist(q_r, Q, _), label([T1,N1,T2,N2]).
%@    error(instantiation_error,instantiation_error(unknown(from_to(n(0),sup)),1)).
%?- #T1 #> 0, #N1 #> 0, T1 #< 4, N1 #< 4, label([T1,N1]).
%@    T1 = 1, N1 = 1
%@ ;  T1 = 1, N1 = 2
%@ ;  T1 = 1, N1 = 3
%@ ;  ... .

% This is easy to appreciate: I can't label unless the domain is truly finite.
% So it would seem a *norm* relation could help.
qs_d(Qs, D) :-
    length(Qs, D),
    maplist(q_r, Qs, _).

qs_d_totn(Qs, D, Nsum) :-
    qs_d(Qs, D),
    maplist(\Q^N^(Q = _/N), Qs, Ns),
    sum(Ns, #=, #Nsum).

%?- qs_d_totn(Q, 2, 6), Q = [T1/N1, T2/N2], label([T1,N1,T2,N2]).
%@    Q = [0/0,0/6], T1 = 0, N1 = 0, T2 = 0, N2 = 6
%@ ;  Q = [0/0,1/6], T1 = 0, N1 = 0, T2 = 1, N2 = 6
%@ ;  Q = [0/0,2/6], T1 = 0, N1 = 0, T2 = 2, N2 = 6
%@ ;  Q = [0/0,3/6], T1 = 0, N1 = 0, T2 = 3, N2 = 6
%@ ;  Q = [0/0,4/6], T1 = 0, N1 = 0, T2 = 4, N2 = 6
%@ ;  Q = [0/0,5/6], T1 = 0, N1 = 0, T2 = 5, N2 = 6
%@ ;  ... .

% Although in *applications* I will generally deal with _fixed_ D,
% for *testing* purposes it will be helpful to have a 'norm' notion
% that applies _across_ D values, partitioning the space 𝒬¹∪𝒬²∪𝒬³∪...
% into a nested sequence of larger-and-larger compact subsets.
% I believe that simply 'penalizing' Q ∈ 𝒬ᴰ jointly on Nsum+D
% will do the trick.  Note that the norm is
qs_norm(Qs, Norm) :-
    D in 1..Norm, indomain(D),
    qs_d_totn(Qs, D, Nsum),
    #Norm #= D + Nsum.

%?- qs_norm(Qs, 0).
%@    false. % NB: D in 1..Norm purposely excludes Qs = [] case.

%?- qs_norm(Qs, 3).
%@    Qs = [_A/2], clpz:(_A in 0..2), clpz:(#_A+ #_B#=2), clpz:(_B in 0..2)
%@ ;  Qs = [_A/_C,_E/_D], clpz:(_A in 0..1), clpz:(#_A+ #_B#= #_C), clpz:(_B in 0..1), clpz:(_C in 0..1), clpz:(#_C+ #_D#=1), clpz:(_D in 0..1), clpz:(#_E+ #_F#= #_D), clpz:(_E in 0..1), clpz:(_F in 0..1)
%@ ;  Qs = [0/0,0/0,0/0].

testpo(Range1, Range2) :-
    Norm1 in Range1, indomain(Norm1),
    Norm2 in Range2, indomain(Norm2),
    qs_norm(Q1, Norm1),
    qs_norm(Q2, Norm2),
    Q1 '≼' Q2,   % Of course, I'll need to check as well for the
    Q1 =/<$ Q2.  % converse error, where Q1 =<$ Q2 yet Q1 '⋠' Q2.

%?- testpo(1..2, 1..2).
%@    false.

%?- testpo(1..2, 1..3).
%@    false.

%?- testpo(1..3, 1..2).
%@    false.

%?- testpo(3, 3).
%@    clpz:(_A in 0..1), clpz:(#_B+ #_A#= #_C), clpz:(#_A+ #_D#= #_E), clpz:(#_A#>= #_F), clpz:(#_A+ #_G#= #_E), clpz:(#_A+ #_H#= #_E), clpz:(_B in 0..1), clpz:(#_B+ #_I#= #_J), clpz:(#_B#>= #_K), clpz:(#_B+ #_L#= #_J), clpz:(#_B+ #_M#= #_J), clpz:(_I in 0..1), clpz:(#_I+ #_D#= #_N), clpz:(_D in 0..1), clpz:(_E in 0..1), clpz:(#_E+ #_J#=1), clpz:(_G in 0..1), clpz:(#_F+ #_G#= #_O), clpz:(_F in 0..1), clpz:(#_P+ #_Q#= #_F), clpz:(#_F+ #_R#= #_S), clpz:(#_F+ #_R#= #_O), clpz:(_P in 0..1), clpz:(#_T+ #_P#= #_U), clpz:(#_P+ #_V#= #_W), clpz:(#_P+ #_X#= #_W), clpz:(#_P+ #_Y#= #_Z), clpz:(#_P+ #_A1#= #_B1), clpz:(#_P+ #_A1#= #_Z), clpz:(#_P+ #_C1#= #_W), clpz:(_T in 0..1), clpz:(#_T+ #_D1#= #_E1), clpz:(#_T+ #_F1#= #_E1), clpz:(#_T+ #_G1#= #_H1), clpz:(#_K+ #_Q#= #_T), clpz:(#_T+ #_I1#= #_H1), clpz:(#_T+ #_J1#= #_E1), clpz:(_D1 in 0..1), clpz:(#_D1+ #_V#= #_K1), clpz:(_V in 0..1), clpz:(_W in 0..1), clpz:(#_W+ #_E1#=1), clpz:(_X in 0..1), clpz:(#_X#>= #_Y), clpz:(_Y in 0..1), clpz:(_Q in 0..1), clpz:(#_I1+ #_Q#= #_L1), clpz:(#_R+ #_Q#= #_A1), clpz:(_K in 0..1), clpz:(#_K+ #_I1#= #_M1), clpz:(#_K+ #_L1#= #_N1), clpz:(#_K+ #_L#= #_N1), clpz:(_I1 in 0..2), clpz:(_L1 in 0..2), clpz:(_N1 in 0..2), clpz:(_L in 0..1), clpz:(_J in 0..1), clpz:(_M in 0..1), clpz:(_H1 in 0..2), clpz:(_G1 in 0..1), clpz:(#_F1#>= #_G1), clpz:(_F1 in 0..1), clpz:(_E1 in 0..1), clpz:(_J1 in 0..1), clpz:(_M1 in 0..3), clpz:(_R in 0..2), clpz:(_A1 in 0..2), clpz:(_B1 in 0..3), clpz:(_Z in 0..2), clpz:(_S in 0..3), clpz:(_O in 0..2), clpz:(_C1 in 0..1), clpz:(_K1 in 0..1), clpz:(#_K1#=< #_N+ -1), clpz:(_N in 1..2), clpz:(_U in 1..2), clpz:(#_C#=< #_U+ -1), clpz:(_C in 0..1), clpz:(_H in 0..1)
%@ ;  false.

%?- testpo(3, 1..3).
%@    clpz:(_A in 0..1), clpz:(#_B+ #_A#= #_C), clpz:(#_A+ #_D#= #_E), clpz:(#_A#>= #_F), clpz:(#_A+ #_G#= #_E), clpz:(#_A+ #_H#= #_E), clpz:(_B in 0..1), clpz:(#_B+ #_I#= #_J), clpz:(#_B#>= #_K), clpz:(#_B+ #_L#= #_J), clpz:(#_B+ #_M#= #_J), clpz:(_I in 0..1), clpz:(#_I+ #_D#= #_N), clpz:(_D in 0..1), clpz:(_E in 0..1), clpz:(#_E+ #_J#=1), clpz:(_G in 0..1), clpz:(#_F+ #_G#= #_O), clpz:(_F in 0..1), clpz:(#_P+ #_Q#= #_F), clpz:(#_F+ #_R#= #_S), clpz:(#_F+ #_R#= #_O), clpz:(_P in 0..1), clpz:(#_T+ #_P#= #_U), clpz:(#_P+ #_V#= #_W), clpz:(#_P+ #_X#= #_W), clpz:(#_P+ #_Y#= #_Z), clpz:(#_P+ #_A1#= #_B1), clpz:(#_P+ #_A1#= #_Z), clpz:(#_P+ #_C1#= #_W), clpz:(_T in 0..1), clpz:(#_T+ #_D1#= #_E1), clpz:(#_T+ #_F1#= #_E1), clpz:(#_T+ #_G1#= #_H1), clpz:(#_K+ #_Q#= #_T), clpz:(#_T+ #_I1#= #_H1), clpz:(#_T+ #_J1#= #_E1), clpz:(_D1 in 0..1), clpz:(#_D1+ #_V#= #_K1), clpz:(_V in 0..1), clpz:(_W in 0..1), clpz:(#_W+ #_E1#=1), clpz:(_X in 0..1), clpz:(#_X#>= #_Y), clpz:(_Y in 0..1), clpz:(_Q in 0..1), clpz:(#_I1+ #_Q#= #_L1), clpz:(#_R+ #_Q#= #_A1), clpz:(_K in 0..1), clpz:(#_K+ #_I1#= #_M1), clpz:(#_K+ #_L1#= #_N1), clpz:(#_K+ #_L#= #_N1), clpz:(_I1 in 0..2), clpz:(_L1 in 0..2), clpz:(_N1 in 0..2), clpz:(_L in 0..1), clpz:(_J in 0..1), clpz:(_M in 0..1), clpz:(_H1 in 0..2), clpz:(_G1 in 0..1), clpz:(#_F1#>= #_G1), clpz:(_F1 in 0..1), clpz:(_E1 in 0..1), clpz:(_J1 in 0..1), clpz:(_M1 in 0..3), clpz:(_R in 0..2), clpz:(_A1 in 0..2), clpz:(_B1 in 0..3), clpz:(_Z in 0..2), clpz:(_S in 0..3), clpz:(_O in 0..2), clpz:(_C1 in 0..1), clpz:(_K1 in 0..1), clpz:(#_K1#=< #_N+ -1), clpz:(_N in 1..2), clpz:(_U in 1..2), clpz:(#_C#=< #_U+ -1), clpz:(_C in 0..1), clpz:(_H in 0..1)
%@ ;  false.

%?- testpo(1..3, 1..3).
%@    clpz:(_A in 0..1), clpz:(#_B+ #_A#= #_C), clpz:(#_A+ #_D#= #_E), clpz:(#_A#>= #_F), clpz:(#_A+ #_G#= #_E), clpz:(#_A+ #_H#= #_E), clpz:(_B in 0..1), clpz:(#_B+ #_I#= #_J), clpz:(#_B#>= #_K), clpz:(#_B+ #_L#= #_J), clpz:(#_B+ #_M#= #_J), clpz:(_I in 0..1), clpz:(#_I+ #_D#= #_N), clpz:(_D in 0..1), clpz:(_E in 0..1), clpz:(#_E+ #_J#=1), clpz:(_G in 0..1), clpz:(#_F+ #_G#= #_O), clpz:(_F in 0..1), clpz:(#_P+ #_Q#= #_F), clpz:(#_F+ #_R#= #_S), clpz:(#_F+ #_R#= #_O), clpz:(_P in 0..1), clpz:(#_T+ #_P#= #_U), clpz:(#_P+ #_V#= #_W), clpz:(#_P+ #_X#= #_W), clpz:(#_P+ #_Y#= #_Z), clpz:(#_P+ #_A1#= #_B1), clpz:(#_P+ #_A1#= #_Z), clpz:(#_P+ #_C1#= #_W), clpz:(_T in 0..1), clpz:(#_T+ #_D1#= #_E1), clpz:(#_T+ #_F1#= #_E1), clpz:(#_T+ #_G1#= #_H1), clpz:(#_K+ #_Q#= #_T), clpz:(#_T+ #_I1#= #_H1), clpz:(#_T+ #_J1#= #_E1), clpz:(_D1 in 0..1), clpz:(#_D1+ #_V#= #_K1), clpz:(_V in 0..1), clpz:(_W in 0..1), clpz:(#_W+ #_E1#=1), clpz:(_X in 0..1), clpz:(#_X#>= #_Y), clpz:(_Y in 0..1), clpz:(_Q in 0..1), clpz:(#_I1+ #_Q#= #_L1), clpz:(#_R+ #_Q#= #_A1), clpz:(_K in 0..1), clpz:(#_K+ #_I1#= #_M1), clpz:(#_K+ #_L1#= #_N1), clpz:(#_K+ #_L#= #_N1), clpz:(_I1 in 0..2), clpz:(_L1 in 0..2), clpz:(_N1 in 0..2), clpz:(_L in 0..1), clpz:(_J in 0..1), clpz:(_M in 0..1), clpz:(_H1 in 0..2), clpz:(_G1 in 0..1), clpz:(#_F1#>= #_G1), clpz:(_F1 in 0..1), clpz:(_E1 in 0..1), clpz:(_J1 in 0..1), clpz:(_M1 in 0..3), clpz:(_R in 0..2), clpz:(_A1 in 0..2), clpz:(_B1 in 0..3), clpz:(_Z in 0..2), clpz:(_S in 0..3), clpz:(_O in 0..2), clpz:(_C1 in 0..1), clpz:(_K1 in 0..1), clpz:(#_K1#=< #_N+ -1), clpz:(_N in 1..2), clpz:(_U in 1..2), clpz:(#_C#=< #_U+ -1), clpz:(_C in 0..1), clpz:(_H in 0..1)
%@ ;  false.
    
% 3. Add facts to database, giving 3+3 dose recs for selected q ∈ Q^2

%% There are 14 distinct terminal states of the D=2 3+3 trial:
rec3plus3([0/3,0/6], 2). % 0,0'
rec3plus3([0/6,2/6], 1). % 0',2'
rec3plus3([0/6,3/6], 1). % 0',3'
rec3plus3([0/3,0/6], 2). % 0,1'
rec3plus3([0/6,4/6], 1). % 0',4'
rec3plus3([0/6,3/3], 1). % 0',3
rec3plus3([0/6,2/3], 1). % 0',2
rec3plus3([1/6,4/6], 1). % 1',4'
rec3plus3([1/6,3/3], 1). % 1',3
rec3plus3([1/6,2/3], 1). % 1',2
rec3plus3([1/6,2/6], 1). % 1',2'
rec3plus3([1/6,3/6], 1). % 1',3'
rec3plus3([1/6,1/6], 2). % 1',1'
rec3plus3([1/6,0/6], 2). % 1',0'

% 4. Find cases where the dose recs are inconsistent with =<$

functorfail(F, X, Y) :-
    call(F, X, Dx),
    call(F, Y, Dy),
    #Dx #> #Dy,
    X '≼' Y.
    %X =<$ Y.

%?- functorfail(rec3plus3, A, B).
%@    A = [1/6,1/6], B = [0/6,2/6]
%@ ;  false.

% 5. Add *all* next-dose recs to the database, and repeat

next3plus3([0/0,0/0], 1).
next3plus3([0/3,0/0], 2). % 1st cohort from ~,~
next3plus3([1/3,0/0], 1).
next3plus3([2/3,0/0], 0).
next3plus3([3/3,0/0], 0).
next3plus3([0/3,0/3], 2). % 2nd cohorts from 0,~
next3plus3([0/3,1/3], 2).
next3plus3([0/3,2/3], 1).
next3plus3([0/3,3/3], 1).
next3plus3([1/6,0/0], 2). % 2nd cohorts from 1,~
next3plus3([2/6,0/0], 0).
next3plus3([3/6,0/0], 0).
next3plus3([4/6,0/0], 0).
next3plus3([1/6,0/3], 2). % 3rd cohorts from 1',~
next3plus3([1/6,1/3], 2).
next3plus3([1/6,2/3], 1).
next3plus3([1/6,3/3], 1).

next3plus3(Q, D) :- rec3plus3(Q, D).

%?- functorfail(next3plus3, A, B).
%@    A = [1/6,1/3], B = [0/6,2/6]
%@ ;  A = [1/6,1/3], B = [0/6,2/3]
%@ ;  A = [1/6,1/6], B = [0/6,2/6]
%@ ;  false. % Results exactly the same with '≼' in place of =<$ in functorfail/3.
%@    A = [1/6,1/3], B = [0/6,2/6]
%@ ;  A = [1/6,1/3], B = [0/6,2/3]
%@ ;  A = [1/6,1/6], B = [0/6,2/6]
%@ ;  false.

% Ah, interesting!  So there are in fact 2 chains here:
%   [1/6,1/3] ≼ [1/6,1/6] ≼ [0/6,2/6],
%   [1/6,1/3] ≼ [1/6,2/3] ≼ [0/6,2/3].
%               \_______/
%                   |
% But the middle elements are not comparable.

%?- _+\(A=[1/6,1/3], B1=[1/6,1/6], A =<$ B1).
%@    true.

%?- _+\(A=[1/6,1/3], B1=[1/6,1/6], C=[0/6,2/6], A =<$ B1, B1 =<$ C).
%@    true.
%?- _+\(A=[1/6,1/3], B2=[0/6,2/3], C=[0/6,2/6], A =<$ B2, B2 =<$ C).
%@    true.
% But note that B1 and B2 are incomparable:
%?- _+\(B1=[1/6,1/6], B2 = [0/6,2/3], (B1 =<$ B2; B2 =<$ B1)).
%@    false. % neither B1 ≼ B2 nor B2 ≼ B1 holds

% This demonstrates, in particular, that =<$ is not a total order.

% From here forward, probably a focused adaptation of the 3+3 design
% will yield the fastest progress:

% But before undertaking this adaptation, I need to get the needed free
% constructions under my belt, and do proper *experimental* work on the
% enlargement of these monoidal preorders.

% 6a. Demonstrate that I can generate the preorder on Q as per Defn 2.2.
%     This means in particular, showing that a preorder equivalent to
%     that given by Fact 2.3 arises out of a simple Prolog program that
%     asserts the elemental facts generating ≼, i.e. both sides of Eq (1).

% --- See https://stackoverflow.com/q/26946133/3338147 -------
:- meta_predicate closure0(2,?,?).
:- meta_predicate closure(2,?,?).

:- meta_predicate closure0(2,?,?,+). % internal

% Note that the goal closure0/4 is only ever invoked with arg 2
% pattern-matching the head of list arg 4.  Therefore, whenever
% this goal succeeds, this always holds.  Consequently, it is a
% part of the *meaning* of this goal that arg 2 is head of arg 4.

% Furthermore, the list in arg 4 grows in such a way that it
% remains sorted in R_2 order.  That is, if we regard R_2
% as a strict *preorder*, and denote it generically by infix ≤,
% then arg 4 is of the form [X0|Xs] = [X0,X1,...,Xn] with
%
%                    X0 > X1 > ... > Xn,
%
% where the *strict inequalities* exclude repeated elements,
% eliminating the infinite regress of circular reasoning.
% Accordingly, a 'strictly descending' arg 4 is also included
% in the *meaning* of closure0/4.

% The final bit of content of closure0/4 might be expressed,
%
%                        X ≥ X0.
%
% The two parts of "≥" correspond to either:
% '=', the reflexive terminating case; or
% '>', the 'inductive' case that extends the proof-list.

% Thus, in summary, closure0(≤, X0,X, Xs) *means* that
% - X0 is the head of Xs, i.e. Xs = [X0|Rest]
% - Xs is strictly monotone decreasing, i.e. maplist(>, Xs) holds
% - X ≥ X0.

% It should be noted that the implementation could be made slightly
% clearer by adopting a 'preorder' perspective, and exploiting the
% suggestiveness of strict/non-strict inequality notations.
% (Connections with the free monoid construction might also be
% elaborated profitably.)

closure0(R_2, X0,X) :-
   closure0(R_2, X0,X, [X0]).

closure(R_2, X0,X) :-
   call(R_2, X0,X1),
   closure0(R_2, X1,X, [X1,X0]). % NB: this goal concludes proof (cf. Agda's refl) if X1=X

% I have used ;/2 to combine the originally separate clauses of closure0/4,
% to accentuate an interpretation of closure0/4 in terms of preorder concepts.
% Specifically, if R_2 is a *strict* preorder ≤ [that is, R(X0,X) ∧ R(X,X0) ⇒ X=X0],
% then the suggestive notation of strict inequality (< or >) becomes useful.
% (Note that neither the original code nor this equivalent refactoring depends
% upon R_2's being a strict preorder.  In my application, however, R_2 always is.)
closure0(R_2, X0,X, Xs) :- % Consider closure0(≤,X0,X,_) ≡ (X≥X0) ≡ (X=X0 or X>X0) 
    (   X = X0 % If X unifies with head of proof-chain Xs≡[X0|_], then QED.
    ;   (   call(R_2, X0,X1),   % Otherwise [or additionally!] we may seek ..
            non_member(X1, Xs), % .. an intervening X1 > X0 [NB: *strictly*] ..
            closure0(R_2, X1,X, [X1|Xs]) % .. with X ≥ X1 > X0.
        )
    ).

non_member(_E, []).
non_member(E, [X|Xs]) :-
   dif(E,X),
   non_member(E, Xs).
% ------------------------------------------------------------

%%%q_r(T/N, T:U) :- 0 #=< #T, T #=< #N, #U #= N - T.
q_r(T/N, T:U) :- 0 #=< #T, 0 #=< #U, #N #= T + U.

%?- q_r(2/6, T:U).
%@    T = 2, U = 4.

% TODO: Ought I leave tallies unbounded, and take pending constraints
%       as more general answers?
denom_tally(N, T/N) :- #N #>= 0, T in 0..N. % aids fair enumeration when D>1
tally(T/N) :- N in 0..6, indomain(N), denom_tally(N, T/N).

%?- tally(T/N).
%@    T = 0, N = 0
%@ ;  N = 1, clpz:(T in 0..1)
%@ ;  N = 2, clpz:(T in 0..2)
%@ ;  N = 3, clpz:(T in 0..3)
%@ ;  N = 4, clpz:(T in 0..4)
%@ ;  N = 5, clpz:(T in 0..5)
%@ ;  N = 6, clpz:(T in 0..6).

le(T1/N1, T2/N2) :-
    tally(T2/N2),
    tally(T1/N1), 
    #T2 + 1 #= #T1 #/\ #N2 + 1 #= #N1.

le(T1/N1, T2/N2) :-
    tally(T2/N2),
    tally(T1/N1), 
    #T1 #= #T2 #/\ #N2 #= #N1 + 1.

le(0/0, 0/0). % an edge-case not captured by the above!
% Note that the reflexive nature of ≼ is /implicit/ in Definition 2.2,
% simply by virtue of its being described as a "preorder relation".
% The inequalities of Eq (1) yield nearly all of the needed reflexivity
% except for this one edge case.

%?- closure(le, T/N, 2/6).
%@    T = 3, N = 3
%@ ;  T = 4, N = 4
% ...
%@ ;  T = 5, N = 5
%@ ;  false.

% But why check by hand, when I have a *theorem* (Fact 2.4)?
lez(T1/N1, T2/N2) :-
    tally(T2/N2),
    tally(T1/N1), 
    T1 #>= T2 + max(0, N1 - N2).

lez(T1:U1, T2/N2) :-
    q_r(T1/N1, T1:U1),
    lez(T1/N1, T2/N2).

%?- lez(T/N, 2/6), #U #= N - T.
%@    T = 2, N = 2, U = 0
%@ ;  N = 3, clpz:(T in 2..3), clpz:(#U+ #T#=3), clpz:(U in 0..1)
%@ ;  N = 4, clpz:(T in 2..4), clpz:(#U+ #T#=4), clpz:(U in 0..2)
%@ ;  N = 5, clpz:(T in 2..5), clpz:(#U+ #T#=5), clpz:(U in 0..3)
%@ ;  N = 6, clpz:(T in 2..6), clpz:(#U+ #T#=6), clpz:(U in 0..4).

%?- lez(T:U, 2/6).
%@    T = 2, U = 0
%@ ;  clpz:(T in 2..3), clpz:(#U+ #T#=3), clpz:(U in 0..1)
%@ ;  clpz:(T in 2..4), clpz:(#U+ #T#=4), clpz:(U in 0..2)
%@ ;  clpz:(T in 2..5), clpz:(#U+ #T#=5), clpz:(U in 0..3)
%@ ;  clpz:(T in 2..6), clpz:(#U+ #T#=6), clpz:(U in 0..4).
% The above results are evidently correct, since T:U ≼ T':U'
% iff T' ≤ T and U ≤ U'.

closuremiss(T/N, Q) :-
    lez(T/N, Q),
    (   closure(le, T/N, Q) -> false
    ;   true % closure/3 missed that T/N ≼ Q
    ).

%?- closuremiss(T/N, 2/6).
%@    false.

closurefalse(T/N, Q) :-
    closure(le, T/N, Q),
    (   lez(T/N, Q) -> false
    ;   true % closure falsely reported T/N ≼ Q
    ).

%?- closurefalse(T/N, 2/6).
%@    false.

counterexample(T/N, Q) :-
    (   closuremiss(T/N, Q)
    ;   closurefalse(T/N, Q)
    ).

%?- counterexample(T/N, 2/6).
%@    false.

%?- time((tally(Q), counterexample(T/N, Q))).
%@    % CPU time: 99.848s, 502_783_701 inferences
%@    false. % this demonstration completes 6a.

% 6b. Show I can do likewise with the generalization of ≼ to 𝒬.
%     In fact, let me just do it for fixed D=2 case to begin.

tally_d(Qs, D) :-
    length(Qs, D),
    maplist(tally, Qs).

%?- tally_d(Q, 2).
%@    Q = [0/0,0/0]
%@ ;  Q = [0/0,_A/1], clpz:(_A in 0..1)
%@ ;  Q = [0/0,_A/2], clpz:(_A in 0..2)
% ...
%@ ;  Q = [_A/6,_B/5], clpz:(_A in 0..6), clpz:(_B in 0..5)
%@ ;  Q = [_A/6,_B/6], clpz:(_A in 0..6), clpz:(_B in 0..6).

% Let's fairly enumerate a pair of D-tallies (Q1, Q2).
tallies_d(Q1, Q2, D) :-
    M in 0..6, % TODO: loosen or altogether release this arbitrary upper limit
    indomain(M),
    #N1 #>= 0,
    #N2 #>= 0,
    sum([N1, N2], #=, M),
    indomain(N1), length(Q1, D), maplist(denom_tally(N1), Q1),
    indomain(N2), length(Q2, D), maplist(denom_tally(N2), Q2).

%?- tallies_d(Q1, Q2, 2).
%@    Q1 = [0/0,0/0], Q2 = [0/0,0/0]
%@ ;  Q1 = [0/0,0/0], Q2 = [_A/1,_B/1], clpz:(_A in 0..1), clpz:(_B in 0..1)
%@ ;  Q1 = [_A/1,_B/1], Q2 = [0/0,0/0], clpz:(_A in 0..1), clpz:(_B in 0..1)
%@ ;  Q1 = [0/0,0/0], Q2 = [_A/2,_B/2], clpz:(_A in 0..2), clpz:(_B in 0..2)
%@ ;  Q1 = [_A/1,_B/1], Q2 = [_C/1,_D/1], clpz:(_A in 0..1), clpz:(_B in 0..1), clpz:(_C in 0..1), clpz:(_D in 0..1)
%@ ;  Q1 = [_A/2,_B/2], Q2 = [0/0,0/0], clpz:(_A in 0..2), clpz:(_B in 0..2)
%@ ;  Q1 = [0/0,0/0], Q2 = [_A/3,_B/3], clpz:(_A in 0..3), clpz:(_B in 0..3)
%@ ;  Q1 = [_A/1,_B/1], Q2 = [_C/2,_D/2], clpz:(_A in 0..1), clpz:(_B in 0..1), clpz:(_C in 0..2), clpz:(_D in 0..2)
%@ ;  ... .

%?- tallies_d(Q1, Q2, 2).
%@    Q1 = [0/0,0/0], Q2 = [0/0,0/0]
%@ ;  Q1 = [0/0,0/0], Q2 = [_A/1,_B/1], clpz:(_A in 0..1), clpz:(_B in 0..1)
%@ ;  Q1 = [_A/1,_B/1], Q2 = [0/0,0/0], clpz:(_A in 0..1), clpz:(_B in 0..1)
%@ ;  Q1 = [0/0,0/0], Q2 = [_A/2,_B/2], clpz:(_A in 0..2), clpz:(_B in 0..2)
%@ ;  Q1 = [_A/1,_B/1], Q2 = [_C/1,_D/1], clpz:(_A in 0..1), clpz:(_B in 0..1), clpz:(_C in 0..1), clpz:(_D in 0..1)
%@ ;  Q1 = [_A/2,_B/2], Q2 = [0/0,0/0], clpz:(_A in 0..2), clpz:(_B in 0..2)
%@ ;  Q1 = [0/0,0/0], Q2 = [_A/3,_B/3], clpz:(_A in 0..3), clpz:(_B in 0..3)
%@ ;  Q1 = [_A/1,_B/1], Q2 = [_C/2,_D/2], clpz:(_A in 0..1), clpz:(_B in 0..1), clpz:(_C in 0..2), clpz:(_D in 0..2)
%@ ;  Q1 = [_A/2,_B/2], Q2 = [_C/1,_D/1], clpz:(_A in 0..2), clpz:(_B in 0..2), clpz:(_C in 0..1), clpz:(_D in 0..1)
%@ ;  Q1 = [_A/3,_B/3], Q2 = [0/0,0/0], clpz:(_A in 0..3), clpz:(_B in 0..3)
%@ ;  Q1 = [0/0,0/0], Q2 = [_A/4,_B/4], clpz:(_A in 0..4), clpz:(_B in 0..4)
%@ ;  ... .

le2(Q1, Q2) :- % componentwise extension of lez/2
    tallies_d(Q1, Q2, 2),
    maplist(lez, Q1, Q2).

le2([1/1, 0/1], [0/1, 1/1]). % dose-monotonicity (Defn 2.7)

% TODO: How to implement the *monoidal* law for this preorder?

%?- closure(le2, Q1, Q2).
%@    Q1 = [0/0,0/0], Q2 = [0/0,0/0]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/1,0/1]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/2,0/2]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/3,0/3]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/4,0/4]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/3,0/3]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/4,0/4]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/5,0/5]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/2,0/2]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/3,0/3]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/4,0/4]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/3,0/3]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/4,0/4]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/5,0/5]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/6,0/6]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/1,0/1]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/2,0/2]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/3,0/3]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/4,0/4]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/3,0/3]
%@ ;  Q1 = [0/0,0/0], Q2 = [0/4,0/4]
%@ ;  ... .
% This is interesting!  Fairly enumerating the le/2 predicate
% did NOT result in fair enumeration of its closure.  Perhaps
% fair enumeration must be implemented at some 'outer' level?

% To that end, let's gain control over the net denominator,
% through an accessory argument to the preorder relation.
denom_le2(N, Q1, Q2) :-
    #N1 #>= 0,
    #N2 #>= 0,
    sum([N1, N2], #=, N),
    indomain(N1), length(Q1, D), maplist(denom_tally(N1), Q1),
    indomain(N2), length(Q2, D), maplist(denom_tally(N2), Q2),
    maplist(lez, Q1, Q2).

denom_le2(4, [1/1, 0/1], [0/1, 1/1]). % dose-monotonicity (Defn 2.7)

%?- N in 0..6, indomain(N), closure(denom_le2(N), Q1, Q2).
%@    N = 4, Q1 = [1/1,0/1], Q2 = [0/1,1/1]
%@ ;  false.

% Aha!  This attempt failed because closure/3 needs to operate with
% the FULL relation, and not merely 'slices' of it.  So perhaps one
% must implement any fair enumeration *within* closure/3 itself,
% say by gradually expanding the length of the proofs collected in
% arg 4 of closure0/4.
% This might indeed be the most natural way to enumerate a transitive
% closure: working from the quickest toward the lengthier deductions.
% Furthermore, it might quite often happen that with *ground* args X0,X
% we have some theoretical understanding that lets us put an upper bound
% on the length of the shortest proof of R_2(X0,X).  Because it is pure,
% closure/3 would be guaranteed to find this proof.

% Therefore, let me create a version of closure*/* that carry along
% a maximum proof-length.  It could be interesting if this length could
% be allowed to be a variable, but I won't demand that of my initial
% implementation.


% 6c. Explore any heuristics that may improve efficiency of proving ≼.
%     The proofs might best be generated as a DCG.

% 6d. Find 'incomparables' in 𝒬, and try to characterize the incomparable
%     neighbors of any given tally.  Can incomparability be 'factored out'
%     in any sense that yields e.g. better visualizations of 𝒬?

% 6. Calculate *the* 'natural' IE from the (non-functorial) 3+3 dose recs.

% 7. Construct a right adjoint F ⊢ E.  This will have the property that
%
%                    E(q) ≤ d  iff  q ≼ F(d),
%
%    and will give rise to a sequence fᵢ = F(i), i ∈ {0,...,D}, in Qᴰ
%    such that the /lower sets/ ∧fᵢ = {q | q ≼ fᵢ} identify all tallies
%    upon which the next-recommended-dose is i or below.  (Are fᵢ then
%    /meets/ of these sets?)

% 8. What would a *left* adjoint L ⊣ E mean?  That
%
%                    L(d) ≼ q  iff  d ≤ E(q).

% Might it be possible to expand ≼ to a monoidal preorder sufficiently
% informed to generate E?  Perhaps this construction would even be
% generally available?  Might it even be 'obvious' how to do this?

% If it does turn out that we can always enlarge ≼ to generate any IE,
% then this fact restores the 'primacy' of evident-safety considerations.

% 6. Examine what modification(s) to the dose recs would restore consistency
%  - Is it at all possible there's some kind of adjunction here,
%    such that we have upper and lower adjustments to the dose recs?
%  - Can we find a *minimal* adjustment to the dose recs?
% 7. Examine how close to total =<$ is; can it be rendered total?

