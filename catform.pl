% Inline code for Categorical sketch

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(si)).
:- use_module(library(lambda)).
:- use_module(library(pairs)).
:- use_module(library(assoc)).
:- use_module(library(time)).
:- use_module(library(format)).
:- use_module(library(debug)).
:- use_module(library(tabling)).
:- use_module(library(iso_ext)).

:- use_module(rcpearl).

clpz:monotonic.

reduce(P_2, [X|Xs], R) :- foldl(P_2, Xs, X, R).

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

%% 1. Via Fact 2.13, define evident-$afety relation ≼ ⊂ 𝒬✕𝒬:
:- op(900, xfx, '≼').
:- op(900, xfx, '⋠').
:- op(900, xfx, '≽').
:- op(900, xfx, '⋡').

% TODO: Consider implementing also the *strict* orders '≺' and '≻',
%       but watch out in case this introduces subtle misconceptions
%       due to any 'excessive' suggestiveness of these symbols!
:- op(900, xfx, '≺').
:- op(900, xfx, '⊀').
:- op(900, xfx, '≻').
:- op(900, xfx, '⊁').

q_r(T/N, T:U) :- 0 #=< #T, 0 #=< #U, #N #= #T + #U.
q_t_u(Q, T, U) :- q_r(Q, T:U).

% The monograph's capitalization notation being ill-suited to
% Prolog (for obvious reasons!), we indicate our partial-sum
% variables below with a prefix Σ.
qs_Ts_Ūs(Qs, ΣTs, ΣŪs) :-
    maplist(q_t_u, Qs, Ts, Us),
    intlist_partsums(Ts, ΣTs),
    reverse(Us, Ūs),
    intlist_partsums(Ūs, RΣŪs),
    reverse(RΣŪs, ΣŪs).

%?- Qs = [1/6,2/6], maplist(q_r, Qs, Rs), qs_Ts_Ūs(Qs, Ts, Ūs).
%@    Qs = [1/6,2/6], Rs = [1:5,2:4], Ts = [1,3], Ūs = [9,4].

% I've discovered that the sufficient condition for ≼
% is actually quite subtle, and necessitates considering
% the exchange relations.

% Let us make this predicate strictly about the equation
% relating tallies Qs to Qas thru the exchange coefs As.
% (I will not even impose a restriction of positivity on
% the As, nor even the resulting Qas.)
qs_as_qas(Qs, As, Qas) :- % 'A' für Austausch
    qs_Ts_Ūs(Qs, Ts, Ūs),
    same_length(Qs, [_|As]), % the As act at the (D-1) *commas* of Qs
    as_Ūs_Ūas(As, Ūs, Ūas),
    as_Ts_Tas(As, Ts, Tas),
    qs_Ts_Ūs(Qas, Tas, Ūas).

%?- qs_as_qas([1/6,1/6], As, [0/6,2/6]).
%@    As = [1].

% The As are the D-1 coefficients of the _comma-wise_ exchanges.
% Because each exchange moves both 'o' and 'x' alike in the _same_
% direction as Ūs and Ts respectively are summed, both of these
% vectors get _decremented_ by an exchange.  The Ūs are decremented
% to the right of each comma (where the 'o' gets taken from), while
% the Ts get decremented to the left (where the 'x' is taken from).
as_Ūs_Ūas(As, [ΣU|Ūs], [ΣU|Ūas]) :- % Ūs head is total count of o's,
    same_length(Ūs, Ūas),           % an _invariant_ under x-o exchange.
    maplist(\U^A^Ua^(#U - #A #= #Ua), Ūs, As, Ūas).

as_Ts_Tas(As, Ts, Tas) :-
    Ts = [_|Ts1], same_length(Ts1, As),
    append(As, [0], As0), % Last of Ts is the total count of x's,
    same_length(Ts, Tas), % which is invariant under x-o exchange.
    maplist(\T^A^Ta^(#T - #A #= #Ta), Ts, As0, Tas).

'≼old'(Q1s, Q2s, Truth) :-
    qs_Ts_Ūs(Q1s, T1s, Ū1s),
    qs_Ts_Ūs(Q2s, T2s, Ū2s),
    %%format("T1s = ~w , T2s = ~w~n", [T1s, T2s]),
    %%format("Ū1s = ~w , Ū2s = ~w~n", [Ū1s, Ū2s]),
    Ū1s = [Ū1|Ū1rs],
    Ū2s = [Ū2|Ū2rs],
    % We next calculate the _smallest_ exchange-adjustment As : Ū1s ⟼ Ū1as
    % that would ensure Ū1as ≤ Ū2s.  (In case this inequality already holds
    % as for unadjusted Ū1s, then this will be the _null_ adjustment.)
    same_length(Ū1rs, As),
    maplist(\A^U1^U2^(#A #= max(0, #U1 - #U2)), As, Ū1rs, Ū2rs),
    % Now we will calculate post-exchange [T1a|T1as] vector.
    as_Ts_Tas(As, T1s, T1as),
    %%format("As = ~w; T1as = ~w~n", [As, T1as]),
    %%format("Ū1 ≤ Ū2 ? ~w ≤ ~w~n", [Ū1, Ū2]),
    %%format("T2s ≤ T1as ? ~w ≤ ~w~n", [T2s, T1as]),
    if_((clpz_t(#Ū1 #=< #Ū2), % Q1 must not have _net_ advantage of more total o's
         T2s '≤' T1as % Even *after* exchange-adjustment, T1 must still exceed T2.
         % (Happily, the above also ensures T1as never 'goes negative'.)
        ),
        Truth = true,
        Truth = false
       ).

% Impose global default for R here:
coefs(Qs, Hs, Os) :- coefs(2, Qs, Hs, Os).
os_enc(Os, OK) :- r_os_enc(2, Os, OK).

%?- [1/6,1/3] '≼' [1/6,0/0].
%@    false. % with R=1
%?- [1/6,1/3] '≼' [1/6,0/0].
%@    true. % with R=2

% Find the unique coefficients of ≼ᵣ-generators for given q ∈ Qᴰ.
% TODO: Here is a good spot to begin renaming the coefficients,
%       once I've rationalized their names in the monograph.
coefs(R, Qs, Hs, Os) :-
    #R #> 0,
    same_length(Qs, Hs), % allows usage (+R, -Qs, +Hs, +Os)
    maplist(\Q^T^N^(Q = T/N), Qs, Ts, Ns),
    % We will set Hs = [ηs]+[ρ] (of length D), since ρ fits in so smoothly.
    % Our first D equations are simply that Hs is minus partial sums of Ts.
    intlist_negated(Ts, NegTs), intlist_partsums(NegTs, Hs),
    reverse(Hs, [Rho|_]),
    % Our next set of equations is formed by γ = ΣU + rρ =: σ₀₁,
    % and then recursively σₖ,ₖ₊₁ = σₖ₋₁,ₖ - nₖ for k in 1..D-1.
    % But an even simpler expression of this, which dispenses
    % altogether with the Us, is to reverse-partial-sum the Ns,
    % then add Rho*(R+1)!
    reverse(Ns, Иs),
    intlist_partsums(Иs, ΣИs),
    reverse(ΣИs, ΞNs),
    #RhoR1 #= #Rho * (#R + 1),
    maplist(sum_(RhoR1), ΞNs, Os).

%?- coefs(1, [0/0,0/0,0/0], Hs, Os).
%@    Hs = [0,0,0], Os = [0,0,0].

%?- transform([0/0,0/0,0/0], [1/2,3/4,4/5], Hs, Os).
%@    Hs = [-1,-4,-8], Os = [-5,-7,-11].
%?- coefs(1, [1/2,3/4,4/5], Hs, Os).
%@    Hs = [-1,-4,-8], Os = [-5,-7,-11].

% Let's check systematically
d_nmax_discordant(D, Nmax, Q1s, Q2s) :-
    qs_d_nmax(Q1s, D, Nmax),
    qs_d_nmax(Q2s, D, Nmax),
    transform(Q1s, Q2s, Hs, Os),
    coefs(Q1s, H1s, O1s),
    coefs(Q2s, H2s, O2s),
    maplist(H2^H1^H_^(#H_ #= #H2 - #H1), H2s, H1s, Hs_),
    maplist(O2^O1^O_^(#O_ #= #O2 - #O1), O2s, O1s, Os_),
    (   Hs \== Hs_
    ;   Os \== Os_
    ).

%?- time(d_nmax_discordant(2, 3, Q1s, Q2s)).
%@    % CPU time: 9.259s, 29_721_540 inferences
%@    false.
%?- time(d_nmax_discordant(3, 2, Q1s, Q2s)).
%@    % CPU time: 60.048s, 199_087_482 inferences
%@    false.
%?- time(d_nmax_discordant(3, 3, Q1s, Q2s)).
%@    % CPU time: 1302.750s, 4_202_019_937 inferences
%@    false.
%?- time(d_nmax_discordant(2, 6, Q1s, Q2s)).
%@    % CPU time: 567.130s, 1_779_337_077 inferences
%@    false.


% I've now worked out in detail a unique transformation of pair
% Q1,Q2 ∈ Qᴰ into 2✕D parameters, *all* nonnegative iff Q1 ⊑ Q2.
transform(Q1s, Q2s, ΔHs, ΔOs) :-
    same_length(Q1s, Q2s),
    coefs(Q1s, H1s, O1s),
    coefs(Q2s, H2s, O2s),
    maplist(diff_, H2s, H1s, ΔHs),
    maplist(diff_, O2s, O1s, ΔOs).

%?- Ňs = [1,2,3], reverse(Ňs, Ns).
%@    Ňs = [1,2,3], Ns = [3,2,1].

%?- transform([1/1,0/1], [0/1,1/1], Hs, Os).
%@    Hs = [1,0], Os = [0,0].
%?- transform([0/1,1/1], [0/0,1/2], Hs, Os).
%@    Hs = [0,0], Os = [0,1].
%?- transform([0/1,1/2], [0/1,0/0], Hs, Os).
%@    Hs = [0,1], Os = [0,0].

%?- transform([0/2,1/2], Q2, [0,1], [1,0]).
%@    Q2 = [0/3,0/0].
%?- transform([0/2,1/2], Q2, [0,1], [1,1]).
%@    Q2 = [0/2,0/1].

q1s_q2s_Δts_Δns(Q1s, Q2s, Δts, Δns) :-
    maplist(\Q^T^N^(Q = T/N), Q1s, T1s, N1s),
    maplist(\Q^T^N^(Q = T/N), Q2s, T2s, N2s),
    maplist(\X1^X2^ΔX^(#ΔX #= #X2 - #X1), T1s, T2s, Δts),
    maplist(\X1^X2^ΔX^(#ΔX #= #X2 - #X1), N1s, N2s, Δns).

%?- q1s_q2s_Δts_Δns([1/1,0/1], [0/1,1/1], Δts, Δns).
%@    Δts = [-1,1], Δns = [0,0].

'≼'(Q1s, Q2s, Truth) :- % QAs ≼toxD QBs ≼tol1 QCs ≼exch QZs
    transform(Q1s, Q2s, Hs, Os),
    % It's as simple now as asserting all Hs & Os are nonnegative!
    % But the more effective way to express this may be to look
    % for any single negative value, then invert truth value.
    if_((   tmember_t(#>(0), Hs)
        ;   tmember_t(#>(0), Os)
        ), Truth = false,
        Truth = true
       ).

#>(X, Y, Truth) :- clpz_t(X #> Y, Truth). % counterpart to clpz:(#<)/3

d_q_nmax(D, Qs, Nmax) :-
    length(Qs, D),
    maplist(\Q^(Q = T/N, 0 #=< #N, #N #=< #Nmax, 0 #=< #T, #T #=< N), Qs).

d_q(D, Qs) :- d_q_nmax(D, Qs, 6).

d_q(D, Qs) :-
    length(Qs, D),
    maplist(\Q^(Q = T/N, N in 0..6, 0 #=< #T, #T #=< N), Qs).

%?- d_q(2, Qs).
%@    Qs = [_B/_A,_D/_C], clpz:(_A in 0..6), clpz:(#_A#>= #_B), clpz:(_B in 0..6), clpz:(_C in 0..6), clpz:(#_C#>= #_D), clpz:(_D in 0..6).

% (Below I redo this earlier investigation, after overwriting
% the 'old' ≼ with the 'new' one initially introduced as '⊑'.)
% Investigating whether certain arrows 'discovered' during Meetup
% and on return flight are present in '≼' as already defined:
%
%         [exch]     [titro]      [1:1]
% [1/1,0/1] ≼ [0/1,1/1] ≼ [0/0,1/2] ≼ [0/0,0/0]
%      \             \_________≼_________/ /
%       \_______________≼_________________/
%
% If I am guessing right, only the [exch] arrow is already present
% in '≼' as currently defined.  But I do wonder if either of the
% composite arrows shown might somehow be present already.

%?- [1/1,0/1] '≼' [0/1,1/1].
%@    true. % (still true after renaming '⊑' ↦ '≼')
%@    true. % as expected [exch]

%?- [0/0,1/2] '≼' [0/0,0/0].
%@    true. % after renaming '⊑' ↦ '≼'
%@    false. % [1:1] absent (as anticipated)

%?- [0/1,1/1] '≼' [0/0,1/2].
%@    true. % (still true after renaming '⊑' ↦ '≼')
%@    true. % ah, but of course: [titro] is basically monotonicity

%?- [0/1,1/1] '≼' [0/0,0/0].
%@    true. % after renaming '⊑' ↦ '≼'
%@    false. % [titro];[1:1] absent (as anticipated)

%?- [1/1,0/1] '≼' [0/0,0/0].
%@    true. % after renaming '⊑' ↦ '≼'
%@    false. % [exch];[titro];[1:1] also absent (as anticipated)

% What about tol1 arrows?
%?- [0/0,0/0] '≼' [0/1,0/0].
%@    true.

% How about toxD?
%?- [0/0,1/1] '≼' [0/0,0/0].
%@    true.

%?- [0/0,1/2] '≼' [0/0,0/1]. % a toxD arrow
%@    true.

%?- [1/1,1/2] '≼' [1/1,0/1]. % also a toxD arrow
%@    true.

%?- [1/1,1/2] '≼' [1/1,0/0]. % a 1:1 arrow
%@    true. % after renaming '⊑' ↦ '≼'
%@    false.

%?- [1/1,1/3] '≼' [1/1,0/1]. % a 1:1 arrow
%@    true. % after renaming '⊑' ↦ '≼'
%@    false.

% I believe that [1:1] = toxD - tol1 - titro, yet that
% all 3 of {toxD, tol1, titro} are present in ≼.
% So why don't I get 1:1 in ≼ as well?
%?- [1/1,1/1] '≼' [1/1,0/0]. % toxD
%@    true.
%?- [1/1,0/0] '≼' [1/2,0/0]. % tol1
%@    true.
%?- [1/2,0/0] '≼' [1/1,0/1]. % titro
%@    true.
% Now if transitivity holds, then we should have...
%?- [1/1,1/1] '≼' [1/1,0/1].
%@    true.

% So the addition of these [1:1] arrows does augment the existing
% order relation, perhaps quite substantially!  Such augmentation
% is sorely needed at this point, given the existing definition's
% refusal to yield up workable Galois trials.
% Furthermore, given how the [1:1] arrows support an intuitive
% argument (based on safety-derogatory information content) for
% the [exch] arrows, including [1:1] would add also _conceptual_
% depth to our partial order.

%?- '≼'([0/1,0/0], [0/0,0/1], Truth).
%@ T1s = [0,0] , T2s = [0,0]
%@ Ū1s = [1,0] , Ū2s = [1,1]
%@ As = [0]; T1as = [0,0]
%@ Ū1 ≤ Ū2 ? 1 ≤ 1
%@ T2s ≤ T1as ? [0,0] ≤ [0,0]
%@    Truth = true.

%?- [1/6,1/6]'≼'[0/6,2/6].
%@    true.

%?- '≼'([1/6,1/6], [0/6,2/6], Truth).
%@ T1s = [1,2] , T2s = [0,2]
%@ Ū1s = [10,5] , Ū2s = [10,4]
%@ As = [1]; T1as = [0,2]
%@ Ū1 ≤ Ū2 ? 10 ≤ 10
%@ T2s ≤ T1as ? [0,2] ≤ [0,2]
%@    Truth = true.

%?- qs_Ts_Ūs([1/6,1/6], Ts, Ūs), reverse(Ūs, Us).
%@    Ts = [1,2], Ūs = [10,5], Us = [5,10].

%?- qs_Ts_Ūs([0/6,2/6], Ts, Ūs), reverse(Ūs, Us).
%@    Ts = [0,2], Ūs = [10,4], Us = [4,10].

'≺'(Q1s, Q2s, Truth) :-
    if_((Q1s '≼' Q2s, dif(Q1s, Q2s)),
        Truth = true,
        Truth = false
        ).

'≽'(Q2s, Q1s, Truth) :-'≼'(Q1s, Q2s, Truth).
'≻'(Q2s, Q1s, Truth) :-'≺'(Q1s, Q2s, Truth).

'≼'(Q1s, Q2s) :- '≼'(Q1s, Q2s, true).
'⋠'(Q1s, Q2s) :- '≼'(Q1s, Q2s, false).
'≽'(Q2s, Q1s) :- '≼'(Q1s, Q2s, true).
'⋡'(Q2s, Q1s) :- '≼'(Q1s, Q2s, false).

'≺'(Q1s, Q2s) :- '≺'(Q1s, Q2s, true).
'⊀'(Q1s, Q2s) :- '≺'(Q1s, Q2s, false).
'≻'(Q2s, Q1s) :- '≺'(Q1s, Q2s, true).
'⊁'(Q2s, Q1s) :- '≺'(Q1s, Q2s, false).

%% Utility predicates used above:

intlist_sum([X|Xs], Sum) :- intlist_sum_([X|Xs], Sum).
intlist_sum_([X|Xs], Sum) :-
    intlist_sum_(Xs, _Sum),
    #Sum #= #X + #_Sum.
intlist_sum_([], 0).

%?- intlist_sum([], Nope).
%@    false. % As desired.

%?- findall(N, (N in 1..100, indomain(N)), Ns), time(intlist_sum(Ns, Sum)).
%@    % CPU time: 0.000s, 379 inferences
%@    Ns = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20|...], Sum = 5050.

intlist_negated([X|Xs], [N|Ns]) :-
    same_length(Xs, Ns),
    #X #= -(#N),
    intlist_negated(Xs, Ns).
intlist_negated([], []).

%?- intlist_negated(Xs, [-1,-2,-3]).
%@    Xs = [1,2,3].

%?- intlist_negated(Xs, Ns).
%@    Xs = [_A], Ns = [_B], clpz:(#_A+ #_B#=0)
%@ ;  Xs = [_A,_C], Ns = [_B,_D], clpz:(#_A+ #_B#=0), clpz:(#_C+ #_D#=0)
%@ ;  Xs = [_A,_C,_E], Ns = [_B,_D,_F], clpz:(#_A+ #_B#=0), clpz:(#_C+ #_D#=0), clpz:(#_E+ #_F#=0)
%@ ;  ... .

intlist_partsums([X|Xs], [X|Σs]) :-
    same_length(Xs, Σs), % eliminate unnecessary choice point
    intlist_partsums_acc(Xs, Σs, X).

intlist_partsums_acc([], [], _).
intlist_partsums_acc([X|Xs], [Σ|Σs], A) :-
    #Σ #= #X + #A,
    intlist_partsums_acc(Xs, Σs, Σ).

%?- [1/3, 1/2] '≼' [0/4, 0/1].
%@    true.

%?- [1/6,1/6] '≼' [0/6,2/6].
%@    true.

%?- [1/6,1/6] '≼' [0/6,2/5].
%@    false.

%?- [1/6,1/6] '≼' [0/6,2/7].
%@    true.

%?- [0/6,2/6] '≽' [1/6,1/6].
%@    true.

%?- [1/3,1/3] '≼' [1/3,1/3].
%@    true.

%?- [1/3,1/3] '≺' [1/3,1/3].
%@    false.

%?- [1/6,1/6] '≺' [0/6,2/6].
%@    true.

%?- as_Ts_Tas(As, [1,2,3], [0,3,3]).
%@    As = [1,-1].

%?- as_Ts_Tas([1,0], [1,2,3], Ts1), as_Ts_Tas([0,-1], Ts1, Ts2).
%@    Ts1 = [0,2,3], Ts2 = [0,3,3].

maxs(N1s, N2s, Ns) :- maplist(\N1^N2^N^(#N #= max(#N1, #N2)), N1s, N2s, Ns).
mins(N1s, N2s, Ns) :- maplist(\N1^N2^N^(#N #= min(#N1, #N2)), N1s, N2s, Ns).

%?- maxs([1,2,6], [3,4,5], Maxs).
%@    Maxs = [3,4,6].
%?- mins([1,2,6], [3,4,5], Mins).
%@    Mins = [1,2,5].

% https://en.wikipedia.org/wiki/Monus#Natural_numbers
monus_(X, Y, X_Y) :- #X #>= 0, #Y #>= 0, #X_Y #= max(0, #X - #Y).
monus([X|Xs], [Y|Ys], [X_Y|Xs_Ys]) :-
    monus_(X, Y, X_Y),
    monus(Xs, Ys, Xs_Ys).
monus([], [], []).
    
%?- X=[5,7], Y=[8,9], monus(X, Y, X_Y), monus(Y, X, Y_X).
%@    X = [5,7], Y = [8,9], X_Y = [0,0], Y_X = [3,2].

%?- X=5, Y=8, monus_(X, Y, X_Y), monus_(Y, X, Y_X).
%@    X = 5, Y = 8, X_Y = 0, Y_X = 3.

all_but_last(Xs, Xs1, X) :-
    reverse(Xs, [X|Vs]),
    reverse(Vs, Xs1).

%?- all_but_last([1,2,3], B, L).
%@    B = [1,2], L = 3.

% Find the maximal Ūs profile such that (Ts:Ūs) ≼ Qs.
qs_Ts_maxŪs(Qs, Ts, Ūs) :-
    qs_Ts_Ūs(Qs, Ts_, Ūs_), Ts_ '≤' Ts,
    monus(Ts, Ts_, As_), all_but_last(As_, As, _),
    same_length(Qs, Ūs),
    maplist(\U^U_^A^(#U #= #U_ + #A), Ūs, Ūs_, [0|As]).

meet_(Q1s, Q2s, Hs, Os) :-
    same_length(Q1s, Q2s),
    coefs(Q1s, H1s, O1s),
    coefs(Q2s, H2s, O2s),
    mins(H1s, H2s, Hs),
    mins(O1s, O2s, Os).

meet_(Q1s, Q2s, Qs) :- % 'formal meet'
    meet_(Q1s, Q2s, Hs, Os),
    coefs(Qs, Hs, Os).

join(Q1s, Q2s, Hs, Os) :-
    same_length(Q1s, Q2s),
    coefs(Q1s, H1s, O1s),
    coefs(Q2s, H2s, O2s),
    maxs(H1s, H2s, Hs),
    maxs(O1s, O2s, Os).

% NB: If, as I believe, 𝒬 = (Qᴰ,≼) is an upper semilattice,
%     then these joins will always exist and are unique.
join(Q1s, Q2s, Qs) :-
    join(Q1s, Q2s, Hs, Os),
    coefs(Qs, Hs, Os).

sum_(Z1, Z2, Sum) :- #Sum #= #Z1 + #Z2.
diff_(Z1, Z2, Diff) :- #Diff #= #Z1 - #Z2.

%?- maplist(diff_, [1,2,3], [0,1,2], Δs).
%@    Δs = [1,1,1].

intlist_downshift(Zs, ΔZs) :-
    intlist_rollmin(Zs, Zs_),
    maplist(diff_, Zs_, Zs, ΔZs).

% Unlike meet_/3, which allows for 'imaginary' meets,
% this predicate succeeds only if a valid meet obtains.
meet(Q1s, Q2s, Qs) :-
    meet_(Q1s, Q2s, Qs),
    maplist(\Q^(Q=T/N, #T #=< #N), Qs).

%?- Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], meet(Q1s, Q2s, Meet).
%@    Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], Meet = [0/1,1/1,1/1].
%?- Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], nmax_meet(2, Q1s, Q2s, Meet0).
%@    Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], Meet0 = [0/1,1/1,1/1]
%@ ;  Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], Meet0 = [1/1,0/0,1/2].
% Ooh!  Now this is really interesting.  We get 2 different meets-by-definition!
%?- M0a = [0/1,1/1,1/1], M0b = [1/1,0/0,1/2], (M0a '≼' M0b; M0b '≼' M0a).
%@    false. % M0a and M0b are incomparable.
%?- Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], M0a = [0/1,1/1,1/1], M0a'≼'Q1s, M0a'≼'Q2s.
%@    Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], M0a = [0/1,1/1,1/1].
%?- Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], M0b = [1/1,0/0,1/2], M0b'≼'Q1s, M0b'≼'Q2s.
%@    Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], M0b = [1/1,0/0,1/2].
% So it appears 𝒬 = (Qᴰ,≼) is NOT a lower semilattice!

%?- Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], nmax_meet(3, Q1s, Q2s, Meet0).
%@    Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], Meet0 = [0/1,1/1,1/1]
%@ ;  Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], Meet0 = [1/1,0/0,1/2].
%?- M0a = [0/1,1/1,1/1], M0b = [1/1,0/0,1/2], coefs(1, M0a, Hsa, Osa), coefs(1, M0b, Hsb, Osb).
%@    M0a = [0/1,1/1,1/1], M0b = [1/1,0/0,1/2],
%     Hsa = [ 0,-1,-2], Osa = [-1,-2,-3],
%     Hsb = [-1,-1,-2], Osb = [-1,-2,-2].
% What do I learn from the above?
%?- Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], coefs(1, Q1s, Hs1, Os1), coefs(1, Q2s, Hs2, Os2).
%@    Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2],
%     Hs1 = [0,-1,-1], Os1 = [-1,-1,-2],
%     Hs2 = [0, 0,-2], Os2 = [-1,-2,-2].
%?- Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2], meet_(Q1s, Q2s, M_), coefs(1, M_, Hs_, Os_).
%@    Q1s = [0/0,1/1,0/0], Q2s = [0/1,0/0,2/2],
%     M_ = [0/1,1/0,1/2],
%     Hs_ = [0,-1,-2], Os_ = [-1,-2,-2].
% So, we see that ≼ as currently defined generates no preference
% for one adjustment approach over another.
% The most compelling *opportunity* revealed by this discovery
% would be to seek plausible additional arrows that _do_ render
% such a judgment!  The more arrows I have in this partial order,
% the fuller my results can be!
%
% Therefore, our important question now is whether either of
% M0a or M0b above can reasonably be deemed the 'safer' one.
%    M0a = [0/1,1/1,1/1]
%    t:u = [0:1,1:0,1:0] t = 0 1 1  u = 1 0 0
%    M0b = [1/1,0/0,1/2]
%    t:u = [1:0,0:0,1:1] t = 1 0 1  u = 0 0 1
% Both have totals T=2, U=1 and (of course) N=3.
% What differs is /how/ these are distributed.
% The issue that appears to have arisen now is
% how to compare exchanges between not just
% adjacent doses, but doses arbitrarily far apart.
% If we adopted the view that even arbitrarily
% high titration of 1 individual cannot cancel
% the safety-loss from moving 1 toxicity down
% one dose, then we would have M0b ≼ M0a ---
% agreeing with our current meet/3 implementation,
% at least for this case.  But I would worry that
% this could be hard to argue for universally.
% (The only really appealing rationale for this
% might be if it obviated the ρ argument.)

%?- meet([3/3,4/4], [4/6,0/0], M).
%@ η₁,...,ηD≡ρ : [-4,-7]
%@ ή₁,...,ήD≡ῤ : [-4,-7]
%@ (γ,σ₁₂,...) : [-7,-10]
%@ (γ-0,σ₁₂-ή₁₂,...) : [-7,-6]
%@ ΔXs : [-1]
%@ min(0,ΔXs) : [-1]
%@ ΣAs : [-1]
%@ γ,ς₁₂,... : [-7,-11]
%@ ῤ : -7
%@ Phew! -11-(-4) ≥ -7 !
%@    M = [4/4,3/3]. % Now a *valid* tally!

%?- meet_([3/3,4/4], [4/6,0/0], M).
%@    M = [4/3,3/4]. % Not a valid tally!

%?- '≼'([4/3,3/4], [3/3,4/4], Truth).
%@    Truth = true.
%?- '≼'([4/3,3/4], [4/6,0/0], Truth).
%@    Truth = true.

%?- meet_def([3/3,4/4], [4/6,0/0], M).
%@    M = [4/4,3/3].

%?- '≼'([4/4,3/3], [3/3,4/4], Truth).
%@    Truth = true.
%?- '≼'([4/4,3/3], [4/6,0/0], Truth).
%@    Truth = true.

%?- [4/4,3/3] '≼' [4/3,3/4].
%@    true.

% What do we learn here?  My oh-so-clever computation
% based on transformation to (Hs,Os) produced an invalid
% tally which however _formally_ was a strictly 'better'
% ('closer') meet than one restricted to valid tallies.

% The 'gap' here consisted of an extra exchange arrow
% which was of course invalid.  But why did my 'clever'
% calculation not work?

%?- M = [4/4,3/3], coefs(1, M, Hs, Os), coefs(1, _M, Hs, Os).
%@    M = [4/4,3/3], Hs = [-4,-7], Os = [-7,-11], _M = [4/4,3/3].

%?- M1 = [4/3,3/4], coefs(1, M1, Hs, Os), coefs(1, _M1, Hs, Os).
%@    M1 = [4/3,3/4], Hs = [-4,-7], Os = [-7,-10], _M1 = [4/3,3/4].

%?- A = [3/3,4/4], coefs(1, A, Hs, Os), coefs(1, _A, Hs, Os).
%@    A = [3/3,4/4], Hs = [-3,-7], Os = [-7,-10], _A = [3/3,4/4].

%?- B = [4/6,0/0], coefs(1, B, Hs, Os), coefs(1, _B, Hs, Os).
%@    B = [4/6,0/0], Hs = [-4,-4], Os = [-2,-8], _B = [4/6,0/0].

%?- M = [4/4,3/3], M1 = [4/3,3/4], M '≼' M1.
%@    M = [4/4,3/3], M1 = [4/3,3/4].

%?- M = [4/4,3/3], M1 = [4/3,3/4], M '≼' M1.

%?- M1 = [4/3,3/4], A = [3/3,4/4], M1 '≼' A.
%@    M1 = [4/3,3/4], A = [3/3,4/4].

%?- M1 = [4/3,3/4], B = [4/6,0/0], M1 '≼' B.
%@    M1 = [4/3,3/4], B = [4/6,0/0].

% This all makes sense, in fact.
% We have _formally_ that M1 ≼ M ≼ A and M1 ≼ M ≼ B.
% The only 'surprise' here is that M is invalid /as a tally/.
% There's nothing terribly 'devastating' about this development,
% which resembles the discovery of 'imaginary numbers' that
% greatly facilitate formal manipulations.

% It would be nice, however, to know that exchange-adjustment
% could always be relied upon to yield a unique valid tally
% *below* any such purely formal meet.  How would a computation
% of this proceed?

% If in general a formal meet can be 'pushed down' to a unique
% valid tally, this will imply at least one of the transformed
% coordinates is actually *too high* [or not negative enough!]
% given the others.  Might it be possible to set up CLP(ℤ)
% constraints that define a unique adjustment?

% To begin, since the Hs (η₁₂,η₂₃,...,ρ) are the partial sums
% of _minus_ toxicity counts (-t₁,-t₂,...,-t_D) at doses 1..D,
% and these must all be negative, the Hs must be a decreasing
% sequence of non-positive numbers.  We obtain D inequalities
% from this, which can [must!] be enforced independently of
% any constraints on the Os.  Therefore, we can simply force
% the whole Hs vector downward in our first adjustment step.

% Next, given the ρ value (final element of Hs) we can set to
% work on the _reversed_ Os!  By adding -2ρ (this is positive!)
% to ROs, we get the right-to-left partial sums of (n₁,...,n_D),
% which must be an *increasing* sequence of positive numbers.
% As we did with Hs, we can then enforce monotonicity upon ROs.

% This all looks extrememly promising, since it delivers the
% desired _uniqueness_ of our result!  Moving to details of the
% implementation, how shall we impose monotonicity?

% Can we generalize a bit?
intlist_rolled([X|Xs], G_3, [X|Zs]) :-
    same_length(Xs, Zs),
    intlist_rolled_(Xs, G_3, Zs, X).

intlist_rolled_([X|Xs], G_3, [Z|Zs], R) :-
    call(G_3, X, R, Z),
    intlist_rolled_(Xs, G_3, Zs, Z).
intlist_rolled_([], _, [], _).

intlist_rollmin(Xs, As) :- intlist_rolled(Xs, clpz:min_, As).

%?- intlist_rollmin([5,3,56,4,9], Ms).
%@    Ms = [5,3,3,3,3].

intlist_rollmax(Xs, Vs) :- intlist_rolled(Xs, clpz:max_, Vs).

%?- intlist_rollmax([5,3,56,4,9], Ms).
%@    Ms = [5,5,56,56,56].

intlist_inverse(Xs, NegXs) :-
    same_length(Xs, NegXs), % avoid choicepoint when used (-Xs, +NegXs)
    maplist(\X^N^(#N #= - #X), Xs, NegXs).

%?- intlist_inverse([5,3,56,4,9], Ns).
%@    Ns = [-5,-3,-56,-4,-9].

%?- intlist_inverse(Xs, [5,3,56,4,9]).
%@    Xs = [-5,-3,-56,-4,-9].

%?- M1 = [4/3,3/4], coefs(1, M1, Hs, Os), coefs(1, _M1, Hs, Os).
%@    M1 = [4/3,3/4], Hs = [-4,-7], Os = [-7,-10], _M1 = [4/3,3/4].
% What are the changes we can make that *increase* these
% transformed coordinates, while 

%?- M = [4/4,3/3], M1 = [4/3,3/4], transform(M, M1, Hs, Os).
%@    M = [4/4,3/3], M1 = [4/3,3/4], Hs = [0,0], Os = [0,1].

%?- meet([0/6,4/6], [1/6,2/3], Qs).
%@    Qs = [1/6,3/5].

%?- meet_def([0/6,4/6], [1/6,2/3], Qs).
%@    Qs = [1/6,3/5].

%?- AmB =[1/6,3/5], A=[0/6,4/6], B=[1/6,2/3], AmB '≼' A, AmB '≼' B.
%@    AmB = [1/6,3/5], A = [0/6,4/6], B = [1/6,2/3].

%?- A = [0/6,4/6], coefs(1, A, Hs, Os), coefs(1, _A, Hs, Os).
%@    A = [0/6,4/6], Hs = [0,-4], Os = [4,-2], _A = [0/6,4/6].
%?- B = [1/6,2/3], coefs(1, B, Hs, Os), coefs(1, _B, Hs, Os).
%@    B = [1/6,2/3], Hs = [-1,-3], Os = [3,-3], _B = [1/6,2/3].
%?- coefs(1, AmB, [-1,-4], [3,-3]).
%@    AmB = [1/6,3/5].


% TODO: Compare the computation by meet/3 against a brute-force calculation
%       that directly implements the _definition_ of meet.  This comparison
%       ought to demonstrate that meets are indeed *unique*.
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

%?- nmax_meet(6, [0/6,4/6], [1/6,2/3], Qs).
%@    Qs = [1/6,3/5].

:- table d_endtally_rec/3.

% This predicate describes precisely the final tallies and dose recommendations
% which terminate the paths of the D-dose 3+3 design as described by our DCG.
% Memoizing it via *tabling* supports a _complete_ description at the cost of
% only a single, one-off comprehensive elaboration of the DCG.
d_endtally_rec(D, FinalTally, Rec) :-
    length(Init, D), maplist(=(0/0), Init), Init = [I|Is],
    phrase(path([I]-Is), Path),
    phrase((..., [Endstate,stop,recommend_dose(Rec)]), Path),
    state_tallies(Endstate, FinalTally).
    
%?- d_endtally_rec(2, Q, D).
%@    Q = [0/3,0/6], D = 2
%@ ;  Q = [0/3,1/6], D = 2
%@ ;  Q = [0/6,2/3], D = 1
%@ ;  Q = [0/6,2/6], D = 1
%@ ;  Q = [0/6,3/3], D = 1
%@ ;  Q = [0/6,3/6], D = 1
%@ ;  Q = [0/6,4/6], D = 1
%@ ;  Q = [1/6,0/6], D = 2
%@ ;  Q = [1/6,1/6], D = 2
%@ ;  Q = [1/6,2/3], D = 1
%@ ;  Q = [1/6,2/6], D = 1
%@ ;  Q = [1/6,3/3], D = 1
%@ ;  Q = [1/6,3/6], D = 1
%@ ;  Q = [1/6,4/6], D = 1
%@ ;  Q = [2/3,0/0], D = 0
%@ ;  Q = [2/6,0/0], D = 0
%@ ;  Q = [2/6,2/3], D = 0
%@ ;  Q = [2/6,2/6], D = 0
%@ ;  Q = [2/6,3/3], D = 0
%@ ;  Q = [2/6,3/6], D = 0
%@ ;  Q = [2/6,4/6], D = 0
%@ ;  Q = [3/3,0/0], D = 0
%@ ;  Q = [3/6,0/0], D = 0
%@ ;  Q = [3/6,2/3], D = 0
%@ ;  Q = [3/6,2/6], D = 0
%@ ;  Q = [3/6,3/3], D = 0
%@ ;  Q = [3/6,3/6], D = 0
%@ ;  Q = [3/6,4/6], D = 0
%@ ;  Q = [4/6,0/0], D = 0
%@ ;  false.

% Now we readily "check the functoriality" of the dose recommendations
/*
?- d_endtally_rec(2, Q1, D1),
   d_endtally_rec(2, Q2, D2),
   Q1 '≼' Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% A different way to put this would be:
/*
?- d_endtally_rec(2, Q1, D1),
   d_endtally_rec(2, Q2, D2),
      Q1 '≼' Q2,  % Q1 is evidently no safer than Q2,
   #\(D1 #=< D2). % yet D1 is NOT likewise related to D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% That initial listing in Section 4.1 ought to have been done with
% this predicate too!
/*
?- N+\(setof(Q-Rec, d_endtally_rec(2, Q, Rec), QRecs),
       maplist(portray_clause, QRecs),
       length(QRecs, N)).
%@ [0/3,0/6]-2.
%@ [0/3,1/6]-2.
%@ [0/6,2/3]-1.
%@ [0/6,2/6]-1.
%@ [0/6,3/3]-1.
%@ [0/6,3/6]-1.
%@ [0/6,4/6]-1.
%@ [1/6,0/6]-2.
%@ [1/6,1/6]-2.
%@ [1/6,2/3]-1.
%@ [1/6,2/6]-1.
%@ [1/6,3/3]-1.
%@ [1/6,3/6]-1.
%@ [1/6,4/6]-1.
%@ [2/3,0/0]-0.
%@ [2/6,0/0]-0.
%@ [2/6,2/3]-0.
%@ [2/6,2/6]-0.
%@ [2/6,3/3]-0.
%@ [2/6,3/6]-0.
%@ [2/6,4/6]-0.
%@ [3/3,0/0]-0.
%@ [3/6,0/0]-0.
%@ [3/6,2/3]-0.
%@ [3/6,2/6]-0.
%@ [3/6,3/3]-0.
%@ [3/6,3/6]-0.
%@ [3/6,4/6]-0.
%@ [4/6,0/0]-0.
%@    N = 29.
*/

% Clearly, some of these 29 final tallies must be shared
% between several of the 46 distinct trial paths.
% Let's demonstrate how!

endtally_path(FinalTally, Path) :-
    phrase(path([0/0]-[0/0]), Path),
    phrase((..., [Endstate,stop,recommend_dose(_)]), Path),
    state_tallies(Endstate, FinalTally).

%?- endtally_path(Q, P).
%@    Q = [0/3,0/6], P = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[0/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  Q = [0/3,1/6], P = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[1/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  ... .

/*
It's time now to investigate what trial designs arise from
a rectified tally-dose mapping.  We are looking for all
incremental enrollments that are consistent with the
preorder obtained 
*/

/*
?- d_mendtally_rec(2, Q1, D1),
   d_mendtally_rec(2, Q2, D2),
   Q1 '≼' Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    false. % Rectification was successful.
*/

% Some good visualizations would seem to be necessary now
% to promote efficient progress.  What Hasse diagrams could
% we draw for the partial order ≼ restricted to final tallies?
% Note that it could be interesting to define Hasse diagrams
% declaratively, and have Prolog find *all* of them for me.
% But to begin, let's explore some special solutions yielded
% by specific heuristics.

% Suppose we take a list (qua set) of all final tallies, and
% recursively peel off the minimal elements, i.e. those which
% have no arrows into the remainder.
minimal_in(M, Qs) :-
    member(M, Qs),
    maplist('⊁'(M), Qs).

/*
?- Ms+\(findall(Q, d_mendtally_rec(2,Q,_), FinalTallies),
        findall(M, minimal_in(M, FinalTallies), Ms)).
%@    Ms = [[3/3,0/0],[3/6,3/3],[3/6,4/6],[4/6,0/0]].
*/

% The https://en.wikipedia.org/wiki/Covering_relation is
% fundamental, and surely warrants a dedicated predicate.
% NB: The time-complexity of in_cover_t/3 could be reduced
%     by exploiting the arithmetized sort behind d_strata/2.
%     But we retain this implementation for the time being,
%     since its simplicity renders it 'obviously' correct.
in_cover_t(Qs, Q1, Q2, Truth) :-
    member(Q1, Qs),
    member(Q2, Qs),
    Q1 '≺' Q2,
    if_(tmember_t(between_t(Q1,Q2), Qs),
        Truth = false,
        Truth = true
       ).

between_t(Q1, Q2, Q, Truth) :-
    if_((Q1 '≺' Q, Q '≺' Q2),
        Truth = true,
        Truth = false
       ).

in_cover(Qs, Q1, Q2) :- in_cover_t(Qs, Q1, Q2, true).

d_ncovers(D, N) :-
    findall(Q, d_mendtally_rec(D,Q,_), Qs),
    findall(Q1-Q2, in_cover(Qs, Q1, Q2), Covers),
    length(Covers, N).

%?- time(d_ncovers(2, N)).
%@    % CPU time: 8.045s, 40_522_204 inferences
%@    N = 50.

%?- time(d_ncovers(3, N)).
%@    % CPU time: 242.710s, 1_230_061_670 inferences
%@    N = 194.

% At least for the D=2 case, a useful Hasse diagram for 𝒬f seems within reach.
% One thing that could be of special help would be finding small sets of q's
% that share the same covered and covering elements, since these could be
% collected into single nodes of the Hasse diagram.
% As a step toward finding any such little collections, let me partition 𝒬f
% into a list of recursively peeled-off minimal sets.

%?- findall(Q, d_mendtally_rec(2, Q, _), Qs), findall(Qm, minimal_in(Qm, Qs), Qms).
%@    Qs = [[0/3,0/6],[0/3,1/6],[0/6,2/3],[0/6,2/6],[0/6,3/3],[0/6,3/6],[0/6,4/6],[1/6,0/6],[1/6,1/6],[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6],[2/3,0/0],[2/6,0/0],[2/6,2/3],[2/6,2/6],[2/6,... / ...],[... / ...|...]|...], Qms = [[3/3,0/0],[3/6,3/3],[3/6,4/6],[4/6,0/0]].

% Thus, it seems k'th element of Hs ranges from -k*Nmax to 0.
% This is at least rather simple!  But the Os look a bit more
% complicated in this respect.
% ---
% And, as expected, the Hs have not changed, since only the
% top, right block --- (γ,σ's) vs (u's) --- of our inverse
% matrix has changed.

%?- coefs(3, [6/6,6/6,6/6,6/6], Hs, Os).
%@    Hs = [-6,-12,-18,-24], Os = [-72,-78,-84,-90].
%?- coefs(2, [6/6,6/6,6/6,6/6], Hs, Os).
%@    Hs = [-6,-12,-18,-24], Os = [-48,-54,-60,-66].
%?- coefs(1, [6/6,6/6,6/6,6/6], Hs, Os).
%@    Hs = [-6,-12,-18,-24], Os = [-24,-30,-36,-42].
% Can we understand the above, in light of the formulae?
% Our γ = -r∑t + ∑u should have minimum value -6rD, and
% maximum value 6D.  Each subsequent element of (γ,σ's)
% (i.e., the σ's in turn) can be no higher, and at most
% 6D lower, than its predecessor.

% But we can say even more about the upper limits,
% since these are attained in the case tₖ≡0!  The
% upper limits are therefore independent of r, and
% just the same descending sequence found for r=1.
%?- coefs(3, [0/6,0/6,0/6,0/6], Hs, Os).
%@    Hs = [0,0,0,0], Os = [24,18,12,6].
%?- coefs(2, [0/6,0/6,0/6,0/6], Hs, Os).
%@    Hs = [0,0,0,0], Os = [24,18,12,6].
%?- coefs(1, [0/6,0/6,0/6,0/6], Hs, Os).
%@    Hs = [0,0,0,0], Os = [24,18,12,6].

% Therefore, the _range_ of Os (which is what matters
% in determining the bases of our 'digits') are all
% equal at 6D(r+1).
% Accordingly, we need only update os_base/2 below.

% To encode the Hs, we can reuse existing infrastructure, as-is
hs_enc(Hs, K) :- ws_int(Hs, K).

% To encode Os, we need only encode a base-(6*D*(R+1)+1) integer.
% (Note that we need not even insist on non-negative 'digits',
% since any bias in a given digit will bias the whole encoding
% consistently, with no effect on the _order_.)
r_os_enc(R, Os, K) :-
    r_os_base(R, Os, B),
    foldl(base_(B), Os, 0, K).

r_os_base(R, Os, B) :-
    #R #> 0, length(Os, D),
    #B #= 6 * #D * (#R+1) + 1.

base_(B, A, N0, N) :- #N #= #B * #N0 + #A.

%?- foldl(base_(10), [1,2,3,4], 0, N).
%@    N = 1234.

%?- Os = [18,12,6], r_os_enc(1, Os, K).
%@    Os = [18,12,6], K = 25092. % Now with the R+1 correction
%@    Os = [18,12,6], K = 6732.  % w/o missing factor (R+1)=2
%@    Os = [18,12,6], K = 6732.

qs_int(Qs, K) :-
    coefs(Qs, Hs, Os),
    hs_enc(Hs, HK),
    os_enc(Os, OK),
    same_length(Hs, _s), placevalues([P|_s]),
    #K #= #OK * #P + #HK.

%?- qs_int([1/1,2/3], K).
%@    K = -4845.

%?- Qs = [0/0,0/0], qs_int(Qs, K).
%@    Qs = [0/0,0/0], K = 0.

% Let's now check this encoding, to be sure it embeds every
% arrow of ≼.
d_nmax_wrongway(D, Nmax, Q1s, Q2s) :-
    qs_d_nmax(Q1s, D, Nmax), qs_int(Q1s, K1),
    qs_d_nmax(Q2s, D, Nmax), qs_int(Q2s, K2),
    #K1 #> #K2, % fail faster
    Q1s '≼' Q2s.

%?- time(d_nmax_wrongway(2, 3, Q1, Q2)).
%@    % CPU time: 9.830s, 49_914_610 inferences
%@    false.
%?- time(d_nmax_wrongway(2, 4, Q1, Q2)).
%@    % CPU time: 50.442s, 253_653_892 inferences
%@    false.
%?- time(d_nmax_wrongway(2, 5, Q1, Q2)).
%@    % CPU time: 188.544s, 971_725_303 inferences
%@    false.
%?- time(d_nmax_wrongway(2, 6, Q1, Q2)).
%@    % CPU time: 614.967s, 3_077_569_171 inferences
%@    false.
%?- time(d_nmax_wrongway(3, 1, Q1, Q2)).
%@    % CPU time: 0.933s, 4_748_033 inferences
%@    false.
%?- time(d_nmax_wrongway(3, 2, Q1, Q2)).
%@    % CPU time: 60.008s, 299_088_422 inferences
%@    false.
%?- time(d_nmax_wrongway(3, 3, Q1, Q2)).
%@    % CPU time: 1147.127s, 4_811_099_116 inferences
%@    false.

% By embedding the partial order ≼ into a *complete* order,
% I could sort 𝒬f so that all arrows of ≼ point left-to-right.
% Then, minimal sets would be in contiguous stretches of this
% sorted list, and identifying the partitions could be done
% potentially quite efficiently.

% I would expect that this list of (recursively) minimal sets
% would itself be useful for computing the covering relation.
% (Exactly *how* it would help remains to be discovered.)

% One way to obtain a complete order would be to arithmetize
% the tallies.

% Let's try a more compact embedding of 𝒬 ↪ (ℕ,≤) ...

% To begin, let's just encode a vector (X_1,..,X_D), where Xn ∈ 0..(6*n).
% This corresponds to a 'variable-base' number where the nth 'place' has
% a 'digit' with value in 0..Mn, with Mn = 6n.
% The _value_ of the nth place in such a number is the product
%   Pn = B1*...*B_{n-1}, n ∈ 0..(D-1).
% For example, the D=3 case would have
%   K = X1 + B1*(X2 + B2*(X3)) = X1 + B1*X2 + B1*B2*X3.
% The general case can be developed more easily by defining the products
%   Pn = B1*...*Bn, for n in 1..D-1.
% Then we have
%   P1 = 1, P2 = B1, ..., P_D = B1*...*B_{D-1}
%   K = P1*X1 + P2*X2 + P3*X3.
% The values (X1,...,XD) may then be recovered from K by repeated
% division-with-remainder operations.

% Could I start with a good, recursive definition of the Ps?
% I think I want to build the list in descending order, so that
% P1 goes deepest, P2 above it, and so on.
% This correlates best with our normal way of writing numbers,
% putting MSD's leftmost and LSD's rightmost.

pvs([P|Ps]) :-
    pvs(Ps),
    pvs_nextup(Ps, P).
pvs([]).

pvs_nextup([], 1).
pvs_nextup([P|Ps], P1) :-
    length([P|Ps], N),
    #P1 #= #P * (6*N + 1).

% Let's just PRECOMPUTE!
%?- length(Ps, 8), pvs(Ps), reverse(Ps, Rs).
%@    Ps = [2131900225,49579075,1339975,43225,1729,91,7,1], Rs = [1,7,91,1729,43225,1339975,49579075,2131900225].

placevalues(Ps) :-
    same_length(Ps, Rs),
    % NB: Taking a _tail_ with append/3 would leave a choice point.
    append(Rs, _, [1,7,91,1729,43225,1339975,49579075,2131900225]),
    reverse(Rs, Ps).

%?- length(Ps, 5), placevalues(Ps).
%@    Ps = [43225,1729,91,7,1].

% At this point, the encoding is extremely straightforward.
%?- scalar_product([1,2,3], [4,5,6], #=, #Ooh).
%@    Ooh = 32.

ws_int(Ws, K) :-
    same_length(Ws, Ps),
    placevalues(Ps),
    reverse(Ws, RWs), % our Us and Ts are typically indexed 1..D
    scalar_product(RWs, Ps, #=, #K).

% Contrary to my presumptions in that last commit, our
% previous encoding should be retained, and continues
% to support sorting of the Qs by their unique keys.
% A clearer accounting for how and why this works is
% sorely needed, however!
%
% Keeping in mind that ≼ is in fact a _partial order_,
% which justifies the use of '≺' for '≼ ∖ =', we want
% to ensure that
%
%    q ≺ q' ⟹ K(q) < K(q')  ∀ q, q'∈ 𝒬,
%
% so that the Key sorting can discriminate between q's
% sharing the same Ts profile but differing in the Us.
% (The weaker implication ≼ ⟹ ≤ simply won't suffice.)

d_sortedQfs(D, SQs) :-
    findall(Q, d_mendtally_rec(D,Q,_), Qs),
    qs_sorted(Qs, SQs).

% TODO: Clear up this 'legacy' default descending sort.
qs_sorted(Qs, DescQs) :- po_qs_sorted('≽', Qs, DescQs).

po_qs_sorted('≼', Qs, AscQs) :-
    maplist(qs_int, Qs, Ks),
    pairs_keys_values(KQs, Ks, Qs),
    sort(KQs, SKQs),
    pairs_values(SKQs, AscQs).
    
po_qs_sorted('≽', Qs, DescQs) :-
    po_qs_sorted('≼', Qs, AscQs),
    reverse(AscQs, DescQs).
    

%?- d_sortedQfs(2, Qfs).
%@ Sorting length-29 list Qs:
%@   .. encoding Qs:   % CPU time: 0.018s, 50_122 inferences
%@    % CPU time: 0.020s, 52_406 inferences
%@    Qfs = [[1/6,0/6],[0/3,0/6],[0/6,2/6],[1/6,1/6],[0/3,1/6],[0/6,3/6],[1/6,2/6],[0/6,2/3],[0/6,4/6],[1/6,3/6],[2/6,2/6],[0/6,3/3],[1/6,2/3],[2/6,0/0],[1/6,4/6],[2/6,3/6],[3/6,2/6],[1/6,3/3],[2/6,... / ...],[... / ...|...]|...].
%?- d_sortedQfs(2, Qfs).

% After PRECOMPUTING placevalues/1
%?- D=3, findall(Q, qs_d_nmax(Q, D, 6), Qs), time(qs_sorted(Qs, SQs)).
%@ Encoding Qs...    % CPU time: 27.665s, 151_958_265 inferences
%@ Sorting Qs....    % CPU time: 0.019s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.020s, 175_617 inferences
%@ Decoding......    % CPU time: 49.427s, 314_906_923 inferences
%@    % CPU time: 77.143s, 467_092_723 inferences
%@    D = 3, Qs = [[0/0,0/0,0/0],[0/0,0/0,0/1],[0/0,0/0,1/1],[0/0,0/0,0/2],[0/0,0/0,1/2],[0/0,0/0,2/2],[0/0,0/0,0/3],[0/0,0/0,1/3],[0/0,0/0,2/3],[0/0,0/0,3/3],[0/0,0/0,0/4],[0/0,0/0,1/4],[0/0,0/0,2/4],[0/0,0/0,3/4],[0/0,0/0,4/4],[0/0,0/0,0/5],[0/0,0/0,1/5],[0/0,0/0,... / ...],[0/0,... / ...|...],[... / ...|...]|...], SQs = [[0/6,0/6,0/6],[0/6,0/6,0/5],[0/6,0/5,0/6],[0/5,0/6,0/6],[0/6,0/6,0/4],[0/6,0/5,0/5],[0/5,0/6,0/5],[0/6,0/4,0/6],[0/5,0/5,0/6],[0/4,0/6,0/6],[0/6,0/6,0/3],[0/6,0/5,0/4],[0/5,0/6,0/4],[0/6,0/4,0/5],[0/5,0/5,0/5],[0/4,0/6,0/5],[0/6,0/3,0/6],[0/5,0/4,... / ...],[0/4,... / ...|...],[... / ...|...]|...].

% After tabling d_placevalues/2 ...
%?- D=3, findall(Q, qs_d_nmax(Q, D, 6), Qs), time(qs_sorted(Qs, SQs)).
%@ Encoding Qs...    % CPU time: 38.165s, 204_883_070 inferences
%@ Sorting Qs....    % CPU time: 0.017s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.020s, 175_617 inferences
%@ Decoding......    % CPU time: 52.788s, 329_439_147 inferences
%@    % CPU time: 91.002s, 534_549_657 inferences
%@    D = 3, Qs = [[0/0,0/0,0/0],[0/0,0/0,0/1],[0/0,0/0,1/1],[0/0,0/0,0/2],[0/0,0/0,1/2],[0/0,0/0,2/2],[0/0,0/0,0/3],[0/0,0/0,1/3],[0/0,0/0,2/3],[0/0,0/0,3/3],[0/0,0/0,0/4],[0/0,0/0,1/4],[0/0,0/0,2/4],[0/0,0/0,3/4],[0/0,0/0,4/4],[0/0,0/0,0/5],[0/0,0/0,1/5],[0/0,0/0,... / ...],[0/0,... / ...|...],[... / ...|...]|...], SQs = [[0/6,0/6,0/6],[0/6,0/6,0/5],[0/6,0/5,0/6],[0/5,0/6,0/6],[0/6,0/6,0/4],[0/6,0/5,0/5],[0/5,0/6,0/5],[0/6,0/4,0/6],[0/5,0/5,0/6],[0/4,0/6,0/6],[0/6,0/6,0/3],[0/6,0/5,0/4],[0/5,0/6,0/4],[0/6,0/4,0/5],[0/5,0/5,0/5],[0/4,0/6,0/5],[0/6,0/3,0/6],[0/5,0/4,... / ...],[0/4,... / ...|...],[... / ...|...]|...]
%@ ;  % CPU time: 0.180s, 768_320 inferences
%@    % CPU time: 0.385s, 2_897_664 inferences
%@    % CPU time: 0.568s, 3_669_656 inferences
%@    false.

% I've discovered qs_sorted/2 accounts for 80% of run-time for d_gs/2 (D=3 case)
%?- D=3, findall(Q, qs_d_nmax(Q, D, 6), Qs), time(qs_sorted(Qs, SQs)).
%@ Encoding Qs...    % CPU time: 101.706s, 580_549_113 inferences
%@ Sorting Qs....    % CPU time: 0.020s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.019s, 175_617 inferences
%@ Decoding......    % CPU time: 72.479s, 438_562_539 inferences
%@    % CPU time: 174.236s, 1_019_339_176 inferences
%@    D = 3, Qs = [[0/0,0/0,0/0],[0/0,0/0,0/1],[0/0,0/0,1/1],[0/0,0/0,0/2],[0/0,0/0,1/2],[0/0,0/0,2/2],[0/0,0/0,0/3],[0/0,0/0,1/3],[0/0,0/0,2/3],[0/0,0/0,3/3],[0/0,0/0,0/4],[0/0,0/0,1/4],[0/0,0/0,2/4],[0/0,0/0,3/4],[0/0,0/0,4/4],[0/0,0/0,0/5],[0/0,0/0,1/5],[0/0,0/0,... / ...],[0/0,... / ...|...],[... / ...|...]|...], SQs = [[0/6,0/6,0/6],[0/6,0/6,0/5],[0/6,0/5,0/6],[0/5,0/6,0/6],[0/6,0/6,0/4],[0/6,0/5,0/5],[0/5,0/6,0/5],[0/6,0/4,0/6],[0/5,0/5,0/6],[0/4,0/6,0/6],[0/6,0/6,0/3],[0/6,0/5,0/4],[0/5,0/6,0/4],[0/6,0/4,0/5],[0/5,0/5,0/5],[0/4,0/6,0/5],[0/6,0/3,0/6],[0/5,0/4,... / ...],[0/4,... / ...|...],[... / ...|...]|...].

%?- D=2, findall(Q, qs_d_nmax(Q, D, 6), Qs), time(qs_sorted(Qs, SQs)).
%@ Encoding Qs...    % CPU time: 2.410s, 13_546_869 inferences
%@ Sorting Qs....    % CPU time: 0.000s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.000s, 4_705 inferences
%@ Decoding......    % CPU time: 1.780s, 11_012_059 inferences
%@    % CPU time: 4.197s, 24_573_088 inferences
%@    D = 2, Qs = [[0/0,0/0],[0/0,0/1],[0/0,1/1],[0/0,0/2],[0/0,1/2],[0/0,2/2],[0/0,0/3],[0/0,1/3],[0/0,2/3],[0/0,3/3],[0/0,0/4],[0/0,1/4],[0/0,2/4],[0/0,3/4],[0/0,4/4],[0/0,0/5],[0/0,1/5],[0/0,2/5],[0/0,... / ...],[... / ...|...]|...], SQs = [[0/6,0/6],[0/6,0/5],[0/5,0/6],[0/6,0/4],[0/5,0/5],[0/4,0/6],[0/6,0/3],[0/5,0/4],[0/4,0/5],[0/3,0/6],[0/6,0/2],[0/5,0/3],[0/4,0/4],[0/3,0/5],[0/2,0/6],[0/6,0/1],[0/5,0/2],[0/4,0/3],[0/3,... / ...],[... / ...|...]|...].

% And the above now points to encoding qs_int/2 and decoding int_qs/2
% as accounting for the ENTIRE run-time of qs_sorted/2!

%?- qs_d_nmax(Q, 2, 6).
%@    Q = [0/0,0/0]
%@ ;  Q = [0/0,0/1]
%@ ;  Q = [0/0,1/1]
%@ ;  Q = [0/0,0/2]
%@ ;  Q = [0/0,1/2]
%@ ;  Q = [0/0,2/2]
%@ ;  Q = [0/0,0/3]
%@ ;  ... .

%?- findall(Q, qs_d_nmax(Q, 2, 6), Qs), length(Qs, N).
%@    Qs = [[0/0,0/0],[0/0,0/1],[0/0,1/1],[0/0,0/2],[0/0,1/2],[0/0,2/2],[0/0,0/3],[0/0,1/3],[0/0,2/3],[0/0,3/3],[0/0,0/4],[0/0,1/4],[0/0,2/4],[0/0,3/4],[0/0,4/4],[0/0,0/5],[0/0,1/5],[0/0,2/5],[0/0,... / ...],[... / ...|...]|...], N = 784.
%@    Qs = [[0/0,0/0],[0/0,0/1],[0/0,1/1],[0/0,0/2],[0/0,1/2],[0/0,2/2],[0/0,0/3],[0/0,1/3],[0/0,2/3],[0/0,3/3],[0/1,0/0],[1/1,0/0],[0/1,0/1],[0/1,1/1],[1/1,0/1],[1/1,1/1],[0/1,0/2],[0/1,1/2],[0/1,... / ...],[... / ...|...]|...], N = 100.

%?- D=3, Nmax=6, L+\(findall(Q, qs_d_nmax(Q, D, Nmax), Qs), qs_sorted(Qs, SQs), length(SQs, L)).
%@    error(existence_error(procedure,qs_d_nmax/3),qs_d_nmax/3).

%?- d_sortedQfs(2, SQs), length(SQs, L).
%@    SQs = [[0/3,0/6],[0/3,1/6],[1/6,0/6],[0/6,2/6],[0/6,2/3],[1/6,1/6],[2/6,0/0],[2/3,0/0],[0/6,3/6],[0/6,3/3],[1/6,2/6],[1/6,2/3],[3/6,0/0],[3/3,0/0],[0/6,4/6],[1/6,3/6],[1/6,3/3],[2/6,2/6],[2/6,... / ...],[... / ...|...]|...], L = 29.

%?- d_sortedQfs(3, SQs), length(SQs, L).
%@    SQs = [[0/3,0/3,0/6],[0/3,0/3,1/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[0/3,0/6,2/6],[0/3,0/6,2/3],[0/3,1/6,1/6],[1/6,0/3,1/6],[0/6,2/6,0/0],[0/6,2/3,0/0],[1/6,1/6,0/6],[2/6,0/0,0/0],[2/3,0/0,0/0],[0/3,0/6,3/6],[0/3,0/6,3/3],[0/3,1/6,2/6],[0/3,1/6,2/3],[1/6,0/6,... / ...],[1/6,... / ...|...],[... / ...|...]|...], L = 93.

%?- d_sortedQfs(4, SQs), length(SQs, L).
%@    SQs = [[0/3,0/3,0/3,0/6],[0/3,0/3,0/3,1/6],[0/3,0/3,1/6,0/6],[0/3,1/6,0/3,0/6],[1/6,0/3,0/3,0/6],[0/3,0/3,0/6,2/6],[0/3,0/3,0/6,2/3],[0/3,0/3,1/6,1/6],[0/3,1/6,0/3,1/6],[1/6,0/3,0/3,1/6],[0/3,0/6,2/6,0/0],[0/3,0/6,2/3,0/0],[0/3,1/6,1/6,0/6],[1/6,0/3,1/6,0/6],[0/6,2/6,0/0,0/0],[0/6,2/3,0/0,0/0],[1/6,1/6,0/3,... / ...],[2/6,0/0,... / ...|...],[2/3,... / ...|...],[... / ...|...]|...], L = 261.

% The guarantee I have regarding such a sorted Qf list is that,
% if I process its elements front-to-back, each next element
% cannot be below any of those previously processed.
% In particular, I do NOT have a guarantee that all minimal
% elements are contiguous in the front of the list!
% Nevertheless, this weaker guarantee is able to support
% an efficient stratification of the list into recursively
% peeled-off maximal sets.

sift(Q, [Bot|Higher], Strata) :-
    if_(tmember_t('≼'(Q), Bot),
        Strata = [[Q],Bot|Higher],
        sift_(Higher, Q, Bot, Strata)).

sift_([], Q, Bot, [[Q|Bot]]).
sift_([Next|More], Q, Bot, Strata) :-
    if_(tmember_t('≼'(Q), Next),
        Strata = [[Q|Bot],Next|More],
        (   Strata = [Bot|Strata1],
            sift_(More, Q, Next, Strata1)
        )
       ).

d_strata(D, Qss) :-
    d_sortedQfs(D, Qfs),
    foldl(sift, Qfs, [[]], RQss),
    reverse(RQss, Qss).

%?- S+\(d_strata(2, Qss), maplist(portray_clause, Qss), length(Qss, S)).
%@ [[0/6,2/6],[1/6,0/6],[0/3,0/6]].
%@ [[0/6,3/6],[1/6,1/6],[0/6,2/3],[0/3,1/6]].
%@ [[0/6,4/6],[1/6,2/6],[0/6,3/3],[2/6,0/0]].
%@ [[1/6,3/6],[1/6,2/3],[2/3,0/0]].
%@ [[1/6,4/6],[2/6,2/6],[1/6,3/3],[3/6,0/0]].
%@ [[2/6,3/6],[2/6,2/3],[3/3,0/0]].
%@ [[2/6,4/6],[3/6,2/6],[2/6,3/3],[4/6,0/0]].
%@ [[3/6,3/6],[3/6,2/3]].
%@ [[3/6,4/6],[3/6,3/3]].
%@    S = 9.

%?- S+\(d_strata(3, Qss), maplist(portray_clause, Qss), length(Qss, S)).
%@ [[0/6,2/6,2/6],[1/6,0/6,2/6],[1/6,1/6,0/6],[0/6,2/6,0/0],[0/3,0/6,2/6],[1/6,0/3,0/6],[0/3,1/6,0/6],[0/3,0/3,0/6]].
%@ [[0/6,2/6,3/6],[0/6,2/6,2/3],[1/6,0/6,3/6],[0/6,3/6,0/0],[1/6,1/6,1/6],[1/6,0/6,2/3],[0/3,0/6,3/6],[0/6,2/3,0/0],[1/6,0/3,1/6],[0/3,1/6,1/6],[0/3,0/6,2/3],[0/3,0/3,1/6]].
%@ [[0/6,2/6,4/6],[0/6,3/6,2/6],[0/6,2/6,3/3],[1/6,0/6,4/6],[0/6,4/6,0/0],[1/6,1/6,2/6],[1/6,0/6,3/3],[0/3,0/6,4/6],[1/6,2/6,0/0],[0/6,3/3,0/0],[0/3,1/6,2/6],[0/3,0/6,3/3],[2/6,0/0,0/0]].
%@ [[0/6,3/6,3/6],[0/6,3/6,2/3],[1/6,1/6,3/6],[1/6,1/6,2/3],[0/3,1/6,3/6],[1/6,2/3,0/0],[0/3,1/6,2/3],[2/3,0/0,0/0]].
%@ [[0/6,3/6,4/6],[0/6,3/6,3/3],[1/6,1/6,4/6],[1/6,2/6,2/6],[1/6,1/6,3/3],[0/3,1/6,4/6],[1/6,3/6,0/0],[0/3,1/6,3/3],[3/6,0/0,0/0]].
%@ [[1/6,2/6,3/6],[1/6,2/6,2/3],[2/6,2/6,0/0],[1/6,3/3,0/0],[3/3,0/0,0/0]].
%@ [[1/6,2/6,4/6],[1/6,3/6,2/6],[1/6,2/6,3/3],[1/6,4/6,0/0],[2/6,2/3,0/0]].
%@ [[1/6,3/6,3/6],[2/6,2/6,2/6],[1/6,3/6,2/3],[2/6,3/6,0/0],[4/6,0/0,0/0]].
%@ [[1/6,3/6,4/6],[2/6,2/6,3/6],[1/6,3/6,3/3],[2/6,2/6,2/3],[3/6,2/6,0/0],[2/6,3/3,0/0]].
%@ [[2/6,2/6,4/6],[2/6,3/6,2/6],[2/6,2/6,3/3],[2/6,4/6,0/0],[3/6,2/3,0/0]].
%@ [[2/6,3/6,3/6],[3/6,2/6,2/6],[2/6,3/6,2/3],[3/6,3/6,0/0]].
%@ [[2/6,3/6,4/6],[3/6,2/6,3/6],[2/6,3/6,3/3],[3/6,2/6,2/3],[3/6,3/3,0/0]].
%@ [[3/6,2/6,4/6],[3/6,3/6,2/6],[3/6,2/6,3/3],[3/6,4/6,0/0]].
%@ [[3/6,3/6,3/6],[3/6,3/6,2/3]].
%@ [[3/6,3/6,4/6],[3/6,3/6,3/3]].
%@    S = 15.

% Write out Hasse diagram as (GraphViz) DOT file.
d_writehassedot(D) :-
    phrase(format_("HasseD~d.dot", [D]), Filename),
    atom_chars(File, Filename),
    format("Opening file ~q...~n", [File]), % feedback to console
    setup_call_cleanup(open(File, write, OS),
		       (   format("Collecting final tallies ..", []),
                           % NB: We use _unrectified_ d_endtally_rec/3 to exhibit
                           %     the non-functoriality of default 3+3 dose recs.
                           findall(Q-X, d_endtally_rec(D,Q,X), QXs),
                           pairs_keys(QXs, Qs),
                           length(Qs, Nf),
                           format("~n sorting ~d final tallies ..", [Nf]),
                           po_qs_sorted('≽', Qs, DescQs),
                           format("~n stratifying ..~n", []),
                           foldl(sift, DescQs, [[]], Qss),
                           reverse(Qss, RQss), maplist(portray_clause, RQss),
                           format(OS, "strict digraph hasseD~d {~n", [D]),
                           format(OS, "  rankdir=~a;~n", ['BT']),
                           format(OS, "  node [colorscheme=~w, fontname=\"~w\"];~n",
                                  ['set14','Helvetica:bold']),
                           format("Writing strata to DOT file ..", []),
                           list_to_assoc(QXs, QXassoc),
                           maplist(write_stratum(OS,QXassoc), Qss),
                           format("~n writing covering relation ..", []) ->
                           reverse(DescQs, AscQs), % speeds cover calculation
                           time((   in_cover(AscQs, Q1, Q2),
			            format(OS, "  \"~w\" -> \"~w\";~n", [Q1,Q2]),
			            fail % exhaust all (Q1 -> Q2) arrows
			        ;   true
			        )),
                           format(OS, "}~n", [])
		       ),
		       close(OS)
		      ),
    format(".. done.~n", []).

write_stratum(OS, QXassoc, Qs) :-
    format(OS, "  { rank=same;~n", []),
    maplist(\Q^(get_assoc(Q, QXassoc, X), #Color #= #X + 1,
                format(OS, "    \"~w\" [fontcolor=~d];~n", [Q,Color])),
            Qs),
    format(OS, "  }~n", []).

%?- d_writehassedot(2). % after reworking qs_mins/2 & qs_maxs/2 ..
%@ Opening file 'HasseD2.dot'...
%@ Collecting final tallies ..
%@  sorting 29 final tallies ..
%@  stratifying ..
%@ [[0/3,0/6],[1/6,0/6]].
%@ [[0/3,1/6],[0/6,2/6]].
%@ [[0/6,2/3],[0/6,3/6],[1/6,1/6]].
%@ [[2/6,0/0],[0/6,3/3],[0/6,4/6],[1/6,2/6]].
%@ [[2/3,0/0],[1/6,2/3],[1/6,3/6]].
%@ [[3/6,0/0],[1/6,3/3],[1/6,4/6],[2/6,2/6]].
%@ [[3/3,0/0],[2/6,2/3],[2/6,3/6]].
%@ [[4/6,0/0],[2/6,3/3],[2/6,4/6],[3/6,2/6]].
%@ [[3/6,2/3],[3/6,3/6]].
%@ [[3/6,3/3],[3/6,4/6]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 6.579s, 22_554_937 inferences
%@ .. done.
%@    true.

%?- d_writehassedot(3).
%@ Opening file 'HasseD3.dot'...
%@ Collecting final tallies ..
%@  sorting 93 final tallies ..
%@  stratifying ..
%@ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@ [[0/3,0/3,1/6],[0/3,0/6,2/6],[1/6,0/3,0/6]].
%@ [[0/3,0/6,2/3],[0/3,0/6,3/6],[0/3,1/6,1/6],[1/6,0/6,2/6]].
%@ [[0/3,0/6,3/3],[0/3,0/6,4/6],[0/6,2/6,0/0],[0/3,1/6,2/6],[0/6,2/6,2/6],[1/6,0/3,1/6],[1/6,1/6,1/6]].
%@ [[0/6,2/3,0/0],[0/3,1/6,2/3],[0/3,1/6,3/6],[0/6,2/6,3/6],[1/6,0/6,2/3],[1/6,0/6,3/6]].
%@ [[2/6,0/0,0/0],[0/3,1/6,3/3],[0/3,1/6,4/6],[0/6,3/6,0/0],[0/6,2/6,2/3],[1/6,0/6,3/3],[0/6,3/6,2/6],[1/6,0/6,4/6],[1/6,1/6,2/6]].
%@ [[2/3,0/0,0/0],[0/6,3/3,0/0],[0/6,4/6,0/0],[0/6,2/6,3/3],[0/6,2/6,4/6],[1/6,2/6,0/0],[1/6,1/6,2/3],[1/6,1/6,3/6]].
%@ [[1/6,2/3,0/0],[1/6,3/6,0/0],[0/6,3/6,2/3],[1/6,1/6,3/3],[0/6,3/6,3/6],[1/6,1/6,4/6],[1/6,2/6,2/6]].
%@ [[3/6,0/0,0/0],[1/6,3/3,0/0],[0/6,3/6,3/3],[0/6,3/6,4/6],[2/6,2/6,0/0],[1/6,2/6,2/3],[1/6,2/6,3/6]].
%@ [[3/3,0/0,0/0],[2/6,2/3,0/0],[1/6,4/6,0/0],[1/6,2/6,3/3],[1/6,2/6,4/6],[1/6,3/6,2/6]].
%@ [[4/6,0/0,0/0],[2/6,3/6,0/0],[1/6,3/6,2/3],[1/6,3/6,3/6],[2/6,2/6,2/6]].
%@ [[2/6,3/3,0/0],[1/6,3/6,3/3],[1/6,3/6,4/6],[3/6,2/6,0/0],[2/6,2/6,2/3],[2/6,2/6,3/6]].
%@ [[3/6,2/3,0/0],[2/6,4/6,0/0],[2/6,2/6,3/3],[2/6,2/6,4/6],[2/6,3/6,2/6]].
%@ [[3/6,3/6,0/0],[2/6,3/6,2/3],[2/6,3/6,3/6],[3/6,2/6,2/6]].
%@ [[3/6,3/3,0/0],[2/6,3/6,3/3],[2/6,3/6,4/6],[3/6,2/6,2/3],[3/6,2/6,3/6]].
%@ [[3/6,4/6,0/0],[3/6,2/6,3/3],[3/6,2/6,4/6],[3/6,3/6,2/6]].
%@ [[3/6,3/6,2/3],[3/6,3/6,3/6]].
%@ [[3/6,3/6,3/3],[3/6,3/6,4/6]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 158.969s, 500_731_928 inferences
%@ .. done.
%@    true.

%?- Q1^Q2+\(findall(Q, user:d_mendtally_rec(2,Q,_), Qfs), user:in_cover(Qfs, Q1, Q2)).
%@    Q1 = [0/3,1/6], Q2 = [0/3,0/6]
%@ ;  Q1 = [0/6,2/3], Q2 = [0/3,1/6]
%@ ;  Q1 = [0/6,2/3], Q2 = [0/6,2/6]
%@ ;  Q1 = [0/6,2/6], Q2 = [0/3,0/6]
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,2/3]
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,3/6]
%@ ;  Q1 = [0/6,3/6], Q2 = [0/3,1/6]
%@ ;  Q1 = [0/6,3/6], Q2 = [0/6,2/6]
%@ ;  Q1 = [0/6,4/6], Q2 = [0/6,2/3]
%@ ;  Q1 = [0/6,4/6], Q2 = [0/6,3/6]
%@ ;  Q1 = [1/6,1/6], Q2 = [0/6,2/6]
%@ ;  Q1 = [1/6,1/6], Q2 = [1/6,0/6]
%@ ;  Q1 = [1/6,2/3], Q2 = [0/6,3/3]
%@ ;  Q1 = [1/6,2/3], Q2 = [1/6,2/6]
%@ ;  Q1 = [1/6,2/6], Q2 = [0/6,3/6]
%@ ;  Q1 = [1/6,2/6], Q2 = [1/6,1/6]
%@ ;  Q1 = [1/6,3/3], Q2 = [1/6,2/3]
%@ ;  Q1 = [1/6,3/3], Q2 = [1/6,3/6]
%@ ;  Q1 = [1/6,3/6], Q2 = [0/6,4/6]
%@ ;  Q1 = [1/6,3/6], Q2 = [1/6,2/6]
%@ ;  Q1 = [1/6,4/6], Q2 = [1/6,2/3]
%@ ;  Q1 = [1/6,4/6], Q2 = [1/6,3/6]
%@ ;  Q1 = [2/3,0/0], Q2 = [2/6,0/0]
%@ ;  Q1 = [2/6,0/0], Q2 = [0/6,2/3]
%@ ;  Q1 = [2/6,0/0], Q2 = [1/6,1/6]
%@ ;  Q1 = [2/6,2/3], Q2 = [1/6,3/3]
%@ ;  Q1 = [2/6,2/3], Q2 = [2/6,0/0]
%@ ;  Q1 = [2/6,2/3], Q2 = [2/6,2/6]
%@ ;  Q1 = [2/6,2/6], Q2 = [1/6,3/6]
%@ ;  Q1 = [2/6,3/3], Q2 = [2/3,0/0]
%@ ;  Q1 = [2/6,3/3], Q2 = [2/6,2/3]
%@ ;  Q1 = [2/6,3/3], Q2 = [2/6,3/6]
%@ ;  Q1 = [2/6,3/6], Q2 = [1/6,4/6]
%@ ;  Q1 = [2/6,3/6], Q2 = [2/6,0/0]
%@ ;  Q1 = [2/6,3/6], Q2 = [2/6,2/6]
%@ ;  Q1 = [2/6,4/6], Q2 = [2/6,2/3]
%@ ;  Q1 = [2/6,4/6], Q2 = [2/6,3/6]
%@ ;  Q1 = [3/3,0/0], Q2 = [2/3,0/0]
%@ ;  Q1 = [3/3,0/0], Q2 = [3/6,0/0]
%@ ;  Q1 = [3/6,0/0], Q2 = [1/6,2/3]
%@ ;  Q1 = [3/6,0/0], Q2 = [2/6,0/0]
%@ ;  Q1 = [3/6,2/3], Q2 = [2/6,3/3]
%@ ;  Q1 = [3/6,2/3], Q2 = [3/6,0/0]
%@ ;  Q1 = [3/6,2/3], Q2 = [3/6,2/6]
%@ ;  Q1 = [3/6,2/6], Q2 = [2/6,3/6]
%@ ;  Q1 = [3/6,3/3], Q2 = [3/3,0/0]
%@ ;  Q1 = [3/6,3/3], Q2 = [3/6,2/3]
%@ ;  Q1 = [3/6,3/3], Q2 = [3/6,3/6]
%@ ;  Q1 = [3/6,3/6], Q2 = [2/6,4/6]
%@ ;  Q1 = [3/6,3/6], Q2 = [3/6,0/0]
%@ ;  Q1 = [3/6,3/6], Q2 = [3/6,2/6]
%@ ;  Q1 = [3/6,4/6], Q2 = [3/6,2/3]
%@ ;  Q1 = [3/6,4/6], Q2 = [3/6,3/6]
%@ ;  Q1 = [4/6,0/0], Q2 = [2/3,0/0]
%@ ;  Q1 = [4/6,0/0], Q2 = [2/6,2/3]
%@ ;  Q1 = [4/6,0/0], Q2 = [3/6,0/0]
%@ ;  false. % Covering relation in 𝒬f (D=2 case) now has has 56 pairs.

/*
We now seek the parameters (g₀, g₁, g₂) of a lower-Galois enrollment for D=2,
as defined in Eq (15).

  F(q) ≤ x ⟹ q ≼ gₓ  ∀ q ∈ 𝒬f, 0 ≤ x ≤ D.

We are looking also for *minimal* such values of the gₓ ∈ 𝒬.
*/

% Generate the several relevant subsets of 𝒬f
% TODO: Keeping in mind that we are calculating F⁻¹(Xrange),
%       there could be some value to a left-to-right naming
%       such as d_rec_Finv/3.
d_qfs_rec(D, Qfs, Xrange) :-
    findall(Qf, (d_mendtally_rec(D, Qf, X), X in Xrange), Qfs).

%?- d_qfs_rec(2, Q0s, 0), length(Q0s, L0).
%@    Q0s = [[2/3,0/0],[2/6,0/0],[2/6,2/3],[2/6,2/6],[2/6,3/3],[2/6,3/6],[2/6,4/6],[3/3,0/0],[3/6,0/0],[3/6,2/3],[3/6,2/6],[3/6,3/3],[3/6,3/6],[3/6,4/6],[4/6,0/0]], L0 = 15.

%?- d_qfs_rec(2, Q12s, 1..2), length(Q12s, L12).
%@    Q12s = [[0/3,0/6],[0/3,1/6],[0/6,2/3],[0/6,2/6],[0/6,3/3],[0/6,3/6],[0/6,4/6],[1/6,0/6],[1/6,1/6],[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]], L12 = 14.

% Construct maximal and minimal subsets
% TODO: Eliminate duplicated code by taking relation as parameter.
flip(R_3, X, Y, T) :- call(R_3, Y, X, T).
%?- '≽'([1/2], [2/3]).
%@    true.
%?- call('≽'([1/2]), [2/3]).
%@    true.
%?- call('≼', [2/3], [1/2]).
%@    true.
%?- call(flip('≼', [1/2]), [2/3], T).
%@    T = true.

po_elts_maxs(_, [], []).
po_elts_maxs(R_3, [X|Xs], Maxs) :-
    tpartition(flip(R_3,X), Xs, _, Xs1),
    if_(tmember_t(call(R_3,X), Xs1),
        po_elts_maxs(R_3, Xs1, Maxs),
        (   Maxs = [X|Maxs1],
            po_elts_maxs(R_3, Xs1, Maxs1)
        )
       ).

%?- D=3, X=3, findall(Qf, d_endtally_rec(D, Qf, X), Qfs), po_elts_maxs('≼', Qfs, Maxs).
%@    D = 3, X = 3, Qfs = [[0/3,0/3,0/6],[0/3,0/3,1/6],[0/3,1/6,0/6],[0/3,1/6,1/6],[1/6,0/3,0/6],[1/6,0/3,1/6],[1/6,1/6,0/6],[1/6,1/6,1/6]], Maxs = [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].

%?- D=3, X=3, findall(Qf, d_endtally_rec(D, Qf, X), Qfs), qs_maxs(Qfs, Maxs).
%@    D = 3, X = 3, Qfs = [[0/3,0/3,0/6],[0/3,0/3,1/6],[0/3,1/6,0/6],[0/3,1/6,1/6],[1/6,0/3,0/6],[1/6,0/3,1/6],[1/6,1/6,0/6],[1/6,1/6,1/6]], Maxs = [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].

qs_maxs(Qs, Maxs) :-
    po_qs_sorted('≽', Qs, DescQs),
    foldl(collect_maximal, DescQs, [], Maxs).

collect_maximal(Q, Maxs0, Maxs) :-
    if_(tmember_t('≼'(Q), Maxs0), % ∃ Q' ∈ Mins s.t. Q ≼ Q'?
        Maxs = Maxs0,             % if so, Q is not maximal;
        Maxs = [Q|Maxs0]          % otherwise, it is.
       ).

qs_mins(Qs, Mins) :-
    po_qs_sorted('≼', Qs, AscQs),
    foldl(collect_minimal, AscQs, [], Mins).

collect_minimal(Q, Mins0, Mins) :-
    if_(tmember_t('≽'(Q), Mins0), % ∃ Q' ∈ Mins s.t. Q ≽ Q'?
        Mins = Mins0,             % if so, Q is not minimal;
        Mins = [Q|Mins0]          % otherwise, it is.
       ).

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

d_gs_rec(D, Gs, X, Nmax) :-
    X in 0..D, indomain(X),
    % Calculate Qls = F⁻¹(0..X)
    findall(Qf, (d_endtally_rec(D, Qf, Xi), Xi in 0..X), Qls),
    qs_maxs(Qls, Qls1), % q ∈ Qls ⟹ ∃ q' ∈ Qls1 . q ≼ q'
    % Having calculated the maximal elements of F⁻¹(0..X),
    % we now proceed to search for all candidate gₓ's.
    format("Found maximal elements of F⁻¹(~d)..~n", [X]),
    % TODO: How might the encoding-based sort speed search for candidates?
    findall(C, (qs_d_nmax(C, D, Nmax),
                maplist('≽'(C), Qls1)), Cs),
    length(Cs, NC),
    format("Found ~d G(~d) candidates 'Cs'..~n", [NC, X]),
    format("Now we seek the minimal elements of this list..~n", []),
    qs_mins(Cs, Gs).

d_gs_rec(D, Gs, X) :- d_gs_rec(D, Gs, X, 6).

%?- time(d_gs_rec(2, Gs, X)). % After rendering qs_maxs/2 space-efficient also..
%@ Found maximal elements of F⁻¹(0)..
%@ Found 138 G(0) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@    % CPU time: 2.119s, 8_062_166 inferences
%@    Gs = [[2/6,0/2]], X = 0
%@ ;  Found maximal elements of F⁻¹(1)..
%@ Found 22 G(1) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 0.762s, 2_347_773 inferences
%@    Gs = [[0/6,2/6]], X = 1
%@ ;  Found maximal elements of F⁻¹(2)..
%@ Found 3 G(2) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 0.748s, 2_138_502 inferences
%@    Gs = [[0/4,0/6]], X = 2.

%?- time(d_gs_rec(2, Gs, X)). % Using space-efficient qs_mins/2 now..
%@ Found maximal elements of F⁻¹(0).
%@ Found 138 G(0) candidates 'Cs'.
%@ Now we seek the minimal elements of this list..
%@ Sorting length-138 list Qs:
%@   .. encoding Qs:   % CPU time: 0.074s, 185_017 inferences
%@    % CPU time: 0.076s, 187_781 inferences
%@    % CPU time: 2.113s, 8_077_036 inferences
%@    Gs = [[2/6,0/2]], X = 0
%@ ;  Found maximal elements of F⁻¹(1).
%@ Found 22 G(1) candidates 'Cs'.
%@ Now we seek the minimal elements of this list..
%@ Sorting length-22 list Qs:
%@   .. encoding Qs:% CPU time: 0.011s, 24_269 inferences
%@    % CPU time: 0.013s, 26_550 inferences
%@    % CPU time: 0.753s, 2_318_991 inferences
%@    Gs = [[0/6,2/6]], X = 1
%@ ;  Found maximal elements of F⁻¹(2).
%@ Found 3 G(2) candidates 'Cs'.
%@ Now we seek the minimal elements of this list..
%@ Sorting length-3 list Qs:
%@   .. encoding Qs:% CPU time: 0.001s, 3_157 inferences
%@    % CPU time: 0.003s, 5_342 inferences
%@    % CPU time: 0.698s, 2_096_567 inferences
%@    Gs = [[0/4,0/6]], X = 2.

%?- time(d_gs_rec(2, Gs, X)). % With enlarged, post-Meetup ≼
%@    % CPU time: 3.408s, 12_449_812 inferences
%@    Gs = [[2/6,0/2]], X = 0
%@ ;  % CPU time: 0.814s, 2_547_519 inferences
%@    Gs = [[0/6,2/6]], X = 1
%@ ;  % CPU time: 0.698s, 2_087_884 inferences
%@    Gs = [[0/4,0/6]], X = 2.

%?- time(d_gs_rec(2, Gs, X)). % After expanding ≼ to include 'escalation condition'
%@    % CPU time: 2.526s, 11_246_152 inferences
%@    Gs = [[2/6,0/4]], X = 0
%@ ;  % CPU time: 0.934s, 4_083_756 inferences
%@    Gs = [[0/6,2/6]], X = 1
%@ ;  % CPU time: 0.918s, 3_999_748 inferences
%@    Gs = [[0/5,0/6]], X = 2.

%?- time(d_gs_rec(2, Gs, X)).
%@    % CPU time: 2.525s, 11_250_583 inferences
%@    Gs = [[2/6,0/4]], X = 0
%@ ;  % CPU time: 0.926s, 4_086_282 inferences
%@    Gs = [[0/6,2/6]], X = 1
%@ ;  % CPU time: 0.912s, 4_002_226 inferences
%@    Gs = [[0/5,0/6]], X = 2.

%?- time(d_gs_rec(3, Gs, X)). % After rendering qs_maxs/2 space-efficient also..
%@ Found maximal elements of F⁻¹(0)..
%@ Found 1754 G(0) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@    % CPU time: 45.557s, 155_196_415 inferences
%@    Gs = [[2/6,0/4,0/0]], X = 0
%@ ;  Found maximal elements of F⁻¹(1)..
%@ Found 424 G(1) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 25.356s, 72_762_939 inferences
%@    Gs = [[0/6,2/6,0/2]], X = 1
%@ ;  Found maximal elements of F⁻¹(2)..
%@ Found 90 G(2) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 21.948s, 59_028_691 inferences
%@    Gs = [[0/4,0/6,2/6]], X = 2
%@ ;  Found maximal elements of F⁻¹(3)..
%@ Found 12 G(3) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 21.371s, 56_737_885 inferences
%@    Gs = [[0/4,0/4,0/6]], X = 3.

%?- time(d_gs_rec(3, Gs, X)). % Using space-efficient qs_emins/2 now..
%@ Found maximal elements of F⁻¹(0).
%@ Found 1754 G(0) candidates 'Cs'.
%@ Now we seek the minimal elements of this list..
%@ Sorting length-1754 list Qs:
%@   .. encoding Qs:   % CPU time: 1.239s, 2_819_309 inferences
%@    % CPU time: 1.246s, 2_828_559 inferences
%@    % CPU time: 45.176s, 155_322_539 inferences
%@    Gs = [[2/6,0/4,0/0]], X = 0
%@ ;  Found maximal elements of F⁻¹(1).
%@ Found 424 G(1) candidates 'Cs'.
%@ Now we seek the minimal elements of this list..
%@ Sorting length-424 list Qs:
%@   .. encoding Qs:% CPU time: 0.291s, 634_286 inferences
%@    % CPU time: 0.293s, 638_195 inferences
%@    % CPU time: 25.143s, 72_730_278 inferences
%@    Gs = [[0/6,2/6,0/2]], X = 1
%@ ;  Found maximal elements of F⁻¹(2).
%@ Found 90 G(2) candidates 'Cs'.
%@ Now we seek the minimal elements of this list..
%@ Sorting length-90 list Qs:
%@   .. encoding Qs:% CPU time: 0.061s, 117_897 inferences
%@    % CPU time: 0.063s, 120_470 inferences
%@    % CPU time: 21.724s, 58_933_507 inferences
%@    Gs = [[0/4,0/6,2/6]], X = 2
%@ ;  Found maximal elements of F⁻¹(3).
%@ Found 12 G(3) candidates 'Cs'.
%@ Now we seek the minimal elements of this list..
%@ Sorting length-12 list Qs:
%@   .. encoding Qs:% CPU time: 0.008s, 15_172 inferences
%@    % CPU time: 0.010s, 17_413 inferences
%@    % CPU time: 21.071s, 56_604_286 inferences
%@    Gs = [[0/4,0/4,0/6]], X = 3.

%?- time(d_gs_rec(3, Gs, X)). % More efficient d_placevalues/2?
%@ Now we seek the minimal elements of this list.. % MEM starts growing, hits 19.9%
%@    % CPU time: 235.606s, 775_247_646 inferences
%@    Gs = [[2/6,0/4,0/0]], X = 0
%@ ;  Found maximal elements of F⁻¹(1).
%@ Found 424 all G(1) candidates 'Cs'.
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 54.086s, 172_168_400 inferences
%@    Gs = [[0/6,2/6,0/2]], X = 1
%@ ;  Found maximal elements of F⁻¹(2).
%@ Found 90 all G(2) candidates 'Cs'.
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 23.072s, 63_984_172 inferences
%@    Gs = [[0/4,0/6,2/6]], X = 2
%@ ;  Found maximal elements of F⁻¹(3).
%@ Found 12 all G(3) candidates 'Cs'.
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 21.216s, 56_657_453 inferences
%@    Gs = [[0/4,0/4,0/6]], X = 3. % MEM use still 19.9%
%@    % CPU time: 244.200s, 775_246_416 inferences
%@    Gs = [[2/6,0/4,0/0]], X = 0
%@ ;  % CPU time: 55.219s, 172_167_173 inferences
%@    Gs = [[0/6,2/6,0/2]], X = 1
%@ ;  % CPU time: 23.135s, 63_982_948 inferences
%@    Gs = [[0/4,0/6,2/6]], X = 2
%@ ;  % CPU time: 21.150s, 56_656_229 inferences
%@    Gs = [[0/4,0/4,0/6]], X = 3.
% Wow!  This change made zero difference, peak %MEM still 20%!

%?- time(d_gs_rec(3, Gs, X)). % With enlarged, post-Meetup ≼
%@    % CPU time: 239.333s, 775_246_474 inferences
%@    Gs = [[2/6,0/4,0/0]], X = 0
%@ ;  % CPU time: 54.181s, 172_167_180 inferences
%@    Gs = [[0/6,2/6,0/2]], X = 1
%@ ;  % CPU time: 23.115s, 63_982_955 inferences
%@    Gs = [[0/4,0/6,2/6]], X = 2
%@ ;  % CPU time: 21.077s, 56_656_236 inferences
%@    Gs = [[0/4,0/4,0/6]], X = 3.
% I wonder if the worsened performance here has anything to do
% with qs_int/2's flamboyant memory allocation merely to find
% the placevalue P.  Let's try changing that!

%?- time(d_gs_rec(3, Gs, X)).
%@    % CPU time: 98.132s, 433_986_805 inferences
%@    Gs = [[2/6,0/6,0/2]], X = 0
%@ ;  % CPU time: 38.251s, 167_709_838 inferences
%@    Gs = [[0/6,2/6,0/4]], X = 1
%@ ;  % CPU time: 32.944s, 144_979_445 inferences
%@    Gs = [[0/5,0/6,2/6]], X = 2
%@ ;  % CPU time: 32.764s, 144_367_573 inferences
%@    Gs = [[0/5,0/5,0/6]], X = 3.

%?- time(d_gs_rec(4, Gs, X)).
%@ Found maximal elements of F⁻¹(0)..
%@ Found 19801 G(0) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@    % CPU time: 1170.849s, 3_573_545_956 inferences
%@    Gs = [[2/6,0/6,0/0,0/0]], X = 0
%@ ;  Found maximal elements of F⁻¹(1)..
%@ Found 6494 G(1) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 824.815s, 2_165_017_840 inferences
%@    Gs = [[0/6,2/6,0/4,0/0]], X = 1
%@ ;  Found maximal elements of F⁻¹(2)..
%@ Found 1911 G(2) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 716.367s, 1_809_452_129 inferences
%@    Gs = [[0/4,0/6,2/6,0/2]], X = 2
%@ ;  Found maximal elements of F⁻¹(3)..
%@ Found 419 G(3) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 677.546s, 1_647_902_233 inferences
%@    Gs = [[0/4,0/4,0/6,2/6]], X = 3
%@ ;  Found maximal elements of F⁻¹(4)..
%@ Found 55 G(4) candidates 'Cs'..
%@ Now we seek the minimal elements of this list..
%@ % CPU time: 673.530s, 1_626_275_209 inferences
%@    Gs = [[0/4,0/4,0/4,0/6]], X = 4.

%?- time(d_gs(3, Gs)).
%@ Listing Qs......    % CPU time: 1.577s, 6_660_460 inferences
%@ Stratifying Qf..    % CPU time: 2.990s, 13_345_839 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/0] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ ↓[0/6,2/6,0/2] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ ↓[0/4,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ ↓[0/4,0/4,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@    % CPU time: 26.587s, 81_393_524 inferences
%@    % CPU time: 47.307s, 137_856_007 inferences
%@    Gs = [[2/6,0/4,0/0],[0/6,2/6,0/2],[0/4,0/6,2/6],[0/4,0/4,0/6]].

%?- time(d_gs(4, Gs)).
%@ Listing Qs......    % CPU time: 43.200s, 182_781_614 inferences
%@    error('$interrupt_thrown',repl/0). % MEM grows to >45% while listing Qs
%@ Listing Qs......    % CPU time: 43.393s, 182_781_614 inferences
%@ Stratifying Qf..    % CPU time: 9.599s, 42_142_294 inferences
%@ Finding g's ..
%@ Listing Qs......    % CPU time: 45.892s, 182_781_614 inferences
%@ Sorting length-614656 list Qs:
%@   .. encoding Qs:   % CPU time: 672.529s, 3_595_990_719 inferences
%@    % CPU time: 674.964s, 3_597_837_005 inferences
%@ Stratifying Qf..    % CPU time: 11.176s, 50_148_136 inferences
%@ Finding g's ..
%@ Listing Qs......    % CPU time: 44.595s, 182_781_614 inferences
%@ Sorting length-614656 list Qs:
%@   .. encoding Qs:   % CPU time: 699.296s, 3_595_990_719 inferences
%@    % CPU time: 702.410s, 3_597_837_005 inferences
%@ Stratifying Qf..    % CPU time: 12.085s, 50_148_136 inferences
%@ Finding g's ..

%?- time(d_gs_rec(4, Gs, X)).
%@    % CPU time: 1146.519s, 5_745_737_901 inferences
%@    Gs = [[2/6,0/4,0/4,0/4]], X = 0
%@ ;  % CPU time: 977.587s, 4_976_964_589 inferences
%@    Gs = [[0/6,2/6,0/4,0/4]], X = 1
%@ ;  % CPU time: 959.801s, 4_916_987_366 inferences
%@    Gs = [[0/6,0/5,2/6,0/4]], X = 2
%@ ;  % CPU time: 962.464s, 4_905_704_908 inferences
%@    Gs = [[0/6,0/5,0/5,2/6]], X = 3
%@ ;  % CPU time: 954.726s, 4_907_056_586 inferences
%@    Gs = [[0/6,0/5,0/5,0/5]], X = 4.

/*
From the above, we see that (as expected) a separate 'rectification'
step is not truly needed, and that the calculation of candidate g's
automatically ensures functoriality of the resulting lower-Galois
enrollment.

That represents progress toward simplification, but (apparently)
not toward improved time-complexity, nor even a substantial speedup.

One thing we might do, however, is to incorporate the minimization
into the search itself.  If we already have a non-empty set of
valid gₓ's that are minimal among those found thus far, then any
new g' that we might like to test can be rejected immediately if
it exceeds *any* element of this set.  Such quick rejection will
avoid costly checking against _all_ of the Qls1.

What if I were scanning a *sorted* list of all admissible tallies?
Would I enjoy any guarantee that allowed me to cut short my scan
at any point?  How might I know that I won't find any additional
minimal gₓ's for some given x?

Suppose I search a list sorted low-to-high along -≼-> arrows,
and find a valid gₓ that is however not minimal relative to the
gₓ's I've already found.  Could this guarantee I will never find
another minimal gₓ further along (higher up) the list?  I think
that's too much to hope for.

But what about the question of minimality?  Because I can never
find a later element in the list that is _below_ a previously
seen element (including any gₓ's collected thus far), I do know
that none of the gₓ's already proven minimal could possibly get
knocked out by a new one.  So the only question I need to ask
under these circumstances is whether any of the previously
collected gₓ's is below g'.  If so, then g' can be ignored.

Perhaps this means rather that I should switch to finding gₓ₊₁?
That is, I may now have a scheme for processing the hypercube
in a single pass.
*/

% Today, let's see how much we can speed this up by such a
% single-pass processing of a sorted hypercube.
% This really starts to look like a job for a DCG!
% But perhaps a foldl/4 is more clearly in order.
% I will need a suitable _accumulator_ for this.
% Accumulator at any time knows the full list of (D+1)
% maximal strata which the gₓ's must sit above.
% Accumulator also knows for which X it is currently
% seeking a gₓ.  (It may rather make sense for accumulator
% to hold only current and yet-unprocessed strata.)
% Since my aim here is to explore *potential* speedups,
% I could even treat first gₓ I find for each X as *the*
% minimal one!  That is, I am announcing from the outset
% that I will seek only single representatives of what may
% generally (unless some theorem holds to the contrary!)
% be non-singleton gₓ lists of options for some X's.

% Aha!  I realized on my walk this morning (10/18) that the
% fact 𝒬 is a _lattice_ guarantees that each gₓ is unique!
% This changes everything.  It allows me to search an
% ascending list of the hypercube, taking the *first*
% 'candidate' gₓ (for each x) as _the_ unique value.
% The search can then increment x and find the next g.

% I think actually a foldl/4 may not allow fully for the
% efficiencies possible here, and that a 'monolithic'
% recursion may better solve the problem.

% Interestingly, I now seem to have found a use for '⋡'/3 below!
'⋡'(Q1s, Q2s, Truth) :- '≽'(Q1s, Q2s, Untruth),
                        reif:non(Untruth, Truth).

% Here, galois/3 is searching [Q|Qs] for the first Gx
% satisfying Q ≼ Gx ∀ Q ∈ Ms, or equivalently ↓Gx ⊇ Ms.
% Severe %MEM growth (as formerly with qs_maxs/2 and
% qs_mins/2, e.g.) still occurs in this predicate.

% Perhaps I'll do well to recast this computation as a foldl?
% [Ms|Mss] are the Hasse diagram strata sorted bottom-up,
% and Qs are tallies to search, also in ascending order.
galoisF(Mss, Qs, Gs) :- foldl(collect_Gs, Mss, Qs-[], _-Gs).

collect_Gs(Ms, [Q|Qs]-Gs, Qs1-Gs1) :-
    if_(tmember_t('⋡'(Q), Ms),          % ∃ M ∈ Ms s.t. M ⋠ Q ?
        collect_Gs(Ms, Qs-Gs, Qs1-Gs1), % if so, Q is not a Gx;
        (   format("↓~w ⊇ ~w.~n", [Q, Ms]),
            Gs1 = [Q|Gs],               % otherwise, collect it.
            Qs1 = Qs
        )
       ).

galois([Ms|Mss], [Q|Qs], [G|Gs]) :-
    if_(tmember_t('⋡'(Q), Ms),        % ∃ M ∈ Ms s.t. M ⋠ Q ?
        galois([Ms|Mss], Qs, [G|Gs]), % if so, Q is not a Gx;
        (   format("↓~w ⊇ ~w.~n", [Q, Ms]),
            G = Q,                    % otherwise, collect it
            galois(Mss, Qs, Gs)       % and recurse.
        )
       ).
galois([], _, []). % Succeed when all strata are accounted-for.

d_gs(D, Gs) :-
    format("Listing Qs...... ", []),
    time(findall(Q, qs_d_nmax(Q, D, 6), Qs)),
    format("Sorting Qs...", []),
    po_qs_sorted('≼', Qs, AscQs),
    format("Stratifying Qf.. ", []),
    time(d_Qfstratamax(D, Mss)),
    format("Finding g's ..~n", []),
    time(galois(Mss, AscQs, Gs)).
    %%%time(galoisF(Mss, AscQs, Gs)).

%?- time(d_gs(2, Gs)).
%@ Listing Qs......    % CPU time: 0.063s, 249_966 inferences
%@ Sorting Qs...Stratifying Qf..    % CPU time: 0.743s, 3_291_174 inferences
%@ Finding g's ..
%@ ↓[2/6,0/2] ⊇ [[2/6,0/0],[2/6,2/6]].
%@ ↓[0/6,2/6] ⊇ [[0/6,2/6]].
%@ ↓[0/4,0/6] ⊇ [[0/3,0/6],[1/6,0/6]].
%@    % CPU time: 0.762s, 2_482_722 inferences
%@    % CPU time: 2.032s, 7_288_555 inferences
%@    Gs = [[2/6,0/2],[0/6,2/6],[0/4,0/6]].
%@ Listing Qs......    % CPU time: 0.066s, 249_966 inferences
%@ Stratifying Qf..    % CPU time: 0.755s, 3_291_174 inferences
%@ Finding g's ..
%@ ↓[2/6,0/2] ⊇ [[2/6,0/0],[2/6,2/6]].
%@ ↓[0/6,2/6] ⊇ [[0/6,2/6]].
%@ ↓[0/4,0/6] ⊇ [[0/3,0/6],[1/6,0/6]].
%@    % CPU time: 0.773s, 2_482_722 inferences
%@    % CPU time: 2.064s, 7_288_408 inferences
%@    Gs = [[2/6,0/2],[0/6,2/6],[0/4,0/6]].

%?- time(d_gs(3, Gs)). % Back to the old galois/3..
%@ Listing Qs......    % CPU time: 1.705s, 6_660_460 inferences
%@ Sorting Qs...Stratifying Qf..    % CPU time: 2.969s, 13_345_839 inferences
%@ Finding g's .. % (Again, MEM grows to ~5% during g-finding)
%@ ↓[2/6,0/4,0/0] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ ↓[0/6,2/6,0/2] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ ↓[0/4,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ ↓[0/4,0/4,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@    % CPU time: 26.548s, 81_393_524 inferences
%@    % CPU time: 47.280s, 137_856_154 inferences
%@    Gs = [[2/6,0/4,0/0],[0/6,2/6,0/2],[0/4,0/6,2/6],[0/4,0/4,0/6]].

%?- time(d_gs(3, Gs)). % Back to the old collect_Gs/3..
%@ Listing Qs......    % CPU time: 1.606s, 6_660_460 inferences
%@ Sorting Qs...Stratifying Qf..    % CPU time: 2.990s, 13_345_839 inferences
%@ Finding g's .. % (MEM still grows to ~5% during this process)
%@ ↓[2/6,0/4,0/0] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ ↓[0/6,2/6,0/2] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ ↓[0/4,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ ↓[0/4,0/4,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@    % CPU time: 26.630s, 81_393_533 inferences
%@    % CPU time: 46.822s, 137_856_163 inferences
%@    Gs = [[0/4,0/4,0/6],[0/4,0/6,2/6],[0/6,2/6,0/2],[2/6,0/4,0/0]].

%?- time(d_gs(3, Gs)). % Trying new galoisF/3..
%@ Listing Qs......    % CPU time: 1.565s, 6_660_460 inferences
%@ Sorting Qs...Stratifying Qf..    % CPU time: 2.996s, 13_345_839 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/0] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ ↓[0/6,2/6,0/2] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ ↓[0/4,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ ↓[0/4,0/4,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@    % CPU time: 26.684s, 81_393_533 inferences
%@    % CPU time: 46.939s, 137_856_163 inferences
%@    Gs = [[0/4,0/4,0/6],[0/4,0/6,2/6],[0/6,2/6,0/2],[2/6,0/4,0/0]].

%?- time(d_gs(3, Gs)). % Investigating %MEM growth in (?) galois/3..
%@ Listing Qs......    % CPU time: 1.614s, 6_660_460 inferences
%@ Sorting Qs...Stratifying Qf..    % CPU time: 3.010s, 13_345_839 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/0] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ ↓[0/6,2/6,0/2] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ ↓[0/4,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ ↓[0/4,0/4,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@    % CPU time: 26.668s, 81_393_524 inferences
%@    % CPU time: 46.900s, 137_856_154 inferences
%@    Gs = [[2/6,0/4,0/0],[0/6,2/6,0/2],[0/4,0/6,2/6],[0/4,0/4,0/6]].

%?- time(d_gs(3, Gs)). % After refining qs_int/2
%@ Listing Qs......    % CPU time: 1.674s, 6_660_460 inferences
%@ Sorting length-21952 list Qs:
%@   .. encoding Qs:   % CPU time: 20.587s, 109_986_469 inferences
%@    % CPU time: 20.654s, 110_054_609 inferences
%@ Stratifying Qf..    % CPU time: 3.261s, 14_740_333 inferences
%@ Finding g's ..
%@ ↓[2/6,0/6,0/2] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@    % CPU time: 36.582s, 163_114_471 inferences
%@    % CPU time: 62.185s, 294_600_224 inferences
%@    Gs = [[2/6,0/6,0/2],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]]. % Yup!
%?- time(d_gs(3, Gs)). % After expanding ≼
%@ Listing Qs......    % CPU time: 1.584s, 6_660_460 inferences
%@ Sorting length-21952 list Qs:
%@   .. encoding Qs:   % CPU time: 15.394s, 82_823_698 inferences
%@    % CPU time: 15.533s, 82_891_818 inferences
%@ Stratifying Qf..    % CPU time: 3.252s, 14_740_333 inferences
%@ Finding g's ..
%@ ↓[2/6,0/6,0/6] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ ↓[0/6,2/6,0/6] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ ↓[0/6,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ ↓[0/6,0/6,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@    % CPU time: 35.345s, 159_516_593 inferences
%@    % CPU time: 55.728s, 263_839_535 inferences
%@    Gs = [[2/6,0/6,0/6],[0/6,2/6,0/6],[0/6,0/6,2/6],[0/6,0/6,0/6]].
%@ Listing Qs......    % CPU time: 1.602s, 6_660_460 inferences
%@ Sorting length-21952 list Qs:
%@   .. encoding Qs:   % CPU time: 20.459s, 109_746_627 inferences
%@   .. decoding Qs:   % CPU time: 31.410s, 207_539_697 inferences
%@    % CPU time: 51.912s, 317_510_405 inferences
%@ Stratifying Qf..    % CPU time: 3.409s, 15_670_513 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@    % CPU time: 29.983s, 153_162_409 inferences
%@    % CPU time: 86.920s, 493_034_138 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- time(d_gs(3, Gs)). % After factoring out ws_cint/2
%@ Listing Qs......    % CPU time: 1.628s, 6_660_460 inferences
%@ Sorting length-21952 list Qs:
%@   .. encoding Qs:   % CPU time: 20.840s, 109_746_627 inferences
%@   .. decoding Qs:   % CPU time: 32.067s, 207_539_697 inferences
%@    % CPU time: 52.955s, 317_510_405 inferences
%@ Stratifying Qf..    % CPU time: 3.472s, 15_670_513 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 30.628s, 153_168_191 inferences
%@    % CPU time: 88.697s, 493_039_926 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- time(d_gs(3, Gs)). % After trimming back instrumentation
%@ Listing Qs......    % CPU time: 1.651s, 6_660_460 inferences
%@ Sorting length-21952 list Qs:
%@   .. encoding Qs:   % CPU time: 21.063s, 109_988_099 inferences
%@   .. decoding Qs:   % CPU time: 32.770s, 207_539_697 inferences
%@    % CPU time: 53.881s, 317_751_877 inferences
%@ Stratifying Qf..    % CPU time: 3.576s, 15_670_513 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 31.390s, 153_168_191 inferences
%@    % CPU time: 90.512s, 493_281_398 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- time(d_gs(4, Gs)). % Perhaps this is feasible _now_?
%@ Listing Qs......    % CPU time: 42.716s, 182_781_614 inferences
%@ Sorting Qs...   error('$interrupt_thrown',repl/0). % MEM grew >50% here
%@ Listing Qs......    % CPU time: 43.456s, 182_781_614 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 679.046s, 3_594_977_411 inferences
%@ Sorting Qs....    % CPU time: 0.632s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.648s, 6_146_561 inferences
%@ Decoding......    % CPU time: 1187.057s, 7_752_694_545 inferences
%@    % CPU time: 1867.513s, 11_355_055_949 inferences
%@ Reversing.......    % CPU time: 0.280s, 614_658 inferences
%@ Stratifying Qf..    % CPU time: 12.384s, 57_444_988 inferences
%@ Finding g's ..

%?- time(d_gs(4, Gs)). % Has this become feasible? (ALMOST!)
%@ Listing Qs......    % CPU time: 43.552s, 182_781_614 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 875.273s, 4_738_223_165 inferences
%@ Sorting Qs....    % CPU time: 0.638s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.643s, 6_146_561 inferences
%@ Decoding......    % CPU time: 185.771s, 1_177_910_766 inferences
% < interrupted during decoding, as %MEM had hit 65% and still growing >
%@    % CPU time: 1066.593s, 5_923_517_910 inferences
%@    % CPU time: 1110.149s, 6_106_303_711 inferences
%@    error('$interrupt_thrown',repl/0).

%?- time(d_gs(3, Gs)). % After precomputing placevalues/1
%@ Listing Qs......    % CPU time: 1.566s, 6_660_460 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 27.714s, 151_958_265 inferences
%@ Sorting Qs....    % CPU time: 0.017s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.019s, 175_617 inferences
%@ Decoding......    % CPU time: 49.405s, 314_906_923 inferences
%@    % CPU time: 77.167s, 467_092_727 inferences
%@ Reversing.......    % CPU time: 0.006s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.343s, 15_549_757 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 28.593s, 145_469_735 inferences
%@    % CPU time: 110.684s, 634_804_811 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- time(d_gs(3, Gs)).
%@ Listing Qs......    % CPU time: 1.638s, 6_660_460 inferences
%@ Sorting Qs......    % CPU time: 192.997s, 1_019_331_176 inferences
%@ Reversing.......    % CPU time: 0.006s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.434s, 15_549_757 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 35.667s, 145_469_735 inferences
%@    % CPU time: 233.751s, 1_187_043_271 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- Pct is 100*193/234.
%@    Pct = 82.47863247863248. % 0.8 of the time is spent in qs_sorted/2!

%?- time(d_gs(2, Gs)).
%@ ↓[2/6,0/4] ⊇ [[2/6,0/0],[2/6,2/6]].
%@ Mss = [[[0/6,2/6]],[[0/3,0/6],[1/6,0/6]]], |Qs| = 207, Gs1 = [[2/6,0/4]].
%@ ↓[0/6,2/6] ⊇ [[0/6,2/6]].
%@ Mss = [[[0/3,0/6],[1/6,0/6]]], |Qs| = 133, Gs1 = [[0/6,2/6],[2/6,0/4]].
%@ ↓[0/5,0/6] ⊇ [[0/3,0/6],[1/6,0/6]].
%@ Mss = [], |Qs| = 2, Gs1 = [[0/5,0/6],[0/6,2/6],[2/6,0/4]].
%@    % CPU time: 5.865s, 32_171_678 inferences
%@    Gs = [[2/6,0/4],[0/6,2/6],[0/5,0/6]].

%?- time(d_gs(3, Gs)).
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 213.793s, 1_187_033_066 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].
% In 'top', this went up to 11% of my 64GB RAM!
% Also, sadly, I see total time nearly doubled compared with d_gs_rec/3!


% Now what about creating the strata?  Do I already have the
% needed predicate?  Not quite, I think: sift/3 builds strata
% for an entire set without regard to the dose recommendation.
% Here, all I want is the maximal elements (i.e., *top* strata)
% for each dose-recommendation level within 𝒬f.
% Note that 𝒬f is in practice so small that qs_maxs/2 should
% do just fine to start.  (TODO: But I really should test this
% claim once gₓ calculations for higher D's become feasible!)

d_Qfstrata(D, Qss) :-
    must_be(integer, D),
    findall(X-Q, d_endtally_rec(D,Q,X), XQs),
    sort(XQs, SXQs),
    group_pairs_by_key(SXQs, GXQs),
    pairs_values(GXQs, Qss).

d_Qfstratamax(D, Mss) :-
    d_Qfstrata(D, Qss),
    maplist(qs_maxs, Qss, Mss).

% These queries corroborate the d_Qfstratamax/2 results below.
%?- D=3, X=3, Maxs+\(findall(Qf, d_endtally_rec(D, Qf, X), Qfs), qs_maxs(Qfs, Maxs)).

%?- d_Qfstratamax(2, Mss), maplist(portray_clause, Mss).
%@ [[2/6,0/0],[2/6,2/6]].
%@ [[0/6,2/6]].
%@ [[0/3,0/6],[1/6,0/6]].
%@    Mss = [[[2/6,0/0],[2/6,2/6]],[[0/6,2/6]],[[0/3,0/6],[1/6,0/6]]].
%@ [[2/6,0/0],[2/6,2/6]].
%@ [[0/6,2/6]].
%@ [[0/3,0/6],[1/6,0/6]].
%@    Mss = [[[2/6,0/0],[2/6,2/6]],[[0/6,2/6]],[[0/3,0/6],[1/6,0/6]]].

%?- d_Qfstratamax(3, Mss), maplist(portray_clause, Mss).
%@ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@    Mss = [[[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]],[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]]].
%@ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@    Mss = [[[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]],[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]].

%?- d_Qfstratamax(4, Mss), maplist(portray_clause, Mss).
%@ [[2/6,0/0,0/0,0/0],[2/6,2/6,0/0,0/0],[2/6,2/6,2/6,0/0],[2/6,2/6,2/6,2/6]].
%@ [[0/6,2/6,0/0,0/0],[0/6,2/6,2/6,0/0],[0/6,2/6,2/6,2/6]].
%@ [[0/3,0/6,2/6,0/0],[0/3,0/6,2/6,2/6],[1/6,0/6,2/6,0/0],[1/6,0/6,2/6,2/6]].
%@ [[0/3,0/3,0/6,2/6],[0/3,1/6,0/6,2/6],[1/6,0/3,0/6,2/6],[1/6,1/6,0/6,2/6]].
%@ [[0/3,0/3,0/3,0/6],[0/3,0/3,1/6,0/6],[0/3,1/6,0/3,0/6],[0/3,1/6,1/6,0/6],[1/6,0/3,0/3,0/6],[1/6,0/3,1/6,0/6],[1/6,1/6,0/3,0/6],[1/6,1/6,1/6,0/6]].
%@    Mss = [[[2/6,0/0,0/0,0/0],[2/6,2/6,0/0,0/0],[2/6,2/6,2/6,0/0],[2/6,2/6,2/6,2/6]],[[0/6,2/6,0/0,0/0],[0/6,2/6,2/6,0/0],[0/6,2/6,2/6,2/6]],[[0/3,0/6,2/6,0/0],[0/3,0/6,2/6,2/6],[1/6,0/6,2/6,0/0],[1/6,0/6,2/6,2/6]],[[0/3,0/3,0/6,2/6],[0/3,1/6,0/6,2/6],[1/6,0/3,0/6,2/6],[1/6,1/6,0/6,2/6]],[[0/3,0/3,0/3,0/6],[0/3,0/3,1/6,0/6],[0/3,1/6,0/3,0/6],[0/3,1/6,1/6,0/6],[1/6,0/3,0/3,0/6],[1/6,0/3,1/6,0/6],[1/6,1/6,0/3,0/6],[1/6,1/6,1/6,0/6]]].

% ============================================================
% Investigate non-functorialities in the D=3 trial:

/*
?- d_endtally_rec(3, Q1, D1),
   d_endtally_rec(3, Q2, D2),
   Q1 '≼' Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    Q1 = [0/3,1/6,1/6], D1 = 3, Q2 = [0/3,0/6,2/6], D2 = 2
%@ ;  Q1 = [1/6,0/3,1/6], D1 = 3, Q2 = [0/3,0/6,2/6], D2 = 2
%@ ;  Q1 = [1/6,1/6,1/6], D1 = 3, Q2 = [1/6,0/6,2/6], D2 = 2
%@ ;  Q1 = [1/6,1/6,2/3], D1 = 2, Q2 = [0/6,2/6,2/3], D2 = 1
%@ ;  Q1 = [1/6,1/6,2/3], D1 = 2, Q2 = [0/6,2/6,2/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,2/6], D1 = 2, Q2 = [0/6,2/6,2/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/3], D1 = 2, Q2 = [0/6,2/6,0/0], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/3], D1 = 2, Q2 = [0/6,2/6,2/3], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/3], D1 = 2, Q2 = [0/6,2/6,2/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/3], D1 = 2, Q2 = [0/6,2/6,3/3], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/3], D1 = 2, Q2 = [0/6,2/6,3/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/6], D1 = 2, Q2 = [0/6,2/6,2/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,3/6], D1 = 2, Q2 = [0/6,2/6,3/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,4/6], D1 = 2, Q2 = [0/6,2/6,2/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,4/6], D1 = 2, Q2 = [0/6,2/6,3/6], D2 = 1
%@ ;  Q1 = [1/6,1/6,4/6], D1 = 2, Q2 = [0/6,2/6,4/6], D2 = 1
%@ ;  false. % 16 non-functorial pairs in D=3 trial!
*/

% Are any of these pharmacologic non-monotonicities genuinely new?
% How many reduce to the lone D=2 case of [1/6,1/6] vs [0/6,2/6],
% after projecting off one dose?
% All of them, in fact!  The first two solutions reduce thus upon
% projecting off the lowest dose, and the remaining 13 do so when
% the top dose is removed.

%:- table d_mendtally_rec_/4. % TODO: Understand why I cannot table this.
% (I can hardly use tabling safely, if I don't understand why it failed here!)
d_mendtally_rec(D, Q, X) :- d_mendtally_rec_(D, Q, X, _).

d_mendtally_rec_(D, Q, X, Xls) :-
    d_endtally_rec(D, Q, Xu), % Q-Xu is a final tally w/ *unrectified* rec, from a D-dose 3+3
    findall(Xl, (d_endtally_rec(D, Ql, Xl),
                 Xu #> Xl,  % Final tally Ql received a rec *lower* than Xu,
                 Q '≼' Ql), % although it is evidently at least as safe as Q.
            Xls),
    foldl(clpz:min_, Xls, Xu, X).

%?- d_mendtally_rec_(3, Q, D, [_|_]).
%@    Q = [0/3,1/6,1/6], D = 2
%@ ;  Q = [1/6,0/3,1/6], D = 2
%@ ;  Q = [1/6,1/6,1/6], D = 2
%@ ;  Q = [1/6,1/6,2/3], D = 1
%@ ;  Q = [1/6,1/6,2/6], D = 1
%@ ;  Q = [1/6,1/6,3/3], D = 1
%@ ;  Q = [1/6,1/6,3/6], D = 1
%@ ;  Q = [1/6,1/6,4/6], D = 1
%@ ;  false.
% NB: Indeed there were only 8 unique Q1's
%     among the 16 solutions found above.

% TODO: Bring the following explorations up-of-date
%       with our now-expanded ≼.

% ~~~~ Rolling enrollment for the D=2 trial ~~~~

% TODO: Of course, getting such a predicate to work in
%       all directions would boost these explorations!

% Now, in constructing an IE from the upper adjoint
% Gx, x ∈ 0..D, I must acknowledge that our default
% partial order ≼ is not sufficient to identify
% _positively_ all q for which d ≤ E(q).
% That is, although by construction we have
%
%       q ≼ G(d) ⟹ E(q) ≤ d ∀ q ∈ 𝒬f,
%
% we cannot obtain from this any lower bound on E(q),
% and therefore lack a principle to drive escalation
% and so guarantee liveness.
%
% So what may be needed ultimately is a reformulation
% of the idea of Galois enrollment, either restoring
% the idea of enlarging ('strengthening') ≼ to  ≼* or else
% *weakening* the iff at the heart of adjointness.
e2(Q, X) :-
    [G0,G1,G2] = [[2/6,0/2],[0/6,2/6],[0/4,0/6]],
    if_(Q '≼' G0, X = 0,
        if_(Q '≼' G1, X = 1,
            if_(Q '≼' G2, X = 2, false))).

%?- e2([0/0,0/0], X).
%@    X = 2.
%@    X = 2. % Is the bottom-up cascade of a lower-Galois IE therefore unsafe?

% Suppose we want a 'cut-off' version c2/2 of the above.
% The main deficiency of e2/2 to be remedied is that it
% lets Q 'slip thru' to the highest dose, simply because
% po ≼ remains too weak to catch it.  What we would need
% then is to impose _additional_ requirements on upward
% percolation of Q.
c2(Q, X) :-
    [G0,G1,G2] = [[2/6,0/2],[0/6,2/6],[0/4,0/6]],
    if_(Q '≼' G0,
        X = 0,
        if_(( Q '⋡' G0
            ; Q '≼' G1
            ), X = 1,
            if_(( Q '⋡' G1
                ; Q '≼' G2
                ), X = 2,
                false))).

%?- c2([0/0,0/0], X).
%@    X = 1.

%?- c2([1/1,0/0], X).
%@    X = 1.

%?- c2([2/2,0/0], X).
%@    X = 0.

%?- c2([0/1,0/0], X).
%@    X = 1.

%?- c2([0/2,0/0], X).
%@    X = 1.

%?- c2([0/3,0/0], X).
%@    X = 1.

%?- c2([0/4,0/0], X).
%@    X = 2.

%?- c2([0/4,1/1], X).
%@    X = 1.

%?- c2([0/4,0/1], X).
%@    X = 2.

%?- c2([0/4,1/2], X).
%@    X = 2.

% From this we see that c2/2 at least does have potential
% as a reasonable 'rolling' version of the 3+3 protocol.
% To enable efficient exploration of such protocols, I'll
% need some infrastructure -- esp. for *visualization*.

% Might there be some small handful of *decision-points*
% in D-E protocols, such that I could obtain a concise
% summary, in textual or graphic form?

% On a long walk with Plato yesterday 11/16, I stumbled on
% the idea of using finite-state machine diagrams for this.

% Clearly, any given D-E protocol identifies subsets of Qᴰ
% with enrollment or recommendation levels in {0,1,...,D}.
% That is, each protocol identifies an accessible subset
% U ⊆ Qᴰ, and partitions it into D+1 disjoint sets labeled
% by {0,1,...,D}.
%
% Accordingly, our process of 'discovery' can proceed by
% identifying these disjoint sets, and then seeking simple
% descriptions of them in terms of our partial order ≼.

d_init(D, Init) :-
    #D #> 0, length(Init, D),
    maplist(=(0/0), Init).

%?- d_init(3, Init).
%@    Init = [0/0,0/0,0/0].

d_tally_dose(D, Tally, X) :-
    (   d_tally_next(D, Tally, X)
    ;   d_mendtally_rec(D, Tally, X)
    ;   d_init(D, Tally), X = 1 % (**)
    ).

%?- d_tally_dose(3, [0/0,0/0,0/0], X).
%@    X = 1. % with (**) clause
%@    false. % before adding (**) above

d_rx_join(D, X, Jx) :-
    setof(Q, d_tally_dose(D, Q, X), Qxs),
    reduce(join, Qxs, Jx).

d_rx_meet(D, X, Mx) :-
    setof(Q, d_tally_dose(D, Q, X), Qxs),
    reduce(meet, Qxs, Mx).

%?- d_rx_join(2, 2, J2).
%@    J2 = [0/3,0/6].

%?- d_rx_meet(2, 2, M2).
%@    M2 = [1/6,1/3].

d_joins(D, Js) :-
    findall(X, (X in 0..D, indomain(X)), Xs),
    maplist(d_rx_join(D), Xs, Js).

d_meets(D, Ms) :-
    findall(X, (X in 0..D, indomain(X)), Xs),
    maplist(d_rx_meet(D), Xs, Ms).

%?- D in 2..6, indomain(D), time(d_meets(D, Ms)).
%@    % CPU time: 3.445s, 14_529_761 inferences
%@    D = 2, Ms = [[4/6,3/5],[1/5,4/5],[1/5,1/2]]
%@ ;  % CPU time: 25.122s, 95_637_410 inferences
%@    D = 3, Ms = [[4/6,3/6,3/5],[1/5,4/6,3/5],[1/5,1/3,3/5],[1/5,1/5,1/2]]
%@ ;  % CPU time: 203.674s, 624_595_369 inferences
%@    D = 4, Ms = [[4/6,3/6,3/6,3/5],[1/5,4/6,3/6,3/5],[1/5,1/3,3/6,3/5],[1/5,1/5,1/3,3/5],[1/5,1/5,1/5,1/2]]
%@ ;  % CPU time: 264.290s, 759_104_851 inferences
%@    error('$interrupt_thrown',repl/0).
% The post-rectification meets above are unchanged from those below.
% That suggests the rectified tallies were not 'binding constraints'.
% But now I must ask whether this fact looks 'obvious' in retrospect!
% Rectification moves tallies _down_, from higher to lower partitions.
% But it does this precisely because the moved tallies sit below some
% other tally already located in that lower-down partition.  Therefore,
% this move will not *necessarily* correct the mis-sorting of that
% other tally.  (So I may not have overlooked anything obvious--phew!)
%@    % CPU time: 2.193s, 9_802_470 inferences
%@    D = 2, Ms = [[4/6,3/5],[1/5,4/5],[1/5,1/2]]
%@ ;  % CPU time: 11.608s, 52_784_623 inferences
%@    D = 3, Ms = [[4/6,3/6,3/5],[1/5,4/6,3/5],[1/5,1/5,4/5],[1/5,1/5,1/2]]
%@ ;  % CPU time: 44.559s, 206_996_580 inferences
%@    D = 4, Ms = [[4/6,3/6,3/6,3/5],[1/5,4/6,3/6,3/5],[1/5,1/5,4/6,3/5],[1/5,1/5,1/5,4/5],[1/5,1/5,1/5,1/2]]
%@ ;  % CPU time: 147.920s, 690_356_469 inferences
%@    D = 5, Ms = [[4/6,3/6,3/6,3/6,3/5],[1/5,4/6,3/6,3/6,3/5],[1/5,1/5,4/6,3/6,3/5],[1/5,1/5,1/5,4/6,3/5],[1/5,1/5,1/5,1/5,4/5],[1/5,1/5,1/5,1/5,1/2]]
%@ ;  % CPU time: 452.192s, 2_087_367_540 inferences
%@    D = 6, Ms = [[4/6,3/6,3/6,3/6,3/6,3/5],[1/5,4/6,3/6,3/6,3/6,3/5],[1/5,1/5,4/6,3/6,3/6,3/5],[1/5,1/5,1/5,4/6,3/6,3/5],[1/5,1/5,1/5,1/5,4/6,3/5],[1/5,1/5,1/5,1/5,1/5,4/5],[1/5,1/5,1/5,1/5,1/5,1/2]].

% Do all these partitions start the trial enrolling at 1?

% The degenerate case D=1 does NOT make a 'clean start' from [0/0]:
%?- d_rx_meet(1, 1, M1).
%@    M1 = [1/3].
%?- d_rx_meet(1, 1, M1), M1 '≼' [0/0].
%@    false.
% But happily, this turns out to be the exception!

d_starts1(D) :-
    D #> 1, % D=1 case is exceptional, in NOT starting cleanly from [0/0].
    length(Init, D), maplist(=(0/0), Init),
    d_rx_meet(D, 1, M1), M1 '≼' Init, % <- (indeed this fails in D=1 case)
    d_rx_meet(D, 2, M2), M2 '⋠' Init.

%?- D in 2..6, indomain(D), time(d_starts1(D)). % (retread timings shown)
%@    % CPU time: 1.452s, 6_525_450 inferences
%@    D = 2
%@ ;  % CPU time: 5.793s, 26_681_589 inferences
%@    D = 3
%@ ;  % CPU time: 18.339s, 84_213_814 inferences
%@    D = 4
%@ ;  % CPU time: 57.714s, 234_167_553 inferences
%@    D = 5
%@ ;  % CPU time: 135.980s, 606_129_161 inferences
%@    D = 6.

% Let's now examine how close an approximation we can achieve
% to the 3+3 protocol, using these cascading partitions.
% Take the D=2 case, to begin.
% By construction, of course, every tally Qx followed by
% either enrollment or recommendation at dose X (or above)
% must obey the condition Mx '≼' Qx.
% Another way to say this, is that the upper set ↑Mx includes
% all Qx that are followed by enrollment/rec at dose X.
% But the converse need not hold: some tallies Q ∈ ↑Mx may be
% followed [per-protocol] by enrec at a dose _below_ X.
% Thus, if we use the Mx to select (cascading top-down) the
% next dose [en/rec TBD] for each given tally, then we may
% end up with a /less cautious/ protocol than we derived
% the Mx from.
% Thus, the 'approximation errors' we must look for are cases
% where My ≼ Qx for x < y.
d_x_mx(D, X, Mx) :-
    D in 2..6, indomain(D),
    d_meets(D, [_|Ms]), % Ms = [M1,...,MD]
    format("Found partition M1..M~d = ~w~n", [D,Ms]),
    nth0(X, Ms, Mx). % Thus, X in 0..(D-1)

%?- d_x_mx(2, X, Mx).
%@ Found partition M1..M2 = [[1/5,4/5],[1/5,1/2]]
%@    X = 0, Mx = [1/5,4/5]
%@ ;  X = 1, Mx = [1/5,1/2].

d_x_escapees(D, X, Qs) :-
    d_x_mx(D, X, Mx),
    #Xplus1 #= #X + 1,
    format("Checking against M~d = ~w..~n", [Xplus1,Mx]),
    setof(Q, (d_tally_dose(D, Q, X), Mx '≼' Q), Qs).

%?- d_x_escapees(2, X, Qs).
%@ Found partition M1..M2 = [[1/5,4/5],[1/5,1/2]]
%@ Checking against M1 = [1/5,4/5]..
%@ Checking against M2 = [1/5,1/2]..
%@    X = 1, Qs = [[0/3,2/6],[0/6,2/3],[0/6,2/6]].
%?- [1/5,1/2]'≼'[0/3,2/6].
%@    true.
%?- [1/5,1/2]'≼'[0/6,2/6].
%@    true.
%?- [1/5,1/2]'≼'[0/6,2/6].
%@    true.
% I think we do learn something from this!
% Let's consider each of these 3 cases, in reverse order:
% * [0/6,2/6]
%   This case has Rec=1 per protocol.  But it is also true that ..
%?- [1/6,1/6]'≼'[0/6,2/6].
%@    true.
%   Thus, perhaps we can in attribute this approximation
%   error to the unrectified Rec=2 for [1/6,1/6].
% * [0/3,2/6]
%   Here again, we seem to have a consequence of non-functorial
%   dose assignment.  By all means, let's see if rectification
%   solves this.
% * [0/6,2/3]
%   By contrast with the above, this would seem to be a case
%   where we might depend on enrollment rules, to augment the
%   filtering performed by Ms.

%?- d_x_escapees(3, X, Qs).
%@ Found partition M1..M3 = [[1/5,4/6,3/5],[1/5,1/5,4/5],[1/5,1/5,1/2]]
%@ Checking against M1 = [1/5,4/6,3/5]..
%@ Checking against M2 = [1/5,1/5,4/5]..
%@    X = 1, Qs = [[0/3,2/6,0/0],[0/3,2/6,2/3],[0/3,2/6,2/6],[0/3,2/6,3/6],[0/3,2/6,4/6],[0/6,2/3,0/0],[0/6,2/6,0/0],[0/6,2/6,2/3],[0/6,2/6,2/6],[0/6,2/6,3/3],[0/6,2/6,3/6],[0/6,2/6,4/6]]
%@ ;  Checking against M3 = [1/5,1/5,1/2]..
%@ X = 2, Qs = [[0/3,0/3,2/6],[0/3,0/3,3/6],[0/3,0/6,2/3],[0/3,0/6,2/6],[0/3,0/6,3/3],[0/3,0/6,3/6],[0/3,1/6,2/3],[0/3,1/6,2/6],[1/6,0/3,2/6],[1/6,0/6,2/3],[1/6,0/6,2/6]].

%?- d_x_escapees(4, X, Qs).
%@ Found partition M1..M4 = [[1/5,4/6,3/6,3/5],[1/5,1/5,4/6,3/5],[1/5,1/5,1/5,4/5],[1/5,1/5,1/5,1/2]]
%@ Checking against M1 = [1/5,4/6,3/6,3/5]..
%@ Checking against M2 = [1/5,1/5,4/6,3/5]..
%@    X = 1, Qs = [[0/3,2/6,0/0,0/0],[0/3,2/6,2/3,0/0],[0/3,2/6,2/6,0/0],[0/3,2/6,2/6,2/3],[0/3,2/6,2/6,2/6],[0/3,2/6,2/6,3/3],[0/3,2/6,2/6,3/6],[0/3,2/6,2/6,4/6],[0/3,2/6,3/6,0/0],[0/3,2/6,3/6,2/3],[0/3,2/6,3/6,2/6],[0/3,2/6,3/6,3/6],[0/3,2/6,3/6,4/6],[0/3,2/6,4/6,0/0],[0/6,2/3,0/0,0/0],[0/6,2/6,0/0,0/0],[0/6,2/6,2/3,... / ...],[0/6,2/6,... / ...|...],[0/6,... / ...|...],[... / ...|...]|...]
%@ ;  Checking against M3 = [1/5,1/5,1/5,4/5]..
%@ X = 2, Qs = [[0/3,0/3,2/6,0/0],[0/3,0/3,2/6,2/3],[0/3,0/3,2/6,2/6],[0/3,0/3,2/6,3/6],[0/3,0/3,2/6,4/6],[0/3,0/3,3/6,0/0],[0/3,0/3,3/6,2/6],[0/3,0/3,3/6,3/6],[0/3,0/6,2/3,0/0],[0/3,0/6,2/6,0/0],[0/3,0/6,2/6,2/3],[0/3,0/6,2/6,2/6],[0/3,0/6,2/6,3/3],[0/3,0/6,2/6,3/6],[0/3,0/6,2/6,4/6],[0/3,0/6,3/3,0/0],[0/3,0/6,3/6,... / ...],[0/3,0/6,... / ...|...],[0/3,... / ...|...],[... / ...|...]|...]
%@ ;  Checking against M4 = [1/5,1/5,1/5,1/2]..
%@ X = 3, Qs = [[0/3,0/3,0/3,2/6],[0/3,0/3,0/3,3/6],[0/3,0/3,0/6,2/3],[0/3,0/3,0/6,2/6],[0/3,0/3,0/6,3/3],[0/3,0/3,0/6,3/6],[0/3,0/3,0/6,4/6],[0/3,0/3,1/6,2/3],[0/3,0/3,1/6,2/6],[0/3,0/3,1/6,3/6],[0/3,1/6,0/3,2/3],[0/3,1/6,0/3,2/6],[0/3,1/6,0/3,3/6],[0/3,1/6,0/6,2/3],[0/3,1/6,0/6,2/6],[0/3,1/6,0/6,3/3],[0/3,1/6,0/6,... / ...],[0/3,1/6,... / ...|...],[0/3,... / ...|...],[... / ...|...]|...].

% From the above, I seem to have learned that meets alone
% do not adequately represent the relevant partitions of
% the accessible tally space.
%
% A more informative summary could be had in the form of
% _minimal sets_ drawn from these regions of the space.
% This of course amounts to generalizing from the special
% case where a singleton set {meet} sufficiently defines
% the region.

d_rx_mins(D, X, Mxs) :-
    setof(Q, d_tally_dose(D, Q, X), Qxs),
    qs_mins(Qxs, Mxs).

%?- d_rx_mins(2, 2, M2s).
%@    M2s = [[1/6,1/3],[1/6,0/0],[0/3,0/0]].

d_minsets(D, Mss) :-
    findall(X, (X in 0..D, indomain(X)), Xs),
    maplist(d_rx_mins(D), Xs, Rss),
    reverse(Rss, Mss). % Top-to-bottom cascade

%?- d_minsets(2, Mss). % now with R=2 (more arrows!)
%@    Mss = [[[1/6,1/3]],
%            [[1/6,4/6]],
%            [[4/6,0/0],[3/6,4/6]]].

%?- d_minsets(3, Mss). % now with R=2 (more arrows!)
%@    Mss = [[[1/6,1/6,1/3]],
%            [[1/6,1/6,1/6],[1/6,1/3,0/0],[1/6,0/3,4/6]],
%            [[1/6,4/6,0/0],[1/6,3/6,4/6]],
%            [[4/6,0/0,0/0],[3/6,4/6,0/0],[3/6,3/6,4/6]]].

% As anticipated, adding more arrows has allowed
% more parsimonious description of the partitions.
%?- qs_mins([[1/6,1/6,1/3],[1/6,1/6,0/0],[1/6,0/3,0/0],[0/3,0/3,0/0]], Mins3).
%@    Mins3 = [[1/6,1/6,1/3]]. % from 4 descriptors to 1
%?- qs_mins([[1/6,1/6,1/6],[1/6,1/3,0/0],[1/6,0/3,4/6],[1/6,0/3,3/3],[0/3,0/3,3/3]], Mins2).
%@    Mins2 = [[1/6,1/6,1/6],[1/6,1/3,0/0],[1/6,0/3,4/6]]. % 5 ~~> 3 descriptors
%?- qs_mins([[1/6,4/6,0/0],[1/6,3/6,4/6],[1/6,3/6,3/3],[0/3,3/6,3/3]], Mins1).
%@    Mins1 = [[1/6,4/6,0/0],[1/6,3/6,4/6]]. % 4 ~~> 2 descriptors
%?- [3/6,3/6,4/6]'≼'[3/6,3/6,3/3].
%@    true. % ..enabling the RHS to be dropped from R=1 4-descriptor list for dose 0.
%?- reduce(meet, [[1/6,1/6,1/6],[1/6,1/3,0/0],[1/6,0/3,4/6]], Meet).
%@    Meet = [1/6,1/3,3/6]. % Perhaps meets of these minimal sets will suffice?

%?- d_minsets(4, Mss). % now with R=2 (more arrows!)
%@    Mss = [[[1/6,1/6,1/6,1/3]],
%            [[1/6,1/6,1/6,1/6],[1/6,1/6,1/3,0/0],[1/6,1/6,0/3,4/6]],
%            [[1/6,1/6,1/6,2/6],[1/6,1/3,0/0,0/0],[1/6,0/3,4/6,0/0],[1/6,0/3,3/6,4/6]],
%            [[1/6,4/6,0/0,0/0],[1/6,3/6,4/6,0/0],[1/6,3/6,3/6,4/6]],
%            [[4/6,0/0,0/0,0/0],[3/6,4/6,0/0,0/0],[3/6,3/6,4/6,0/0],[3/6,3/6,3/6,4/6]]].

% Apparently, I had already anticipated this possibility,
% and had implemented d_meets/2!

%?- time(d_meets(2, Ms)).
%@    % CPU time: 2.738s, 12_779_110 inferences
%@    Ms = [[4/6,3/6],[1/6,4/6],[1/6,1/3]].
%@    % CPU time: 3.444s, 15_872_829 inferences
%@    Ms = [[4/6,3/6],[1/6,4/6],[1/6,1/3]].
%?- time(d_meets(3, Ms)).
%@    % CPU time: 27.010s, 132_516_876 inferences
%@    Ms = [[4/6,3/6,3/6],[1/6,4/6,3/6],[1/6,1/3,3/6],[1/6,1/6,1/3]].
%?- time(d_meets(4, Ms)).
%@    % CPU time: 240.604s, 1_166_191_534 inferences
%@    Ms = [[4/6,3/6,3/6,3/6],[1/6,4/6,3/6,3/6],[1/6,1/3,3/6,3/6],[1/6,1/6,1/3,3/6],[1/6,1/6,1/6,1/3]].

% Given a descending cascade of tallies [L|Ls] = [Lᴅ ≻ ... ≻ L₁],
% we have a nested sequence of principal upper sets,
%
%               ↑Lᴅ ⊂ ... ⊂ ↑L₁ ⊂ ↑𝟘 ≡ 𝒬,
%
% where 𝟘 denotes the initial object for the accessible part of 𝒬,
% for example [6/6,6/6] in the 2-dose 3+3 trial.
% Because this covers [the accessible region of] 𝒬, we obtain a
% functor E:𝒬⟶{0≤...≤D} according to
%
%             E(q) = max[{k | Q ≽ Lₖ}∪{0}].
%
% Provided we understand L₀ = 𝟘, we can write equivalently,
%
%                 k ≤ E(q)  iff  Lₖ ≼ q,
%
% revealing an adjunction L ⊣ E, in which L₋:{0≤...≤D}→𝒬 is the
% lower adjoint to an upper-Galois enrollment E:𝒬⟶𝒟={0≤...≤D}.
cascade_tally_uadjoint([], _, 0).
cascade_tally_uadjoint([L|Ls], Q, X) :-
    if_(Q '≽' L, length([L|Ls], X),
        cascade_tally_uadjoint(Ls, Q, X)).

% Conversely, any length-D tally cascade [Gᴅ-1 ≻ ... ≻ G₀]
% defines also a nested sequence of principal _lower_ sets,
%
%    Gᴅ≡𝟙 ≻ Gᴅ-1 ≻ ... ≻ L₀  ⟹  𝒬 ⊃ ↓Gᴅ-1 ⊃ ... ⊃ ↓G₀,
%
% where 𝟙 denotes the _final_ object for [the accessible part
% of] 𝒬 -- for example, [0/6,0/6] in the 2-dose 3+3 trial.
% From this we obtain in like manner a lower-Galois E⊣G, with
%
%                E(q) ≤ k  iff  q ≼ Gₖ.
%
% Operationally, the implementation keeps discarding the earlier
% (and so higher-up) elements of the cascade Gs so long as they
% are above Q (i.e., Q ≼ Gᵢ), until Q is above the remainder.
% Consequently, the last Gₖ peeled off will be the highest level
% in the cascade that exceeds Q.  Because we've used zero-based
% indexing here, however, the remainder of the list will be of
% length k -- precisely the index we seek.
cascade_tally_ladjoint([], _, 0).
cascade_tally_ladjoint([G|Gs], Q, X) :-
    if_(Q '≼' G, cascade_tally_ladjoint(Gs, Q, X),
       length([G|Gs], X)).


d_meetscascade(D, Ls) :-
    d_meets(D, [_|Ms]), % drop trivial bottom meet qua 𝟘
    reverse(Ms, Ls).

%?- d_meetscascade(3, Ls).
%@    Ls = [[1/6,1/6,1/3],[1/6,1/3,3/6],[1/6,4/6,3/6]].

ug3(Q, X) :-
    cascade_tally_uadjoint(
        [[1/6,1/6,1/3],[1/6,1/3,3/6],[1/6,4/6,3/6]],
        Q, X).

%?- ug3([0/0,0/0,0/0], StartD).
%@    StartD = 2.

d_joinscascade(D, Gs) :-
    d_joins(D, Js),
    reverse(Js, [_|Gs]). % drop trivial top join qua 𝟙

%?- d_joinscascade(3, Gs).
%@    Gs = [[0/3,0/6,0/0],[0/6,0/0,0/0],[2/6,0/0,0/0]].

lg3(Q, X) :-
    cascade_tally_ladjoint(
        [[0/3,0/6,0/0],[0/6,1/3,0/0],[2/6,0/0,0/0]],
        Q, X).

%?- lg3([0/0,0/0,0/0], StartD).
%@    StartD = 2.

% Interestingly, in neither case do we obtain the 'clean start'
% from an initial〈0/0〉dose.  On the one hand, perhaps I ask
% for too much, that miraculously the rest of the 3+3 protocol
% just so happens to be consistent with the very special case
% of initial dosing.  OTOH, maybe this type of self-consistency
% will turn out to be a desirable property of dose-escalation
% protocols generally.  But either way, such investigations lie
% farther down the road; the more pressing question is whether
% I can achieve reasonably close approximations to 3+3 protocol
% in the form of (upper/lower) Galois enrollments.

% Since if anything we ought to be interested in protocols
% that are SAFER than 3+3, let us focus on the behavior of
% the lower-Galois enrollment lg/2, which (except at <0/0>)
% yields dose recommendations matching or below 3+3's.

lg3_approx_perprotocol(E, QXs) :-
    D = 3,
    E in 0..D, indomain(E),
    setof(Q-X,
          (   d_tally_dose(D, Q, X),
              lg3(Q, E),
              X \== E
          ), QXs).

%?- lg3_approx_perprotocol(3, QXs).
%@    false. % lg3 assigns dose 3 at least as cautiously as 3+3
%?- lg3_approx_perprotocol(2, QXs).
%@    QXs = [[0/0,0/0,0/0]-1,
%            [0/3,0/3,0/0]-3,
%            [0/3,0/3,1/3]-3, (a)
%            [0/3,1/6,0/0]-3,
%            [0/3,1/6,0/3]-3,
%            [0/3,1/6,1/3]-3, (b)
%            [1/6,0/3,0/3]-3,
%            [1/6,1/6,0/3]-3].
% What do we learn here?
% Apart from the 'messy' start-up (to be dealt with separately),
% we find at least one case (a) where lg3 backs away from quite
% incautious behavior by 3+3.  The same might be said of (b) as
% well, except that it implicates also 3+3's maximum dose-wise
% enrollment constraint in addition to its dose-assignment rule
% (inasmuch as one can even discuss these elements separately).
%
% Let's ask what would happen if we followed lg3's rules:
%?- lg3([0/3,1/6,1/3], E).
%@    E = 2.
%?- lg3([0/3,1/7,1/3], E).
%@    E = 2.
%?- lg3([0/3,1/8,1/3], E).
%@    E = 2.
%?- lg3([0/3,1/9,1/3], E).
%@    E = 2.
%?- lg3([0/3,1/10,1/3], E).
%@    E = 3. % INTERESTING!
% Wow!!  I didn't expect this at all!
% My intuition was that we would remain stuck forever at E=2.
% But now I'll hazard the guess that our 1:2 generator arrow
% (ie, r:=2) now yields enough linkage between adjacent doses
% to enable ultimately an escalation out of E=2.
% This is a really important discovery, since it opens up the
% possibility of abstracting dose-escalation rules from trial
% size limits, allowing analysis of ASYMPTOTIC PROPERTIES.
% This, in turn, suggests that dose-escalation protocols of
% this general form (ie, Galois, or at least _lower_-Galois)
% hold enough promise to be worth exploring _systematically_,
% searching with high degrees of freedom, far beyond simple
% heuristics such as d_meetscascade/2 and d_joinscascade/2.
% Accordingly, I'll need to resume work on the visualization,
% and bring that to a usable state!

/*
?- E = 2, setof(Q-X, (d_tally_dose(3, Q, X), lg(Q, E), X \== E), QXs),
   maplist(portray_clause, QXs).
%@ [0/0,0/0,0/0]-1.
%@ [0/3,0/3,0/0]-3.
%@ [0/3,0/3,1/3]-3.
%@ [0/3,1/6,0/0]-3.
%@ [0/3,1/6,0/3]-3.
%@ [0/3,1/6,1/3]-3.
%@ [1/6,0/3,0/3]-3.
%@ [1/6,1/6,0/3]-3.
%@    E = 2, QXs = [[0/0,0/0,0/0]-1,[0/3,0/3,0/0]-3,[0/3,0/3,1/3]-3,[0/3,1/6,0/0]-3,[0/3,1/6,0/3]-3,[0/3,1/6,1/3]-3,[1/6,0/3,0/3]-3,[1/6,1/6,0/3]-3].
%@ [0/3,1/3,0/0]-2.
%@ [0/3,1/6,2/3]-2.
%@ [0/3,1/6,3/3]-2.
%@ [0/3,1/6,3/6]-2.
%@ [0/3,1/6,4/6]-2.
%@ [1/6,0/0,0/0]-2.
%@ [1/6,0/3,0/0]-3.
%@ [1/6,0/3,1/3]-3.
%@ [1/6,0/3,2/3]-2.
%@ [1/6,0/3,2/6]-2.
%@ [1/6,0/3,3/3]-2.
%@ [1/6,0/3,3/6]-2.
%@ [1/6,0/3,4/6]-2.
%@ [1/6,0/6,2/3]-2.
%@ [1/6,0/6,3/3]-2.
%@ [1/6,0/6,3/6]-2.
%@ [1/6,0/6,4/6]-2.
%@ [1/6,1/3,0/0]-2.
%@ [1/6,1/6,0/0]-3.
%@ [1/6,1/6,1/3]-3.
%@    E = 1, QXs = [[0/3,1/3,0/0]-2,[0/3,1/6,2/3]-2,[0/3,1/6,3/3]-2,[0/3,1/6,3/6]-2,[0/3,1/6,4/6]-2,[1/6,0/0,0/0]-2,[1/6,0/3,0/0]-3,[1/6,0/3,1/3]-3,[1/6,0/3,2/3]-2,[1/6,0/3,2/6]-2,[1/6,0/3,3/3]-2,[1/6,0/3,3/6]-2,[1/6,0/3,4/6]-2,[1/6,0/6,2/3]-2,[1/6,0/6,3/3]-2,[1/6,0/6,3/6]-2,[1/6,0/6,... / ...]-2,[1/6,... / ...|...]-2,[... / ...|...]-3,... - ...]
%@ ;  [0/0,0/0,0/0]-1.
%@ [0/3,0/3,0/0]-3.
%@ [0/3,0/3,1/3]-3.
%@ [0/3,1/6,0/0]-3.
%@ [0/3,1/6,0/3]-3.
%@ [0/3,1/6,1/3]-3.
%@ [1/6,0/3,0/3]-3.
%@ [1/6,1/6,0/3]-3.
%@ E = 2, QXs = [[0/0,0/0,0/0]-1,[0/3,0/3,0/0]-3,[0/3,0/3,1/3]-3,[0/3,1/6,0/0]-3,[0/3,1/6,0/3]-3,[0/3,1/6,1/3]-3,[1/6,0/3,0/3]-3,[1/6,1/6,0/3]-3].
*/

d_path(D, Path) :-
    length(Init, D), maplist(=(0/0), Init), Init = [I|Is],
    phrase(path([I]-Is), Path).

%?- d_path(2, Path).
%@    Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[0/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[1/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[0/6]-[2/6],stop,recommend_dose(1)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[1/6]-[2/6],stop,recommend_dose(1)]
%@ ;  ... .

%?- J+\(findall(Path, user:d_path(2, Path), Paths), lists:length(Paths, J)).
%@    J = 46.

% Let's enable checking all the interim tallies and dose recs
d_tally_next(D, Tally, Next) :-
    length(Init, D), maplist(=(0/0), Init), Init = [I|Is],
    phrase(path([I]-Is), Path),
    phrase((..., [State0,E,Ls-_], ...), Path),
    member(E, [esc,des,sta]),
    state_tallies(State0, Tally),
    length(Ls, Next).

% How, in general, do I transform a trial _state_
% (in the form of a pair of lists) into the tally
% applicable at that time?
% The LHS list is a descending 

%?- setof(Q-X, d_tally_next(2, Q, X), QXs).
%@    QXs = [[0/3,0/0]-2,
%            [0/3,0/3]-2,
%            [0/3,1/3]-2,
%            [0/3,2/3]-1,
%            [0/3,2/6]-1,
%            [0/3,3/3]-1,
%            [0/3,3/6]-1,
%            [0/3,4/6]-1,
%            [1/3,0/0]-1,
%            [1/6,0/0]-2,
%            [1/6,0/3]-2,
%            [1/6,1/3]-2].
% The above look all correct.  Now let's check against c2 ...

%?- setof(Q^X^Y, (d_tally_next(2, Q, X), c2(Q, Y)), QXYs).
%@    QXYs = [[0/3,0/0]^2^1,
%             [0/3,0/3]^2^1,
%             [0/3,1/3]^2^1,
%             [0/3,2/3]^1^1,
%             [0/3,2/6]^1^1,
%             [0/3,3/3]^1^1,
%             [0/3,3/6]^1^1,
%             [0/3,4/6]^1^1,
%             [1/3,0/0]^1^1,
%             [1/6,0/0]^2^1, % **
%             [1/6,0/3]^2^2, % **
%             [1/6,1/3]^2^1].

% The starred (**) rows are quite interesting.
% Apparently, c2/2 is trapped in a 'Catch-22',
% such that it cannot escalate even from [1/6,0/0]
% without already having some data at dose level 2!

% Thus, it would appear that I need to define my 'ladder' to propel
% dose escalation.  Let's investigate the _meets_ of the several
% Qf strata.
/*
?- D = 2, X in 0..D, indomain(X),
   findall(Qf, d_mendtally_rec(D, Qf, X), Qfs),
   qs_mins(Qfs, Qfs1).
%@    D = 2, X = 0, Qfs = [[2/3,0/0],[2/6,0/0],[2/6,2/3],[2/6,2/6],[2/6,3/3],[2/6,3/6],[2/6,4/6],[3/3,0/0],[3/6,0/0],[3/6,2/3],[3/6,2/6],[3/6,3/3],[3/6,3/6],[3/6,4/6],[4/6,0/0]], Qfs1 = [[3/3,0/0],[3/6,3/3],[3/6,4/6],[4/6,0/0]]
%@ ;  D = 2, X = 1, Qfs = [[0/6,2/3],[0/6,2/6],[0/6,3/3],[0/6,3/6],[0/6,4/6],[1/6,1/6],[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]], Qfs1 = [[1/6,3/3],[1/6,4/6]]
%@ ;  D = 2, X = 2, Qfs = [[0/3,0/6],[0/3,1/6],[1/6,0/6]], Qfs1 = [[0/3,1/6],[1/6,0/6]].
*/

/*
RQss = [[[0/6,2/6],[1/6,0/6],[0/3,0/6]],
        [[0/6,3/6],[1/6,1/6],[0/3,1/6]],[[0/6,4/6],[1/6,2/6],[0/6,2/3]],[[1/6,3/6],[0/6,3/3],[2/6,0/0]],[[1/6,4/6],[2/6,2/6],[1/6,2/3],[2/3,0/0]],[[2/6,3/6],[1/6,3/3],[3/6,0/0]],[[2/6,4/6],[3/6,2/6],[2/6,2/3],[3/3,0/0]],[[3/6,3/6],[2/6,3/3],[4/6,0/0]],[[3/6,4/6],[3/6,2/3]],[[3/6,3/3]]].
*/

%?- c2([0/0,0/0], X).
%@    X = 1. % unch
%@    X = 1.

%?- c2([1/1,0/0], X).
%@    X = 1. % unch
%@    X = 1.

%?- c2([2/2,0/0], X).
%@    X = 0. % unch
%@    X = 0.

%?- c2([0/3,0/0], X).
%@    X = 1. % unch
%@    X = 1.

%?- c2([0/4,0/0], X).
%@    X = 1. % unch
%@    X = 1.

%?- c2([0/6,0/0], X).
%@    X = 1. % still unch!
%@    X = 1. % Huh!

%?- [0/6,0/0] '≼' [2/6,0/4].
%@    false.

%?- [0/6,0/0] '≼' [0/6,2/6].
%@    false.

%?-  [2/6,0/4] '≼' [0/6,0/0].
%@    false.

%?- [0/6,0/0] '≼' [0/6,2/6].
%@    false.

%?- [0/6,0/0] '≽' [0/6,2/6].
%@    false.

%?- [0/6,0/0] '≼' [0/5,0/6].
%@    true. % Repaired!
%@    false. % This CAN'T be right, can it?

%?- [0/6,0/0] '≼' [0/6,0/6].
%@    true.

%?- [0/6,0/0] '≼' [0/0,0/6].
%@    true. % Repaired!
%@    false. % This ALSO CAN'T be right!

%?- qs_Ts_Ñs([0/6,0/0], Ts, Ñs).
%@    Ts = [0,0], Ñs = [0,6].

%?- qs_Ts_Ñs([0/0,0/6], Ts, Ñs).
%@    Ts = [0,0], Ñs = [6,6].

% This means I need to refer to the developments in the monograph.
% Perhaps even those were wrong?

%?- [0/6,0/0] '≽' [2/6,0/4].
%@    false.

% Let's make sure to gain access to upper-Galois enrollments, too.
% These correspond to the lower (left) adjoint L of Def 4.2.

% Interestingly, I now seem to have found a use for '⋡'/3 below!
'⋠'(Q1s, Q2s, Truth) :- '≼'(Q1s, Q2s, Untruth),
                        reif:non(Untruth, Truth).

% lgalois/3 ought to be _dual_ to galois/3, and the
% dual construction may prove quite straighforward!
% Here the Mss should be an _ascending_ sequence of
% _minimal_ sets, and order relations reversed so
% that '⋡' becomes '⋠'; accordingly, the Qs must now
% be sorted in _??scending_ order.
% Thus lgalois/3 searches the ascending list [Q|Qs]
% for the first Lx satisfying Lx ≼ Q ∀ Q ∈ Ms, or
% equivalently ↑Lx ⊇ Ms.
lgalois([Ms|Mss], [Q|Qs], [L|Ls]) :-
    if_(tmember_t('⋠'(Q), Ms),         % ∃ M ∈ Ms s.t. Q ⋠ M ?
        lgalois([Ms|Mss], Qs, [L|Ls]), % if so, Q is not an Lx;
        (   format("↑~w ⊇ ~w.~n", [Q, Ms]),
            L = Q,                     % otherwise, collect it
            lgalois(Mss, Qs, Ls)       % and recurse.
        )
       ).
lgalois([], _, []). % Succeed when all strata are accounted-for.

d_ls(D, Ls) :-
    format("Listing Qs...... ", []),
    time(findall(Q, qs_d_nmax(Q, D, 6), Qs)),
    qs_sorted(Qs, SQs), % instrumentation included
    %%reverse(SQs, RQs),
    format("Stratifying Qf.. ", []),
    time(d_Qfstratamin(D, Mss)), % NB: We require MINIMAL strata here.
    format("Finding g's ..~n", []),
    %%time(lgalois(Mss, RQs, Ls)).
    time(lgalois(Mss, SQs, Ls)).

%?- d_ls(2, Ls). % With new, post-Meetup ≼
%@ Listing Qs......    % CPU time: 0.079s, 249_943 inferences
%@ Stratifying Qf..    % CPU time: 0.762s, 3_304_065 inferences
%@ Finding g's ..
%@ ↑[4/6,3/5] ⊇ [[4/6,0/0],[3/6,4/6],[3/6,3/3]].
%@ ↑[5/6,2/5] ⊇ [[1/6,4/6],[1/6,3/3]].
%@ ↑[6/6,1/5] ⊇ [[1/6,1/6],[0/3,1/6]].
%@    % CPU time: 0.486s, 1_396_488 inferences
%@    Ls = [[4/6,3/5],[5/6,2/5],[6/6,1/5]].

%?- [0/0,0/0] '≽' [4/6,3/5].
%@    true.

%@ Listing Qs......    % CPU time: 0.067s, 249_943 inferences
%@ Sorting length-784 list Qs:
%@   .. encoding Qs:   % CPU time: 0.646s, 3_382_043 inferences
%@    % CPU time: 0.650s, 3_386_626 inferences
%@ Stratifying Qf..    % CPU time: 1.134s, 5_056_454 inferences
%@ Finding g's ..
%@ ↑[4/4,3/3] ⊇ [[3/3,0/0],[3/6,3/3],[3/6,4/6],[4/6,0/0]].
%@ ↑[5/6,2/6] ⊇ [[1/6,3/3],[1/6,4/6]].
%@ ↑[5/5,2/6] ⊇ [[0/3,1/6],[1/6,0/6]].
%@    % CPU time: 0.744s, 3_284_627 inferences
%@    Ls = [[4/4,3/3],[5/6,2/6],[5/5,2/6]]. % Unchanged with rectified d_mendtally_rec/3.
%?- d_ls(2, Ls).
%@ Listing Qs......    % CPU time: 0.068s, 249_943 inferences
%@ Sorting length-784 list Qs:
%@   .. encoding Qs:   % CPU time: 0.649s, 3_382_043 inferences
%@    % CPU time: 0.652s, 3_386_626 inferences
%@ Stratifying Qf..    % CPU time: 0.861s, 3_801_888 inferences
%@ Finding g's ..
%@ ↑[4/4,3/3] ⊇ [[3/3,0/0],[3/6,3/3],[3/6,4/6],[4/6,0/0]].
%@ ↑[5/6,2/6] ⊇ [[1/6,3/3],[1/6,4/6]].
%@ ↑[5/5,2/6] ⊇ [[0/3,1/6],[1/6,1/6]].
%@    % CPU time: 0.747s, 3_284_633 inferences
%@    Ls = [[4/4,3/3],[5/6,2/6],[5/5,2/6]].

% These look a bit more reasonable now.  Can I check 'by hand'
% that they obey the conditions I expect?
%?- X^Mxs+\(X in 0..2, clpz:indomain(X), findall(Qfx, user:d_endtally_rec(2, Qfx, X), Qfxs), user:qs_mins(Qfxs, Mxs)).
%@    X = 0, Mxs = [[3/3,0/0],[3/6,3/3],[3/6,4/6],[4/6,0/0]]
%@ ;  X = 1, Mxs = [[1/6,3/3],[1/6,4/6]]
%@ ;  X = 2, Mxs = [[0/3,1/6],[1/6,1/6]].
% Thus, the minimal subsets of the several Qf strata look correct.

%?- [4/4,3/3] '≼' [3/3,0/0].
%@    true.
%?- [4/4,3/3] '≼' [3/6,3/3].
%@    true.
%?- [4/4,3/3] '≼' [3/6,4/6].
%@    true.
%?- [4/4,3/3] '≼' [4/6,0/0].
%@    true.
% So the given L0 is indeed below all of X=0 Qf's.

%?- [0/0,0/0] '≽' [4/4,3/3].
%@    true.
%?- [0/0,0/0] '≽' [5/6,2/6].
%@    false.
%?- [0/0,0/0] '≽' [5/5,2/6].
%@    false.
% According to the above, we would at least *start* the trial
% at does level 1.

%?- [2/3,0/0] '≽' [4/4,3/3].
%@    true.
% But here we see that a trial based naively on (L0,L1,L2)
% would continue to enroll even after 2/3 toxicities at
% the lowest dose!
% But this now leads me to question whether these L's
% truly capture what I thought!
% 1. Is [2/3,0/0] in Qf0s?
%?- d_endtally_rec(2, [2/3,0/0], X).
%@    X = 0 % Yes.
%@ ;  false.
% 2. What are the supposed relations of L0 & L1 to this?
%?- [L0,L1,L2] = [[4/4,3/3],[5/6,2/6],[5/5,2/6]], Q0 = [2/3,0/0], L0 '≼' Q0.
%@    L0 = [4/4,3/3], L1 = [5/6,2/6], L2 = [5/5,2/6], Q0 = [2/3,0/0].
%?- [L0,L1,L2] = [[4/4,3/3],[5/6,2/6],[5/5,2/6]], Q0 = [2/3,0/0], L1 '≼' Q0.
%@    false.
% Is this what I expected or hoped?  Yes, I think so!
% We have L0 indeed being under all of F⁻¹(0), but L1 not being below
% at least this one value.  Might L1 sit below any elements of F⁻¹(0)?
%?- d_endtally_rec(2,Qf,0), L1 = [5/6,2/6], L1 '≼' Qf.
%@    Qf = [2/6,2/3], L1 = [5/6,2/6]
%@ ;  Qf = [2/6,2/6], L1 = [5/6,2/6]
%@ ;  Qf = [2/6,3/6], L1 = [5/6,2/6]
%@ ;  Qf = [2/6,4/6], L1 = [5/6,2/6]
%@ ;  Qf = [3/6,2/6], L1 = [5/6,2/6]
%@ ;  Qf = [3/6,3/6], L1 = [5/6,2/6]
%@ ;  Qf = [3/6,4/6], L1 = [5/6,2/6]
%@ ;  false.
% So this partition does a pretty poor job of separating
% even the final tallies!

/*
What if I ultimately need two distinct sets of cutoffs?
During the calculation of Gs, we learn that
 ↓[2/6,0/4] ⊇ [[2/6,0/0],[2/6,2/6]].

*/
%?- [2/6,0/4] '≽' [2/6,0/0]. % G0 is above all of F⁻¹(0).
%@    true.
%?- [2/6,0/4] '≽' [2/6,2/6].
%@    true.
%?- d_mendtally_rec(2, Qrf, 0), Qrf '⋠' [2/6,0/4].
%@    false.
%?- d_endtally_rec(2, Qrf, 0), Qrf '⋠' [2/6,0/4].
%@    false.
/*
?- Gs = [[2/6,0/4], [0/6,2/6], [0/5,0/6]],
   X in 0..2, indomain(X),
   d_endtally_rec(2, Qf, X),
   nth0(X, Gs, Gx), Qf '⋠' Gx.
%@    false.
% Does this just trivially recapitulate some part of
% the definition of the G's?  Does it say anything new?
*/

d_Qfstratamin(D, Mss) :-
    d_Qfstrata(D, Qss),
    maplist(qs_mins, Qss, Mss). % qs_maxs/2 ~~> qs_mins/2 is all that changed!
    %%%maplist(qs_emins, Qss, Mss). % qs_maxs/2 ~~> qs_mins/2 is all that changed!

%?- D = 3, time(d_Qfstratamin(D, Mss)). % back to qs_mins/2 for comparison..
%@    % CPU time: 3.803s, 15_635_161 inferences
%@    D = 3, Mss = [[[3/6,3/6,3/3],[3/6,3/6,4/6],[3/6,4/6,0/0],[4/6,0/0,0/0]],[[1/6,3/6,3/3],[1/6,3/6,4/6],[1/6,4/6,0/0]],[[0/3,1/6,3/3],[1/6,1/6,3/3],[1/6,1/6,4/6]],[[0/3,0/3,1/6],[1/6,0/3,1/6],[1/6,1/6,1/6]]].

%?- D = 3, time(d_Qfstratamin(D, Mss)). % using qs_emins/2
%@ Sorting length-35 list Qs:
%@   .. encoding Qs:   % CPU time: 0.027s, 65_927 inferences
%@    % CPU time: 0.029s, 68_259 inferences
%@ Sorting length-30 list Qs:
%@   .. encoding Qs:   % CPU time: 0.022s, 52_321 inferences
%@    % CPU time: 0.024s, 54_633 inferences
%@ Sorting length-20 list Qs:
%@   .. encoding Qs:   % CPU time: 0.015s, 32_542 inferences
%@    % CPU time: 0.016s, 34_814 inferences
%@ Sorting length-8 list Qs:
%@   .. encoding Qs:   % CPU time: 0.005s, 10_447 inferences
%@    % CPU time: 0.006s, 12_671 inferences
%@    % CPU time: 3.115s, 13_526_584 inferences
%@    D = 3, Mss = [[[4/6,0/0,0/0],[3/6,4/6,0/0],[3/6,3/6,4/6],[3/6,3/6,3/3]],[[1/6,4/6,0/0],[1/6,3/6,4/6],[1/6,3/6,3/3]],[[1/6,1/6,4/6],[1/6,1/6,3/3],[0/3,1/6,3/3]],[[1/6,1/6,1/6],[1/6,0/3,1/6],[0/3,0/3,1/6]]].

%?- D = 3, time(d_Qfstratamin(D, Mss)).
%@    % CPU time: 3.763s, 15_635_161 inferences
%@    D = 3, Mss = [[[3/6,3/6,3/3],[3/6,3/6,4/6],[3/6,4/6,0/0],[4/6,0/0,0/0]],[[1/6,3/6,3/3],[1/6,3/6,4/6],[1/6,4/6,0/0]],[[0/3,1/6,3/3],[1/6,1/6,3/3],[1/6,1/6,4/6]],[[0/3,0/3,1/6],[1/6,0/3,1/6],[1/6,1/6,1/6]]].


%?- d_ls(3, Ls).
%@ Listing Qs......    % CPU time: 1.585s, 6_660_437 inferences
%@ Sorting length-21952 list Qs:
%@   .. encoding Qs:   % CPU time: 20.381s, 109_986_469 inferences
%@    % CPU time: 20.448s, 110_054_608 inferences
%@ Stratifying Qf..    % CPU time: 4.332s, 19_509_965 inferences
%@ Finding g's ..
%@ ↑[4/4,3/3,3/3] ⊇ [[3/3,0/0,0/0],[3/6,3/3,0/0],[3/6,3/6,3/3],[3/6,3/6,4/6],[3/6,4/6,0/0],[4/6,0/0,0/0]].
%@ ↑[5/6,2/4,3/5] ⊇ [[1/6,3/3,0/0],[1/6,3/6,3/3],[1/6,3/6,4/6],[1/6,4/6,0/0]].
%@ ↑[5/5,2/4,3/5] ⊇ [[0/3,1/6,3/3],[1/6,1/6,3/3],[1/6,1/6,4/6]].
%@ ↑[5/6,2/3,3/5] ⊇ [[0/3,0/3,1/6],[1/6,0/3,1/6],[1/6,1/6,1/6]].
%@    % CPU time: 27.944s, 124_266_679 inferences
%@    Ls = [[4/4,3/3,3/3],[5/6,2/4,3/5],[5/5,2/4,3/5],[5/6,2/3,3/5]].
%@ Listing Qs......    % CPU time: 1.583s, 6_660_437 inferences
%@ Sorting length-21952 list Qs:
%@   .. encoding Qs:   % CPU time: 20.625s, 109_772_974 inferences
%@    % CPU time: 20.626s, 109_775_250 inferences
%@    error('$interrupt_thrown',repl/0).
%@ Listing Qs......    % CPU time: 1.592s, 6_660_460 inferences
%@ Sorting length-21952 list Qs:
%@   .. encoding Qs:   % CPU time: 20.488s, 109_986_469 inferences
%@    % CPU time: 20.556s, 110_054_608 inferences
%@ Stratifying Qf..    % CPU time: 4.339s, 19_509_999 inferences
%@ Finding g's ..
%@ ↑[4/4,3/3,3/3] ⊇ [[3/3,0/0,0/0],[3/6,3/3,0/0],[3/6,3/6,3/3],[3/6,3/6,4/6],[3/6,4/6,0/0],[4/6,0/0,0/0]].
%@ ↑[5/6,2/4,3/5] ⊇ [[1/6,3/3,0/0],[1/6,3/6,3/3],[1/6,3/6,4/6],[1/6,4/6,0/0]].
%@ ↑[5/5,2/4,3/5] ⊇ [[0/3,1/6,3/3],[1/6,1/6,3/3],[1/6,1/6,4/6]].
%@ ↑[5/6,2/3,3/5] ⊇ [[0/3,0/3,1/6],[1/6,0/3,1/6],[1/6,1/6,1/6]].
%@    % CPU time: 28.044s, 124_266_679 inferences
%@    Ls = [[4/4,3/3,3/3],[5/6,2/4,3/5],[5/5,2/4,3/5],[5/6,2/3,3/5]].

% Let's try 'hand-crafting' a 2-dose trial with reasonable properties.
% This needs to begin with liveness at [0/0,0/0]!  So we might do well
% to let an X=0 recommendation happen for a positive finding of Q ≼ H0.
%?- Q = [T1/N1,T2/N2], maplist(q_r, Q, _), N1 #=< 6, N2 #=< 6, [0/0,0/0] '≼' Q, label([T1,N1,T2,N2]).
%@    Q = [0/0,0/0], T1 = 0, N1 = 0, T2 = 0, N2 = 0
%@ ;  Q = [0/0,0/1], T1 = 0, N1 = 0, T2 = 0, N2 = 1
%@ ;  Q = [0/0,0/2], T1 = 0, N1 = 0, T2 = 0, N2 = 2
%@ ;  Q = [0/0,0/3], T1 = 0, N1 = 0, T2 = 0, N2 = 3
%@ ;  Q = [0/0,0/4], T1 = 0, N1 = 0, T2 = 0, N2 = 4
%@ ;  Q = [0/0,0/5], T1 = 0, N1 = 0, T2 = 0, N2 = 5
%@ ;  Q = [0/0,0/6], T1 = 0, N1 = 0, T2 = 0, N2 = 6
%@ ;  Q = [0/1,0/0], T1 = 0, N1 = 1, T2 = 0, N2 = 0
%@ ;  Q = [0/1,0/1], T1 = 0, N1 = 1, T2 = 0, N2 = 1
%@ ;  Q = [0/1,0/2], T1 = 0, N1 = 1, T2 = 0, N2 = 2
%@ ;  Q = [0/1,0/3], T1 = 0, N1 = 1, T2 = 0, N2 = 3
%@ ;  Q = [0/1,0/4], T1 = 0, N1 = 1, T2 = 0, N2 = 4
%@ ;  Q = [0/1,0/5], T1 = 0, N1 = 1, T2 = 0, N2 = 5
%@ ;  Q = [0/1,0/6], T1 = 0, N1 = 1, T2 = 0, N2 = 6
%@ ;  Q = [0/2,0/0], T1 = 0, N1 = 2, T2 = 0, N2 = 0
%@ ;  Q = [0/2,0/1], T1 = 0, N1 = 2, T2 = 0, N2 = 1
%@ ;  Q = [0/2,0/2], T1 = 0, N1 = 2, T2 = 0, N2 = 2
%@ ;  Q = [0/2,0/3], T1 = 0, N1 = 2, T2 = 0, N2 = 3
%@ ;  Q = [0/2,0/4], T1 = 0, N1 = 2, T2 = 0, N2 = 4
%@ ;  Q = [0/2,0/5], T1 = 0, N1 = 2, T2 = 0, N2 = 5
%@ ;  Q = [0/2,0/6], T1 = 0, N1 = 2, T2 = 0, N2 = 6
%@ ;  Q = [0/3,0/0], T1 = 0, N1 = 3, T2 = 0, N2 = 0
%@ ;  Q = [0/3,0/1], T1 = 0, N1 = 3, T2 = 0, N2 = 1
%@ ;  Q = [0/3,0/2], T1 = 0, N1 = 3, T2 = 0, N2 = 2
%@ ;  Q = [0/3,0/3], T1 = 0, N1 = 3, T2 = 0, N2 = 3
%@ ;  Q = [0/3,0/4], T1 = 0, N1 = 3, T2 = 0, N2 = 4
%@ ;  Q = [0/3,0/5], T1 = 0, N1 = 3, T2 = 0, N2 = 5
%@ ;  Q = [0/3,0/6], T1 = 0, N1 = 3, T2 = 0, N2 = 6
%@ ;  Q = [0/4,0/0], T1 = 0, N1 = 4, T2 = 0, N2 = 0
%@ ;  ... .
%@    Q = [T1/N1,T2/N2], clpz:(T1 in 0..sup), clpz:(#T1+ #_A#= #N1), clpz:(_A in 0..sup), clpz:(N1 in 0..sup), clpz:(T2 in 0..sup), clpz:(#T2+ #_B#= #N2), clpz:(_B in 0..sup), clpz:(N2 in 0..sup).
%@    error(instantiation_error,instantiation_error(unknown(from_to(n(0),sup)),1)).
%@    error(instantiation_error,instantiation_error(unknown(from_to(n(0),sup)),1)).
%@    error(type_error(integer,0/_151),must_be/2).
%@    error(existence_error(procedure,labeling/1),labeling/1).
%@    Q = [0/_A,0/_B], clpz:(_A in 0..sup), clpz:(#_A+ #_B#= #_C), clpz:(_B in 0..sup), clpz:(#_D+ #_B#=0), clpz:(_D in inf..0), clpz:(_C in 0..sup).

% This is promising, at least.  Can I set forth
% some reasonable conditions on H0?
% Or maybe what this means, is deciding how a
% small set of comparator tallies is supposed
% to shape a dose-escalation protocol.
% And yet, I already HAVE this, in the form of
% upper and lower adjoints G ⊢ E and L ⊣ E.

% How about something like this?
% Q ≼ H0 => X=0 [stop trial]
% Q ⋠ H0 => can continue, at least with DL-1
% - H0 ⋡ Q ≼ H1 => X=1
% - H1 ⋡ Q ≼ H2 => X=2.
% If I really pursue something like that,
% the value of H2 becomes trivial, and I
% truly need only (H0, H1).  That's a
% pretty small parameter space, which I
% should be able to search tonight!
% _BUT_ more to the point, perhaps I've
% [effectively] *already* searched this,
% and come up empty-handed?

% TONIGHT:
% Upon returning from dinner, I should find an H0
% that correctly stops the trial in every situation
% where this is required, yet also allows the trial
% to begin by allowing X=1 at [0/0,0/0].

%?- d_q(2, H0), [1/3,0/0] '⋠' H0, [2/3,0/0] '≼' H0.
%@    H0 = [0/0,0/1]
%@ ;  H0 = [0/0,1/2]
%@ ;  H0 = [0/0,2/3]
%@ ;  H0 = [0/0,2/4]
%@ ;  ... .
%@    H0 = [0/0,0/1]
%@ ;  H0 = [0/0,1/2]
%@ ;  H0 = [0/0,2/3]
%@ ;  H0 = [0/0,2/4]
%@ ;  H0 = [0/0,2/5]
%@ ;  H0 = [0/0,2/6]
%@ ;  H0 = [0/1,0/0]
%@ ;  H0 = [0/1,1/1]
%@ ;  H0 = [0/1,2/2]
%@ ;  H0 = [0/1,2/3]
%@ ;  H0 = [0/1,2/4]
%@ ;  H0 = [0/1,2/5]
%@ ;  H0 = [0/1,2/6]
%@ ;  H0 = [1/1,0/1]
%@ ;  H0 = [1/1,1/2]
%@ ;  H0 = [1/1,1/3]
%@ ;  H0 = [1/1,1/4]
%@ ;  H0 = [1/1,1/5]
%@ ;  H0 = [1/1,1/6]
%@ ;  H0 = [0/2,2/2]
%@ ;  H0 = [0/2,2/3]
%@ ;  H0 = [0/2,2/4]
%@ ;  H0 = [0/2,2/5]
%@ ;  H0 = [0/2,2/6]
%@ ;  H0 = [1/2,0/0]
%@ ;  H0 = [1/2,1/1]
%@ ;  H0 = [1/2,1/2]
%@ ;  H0 = [1/2,1/3]
%@ ;  H0 = [1/2,1/4]
%@ ;  H0 = [1/2,1/5]
%@ ;  H0 = [1/2,1/6]
%@ ;  H0 = [2/2,0/1]
%@ ;  H0 = [2/2,0/2]
%@ ;  H0 = [2/2,0/3]
%@ ;  H0 = [2/2,0/4]
%@ ;  H0 = [2/2,0/5]
%@ ;  H0 = [2/2,0/6]
%@ ;  H0 = [0/3,2/2]
%@ ;  H0 = [0/3,2/3]
%@ ;  H0 = [0/3,2/4]
%@ ;  H0 = [0/3,2/5]
%@ ;  H0 = [0/3,2/6]
%@ ;  H0 = [1/3,1/1]
%@ ;  H0 = [1/3,1/2]
%@ ;  H0 = [1/3,1/3]
%@ ;  H0 = [1/3,1/4]
%@ ;  H0 = [1/3,1/5]
%@ ;  H0 = [1/3,1/6]
%@ ;  H0 = [2/3,0/0]
%@ ;  H0 = [2/3,0/1]
%@ ;  H0 = [2/3,0/2]
%@ ;  H0 = [2/3,0/3]
%@ ;  H0 = [2/3,0/4]
%@ ;  H0 = [2/3,0/5]
%@ ;  H0 = [2/3,0/6]
%@ ;  H0 = [0/4,2/2]
%@ ;  H0 = [0/4,2/3]
%@ ;  H0 = [0/4,2/4]
%@ ;  H0 = [0/4,2/5]
%@ ;  H0 = [0/4,2/6]
%@ ;  H0 = [1/4,1/1]
%@ ;  H0 = [1/4,1/2]
%@ ;  H0 = [1/4,1/3]
%@ ;  H0 = [1/4,1/4]
%@ ;  H0 = [1/4,1/5]
%@ ;  H0 = [1/4,1/6]
%@ ;  H0 = [2/4,0/0]
%@ ;  H0 = [2/4,0/1]
%@ ;  H0 = [2/4,0/2]
%@ ;  H0 = [2/4,0/3]
%@ ;  H0 = [2/4,0/4]
%@ ;  H0 = [2/4,0/5]
%@ ;  H0 = [2/4,0/6]
%@ ;  H0 = [0/5,2/2]
%@ ;  H0 = [0/5,2/3]
%@ ;  H0 = [0/5,2/4]
%@ ;  H0 = [0/5,2/5]
%@ ;  H0 = [0/5,2/6]
%@ ;  H0 = [1/5,1/1]
%@ ;  H0 = [1/5,1/2]
%@ ;  H0 = [1/5,1/3]
%@ ;  H0 = [1/5,1/4]
%@ ;  H0 = [1/5,1/5]
%@ ;  H0 = [1/5,1/6]
%@ ;  H0 = [2/5,0/0]
%@ ;  H0 = [2/5,0/1]
%@ ;  H0 = [2/5,0/2]
%@ ;  H0 = [2/5,0/3]
%@ ;  H0 = [2/5,0/4]
%@ ;  H0 = [2/5,0/5]
%@ ;  H0 = [2/5,0/6]
%@ ;  H0 = [0/6,2/2]
%@ ;  ... .
%@    H0 = [0/0,1/2]
%@ ;  H0 = [0/0,1/3]
%@ ;  H0 = [0/0,2/3]
%@ ;  H0 = [0/0,1/4]
%@ ;  H0 = [0/0,2/4]
%@ ;  H0 = [0/0,1/5]
%@ ;  H0 = [0/0,2/5]
%@ ;  H0 = [0/0,1/6]
%@ ;  H0 = [0/0,2/6]
%@ ;  H0 = [0/1,1/1]
%@ ;  H0 = [0/1,1/2]
%@ ;  H0 = [0/1,2/2]
%@ ;  H0 = [0/1,1/3]
%@ ;  H0 = [0/1,2/3]
%@ ;  H0 = [0/1,1/4]
%@ ;  H0 = [0/1,2/4]
%@ ;  H0 = [0/1,1/5]
%@ ;  H0 = [0/1,2/5]
%@ ;  H0 = [0/1,1/6]
%@ ;  H0 = [0/1,2/6]
%@ ;  H0 = [1/1,0/1]
%@ ;  H0 = [1/1,0/2]
%@ ;  H0 = [1/1,1/2]
%@ ;  H0 = [1/1,0/3]
%@ ;  H0 = [1/1,1/3]
%@ ;  H0 = [1/1,0/4]
%@ ;  H0 = [1/1,1/4]
%@ ;  H0 = [1/1,0/5]
%@ ;  H0 = [1/1,1/5]
%@ ;  H0 = [1/1,0/6]
%@ ;  H0 = [1/1,1/6]
%@ ;  H0 = [0/2,1/1]
%@ ;  H0 = [0/2,1/2]
%@ ;  H0 = [0/2,2/2]
%@ ;  H0 = [0/2,1/3]
%@ ;  H0 = [0/2,2/3]
%@ ;  H0 = [0/2,1/4]
%@ ;  H0 = [0/2,2/4]
%@ ;  H0 = [0/2,1/5]
%@ ;  H0 = [0/2,2/5]
%@ ;  H0 = [0/2,1/6]
%@ ;  H0 = [0/2,2/6]
%@ ;  H0 = [1/2,0/0]
%@ ;  H0 = [1/2,0/1]
%@ ;  H0 = [1/2,1/1]
%@ ;  H0 = [1/2,0/2]
%@ ;  H0 = [1/2,1/2]
%@ ;  H0 = [1/2,0/3]
%@ ;  H0 = [1/2,1/3]
%@ ;  H0 = [1/2,0/4]
%@ ;  H0 = [1/2,1/4]
%@ ;  H0 = [1/2,0/5]
%@ ;  H0 = [1/2,1/5]
%@ ;  H0 = [1/2,0/6]
%@ ;  H0 = [1/2,1/6]
%@ ;  H0 = [2/2,0/1]
%@ ;  H0 = [2/2,0/2]
%@ ;  H0 = [2/2,0/3]
%@ ;  H0 = [2/2,0/4]
%@ ;  H0 = [2/2,0/5]
%@ ;  H0 = [2/2,0/6]
%@ ;  ... .
%@    H0 = [0/0,1/1]
%@ ;  H0 = [0/0,1/2]
%@ ;  H0 = [0/0,2/2]
%@ ;  H0 = [0/0,1/3]
%@ ;  H0 = [0/0,2/3]
%@ ;  H0 = [0/0,3/3]
%@ ;  H0 = [0/0,1/4]
%@ ;  H0 = [0/0,2/4]
%@ ;  H0 = [0/0,3/4]
%@ ;  H0 = [0/0,4/4]
%@ ;  H0 = [0/0,1/5]
%@ ;  H0 = [0/0,2/5]
%@ ;  H0 = [0/0,3/5]
%@ ;  H0 = [0/0,4/5]
%@ ;  H0 = [0/0,5/5]
%@ ;  H0 = [0/0,1/6]
%@ ;  H0 = [0/0,2/6]
%@ ;  H0 = [0/0,3/6]
%@ ;  H0 = [0/0,4/6]
%@ ;  H0 = [0/0,5/6]
%@ ;  H0 = [0/0,6/6]
%@ ;  H0 = [0/1,1/1]
%@ ;  H0 = [0/1,1/2]
%@ ;  H0 = [0/1,2/2]
%@ ;  H0 = [0/1,1/3]
%@ ;  H0 = [0/1,2/3]
%@ ;  H0 = [0/1,3/3]
%@ ;  H0 = [0/1,1/4]
%@ ;  H0 = [0/1,2/4]
%@ ;  H0 = [0/1,3/4]
%@ ;  H0 = [0/1,4/4]
%@ ;  H0 = [0/1,1/5]
%@ ;  H0 = [0/1,2/5]
%@ ;  H0 = [0/1,3/5]
%@ ;  H0 = [0/1,4/5]
%@ ;  H0 = [0/1,5/5]
%@ ;  H0 = [0/1,1/6]
%@ ;  H0 = [0/1,2/6]
%@ ;  H0 = [0/1,3/6]
%@ ;  H0 = [0/1,4/6]
%@ ;  H0 = [0/1,5/6]
%@ ;  H0 = [0/1,6/6]
%@ ;  H0 = [1/1,0/0]
%@ ;  H0 = [1/1,0/1]
%@ ;  H0 = [1/1,1/1]
%@ ;  H0 = [1/1,0/2]
%@ ;  H0 = [1/1,1/2]
%@ ;  ... .
%@    H0 = [_A/_E,_B/_G], clpz:(_A in 1..sup), clpz:(#_B+ #_A#= #_C), clpz:(#_A+ #_D#= #_E), clpz:(_B in 0..sup), clpz:(#_B+ #_F#= #_G), clpz:(_F in 0..sup), clpz:(#_H+ #_F#=0), clpz:(#_D+ #_F#= #_I), clpz:(_H in inf..0), clpz:(_D in 0..sup), clpz:(_E in 1..sup), clpz:(_I in 0..sup), clpz:(_G in 0..sup), clpz:(_C in 1..sup)
%@ ;  H0 = [0/_A,_E/_F], clpz:(_A in 0..sup), clpz:(#_A+ #_B#= #_C), clpz:(_B in 0..sup), clpz:(#_D+ #_B#=0), clpz:(#_E+ #_B#= #_F), clpz:(_D in inf..0), clpz:(_E in 1..sup), clpz:(_F in 1..sup), clpz:(_C in 0..sup)
%@ ;  ... .
%@    H0 = [_A/_E,_B/_G], clpz:(_A in 1..sup), clpz:(#_B+ #_A#= #_C), clpz:(#_A+ #_D#= #_E), clpz:(_B in 0..sup), clpz:(#_B+ #_F#= #_G), clpz:(_F in 0..sup), clpz:(#_H+ #_F#=0), clpz:(#_D+ #_F#= #_I), clpz:(_H in inf..0), clpz:(_D in 0..sup), clpz:(_E in 1..sup), clpz:(_I in 0..sup), clpz:(_G in 0..sup), clpz:(_C in 1..sup)
%@ ;  H0 = [0/_A,_E/_F], clpz:(_A in 0..sup), clpz:(#_A+ #_B#= #_C), clpz:(_B in 0..sup), clpz:(#_D+ #_B#=0), clpz:(#_E+ #_B#= #_F), clpz:(_D in inf..0), clpz:(_E in 1..sup), clpz:(_F in 1..sup), clpz:(_C in 0..sup)
%@ ;  ... .
%@    H0 = [_A/_E,_B/_G], clpz:(_A in 1..sup), clpz:(#_B+ #_A#= #_C), clpz:(#_A+ #_D#= #_E), clpz:(_B in 0..sup), clpz:(#_B+ #_F#= #_G), clpz:(_F in 0..sup), clpz:(#_H+ #_F#=0), clpz:(#_D+ #_F#= #_I), clpz:(_H in inf..0), clpz:(_D in 0..sup), clpz:(_E in 1..sup), clpz:(_I in 0..sup), clpz:(_G in 0..sup), clpz:(_C in 1..sup)
%@ ;  ... .
%@    H0 = [_A/_E,_B/_G], clpz:(_A in 1..sup), clpz:(#_B+ #_A#= #_C), clpz:(#_A+ #_D#= #_E), clpz:(_B in 0..sup), clpz:(#_B+ #_F#= #_G), clpz:(_F in 0..sup), clpz:(#_H+ #_F#=0), clpz:(#_D+ #_F#= #_I), clpz:(_H in inf..0), clpz:(_D in 0..sup), clpz:(_E in 1..sup), clpz:(_I in 0..sup), clpz:(_G in 0..sup), clpz:(_C in 1..sup)
%@ ;  H0 = [0/_A,_E/_F], clpz:(_A in 0..sup), clpz:(#_A+ #_B#= #_C), clpz:(_B in 0..sup), clpz:(#_D+ #_B#=0), clpz:(#_E+ #_B#= #_F), clpz:(_D in inf..0), clpz:(_E in 1..sup), clpz:(_F in 1..sup), clpz:(_C in 0..sup)
%@ ;  ... .

%?- d_q(2, Q).
%@    Q = [0/0,0/0]
%@ ;  Q = [0/0,_A/1], clpz:(_A in 0..1), clpz:(#_A+ #_B#=1), clpz:(_B in 0..1)
%@ ;  Q = [0/0,_A/2], clpz:(_A in 0..2), clpz:(#_A+ #_B#=2), clpz:(_B in 0..2)
%@ ;  Q = [0/0,_A/3], clpz:(_A in 0..3), clpz:(#_A+ #_B#=3), clpz:(_B in 0..3)
%@ ;  Q = [0/0,_A/4], clpz:(_A in 0..4), clpz:(#_A+ #_B#=4), clpz:(_B in 0..4)
%@ ;  Q = [0/0,_A/5], clpz:(_A in 0..5), clpz:(#_A+ #_B#=5), clpz:(_B in 0..5)
%@ ;  Q = [0/0,_A/6], clpz:(_A in 0..6), clpz:(#_A+ #_B#=6), clpz:(_B in 0..6)
%@ ;  Q = [_A/1,0/0], clpz:(_A in 0..1), clpz:(#_A+ #_B#=1), clpz:(_B in 0..1)
%@ ;  Q = [_A/1,_C/1], clpz:(_A in 0..1), clpz:(#_A+ #_B#=1), clpz:(_B in 0..1), clpz:(_C in 0..1), clpz:(#_C+ #_D#=1), clpz:(_D in 0..1)
%@ ;  Q = [_A/1,_C/2], clpz:(_A in 0..1), clpz:(#_A+ #_B#=1), clpz:(_B in 0..1), clpz:(_C in 0..2), clpz:(#_C+ #_D#=2), clpz:(_D in 0..2)
%@ ;  Q = [_A/1,_C/3], clpz:(_A in 0..1), clpz:(#_A+ #_B#=1), clpz:(_B in 0..1), clpz:(_C in 0..3), clpz:(#_C+ #_D#=3), clpz:(_D in 0..3)
%@ ;  Q = [_A/1,_C/4], clpz:(_A in 0..1), clpz:(#_A+ #_B#=1), clpz:(_B in 0..1), clpz:(_C in 0..4), clpz:(#_C+ #_D#=4), clpz:(_D in 0..4)
%@ ;  Q = [_A/1,_C/5], clpz:(_A in 0..1), clpz:(#_A+ #_B#=1), clpz:(_B in 0..1), clpz:(_C in 0..5), clpz:(#_C+ #_D#=5), clpz:(_D in 0..5)
%@ ;  ... .
%@    error(instantiation_error,list_si/1).
%@    error(instantiation_error,list_si/1).
%@    error(instantiation_error,list_si/1).
%@    error(instantiation_error,instantiation_error(unknown(from_to(inf,sup)),1)).
%@    error(existence_error(procedure,labeling/1),labeling/1).
%@    Q = [_A/_C,_D/_F], clpz:(_A in 0..6), clpz:(#_A+ #_B#= #_C), clpz:(_B in 0..6), clpz:(_C in 0..6), clpz:(_D in 0..6), clpz:(#_D+ #_E#= #_F), clpz:(_E in 0..6), clpz:(_F in 0..6).
%@    Q = []
%@ ;  error('$interrupt_thrown',repl/0).
%@    error(existence_error(procedure,d_q/2),d_q/2).
%@    error(existence_error(procedure,d_q/2),d_q/2).

h2(Q, X) :-
    [H0,H1,H2] = [[2/6,0/4], [0/6,2/6], [0/5,0/6]],
    if_(Q '≼' H0,
        X = 0,
        if_(( Q '⋡' H0
            ; Q '≼' H1
            ), X = 1,
            if_(( Q '⋡' H1
                ; Q '≼' H2
                ), X = 2,
                false))).

/*
TODO:

1. Simulate and visualize rolling-enrollment trials.

*/
