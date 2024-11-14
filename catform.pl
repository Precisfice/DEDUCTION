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

% The monograph's capitalization notation being ill-suited to
% Prolog (for obvious reasons!), we indicate our partial-sum
% variables below with a prefix Σ.
qs_Ts_Ūs(Qs, ΣTs, ΣŪs) :-
    maplist(\Q^T^U^(q_r(Q, T:U)), Qs, Ts, Us),
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

% I've now worked out in detail a unique transformation of pair
% Q1,Q2 ∈ Qᴰ into 2✕D parameters, *all* nonnegative iff Q1 ⊑ Q2.
transform(Q1s, Q2s, Hs, Os) :-
    same_length(Q1s, Q2s),
    % We will set Hs = [ηs]+[ρ] (of length D),
    % since ρ fits so smoothly into the sequence.
    q1s_q2s_Δts_Δns(Q1s, Q2s, Δts, Δns),
    maplist(\X^NegX^(#NegX #= -1 * #X), Δts, Δ_ts),
    intlist_partsums(Δ_ts, Hs), reverse(Hs, [Rho|_]),
    reverse(Δns, RΔns),
    intlist_partsums(RΔns, Ňs),
    maplist(\N^O^(#O #= #N + 2 * #Rho), Ňs, ROs),
    reverse(ROs, Os). % Os = [σs]+[γ] (length-D).

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

meet(Q1s, Q2s, Qs) :-
    same_length(Q1s, Q2s), same_length(Q2s, Qs),
    qs_Ts_Ūs(Q1s, T1s, _), qs_Ts_Ūs(Q2s, T2s, _),
    maxs(T1s, T2s, Ts), % q = q₁ ∧ q₂ ⟹ Ts ≥ T1s ∨ T2s
    % Having set Ts to the bare-minimum T1s ∨ T2s compatible with
    % q = q₁ ∧ q₂, we now seek the highest compatible Ūs profile:
    qs_Ts_maxŪs(Q1s, Ts, Ū1s),
    qs_Ts_maxŪs(Q2s, Ts, Ū2s),
    mins(Ū1s, Ū2s, Ūs),
    qs_Ts_Ūs(Qs, Ts, Ūs).

%?- meet([3/3,4/4], [4/6,0/0], M).
%@    M = [4/4,3/3].

%?- meet_def([3/3,4/4], [4/6,0/0], M).
%@    M = [4/4,3/3].

%?- meet([0/6,4/6], [1/6,2/3], Qs).
%@    Qs = [1/6,3/4].

%?- meet_def([0/6,4/6], [1/6,2/3], Qs).
%@    Qs = [1/6,3/4].

%?- [1/6,3/4] '≼' [0/6,4/6], [1/6,3/4] '≼' [0/6,2/3].
%@    true.

% TODO: Compare the computation by meet/3 against a brute-force calculation
%       that directly implements the _definition_ of meet.  This comparison
%       ought to demonstrate that meets are indeed *unique*.
meet_def(Q1s, Q2s, Qs) :-
    % 1. Generate a list of 'all possible' Qss to test.
    same_length(Q1s, Q2s),
    length(Q1s, D),
    findall(Qs, qs_d_nmax(Qs, D, 6), Qss),
    % 2. Filter out elements that are below both Q1s and Q2s.
    tfilter('≽'(Q1s), Qss, Qss1),
    tfilter('≽'(Q2s), Qss1, Qss12),
    % 3. Find the maximal elements of the resulting list.
    qs_maxs(Qss12, Meets),
    member(Qs, Meets).

%?- meet_def([0/6,4/6], [1/6,2/3], Qs).
%@ Generated Qss of length 784.
%@    Qs = [1/6,3/4].

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

% In order to reconstitute the embedding (Qᴰ,≼) ↪ (ℕ²ᴰ,≤)
% for our enlarged ≼, we need to investigate the ranges
% of the 'digits' in the transformation.
transform(Qs, Hs, Os) :-
    same_length(Qs, Zeros),
    maplist(=(0/0), Zeros),
    transform(Zeros, Qs, Hs, Os).

%?- transform([0/6,0/6,0/6], Hs, Os).
%@    Hs = [0,0,0], Os = [18,12,6].
%?- transform([6/6,6/6,6/6], Hs, Os).
%@    Hs = [-6,-12,-18], Os = [-18,-24,-30].

% Ah, this is a little surprising!  It shows I will need to
% take care to use the correct 'base' for each 'digit' of
% the arithmetized tally.

% Furthermore, I'll need to search systematically over the
% whole accessible 'sphere' of tallies to be sure I find
% the entire range of each transformed coordinate.
% Find min & max η₁₂ (the head element of Hs).
d_nmax_minH12_maxH12(D, Nmax, MinH12, MaxH12) :-
    findall(H12, (qs_d_nmax(Qs, D, Nmax),
                  transform(Qs, [H12|_], _)
                 ), H12s),
    length(H12s, V),
    format("found ~d η₁₂ values..", [V]),
    foldl(clpz:min_, H12s, 1_000_000, MinH12),
    foldl(clpz:max_, H12s, -1_000_000, MaxH12).

%?- foldl(clpz:min_, [3,1,4,2,5,9,2], 100, Min).
%@    Min = 1.
%?- foldl(clpz:max_, [3,1,4,2,5,9,2], -100, Max).
%@    Max = 9.

%?- d_nmax_minH12_maxH12(2, 3, MinH12, MaxH12).
%@ found 100 η₁₂ values..   MinH12 = -3, MaxH12 = 0.
%?- d_nmax_minH12_maxH12(2, 4, MinH12, MaxH12).
%@ found 225 η₁₂ values..   MinH12 = -4, MaxH12 = 0.
%?- d_nmax_minH12_maxH12(2, 5, MinH12, MaxH12).
%@ found 441 η₁₂ values..   MinH12 = -5, MaxH12 = 0.
%?- d_nmax_minH12_maxH12(2, 6, MinH12, MaxH12).
%@ found 784 η₁₂ values..   MinH12 = -6, MaxH12 = 0.
%?- d_nmax_minH12_maxH12(3, 3, MinH12, MaxH12).
%@ found 1000 η₁₂ values..   MinH12 = -3, MaxH12 = 0.
%?- d_nmax_minH12_maxH12(3, 4, MinH12, MaxH12).
%@ found 3375 η₁₂ values..   MinH12 = -4, MaxH12 = 0.
%?- d_nmax_minH12_maxH12(3, 5, MinH12, MaxH12).
%@ found 9261 η₁₂ values..   MinH12 = -5, MaxH12 = 0.
%?- d_nmax_minH12_maxH12(3, 6, MinH12, MaxH12).
%@ found 21952 η₁₂ values..   MinH12 = -6, MaxH12 = 0.

% This suggests η₁₂ in -Nmax..0.

d_nmax_minH23_maxH23(D, Nmax, MinH23, MaxH23) :-
    D #>= 3,
    findall(H23, (qs_d_nmax(Qs, D, Nmax),
                  transform(Qs, [_,H23|_], _)
                 ), H23s),
    length(H23s, V),
    format("found ~d η₂₃ values..", [V]),
    foldl(clpz:min_, H23s, 1_000_000, MinH23),
    foldl(clpz:max_, H23s, -1_000_000, MaxH23).

%?- d_nmax_minH23_maxH23(3, 6, MinH23, MaxH23).
%@ found 21952 η₂₃ values..   MinH23 = -12, MaxH23 = 0.
%?- d_nmax_minH23_maxH23(3, 5, MinH23, MaxH23).
%@ found 9261 η₂₃ values..   MinH23 = -10, MaxH23 = 0.

% This suggests η₂₃ in -2*Nmax..0.

d_nmax_minRho_maxRho(D, Nmax, MinRho, MaxRho) :-
    findall(Rho, (qs_d_nmax(Qs, D, Nmax),
                  transform(Qs, Hs, _),
                  reverse(Hs, [Rho|_])
                 ), Rhos),
    length(Rhos, V),
    format("found ~d ρ's..", [V]),
    foldl(clpz:min_, Rhos, 1_000_000, MinRho),
    foldl(clpz:max_, Rhos, -1_000_000, MaxRho).

%?- d_nmax_minRho_maxRho(3, 6, MinRho, MaxRho).
%@ found 21952 ρ's..   MinRho = -18, MaxRho = 0.

% Thus, it seems k'th element of Hs ranges from -k*Nmax to 0.
% This is at least rather simple!  But the Os look a bit more
% complicated in this respect.

d_nmax_minO12_maxO12(D, Nmax, MinO12, MaxO12) :-
    findall(O12, (qs_d_nmax(Qs, D, Nmax),
                  transform(Qs, _, [O12|_])
                 ), O12s),
    length(O12s, V),
    format("found ~d σ₁₂ values..", [V]),
    foldl(clpz:min_, O12s, 1_000_000, MinO12),
    foldl(clpz:max_, O12s, -1_000_000, MaxO12).

%?- d_nmax_minO12_maxO12(3, 6, MinO12, MaxO12).
%@ found 21952 σ₁₂ values..   MinO12 = -18, MaxO12 = 18.

d_nmax_minO23_maxO23(D, Nmax, MinO23, MaxO23) :-
    D #>= 3,
    findall(O23, (qs_d_nmax(Qs, D, Nmax),
                  transform(Qs, _, [_,O23|_])
                 ), O23s),
    length(O23s, V),
    format("found ~d σ₂₃ values..", [V]),
    foldl(clpz:min_, O23s, 1_000_000, MinO23),
    foldl(clpz:max_, O23s, -1_000_000, MaxO23).

%?- d_nmax_minO23_maxO23(3, 6, MinO23, MaxO23).
%@ found 21952 σ₂₃ values..   MinO23 = -24, MaxO23 = 12.

d_nmax_minGamma_maxGamma(D, Nmax, MinGamma, MaxGamma) :-
    findall(Gamma, (qs_d_nmax(Qs, D, Nmax),
                    transform(Qs, _, Os),
                    reverse(Os, [Gamma|_])
                 ), Gammas),
    length(Gammas, V),
    format("found ~d γ's..", [V]),
    foldl(clpz:min_, Gammas, 1_000_000, MinGamma),
    foldl(clpz:max_, Gammas, -1_000_000, MaxGamma).

%?- d_nmax_minGamma_maxGamma(3, 6, MinGamma, MaxGamma).
%@ found 21952 γ's..   MinGamma = -30, MaxGamma = 6.

% So interestingly the MAXima for Os are in descending
% arithmetic sequence [18,12,6],
% while the MINima are all 36 below these: [-18,-24,-30].
% Accordingly, each of the Os will have to be encoded in
% base-(D*Nmax + 1), after upward shifting by Nmax*(d+2)
% for d in 1..D.

% Given how all the transformed coordinates look quite 'negative',
% I may do better to form my integer with their opposites -- and
% of course keep track of this decision, since it should reverse
% the order relation.

% To encode the Hs, we can reuse existing infrastructure, as-is
hs_enc(Hs, K) :- ws_int(Hs, K).

% To encode Os, we need only shift the values downward
% so they are non-positive, then encode a base-(6*D+1)
% integer from them.
os_enc(Os, K) :-
    os_base(Os, B),
    foldl(base_(B), Os, 0, K).

os_base(Os, B) :- length(Os, D), #B #= 6 * #D + 1.

base_(B, A, N0, N) :- #N #= #B * #N0 + #A.

%?- foldl(base_(10), [1,2,3,4], 0, N).
%@    N = 1234.

%?- Os = [18,12,6], os_enc(Os, K).
%@    Os = [18,12,6], K = 6732.

qs_int(Qs, K) :-
    transform(Qs, Hs, Os),
    hs_enc(Hs, HK),
    os_enc(Os, OK),
    % I know what range of HK is, thanks to existing d_maxenc/2,
    % and so can use it as the less-significant part of K.
    length(Os, D), d_maxenc(D, Hmax),
    #K #= #OK * (#Hmax + 1) + #HK.

%?- Qs = [0/0,0/0], qs_int(Qs, K).
%@    Qs = [0/0,0/0], K = -14580.

% Let's now check this encoding, to be sure it embeds every
% arrow of ≼.
d_nmax_wrongway(D, Nmax, Q1s, Q2s) :-
    qs_d_nmax(Q1s, D, Nmax), qs_int(Q1s, K1),
    qs_d_nmax(Q2s, D, Nmax), qs_int(Q2s, K2),
    #K1 #> #K2, % fail faster
    Q1s '≼' Q2s.

%?- time(d_nmax_wrongway(2, 3, Q1, Q2)).
%@    % CPU time: 10.501s, 30_671_113 inferences
%@    false.
%?- time(d_nmax_wrongway(2, 4, Q1, Q2)).
%@    % CPU time: 53.085s, 156_313_540 inferences
%@    false.
%?- time(d_nmax_wrongway(2, 5, Q1, Q2)).
%@    % CPU time: 204.149s, 597_970_856 inferences
%@    false.
%?- time(d_nmax_wrongway(2, 6, Q1, Q2)).
%@    % CPU time: 640.739s, 1_896_641_140 inferences
%@    false.
%?- time(d_nmax_wrongway(3, 1, Q1, Q2)).
%@    % CPU time: 0.993s, 2_631_428 inferences
%@    false.
%?- time(d_nmax_wrongway(3, 2, Q1, Q2)).
%@    % CPU time: 61.371s, 164_168_062 inferences
%@    false.
%?- time(d_nmax_wrongway(3, 3, Q1, Q2)).
%@    % CPU time: 1305.276s, 3_442_932_293 inferences
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

%?- ws_int([3,7,13], K).
%@    K = 1235.

%?- #W1 #= 1235 mod 7.
%@    W1 = 3.

%?- #W2 #= (1235 div 7) mod 13.
%@    W2 = 7.

%?- #W3 #= (1235 div 7) div 13.
%@    W3 = 13.

%?- placevalues([P3,P2,P1]).
%@    P3 = 91, P2 = 7, P1 = 1.

%?- #K #= 91*13 + 7*7 + 3.
%@    K = 1235.

%?- #W3 #= 1235 div 91.
%@    W3 = 13.

%?- #W2 #= (1235 mod 91) div 7.
%@    W2 = 7.

%?- #W1 #= ((1235 mod 91) mod 7) div 1.
%@    W1 = 3.

% Finally, I need to write int_ws/2 implementing the _decoding_.
% Again, I will suppose Ws is an uninstantiated list that is
% however of known length.

% Ah, after our afternoon walk (70F!) I see that the needed predicate is:
int_bases_digits(K, [B|Bs], [W|Ws]) :-
    same_length(Bs, Ws),
    #W #= #K mod #B,
    #K1 #= #K div #B,
    int_bases_digits(K1, Bs, Ws).

int_bases_digits(_, [], []). % ... or something like that!

%?- int_bases_digits(Y, [], []).
%@    true.

%?- int_bases_digits(1023, [2,2,2,2,2,2,2,2,2,2], Ds).
%@    Ds = [1,1,1,1,1,1,1,1,1,1].

%?- int_bases_digits(1023, [16,16,2,2], Ds).
%@    Ds = [15,15,1,1].

%?- int_bases_digits(1235, [7,13,19], Ws).
%@    Ws = [3,7,13].

% The length-D list of bases starts with 6 + 1 = 7,
% and adds 6 at each level.  What is the simplest way
% to create such an arithmetic sequence in Prolog?
d_bases(D, [B|Bs]) :-
    length([B|Bs], D),
    same_length(Xs, Bs),
    maplist(=(6), Xs),
    intlist_partsums([7|Xs], [B|Bs]).

d_int_ws(D, K, Ws) :-
    d_bases(D, Bs),
    int_bases_digits(K, Bs, Ws).
    
%?- d_bases(3, Bs).
%@    Bs = [7,13,19].

%?- d_int_ws(3, 1235, Ws).
%@    Ws = [3,7,13].

% What about complements in general?

%?- ws_int([1,2,3,4,5], K).
%@    K = 223329.

%?- ws_int([1,2,3,4,5], K).
%@    K = 223329.

%% d_maxenc(D, Kmax) :-
%%     length(Ps, D),
%%     placevalues([Kmax1|Ps]),
%%     #Kmax #= Kmax1 - 1.

%?- d_maxenc(5, Kmax).
%@    Kmax = 1339974.

% I've already precomputed placevalues/1, but might I still
% gain additional speedup by precomputing d_maxenc/2 also?
%?- D in 0..7, indomain(D), d_maxenc(D, Kmax).
%@    D = 0, Kmax = 0
%@ ;  D = 1, Kmax = 6
%@ ;  D = 2, Kmax = 90
%@ ;  D = 3, Kmax = 1728
%@ ;  D = 4, Kmax = 43224
%@ ;  D = 5, Kmax = 1339974
%@ ;  D = 6, Kmax = 49579074
%@ ;  D = 7, Kmax = 2131900224.

% TODO: Consider whether this name must be changed to
%       (say) d_encspan/2, if I allow encodings with
%       digits that aren't all one side of zero.
d_maxenc(1, 6).
d_maxenc(2, 90).
d_maxenc(3, 1728).
d_maxenc(4, 43224).
d_maxenc(5, 1339974).
d_maxenc(6, 49579074).
d_maxenc(7, 2131900224).

%?- d_maxenc(5, Kmax).
%@    Kmax = 1339974.

% NB: We could encode D=7 tallies in 62-bit integers!
%?- #M #= 2^31, d_maxenc(7, Kmax), M > Kmax.
%@    M = 2147483648, Kmax = 2131900224.

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
/* Now replaced; see above.
qs_int(Qs, K) :-
    qs_Ts_Ūs(Qs, Ts, Ūs),
    ws_int(Ts, KT),
    ws_int(Ūs, KŪ),
    length(Qs, D), d_maxenc(D, Kmax),
    #K #= (#Kmax + 1) * #KT + (#Kmax - #KŪ).
*/
%?- Qs = [[1/6,1/6],[0/6,2/6]], qs_sorted(Qs, SQs).
%@ Sorting length-2 list Qs:
%@   .. encoding Qs:   % CPU time: 0.002s, 6_220 inferences
%@    % CPU time: 0.005s, 8_395 inferences
%@    Qs = [[1/6,1/6],[0/6,2/6]], SQs = [[0/6,2/6],[1/6,1/6]].

%?- Qs=[1/6,0/3,2/6], time(qs_int(Qs, K)). % now TABLING d_placevalues/2
%@ qs_Ts_Us/3 ..   % CPU time: 0.002s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.000s, 1_473 inferences
%@ ws_cint/2 ...   % CPU time: 0.002s, 4_912 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 2_752 inferences
%@    % CPU time: 0.015s, 19_172 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.000s, 62 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.011s, 5_356 inferences
%@    false.
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.004s, 16_480 inferences
%@ ws_cint/2 ...   % CPU time: 0.001s, 4_912 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 2_752 inferences
%@    % CPU time: 0.015s, 34_176 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.000s, 62 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.009s, 5_356 inferences
%@    false.
%@ qs_Ts_Us/3 ..   % CPU time: 0.002s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.000s, 1_492 inferences
%@ ws_cint/2 ...   % CPU time: 0.001s, 4_950 inferences
%@ d_maxenc/2 ..   % CPU time: 0.000s, 2_771 inferences
%@    % CPU time: 0.014s, 19_248 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.000s, 62 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.009s, 5_356 inferences
%@    false.
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.008s, 17_777 inferences
%@ ws_cint/2 ...   % CPU time: 0.002s, 4_950 inferences
%@ d_maxenc/2 ..   % CPU time: 0.001s, 2_771 inferences
%@    % CPU time: 0.025s, 35_530 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424
%@ ;  % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.000s, 62 inferences
%@    % CPU time: 0.000s, 31 inferences
%@    % CPU time: 0.013s, 5_356 inferences
%@    false.

%?- Qs=[1/6,0/3,2/6], time(qs_int(Qs, K)). % AFTER placevalues/1 ~~> d_placevalues/2
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.001s, 6_338 inferences
%@ ws_cint/2 ...   % CPU time: 0.003s, 14_662 inferences
%@ d_maxenc/2 ..   % CPU time: 0.001s, 7_627 inferences
%@    % CPU time: 0.016s, 38_770 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424.

%?- Qs=[1/6,0/3,2/6], time(qs_int(Qs, K)).
%@ qs_Ts_Us/3 ..   % CPU time: 0.001s, 2_356 inferences
%@ ws_int/2 ....   % CPU time: 0.002s, 5_049 inferences
%@ ws_cint/2 ...   % CPU time: 0.005s, 12_084 inferences
%@ d_maxenc/2 ..   % CPU time: 0.002s, 6_338 inferences
%@    % CPU time: 0.024s, 33_614 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424.
%@    % CPU time: 0.003s, 2_333 inferences
%@    % CPU time: 0.001s, 5_049 inferences
%@    % CPU time: 0.003s, 12_084 inferences
%@    % CPU time: 0.001s, 6_338 inferences
%@    Qs = [1/6,0/3,2/6], K = 486424.
%@    error(existence_error(procedure,qs_int/3),qs_int/3).


d_sortedQfs(D, SQs) :-
    findall(Q, d_mendtally_rec(D,Q,_), Qs),
    qs_sorted(Qs, SQs).

qs_sorted(Qs, SQs) :-
    length(Qs, LQs), format("Sorting length-~d list Qs:~n", [LQs]),
    time((
    format("  .. encoding Qs:", []),
    time(maplist(qs_int, Qs, Ks)),
    pairs_keys_values(KQs, Ks, Qs),
    sort(KQs, SKQs), % too fast to be worth timing!
    pairs_values(SKQs, SQs)
    )).

%?- d_sortedQfs(2, Qfs).
%@ Sorting length-29 list Qs:
%@   .. encoding Qs:   % CPU time: 0.025s, 133_012 inferences
%@   .. decoding Qs:   % CPU time: 0.028s, 182_750 inferences
%@    % CPU time: 0.057s, 320_382 inferences
%@    Qfs = [[0/3,0/6],[0/3,1/6],[1/6,0/6],[0/6,2/6],[0/6,2/3],[1/6,1/6],[2/6,0/0],[2/3,0/0],[0/6,3/6],[0/6,3/3],[1/6,2/6],[1/6,2/3],[3/6,0/0],[3/3,0/0],[0/6,4/6],[1/6,3/6],[1/6,3/3],[2/6,2/6],[2/6,... / ...],[... / ...|...]|...].

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
                           qs_sorted(Qs, SQs),
                           format("~n stratifying ..~n", []),
                           foldl(sift, SQs, [[]], Qss),
                           reverse(Qss, RQss), maplist(portray_clause, RQss),
                           format(OS, "strict digraph hasseD~d {~n", [D]),
                           format(OS, "  rankdir=~a;~n", ['BT']),
                           format(OS, "  node [colorscheme=~w, fontname=\"~w\"];~n",
                                  ['set14','Helvetica:bold']),
                           format("Writing strata to DOT file ..", []),
                           list_to_assoc(QXs, QXassoc),
                           maplist(write_stratum(OS,QXassoc), Qss),
                           format("~n writing covering relation ..", []) ->
                           reverse(SQs, RSQs), % speeds cover calculation
                           time((   in_cover(RSQs, Q1, Q2),
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

%?- d_writehassedot(2).
%@ Opening file 'HasseD2.dot'...
%@ Collecting final tallies ..
%@  sorting 29 final tallies ..Sorting length-29 list Qs:
%@   .. encoding Qs:   % CPU time: 0.026s, 133_160 inferences
%@    % CPU time: 0.028s, 135_433 inferences
%@ 
%@  stratifying ..
%@ [[0/6,2/6],[1/6,0/6],[0/3,0/6]].
%@ [[0/6,3/6],[1/6,1/6],[0/3,1/6]].
%@ [[0/6,4/6],[1/6,2/6],[0/6,2/3]].
%@ [[1/6,3/6],[0/6,3/3],[2/6,0/0]].
%@ [[1/6,4/6],[2/6,2/6],[1/6,2/3],[2/3,0/0]].
%@ [[2/6,3/6],[1/6,3/3],[3/6,0/0]].
%@ [[2/6,4/6],[3/6,2/6],[2/6,2/3],[3/3,0/0]].
%@ [[3/6,3/6],[2/6,3/3],[4/6,0/0]].
%@ [[3/6,4/6],[3/6,2/3]].
%@ [[3/6,3/3]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 6.912s, 30_494_743 inferences
%@ .. done.
%@    true.
%@ Opening file 'HasseD2.dot'...
%@ Collecting final tallies ..
%@  sorting 29 final tallies ..Sorting length-29 list Qs:
%@   .. encoding Qs:   % CPU time: 0.017s, 91_073 inferences
%@    % CPU time: 0.019s, 93_326 inferences
%@ 
%@  stratifying ..
%@ [[0/6,2/6],[1/6,0/6],[0/3,0/6]].
%@ [[0/6,3/6],[1/6,1/6],[0/3,1/6]].
%@ [[0/6,4/6],[1/6,2/6],[0/6,2/3]].
%@ [[1/6,3/6],[0/6,3/3],[2/6,0/0],[2/3,0/0]].
%@ [[1/6,4/6],[2/6,2/6],[1/6,2/3]].
%@ [[2/6,3/6],[1/6,3/3],[3/6,0/0],[3/3,0/0]].
%@ [[2/6,4/6],[3/6,2/6],[2/6,2/3]].
%@ [[3/6,3/6],[2/6,3/3],[4/6,0/0]].
%@ [[3/6,4/6],[3/6,2/3]].
%@ [[3/6,3/3]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 6.690s, 30_026_332 inferences
%@ .. done.
%@    true.
%@ Opening file 'HasseD2.dot'...
%@ Collecting final tallies ..
%@  sorting 29 final tallies ..Sorting length-29 list Qs:
%@   .. encoding Qs:   % CPU time: 0.020s, 102_926 inferences
%@   .. decoding Qs:   % CPU time: 0.029s, 182_252 inferences
%@    % CPU time: 0.052s, 289_798 inferences
%@ 
%@  stratifying ..
%@ [[0/6,2/6],[1/6,0/6],[0/3,0/6]].
%@ [[0/6,3/6],[1/6,1/6],[0/3,1/6]].
%@ [[0/6,4/6],[1/6,2/6],[0/6,2/3]].
%@ [[1/6,3/6],[0/6,3/3],[2/6,0/0]].
%@ [[1/6,4/6],[2/6,2/6],[1/6,2/3],[2/3,0/0]].
%@ [[2/6,3/6],[1/6,3/3],[3/6,0/0]].
%@ [[2/6,4/6],[3/6,2/6],[2/6,2/3],[3/3,0/0]].
%@ [[3/6,3/6],[2/6,3/3],[4/6,0/0]].
%@ [[3/6,4/6],[3/6,2/3]].
%@ [[3/6,3/3]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 2.482s, 11_535_864 inferences
%@ .. done.
%@    true.

%?- d_writehassedot(3).
%@ Opening file 'HasseD3.dot'...
%@ Collecting final tallies ..
%@  sorting 93 final tallies ..Sorting length-93 list Qs:
%@   .. encoding Qs:   % CPU time: 0.095s, 480_900 inferences
%@    % CPU time: 0.097s, 483_365 inferences
%@ 
%@  stratifying ..
%@ [[1/6,0/6,2/6],[1/6,1/6,0/6],[0/3,0/6,2/6],[0/3,1/6,0/6],[0/3,0/3,0/6]].
%@ [[0/6,2/6,2/6],[1/6,1/6,1/6],[0/3,0/6,3/6],[0/3,1/6,1/6],[1/6,0/3,0/6],[0/3,0/3,1/6]].
%@ [[0/6,2/6,3/6],[1/6,0/6,3/6],[0/3,0/6,4/6],[0/3,1/6,2/6],[1/6,0/3,1/6],[0/3,0/6,2/3]].
%@ [[0/6,2/6,4/6],[0/6,3/6,2/6],[1/6,0/6,4/6],[1/6,1/6,2/6],[0/3,1/6,3/6],[1/6,0/6,2/3],[0/3,0/6,3/3],[0/6,2/6,0/0]].
%@ [[0/6,3/6,3/6],[1/6,1/6,3/6],[0/3,1/6,4/6],[0/6,2/6,2/3],[1/6,0/6,3/3],[0/3,1/6,2/3],[0/6,2/3,0/0]].
%@ [[0/6,3/6,4/6],[1/6,1/6,4/6],[1/6,2/6,2/6],[0/6,2/6,3/3],[1/6,1/6,2/3],[0/3,1/6,3/3],[0/6,3/6,0/0],[2/6,0/0,0/0]].
%@ [[1/6,2/6,3/6],[0/6,3/6,2/3],[1/6,1/6,3/3],[0/6,4/6,0/0],[1/6,2/6,0/0],[0/6,3/3,0/0],[2/3,0/0,0/0]].
%@ [[1/6,2/6,4/6],[1/6,3/6,2/6],[0/6,3/6,3/3],[1/6,2/6,2/3],[1/6,3/6,0/0],[1/6,2/3,0/0]].
%@ [[1/6,3/6,3/6],[2/6,2/6,2/6],[1/6,2/6,3/3],[1/6,4/6,0/0],[2/6,2/6,0/0],[1/6,3/3,0/0],[3/6,0/0,0/0]].
%@ [[1/6,3/6,4/6],[2/6,2/6,3/6],[1/6,3/6,2/3],[2/6,3/6,0/0],[2/6,2/3,0/0],[3/3,0/0,0/0]].
%@ [[2/6,2/6,4/6],[2/6,3/6,2/6],[1/6,3/6,3/3],[2/6,2/6,2/3],[3/6,2/6,0/0],[2/6,3/3,0/0],[4/6,0/0,0/0]].
%@ [[2/6,3/6,3/6],[3/6,2/6,2/6],[2/6,2/6,3/3],[2/6,4/6,0/0],[3/6,2/3,0/0]].
%@ [[2/6,3/6,4/6],[3/6,2/6,3/6],[2/6,3/6,2/3],[3/6,3/6,0/0]].
%@ [[3/6,2/6,4/6],[3/6,3/6,2/6],[2/6,3/6,3/3],[3/6,2/6,2/3],[3/6,3/3,0/0]].
%@ [[3/6,3/6,3/6],[3/6,2/6,3/3],[3/6,4/6,0/0]].
%@ [[3/6,3/6,4/6],[3/6,3/6,2/3]].
%@ [[3/6,3/6,3/3]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 181.423s, 793_854_108 inferences
%@ .. done.
%@    true.
%@ Opening file 'HasseD3.dot'...
%@ Collecting final tallies ..
%@  sorting 93 final tallies ..Sorting length-93 list Qs:
%@   .. encoding Qs:   % CPU time: 0.069s, 359_513 inferences
%@    % CPU time: 0.071s, 361_978 inferences
%@ 
%@  stratifying ..
%@ [[1/6,0/6,2/6],[1/6,1/6,0/6],[0/3,0/6,2/6],[0/3,1/6,0/6],[0/3,0/3,0/6]].
%@ [[0/6,2/6,2/6],[1/6,1/6,1/6],[0/3,0/6,3/6],[0/3,1/6,1/6],[1/6,0/3,0/6],[0/3,0/3,1/6]].
%@ [[0/6,2/6,3/6],[1/6,0/6,3/6],[0/3,0/6,4/6],[0/3,1/6,2/6],[1/6,0/3,1/6],[0/3,0/6,2/3]].
%@ [[0/6,2/6,4/6],[0/6,3/6,2/6],[1/6,0/6,4/6],[1/6,1/6,2/6],[0/3,1/6,3/6],[1/6,0/6,2/3],[0/3,0/6,3/3],[0/6,2/6,0/0],[0/6,2/3,0/0]].
%@ [[0/6,3/6,3/6],[1/6,1/6,3/6],[0/3,1/6,4/6],[0/6,2/6,2/3],[1/6,0/6,3/3],[0/3,1/6,2/3],[2/6,0/0,0/0],[2/3,0/0,0/0]].
%@ [[0/6,3/6,4/6],[1/6,1/6,4/6],[1/6,2/6,2/6],[0/6,2/6,3/3],[1/6,1/6,2/3],[0/3,1/6,3/3],[0/6,3/6,0/0],[0/6,3/3,0/0]].
%@ [[1/6,2/6,3/6],[0/6,3/6,2/3],[1/6,1/6,3/3],[0/6,4/6,0/0],[1/6,2/6,0/0],[1/6,2/3,0/0]].
%@ [[1/6,2/6,4/6],[1/6,3/6,2/6],[0/6,3/6,3/3],[1/6,2/6,2/3],[1/6,3/6,0/0],[1/6,3/3,0/0],[3/6,0/0,0/0],[3/3,0/0,0/0]].
%@ [[1/6,3/6,3/6],[2/6,2/6,2/6],[1/6,2/6,3/3],[1/6,4/6,0/0],[2/6,2/6,0/0],[2/6,2/3,0/0]].
%@ [[1/6,3/6,4/6],[2/6,2/6,3/6],[1/6,3/6,2/3],[2/6,3/6,0/0],[2/6,3/3,0/0],[4/6,0/0,0/0]].
%@ [[2/6,2/6,4/6],[2/6,3/6,2/6],[1/6,3/6,3/3],[2/6,2/6,2/3],[3/6,2/6,0/0],[3/6,2/3,0/0]].
%@ [[2/6,3/6,3/6],[3/6,2/6,2/6],[2/6,2/6,3/3],[2/6,4/6,0/0]].
%@ [[2/6,3/6,4/6],[3/6,2/6,3/6],[2/6,3/6,2/3],[3/6,3/6,0/0],[3/6,3/3,0/0]].
%@ [[3/6,2/6,4/6],[3/6,3/6,2/6],[2/6,3/6,3/3],[3/6,2/6,2/3]].
%@ [[3/6,3/6,3/6],[3/6,2/6,3/3],[3/6,4/6,0/0]].
%@ [[3/6,3/6,4/6],[3/6,3/6,2/3]].
%@ [[3/6,3/6,3/3]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 176.904s, 788_714_092 inferences
%@ .. done.
%@    true.
%@ Opening file 'HasseD3.dot'...
%@ Collecting final tallies ..
%@  sorting 93 final tallies ..Sorting length-93 list Qs:
%@   .. encoding Qs:   % CPU time: 0.063s, 332_037 inferences
%@   .. decoding Qs:   % CPU time: 0.138s, 877_246 inferences
%@    % CPU time: 0.204s, 1_214_601 inferences
%@ 
%@  stratifying ..
%@ [[0/6,2/6,2/6],[1/6,0/6,2/6],[1/6,1/6,0/6],[0/3,0/6,2/6],[0/3,1/6,0/6],[0/3,0/3,0/6]].
%@ [[0/6,2/6,3/6],[1/6,0/6,3/6],[1/6,1/6,1/6],[0/3,0/6,3/6],[0/3,1/6,1/6],[1/6,0/3,0/6],[0/3,0/3,1/6]].
%@ [[0/6,2/6,4/6],[0/6,3/6,2/6],[1/6,0/6,4/6],[1/6,1/6,2/6],[0/3,0/6,4/6],[0/3,1/6,2/6],[1/6,0/3,1/6],[0/3,0/6,2/3]].
%@ [[0/6,3/6,3/6],[1/6,1/6,3/6],[0/3,1/6,3/6],[1/6,0/6,2/3],[0/3,0/6,3/3],[0/6,2/6,0/0]].
%@ [[0/6,3/6,4/6],[1/6,1/6,4/6],[1/6,2/6,2/6],[0/3,1/6,4/6],[0/6,2/6,2/3],[1/6,0/6,3/3],[0/3,1/6,2/3],[0/6,2/3,0/0]].
%@ [[1/6,2/6,3/6],[0/6,2/6,3/3],[1/6,1/6,2/3],[0/3,1/6,3/3],[0/6,3/6,0/0],[2/6,0/0,0/0]].
%@ [[1/6,2/6,4/6],[1/6,3/6,2/6],[0/6,3/6,2/3],[1/6,1/6,3/3],[0/6,4/6,0/0],[1/6,2/6,0/0],[0/6,3/3,0/0],[2/3,0/0,0/0]].
%@ [[1/6,3/6,3/6],[2/6,2/6,2/6],[0/6,3/6,3/3],[1/6,2/6,2/3],[1/6,3/6,0/0],[1/6,2/3,0/0]].
%@ [[1/6,3/6,4/6],[2/6,2/6,3/6],[1/6,2/6,3/3],[1/6,4/6,0/0],[2/6,2/6,0/0],[1/6,3/3,0/0],[3/6,0/0,0/0]].
%@ [[2/6,2/6,4/6],[2/6,3/6,2/6],[1/6,3/6,2/3],[2/6,3/6,0/0],[2/6,2/3,0/0],[3/3,0/0,0/0]].
%@ [[2/6,3/6,3/6],[3/6,2/6,2/6],[1/6,3/6,3/3],[2/6,2/6,2/3],[3/6,2/6,0/0],[2/6,3/3,0/0],[4/6,0/0,0/0]].
%@ [[2/6,3/6,4/6],[3/6,2/6,3/6],[2/6,2/6,3/3],[2/6,4/6,0/0],[3/6,2/3,0/0]].
%@ [[3/6,2/6,4/6],[3/6,3/6,2/6],[2/6,3/6,2/3],[3/6,3/6,0/0]].
%@ [[3/6,3/6,3/6],[2/6,3/6,3/3],[3/6,2/6,2/3],[3/6,3/3,0/0]].
%@ [[3/6,3/6,4/6],[3/6,2/6,3/3],[3/6,4/6,0/0]].
%@ [[3/6,3/6,2/3]].
%@ [[3/6,3/6,3/3]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 49.716s, 233_678_798 inferences
%@ .. done.
%@    true.
%@ Opening file 'HasseD3.dot'...
%@ Collecting final tallies ..
%@  sorting 93 final tallies ..
%@  stratifying ..
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
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 121.519s, 612_386_652 inferences
%@ .. done.
%@    true.

%?- Q1^Q2+\(findall(Q, user:d_mendtally_rec(2,Q,_), Qfs), user:in_cover(Qfs, Q1, Q2)).
%@    Q1 = [0/3,1/6], Q2 = [0/3,0/6]
%@ ;  Q1 = [0/6,2/3], Q2 = [0/3,1/6]
%@ ;  Q1 = [0/6,2/3], Q2 = [0/6,2/6]
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,2/3]
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,3/6]
%@ ;  Q1 = [0/6,3/6], Q2 = [0/3,0/6]
%@ ;  Q1 = [0/6,3/6], Q2 = [0/6,2/6]
%@ ;  Q1 = [0/6,4/6], Q2 = [0/3,1/6]
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
%@ ;  Q1 = [1/6,4/6], Q2 = [0/6,2/3]
%@ ;  Q1 = [1/6,4/6], Q2 = [1/6,3/6]
%@ ;  Q1 = [2/3,0/0], Q2 = [2/6,0/0]
%@ ;  Q1 = [2/6,0/0], Q2 = [0/6,2/3]
%@ ;  Q1 = [2/6,0/0], Q2 = [1/6,1/6]
%@ ;  Q1 = [2/6,2/3], Q2 = [1/6,3/3]
%@ ;  Q1 = [2/6,2/3], Q2 = [2/6,2/6]
%@ ;  Q1 = [2/6,2/6], Q2 = [1/6,3/6]
%@ ;  Q1 = [2/6,3/3], Q2 = [2/6,0/0]
%@ ;  Q1 = [2/6,3/3], Q2 = [2/6,2/3]
%@ ;  Q1 = [2/6,3/3], Q2 = [2/6,3/6]
%@ ;  Q1 = [2/6,3/6], Q2 = [1/6,4/6]
%@ ;  Q1 = [2/6,3/6], Q2 = [2/6,2/6]
%@ ;  Q1 = [2/6,4/6], Q2 = [1/6,2/3]
%@ ;  Q1 = [2/6,4/6], Q2 = [2/6,3/6]
%@ ;  Q1 = [3/3,0/0], Q2 = [2/3,0/0]
%@ ;  Q1 = [3/3,0/0], Q2 = [3/6,0/0]
%@ ;  Q1 = [3/6,0/0], Q2 = [1/6,2/3]
%@ ;  Q1 = [3/6,0/0], Q2 = [2/6,0/0]
%@ ;  Q1 = [3/6,2/3], Q2 = [2/6,3/3]
%@ ;  Q1 = [3/6,2/3], Q2 = [3/6,2/6]
%@ ;  Q1 = [3/6,2/6], Q2 = [2/6,3/6]
%@ ;  Q1 = [3/6,3/3], Q2 = [3/6,0/0]
%@ ;  Q1 = [3/6,3/3], Q2 = [3/6,2/3]
%@ ;  Q1 = [3/6,3/3], Q2 = [3/6,3/6]
%@ ;  Q1 = [3/6,3/6], Q2 = [2/6,4/6]
%@ ;  Q1 = [3/6,3/6], Q2 = [3/6,2/6]
%@ ;  Q1 = [3/6,4/6], Q2 = [2/6,2/3]
%@ ;  Q1 = [3/6,4/6], Q2 = [3/6,3/6]
%@ ;  Q1 = [4/6,0/0], Q2 = [2/6,2/3]
%@ ;  Q1 = [4/6,0/0], Q2 = [3/6,0/0]
%@ ;  false. % Covering relation in 𝒬f (D=2 case) _still_ has 50 pairs.

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

qs_maxs([], []).
qs_maxs([Q|Qs], Maxs) :-
    tpartition('≽'(Q), Qs, _, Qs1),
    if_(tmember_t('≼'(Q), Qs1), % ∃ Q' ∈ Qs s.t. Q ≼ Q' ?
        qs_maxs(Qs1, Maxs), % if so, Q is not maximal
        (   Maxs = [Q|Maxs1], % otherwise, it is
            qs_maxs(Qs1, Maxs1)
        )
       ).

qs_mins([], []).
qs_mins([Q|Qs], Mins) :-
    tpartition('≼'(Q), Qs, _, Qs1),
    if_(tmember_t('≽'(Q), Qs1), % ∃ Q' ∈ Qs s.t. Q' ≼ Q ?
        qs_mins(Qs1, Mins), % if so, Q is not minimal
        (   Mins = [Q|Mins1], % otherwise, it is
            qs_mins(Qs1, Mins1)
        )
       ).

% Regions near the origin
% TODO: Find a name conveying geometrical intutition ('sphere'? 'hypercube'?),
%       or perhaps link this to *accessible* tallies as discussed in Fact 1.27.
% TODO: Also deal with the 'qs' plurality; perhaps in this module, a given tally
%       counts as 'q', and only _lists_ of tallies should be regarded a plural?
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
    findall(C, (qs_d_nmax(C, D, Nmax),
                maplist('≽'(C), Qls1)), Cs),
    qs_mins(Cs, Gs).

d_gs_rec(D, Gs, X) :- d_gs_rec(D, Gs, X, 6).

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
%@    error('$interrupt_thrown',repl/0). % unbounded mem growth

%?- time(d_gs(3, Gs)).
%@ Listing Qs......    % CPU time: 1.597s, 6_660_460 inferences
%@ Sorting length-21952 list Qs:
%@   .. encoding Qs:   % CPU time: 20.597s, 109_986_469 inferences
%@    % CPU time: 20.665s, 110_054_609 inferences
%@ Stratifying Qf..    % CPU time: 3.277s, 14_741_613 inferences
%@ Finding g's ..
%@ ↓[2/6,0/6,0/2] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@    % CPU time: 36.546s, 163_202_935 inferences
%@    % CPU time: 62.099s, 294_689_968 inferences
%@    Gs = [[2/6,0/6,0/2],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- [2/6,0/4,0/4] '≼' [0/6,2/6,0/4].
%@    true.

%?- time(d_gs(4, Gs)).
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
    qs_sorted(Qs, SQs), % instrumentation included
    reverse(SQs, RQs),
    format("Stratifying Qf.. ", []),
    time(d_Qfstratamax(D, Mss)),
    format("Finding g's ..~n", []),
    time(galois(Mss, RQs, Gs)).

%?- time(d_gs(2, Gs)).
%@ Listing Qs......    % CPU time: 0.072s, 249_966 inferences
%@ Sorting length-784 list Qs:
%@   .. encoding Qs:   % CPU time: 0.636s, 3_382_043 inferences
%@    % CPU time: 0.640s, 3_386_627 inferences
%@ Stratifying Qf..    % CPU time: 0.769s, 3_442_312 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4] ⊇ [[2/6,0/0],[2/6,2/6]].
%@ ↓[0/6,2/6] ⊇ [[0/6,2/6]].
%@ ↓[0/5,0/6] ⊇ [[0/3,0/6],[1/6,0/6]].
%@    % CPU time: 0.893s, 3_980_654 inferences
%@    % CPU time: 2.382s, 11_068_590 inferences
%@    Gs = [[2/6,0/4],[0/6,2/6],[0/5,0/6]].
%@ Listing Qs......    % CPU time: 0.067s, 249_966 inferences
%@ Sorting length-784 list Qs:
%@   .. encoding Qs:   % CPU time: 0.445s, 2_352_998 inferences
%@    % CPU time: 0.450s, 2_357_582 inferences
%@ Stratifying Qf..    % CPU time: 0.767s, 3_442_117 inferences
%@ Finding g's ..
%@ ↓[2/6,0/6] ⊇ [[2/6,0/0],[2/6,2/6]].
%@ ↓[0/6,2/6] ⊇ [[0/6,2/6]].
%@ ↓[0/6,0/6] ⊇ [[0/3,0/6],[1/6,0/6]].
%@    % CPU time: 0.822s, 3_665_015 inferences
%@    % CPU time: 2.114s, 9_723_711 inferences
%@    Gs = [[2/6,0/6],[0/6,2/6],[0/6,0/6]].
% TODO: These differ from the Gₓ's calculated by d_gs_rec/3; WHY?

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
%@ Listing Qs......    % CPU time: 43.456s, 182_781_614 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 679.046s, 3_594_977_411 inferences
%@ Sorting Qs....    % CPU time: 0.632s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.648s, 6_146_561 inferences
%@ Decoding......    % CPU time: 1187.057s, 7_752_694_545 inferences
%@    % CPU time: 1867.513s, 11_355_055_949 inferences
%@ Reversing.......    % CPU time: 0.280s, 614_658 inferences
%@ Stratifying Qf..    % CPU time: 12.384s, 57_444_988 inferences
%@ Finding g's ..

%?- time(d_gs(3, Gs)). % After #'ing everything in q_r/2
%@ Listing Qs......    % CPU time: 1.588s, 6_660_460 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 20.434s, 109_988_099 inferences
%@ Sorting Qs....    % CPU time: 0.017s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.019s, 175_617 inferences
%@ Decoding......    % CPU time: 31.490s, 207_539_697 inferences
%@    % CPU time: 51.972s, 317_755_335 inferences
%@ Reversing.......    % CPU time: 0.005s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.393s, 15_670_513 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 29.991s, 153_168_191 inferences
%@    % CPU time: 86.957s, 493_286_608 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- time(d_gs(3, Gs)). % After #'ing stuff in d_int_kt_ku/4
%@ Listing Qs......    % CPU time: 1.610s, 6_660_460 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 19.827s, 106_168_451 inferences
%@ Sorting Qs....    % CPU time: 0.018s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.020s, 175_617 inferences
%@ Decoding......    % CPU time: 38.164s, 245_604_465 inferences
%@    % CPU time: 58.040s, 352_000_455 inferences
%@ Reversing.......    % CPU time: 0.006s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.358s, 15_549_757 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 28.801s, 145_469_735 inferences
%@    % CPU time: 91.824s, 519_712_516 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

%?- time(d_gs(3, Gs)). % After precomputing d_maxenc/2
%@ Listing Qs......    % CPU time: 1.603s, 6_660_460 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 20.060s, 106_168_451 inferences
%@ Sorting Qs....    % CPU time: 0.017s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.019s, 175_617 inferences
%@ Decoding......    % CPU time: 45.324s, 286_742_507 inferences
%@    % CPU time: 65.432s, 393_138_497 inferences
%@ Reversing.......    % CPU time: 0.006s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.404s, 15_549_757 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 29.085s, 145_469_735 inferences
%@    % CPU time: 99.538s, 560_850_558 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].
%@ Listing Qs......    % CPU time: 1.613s, 6_660_460 inferences
%@ Sorting Qs...... Encoding Qs...    % CPU time: 22.714s, 121_049_849 inferences
%@ Sorting Qs....    % CPU time: 0.019s, 2 inferences
%@ Sizing Qs.....    % CPU time: 0.019s, 175_617 inferences
%@ Decoding......    % CPU time: 47.516s, 299_452_715 inferences
%@    % CPU time: 70.279s, 420_730_103 inferences
%@ Reversing.......    % CPU time: 0.005s, 21_954 inferences
%@ Stratifying Qf..    % CPU time: 3.404s, 15_549_757 inferences
%@ Finding g's ..
%@ ↓[2/6,0/4,0/4] ⊇ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ Mss = [[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 2494, Gs1 = [[2/6,0/4,0/4]].
%@ ↓[0/6,2/6,0/4] ⊇ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ Mss = [[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1978, Gs1 = [[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/6,2/6] ⊇ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ Mss = [[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]]], |Qs| = 1228, Gs1 = [[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@ ↓[0/5,0/5,0/6] ⊇ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].
%@ Mss = [], |Qs| = 8, Gs1 = [[0/5,0/5,0/6],[0/5,0/6,2/6],[0/6,2/6,0/4],[2/6,0/4,0/4]].
%@    % CPU time: 29.068s, 145_469_735 inferences
%@    % CPU time: 104.378s, 588_442_164 inferences
%@    Gs = [[2/6,0/4,0/4],[0/6,2/6,0/4],[0/5,0/6,2/6],[0/5,0/5,0/6]].

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
% the enlargement ('strengthening') ≼ to  ≼* or else
% *weakening* the iff at the heart of adjointness.
e2(Q, X) :-
    [G0,G1,G2] = [[2/6,0/4], [0/6,2/6], [0/5,0/6]],
    if_(Q '≼' G0, X = 0,
        if_(Q '≼' G1, X = 1,
            if_(Q '≼' G2, X = 2, false))).

%?- e2([0/0,0/0], X).
%@    X = 2. % Is the bottom-up cascade of a lower-Galois IE therefore unsafe?

% Suppose we want a 'cut-off' version c2/2 of the above.
% The main deficiency of e2/2 to be remedied is that it
% lets Q 'slip thru' to the highest dose, simply because
% the po ≼ is too weak to catch it.  What we would need
% then is to impose _additional_ requirements on upward
% percolation of Q.
c2(Q, X) :-
    [G0,G1,G2] = [[2/6,0/4], [0/6,2/6], [0/5,0/6]],
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
    state_tallies(State0, Tally), % I think this calculation is wrong.
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

%?- meet([3/3,0/0],[3/6,3/3],M1).
%@    M1 = [3/3,3/3].
%?- meet([3/3,3/3], [3/6,4/6], M2).
%@    M2 = [3/3,4/4].
%?- meet([3/3,4/4], [4/6,0/0], M3).
%@    M3 = [4/4,3/3].

%?- foldl(meet, [[3/3,0/0],[3/6,3/3],[3/6,4/6],[4/6,0/0]], [0/6,0/6], Meet).
%@    Meet = [4/4,3/3].

% Let's calculate the meet of the pair { [1/6,3/3] , [1/6,4/6] }.
%?- meet([1/6,3/3], [1/6,4/6], Meet).
%@    Meet = [1/6,4/4].
%?- [1/6,4/4] '≼' [1/6,3/3], [1/6,4/4] '≼' [1/6,4/6].
%@    true.

%?- [0/1,1/1] '≼' [0/1,0/0].
%@    true.

%?- [4/4] '≼' [3/3].
%@    true.

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

%?- d_ls(2, Ls). % (After switching to d_mendtally_rec/3 in d_Qfstratamin/2)
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
