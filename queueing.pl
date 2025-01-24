% Exploring idioms for modeling arrivals processes and their servicing

:- use_module(library(random)).
:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(lambda)).
:- use_module(library(dif)).
:- use_module(library(pairs)).
:- use_module(library(clpz)).

clpz:monotonic.

:- use_module(probdist).

rate_arrivals(Rate, Ts) :-
    same_length(Ts, ΔTs),
    maplist(rexp(Rate), ΔTs),
    numlist_partsums(ΔTs, Ts).

?- length(Ts, 4), rate_arrivals(2.0, Ts).
   Ts = [0.5662067068679191,1.40316178028145,1.617681423182813,1.9161774261915316].
   Ts = [0.05990944141731505,0.3684931225434027,0.41019471665761614,0.7406373917462235].
   Ts = [0.22713646401782478,0.3990310183928857,0.44462988541493365,0.8934476284250478].
   Ts = [0.21588283841756808,0.3412300892149634,1.2039454695297602,2.00139750572733].

?- rate_arrivals(1, Ts).
   Ts = [0.10930209769116438]
;  Ts = [1.9241620786500748,2.3662116568817693]
;  Ts = [1.0746998885641768,1.1487024434865538,3.5952139696514047]
;  Ts = [0.9603219746053693,2.1080645360024977,2.7963162628534546,2.956646474384808]
;  ... .

numlist_partsums([X|Xs], [X|Σs]) :-
    same_length(Xs, Σs), % (eliminates an unnecessary choice point)
    numlist_partsums_acc(Xs, Σs, X).

numlist_partsums_acc([], [], _).
numlist_partsums_acc([X|Xs], [Σ|Σs], A) :-
    Σ is X + A,
    numlist_partsums_acc(Xs, Σs, Σ).

% Especially because it depends on numlist_partsums/2, the above feels
% heavy-handed in comparison to the lightweight and elegant DCG below.
% This DCG does suffer (inherently?) from a choice-point that somehow
% really annoys me.  But noting how numlist_partsums/2 incorporates a
% special-purpose choicepoint-eliminating goal, I suppose there may be
% little harm in wrapping this _generative_ DCG with one little !/0
% that commits to the generated list.

% TODO: Document persistence of the choice-point despite permutations
%       of the DCG rules.

poisson_arrival_times(Rate) --> poisson_arrival_times(Rate, 0.0).
poisson_arrival_times(_, _) --> [].
poisson_arrival_times(Rate, T) --> [T1],
                                   { rexp(Rate, Δt), T1 is T + Δt },
                                   poisson_arrival_times(Rate, T1).

?- length(Ts, 4), phrase(poisson_arrival_times(0.5, 0.0), Ts).
   Ts = [0.7966409316111609,2.7995495134211916,3.345313542829656,3.624776053147931]
;  false. % Is a choice-point unavoidable with such generative DCGs?

?- length(Ts, N), phrase(poisson_arrival_times(0.5, 0.0), Ts).
   Ts = [], N = 0
;  Ts = [2.7800882836878307], N = 1
;  Ts = [3.288944117177038,6.17740671216914], N = 2
;  Ts = [0.018309727216998195,0.12343297062464463,1.3640943200409386], N = 3
;  ... .

% Note how the cut here allows multiple invocations of the query.
% Doing a cut after PRNG seems entirely unobjectionable, given that
% RNG by its very nature renders 'do-overs' inadmissible!  That is,
% the act of RNG implicitly involves the irreversibility of !/0.
?- phrase(poisson_arrival_times(0.5, 100), [T1,T2,T3]), !.
   T1 = 104.37649502158831, T2 = 104.87229743666023, T3 = 107.48527696201455.
   T1 = 101.45398386792101, T2 = 101.89445295777217, T3 = 105.22004591280482.
   T1 = 102.05680287259786, T2 = 108.09969402709206, T3 = 108.15661268827373.

% ==================== Toxicity Thresholds ====================

% Now it's time to specify the random generation of enrolling
% participants.  Each participant *on arrival* presents only the
% arrival time and a toxicity threshold.  The work above suffices
% for generating the arrival times; I must next consider how to
% sample the toxicity thresholds.

% The log-normally distributed MTDᵢ of "What Were They Thinking?" [1]
% would seem to be ideal here.
%
% 1. Norris DC. What Were They Thinking? Pharmacologic priors implicit
%    in a choice of 3+3 dose-escalation design. arXiv:201205301
%    [statME]. December 24, 2020. https://arxiv.org/abs/2012.05301

% Now lognormal distributions always bring up the issue of _scale_,
% with the μ parameter being problematic.  What is the scale here?
% What would it mean to have MTDᵢ ~ Lognorm(μ,σ)?

% A quick reminder about reading the Lognormal parameters: it is best
% to write them as log(μ) and log(σ), respectively, thereby referring
% them quantities μ and σ that act _on the dose scale_.

% When MDTᵢ ~ Lognormal(log(μ), log(σ)), then we have the very simple
% story that median MTDᵢ is μ, and that doses μ/σ and μ*σ bracket a
% range between the 16% and 84% points on the CDF.  This means that
% half of individuals in the population will have a DLT at dose μ,
% whereas only 16% will have one at μ/σ but 84% will at dose μ*σ.

% To support this intuition, let's _tabulate_ the CDF at various
% values of μ and σ.

dltprobs(Mu_, Sigma_, Probs) :-
    Mu is Mu_,
    Sigma is Sigma_,
    Doses = [1,2,3,4,5,6],
    maplist(dlognorm(Mu, Sigma), Doses, Ps),
    maplist(\P^P_^(P_ is round(1000*P)/1000), Ps, Probs).

?- dltprobs(log(6), log(2), Probs).
   Probs = [0.005,0.056,0.159,0.279,0.396,0.5].
?- dltprobs(log(6), log(3), Probs).
   Probs = [0.051,0.159,0.264,0.356,0.434,0.5].
?- dltprobs(log(6), log(4), Probs).
   Probs = [0.098,0.214,0.309,0.385,0.448,0.5].

?- dlognorm(log(6), log(3), 18, P).
   P = 0.8413447460685429.
?- dlognorm(log(6), log(3), 2, P).
   P = 0.15865525393145707.
?- dlognorm(log(6), log(3), 6, P).
   P = 0.5.

% Now, at long last, we need a queue servicing function that takes a
% current trial state to a new one upon admitting a new participant.
% Of course, this requires that we specify what this state is!

% At any time, the state consists of:
% - a 'pessimistic' tally
% - a dosewise list of pending non-toxicities
% - a queue of _waiting_ enrollees, which may grow during intervals
%   when pending assessments are keeping the tally so pessimistic
%   that the current recommended dose is zero.

% Servicing of a new arrival at time t requires the following steps:
% 1. Tally any non-toxicities that have resolved before time t
% 2. Based on this now-current tally, determine enrolling dose dᵢ
% 3. 'Pessimistically' tally a [provisional] toxicity at dᵢ
% 3. If arrival's MTDᵢ exceeds dᵢ, record a pending non-toxicity
%    to be resolved at time T+Δ.

% The above requires maintaining a current, worst-case tally, as well
% as a FIFO queue of pending non-tox assessments.  Representing the
% latter requires only a list of (tᵢ, dᵢ) _pairs_, the (-1) magnitude
% of the T adjustment being implicit.  Note also that with arrivals
% occuring in ℝeal time, all arrival times are distinct.

% Perhaps this FIFO queue is my opportunity to use list-differences?
% Yes, indeed -- see §15.4 of Sterling & Shapiro!

% Let's proceed in as declarative a spirit as possible, seeking a
% _meaning_ (ontology?) for our list difference.  I would like to say
% that pending assessments in list-difference form As-Bs *means* that
% As is the sorted list of current _and future_ pending assessments
% for participants destined to record an 'o', while Bs is the future
% tail of this list.  (Thus, As is partially uninstantiated, and Bs
% would be totally uninstantiated, I think.)

% By recognizing that the _state_ of the trial consists of a pair of
% 'pessimistic' current tally with pending assessents, we can reduce
% the arity of these predicates.

%% rec_state0_arrival_state(+Rec_2, +S0, +(Z-MTD), -S)
%
% Under the dose-recommendation rule Rec_2, and given trial state S0,
% S is the new trial state which results from enrolling at time Z a
% new participant who has the given MTD ∈ ℝ⁺:
%
% TODO: Must I include an Enr_4 argument as well?
%
% - Rec_2(+Q, -X) :- X is recommended enrolling dose from tally Q.
% - Enr_4(+Qs0, +X, -Qs, ?Truth) reifies enrollability of Qs0
%                                at dose X to yield Qs.
%
/*
rec_state0_arrival_state(Rec_2, S0, Z-MTD, S) :-
    state0_now_state(S0, Z, S),
    todo.
*/

%% pending0_now_resolved_pending(+P0, +Z, -R, -P)
%
% R is the list of doses from the head of pending-assessments list P0
% for which toxicity assessments have resolved by time Z, and P is the
% remaining tail of assessments still pending as of time Z.
%
% Implementation notes:
% * Pending-assessments lists are sorted chronologically.
% * Our right-continuous treatment of _time_ accords with our usage,
%   "resolved BY time Z".
pending0_now_resolved_pending([], _, [], []).
pending0_now_resolved_pending([Z1-X1|ZXs], Z, [], [Z1-X1|ZXs]) :- Z1 > Z, !.
pending0_now_resolved_pending([Z0-X0|ZX0s], Z, [X0|X0s], ZXs) :-
    Z0 =< Z,
    pending0_now_resolved_pending(ZX0s, Z, X0s, ZXs).

?- pending0_now_resolved_pending([1.2-3,4.5-2], 0.1, R, P).
   R = [], P = [1.2-3,4.5-2].

?- pending0_now_resolved_pending([1.2-3,4.5-2], 2.1, R, P).
   R = [3], P = [4.5-2].

?- pending0_now_resolved_pending([1.2-3,4.5-2], 5.1, R, P).
   R = [3,2], P = [].


%% tally0_resolved_tally(+Q0s, +Xs, -Qs)
%
% Qs is the tally which results from the non-tox resolution of pending
% assessments at doses in list Xs.
/*
tally0_resolved_tally(Qs, [], Qs).
tally0_resolved_tally(Q0s, [X|Xs], Qs) :-
    nth1(X, Q0s, T0/N),
    #T #= #T0 - 1,
    tally0_resolved_tally(Q1s, Xs, Qs),
    todo.
*/

?- nth1(2, [a,b,c,d,e], C, R).
   C = b, R = "acde".

% By implementing natlist_freqs/2 below, we will set ourselves up to
% apply resolved assessments efficiently to an outdated tally.

%% natlist_freqs(+Ns, -Freqs)
%
% Ns is a list of non-negative integers, and Freqs is an integer list
% of length M = max(Ns), such that nth0(N, Freqs, C) iff the number N
% appears C times in Ns.
%
natlist_freqs(Ns, Freqs) :-
    foldl(clpz:max_, Ns, 0, Max),
    findall(X, (X in 0..Max, indomain(X)), Xs),
    append(Ns, Xs, N1s),  % each of 0..Max appears at least once
    multisort(N1s, SN1s),
    list_rle(SN1s, NC1s),  % RLE now overcounts each of 0..Max by 1
    pairs_values(NC1s, Freqs1),
    maplist(\F1^F^(#F1 #= #F + 1), Freqs1, Freqs).

?- natlist_freqs([0,1,1,2,4,4,4,6], Freqs).
   Freqs = [1,2,1,0,3,0,1]
;  false.

%% multisort(+Xs, -SXs)
%
% SXs is Xs sorted _without_ removing duplicates as sort/2 does.
multisort(Xs, SXs) :-
    length(Xs, N),
    findall(Y, (Y in 1..N, indomain(Y)), Ys),
    pairs_keys_values(XYs, Xs, Ys),
    sort(XYs, SXYs),
    pairs_keys_values(SXYs, SXs, _).

?- multisort([4,2,4,2,3,5], SXs).
   SXs = [2,2,3,4,4,5].

%% list_rle(?Xs, ?XNs)
%
% The list XNs is a run-length decoding of list Xs.
list_rle(Xs, XNs) :- phrase(rle(XNs), Xs).

?- list_rle("Bwwaaahaaahaaaa!", RLE).
   RLE = ['B'-1,w-2,a-3,h-1,a-3,h-1,a-4,!-1]
;  false.

?- list_rle(Bwahaha, ['B'-1,w-2,a-3,h-1,a-3,h-1,a-4,!-1]).
   Bwahaha = "Bwwaaahaaahaaaa!"
;  false.

%% rle//1
% 
% Describes a list by run-length encoding.
rle([X-N|XNs]) --> { #N #> 1, #N_ #= #N - 1 },
                   [X],
                   rle([X-N_|XNs]).
rle([X-1,Y-N|XNs]) --> { dif(X,Y) },
                       [X],
                       rle([Y-N|XNs]).
rle([X-1]) --> [X].
rle([]) --> [].

?- phrase(rle([a-2,b-3,z-1]), List).
   List = "aabbbz"
;  false.
?- phrase(rle(RLE), "aabbbz").
   RLE = [a-2,b-3,z-1]
;  false.

% Copied from catform.pl:
qs_ts_ns([T/N|Qs], [T|Ts], [N|Ns]) :- qs_ts_ns(Qs, Ts, Ns).
qs_ts_ns([], [], []).

/*
%% state0_now_state(+S0, +Z, -S)
%
% Renders a state S0 = Q0-P0, consisting of pessimistic tally Q0
% paired with pending assessments P0, _current_ as of time Z.
state0_now_state(Q-[], _, Q-[]).
state0_now_state(Q0-[Z-X|_P0], Q-):-
    P0 = [].

tally0_pending0_arrival_tally_pending(Q0, P0, Z-MTD, Q, P) :-
    tally0_pending0_time_tally(Q0, P0, Z, Q),
    todo.
    
*/
