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

%% rolling(Rec_2, Q, Ps, Ws, As)//5
%
% Describes events of a rolling-enrollment trial defined by the
% dose-recommendation rule Rec_2, given a current state consisting of:
% - Q ∈ 𝒬, a realized tally from assessments completed up to now
% - Rx ∈ 0..D, the current dose recommendation
% - Ws, a queue of enrolled participants Waiting for dose assignments
% - As, an assoc mapping times to future Arrivals or Assessments:
%   - Arrivals are denoted arr(t, MTD)
%   - Assessments are denoted ao(t, d) or ax(t, d).
%
% We scale _time_ so that the DLT assessment period is 1.  This allows
% us (among other conveniences) to model the time-to-toxicity in case
% MTD < Rx simply as Delay = MTD/Rx.
%
% Sketching out some DCG rules will help me to elaborate these ideas.
% We implement Ws as a list with enqueuing via append/3 at O(n) cost.
% Instead of maintaining a separate list of pending assessments, for
% the express purpose of computing the pessimistic tally, we will just
% filter the whole list of upcoming events to identify unresolved
% assessments.
rolling(Rec_2, Q, Rx, Ws, [arr(Z,MTD)|As]) -->
    { (   Rx == 0 % TODO: Ensure that Rx=0 only if assessments remain pending.
      ;   Ws = [W|_]
      )
    },
    [enqueue(Z,MTD)],
    % Note that except in unusual scenarios with high arrival rates
    % (or during brief bursts of arrivals), the list Ws will stay
    % quite short on average.  Consequently, this O(n) append/3 does
    % negligible harm to sim speed.
    { append(Ws, [MTD], Ws1) },
    rolling(Rec_2, Q, Rx, Ws1, As).
rolling(Rec_2, Q, Rx, [], [arr(Z,MTD)|As]) -->
    { Rx > 0,
      (   MTD <  Rx, T = 1, Za is Z + MTD/Rx
      ;   MTD >= Rx, T = 0, Za is Z + 1.0
      ),
      % Although `Za is min(MTD/Rx, 1.0)` would yield Za in one go,
      % the elementary branches above seem clearer.
      sched(As, asx(Za, Rx, T), As1),
      upcoming_assessments(As1, Ps),
      tally_pending_pesstally(Q, Ps, Qp),
      call(Rec_2, Qp, Rx1)
    },
    [enroll(Z,MTD)],
    rolling(Rec_2, Q, Rx1, [], As1).
rolling(Rec_2, Q, Rx, Ws, [ax(Z,Dose)|As]) -->
    {
        tallyx(Q, Dose, Q1),
        % Tallying an 'x' has no effect on Qpess,
        % and therefore leaves Rx unchanged.
        upcoming_assessments(As, Ps),
        tally_pending_pesstally(Q, Ps, Qp),
        call(Rec_2, Qp, Rx1)
    },
    [x(Dose)],
    rolling(Rec_2, Q1, Rx1, Ws, As).
rolling(Rec_2, Q, Rx, Ws, [ao(Z,Dose)|As]) -->
    {
        tallyo(Q, Dose, Q1),
        % Tallying an 'o' DOES affect Qpess,
        % so Rx may have changed, and requires
        % recalculation.
        upcoming_assessments(As, Ps),
        tally_pending_pesstally(Q1, Ps, Q1p),
        call(Rec_2, Q1p, Rx1)
    },
    [o(Dose)],
    rolling(Rec_2, Q1, Rx1, Ws, As).

% TODO: Basic tally-arithmetic predicates belong in tally.pl!
%       But let's hold off defining these there, until we see
%       how the construction of a 'pessimistic' tally works.
tallyx(Q, Dose, Q1) :-
    todo.
tallyo(Q, Dose, Q1) :-
    todo.

sched(As, A, As1) :-
    todo.

upcoming_assessments(As, Ps) :-
    todo.

tally_pending_pesstally(Q, Ps, Qp) :-
    todo.

% At any time, the realized state consists of:
% - a tally of completed assessments ('the current tally')
% - a queue of _waiting_ enrollees, which may grow during intervals
%   when pending assessments are keeping the tally so pessimistic
%   that the current recommended dose is zero.

% Additionally, there is 'unrealized state' in the form of a time-series
% of all upcoming events, which are all either:
% - resolutions of pending assessments (time, dose, 0..1), or
% - new arrivals (time, MTDᵢ).

% The evolution of this state should generate a list of events
% described by a DCG.

% Servicing of a new arrival at time t requires the following steps:
% 1. Tally any assessments that have resolved before time t
% 2. Construct a 'pessimistic' tally by tallying all still-pending
%    assessments as toxicities
% 3. Based on this pessimistic tally, determine enrolling dose dᵢ
% 4. If arrival's MTDᵢ exceeds dᵢ, record a pending non-toxicity
%    to be resolved at time T+Δ.  Otherwise, calculate the delay
%    to observation of the toxic respons via to exp(dᵢ - MTDᵢ),
%    and schedule a pending toxicity accordingly.
% 5. In case dᵢ = 0, but the *actual* current tally would permit
%    enrollment, place the arrival in the _waiting_ queue. 

% The above requires maintaining several FIFO queues, but because
% these are indexed by time, their representation requires only
% pairlists, which are easily sorted.  Note moreover that, with
% arrivals occuring in ℝeal time, all arrival times are distinct.

% Furthermore, since we can quickly keysort/2 this pending-assessments
% list by _time_, there is no need to pursue the efficiencies of a
% list-differences formulation.

% By recognizing that the _state_ of the trial consists of a pair Q-P
% of 'pessimistic' current tally Q with pending assessents P, we can
% reduce the arity of these predicates.

%% rec_state0_arrival_state(+Rec_2, +S0, +(Z-MTD), -S)
%
% Under the dose-recommendation rule Rec_2, and given trial state S0,
% S is the new trial state which results from enrolling at time Z a
% new participant who has the given MTD ∈ ℝ⁺:
%
% TODO: Should I include an Enr_4 argument as well?
%
% - Rec_2(+Q, -X) :- X is recommended enrolling dose from tally Q.
% - Enr_4(+Qs0, +X, -Qs, ?Truth) reifies enrollability of Qs0
%                                at dose X to yield Qs.
%
rec_state0_arrival_state(Rec_2, S0, Z-MTD, S) :-
    state0_now_state(S0, Z, S1),
    % We now have a 'transient' state S1 = Q1-P1, including an
    % up-to-date tally Q1 which we may use to determine the dose at
    % which to enroll the arriving participant.
    Rec_2(Q1, X),
    % Given this recommended enrolling dose X, we consider 3 cases:
    %
    % 1. X = 0 means the trial is not currently enrolling.  But this
    % in turn could be true for several distinct reasons.  If there
    % are no pending assessments, then the trial has stopped!  But in
    % case there _are_ pending assessments, it is possible that the
    % enrollment will resume.  The challenge of looking ahead to such
    % a possibility might be something Prolog handles very nicely.
    % Also, the spirit of Losing No Solutions helps to ensure we fully
    % consider every such possibility.  But have I preserved enough
    % information about the pending assessments, to enable all proper
    % considerations to be made, upon enrollment?  Thus far, I have
    % treated the list P in S=Q-P as a mere *accounting* device that
    % embodies simulated foreknowledge of assessment outcomes.  But
    % this does not reflect full information available on enrollment.
    todo.

%% state0_now_state(+S0, +Z, -S)
%
% Given a state S0 = Q0-P0, consisting of pessimistic tally Q0 paired
% with pending non-tox assessments P0, renders a new state S = Q-P
% that is _current_ as of time Z, adapted to the new information from
% those P0 assessments which have resolved by time Z.
state0_now_state(Q0-P0, Z, Q-P):-
    pending_now_resolved_pending(P0, Z, As, P),
    tally0_resolved_tally(Q0, As, Q).

tally0_pending0_arrival_tally_pending(Q0, P0, Z-MTD, Q, P) :-
    tally0_pending0_time_tally(Q0, P0, Z, Q),
    todo.
    

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
tally0_resolved_tally(Q0s, Xs, Qs) :-
    same_length(Q0s, ΔTs),
    posints_bins(Xs, ΔTs),
    qs_ts_ns(Q0s, T0s, Ns),
    maplist(\T0^ΔT^T^(#T0 - #ΔT #= #T), T0s, ΔTs, Ts),
    qs_ts_ns(Qs, Ts, Ns).

?- tally0_resolved_tally([1/5,2/3,0/0], [2,1], Qs).
   Qs = [0/5,1/3,0/0]
;  false.

%% posints_bins(+Ns, -Bins)
%
% Ns is a list of positive integers, and Bins is a 1-indexed list
% such that nth1(N, Bins, F) iff N appears exactly F times in Ns.
% That is, Bins lists the _frequency_ in Ns for each number 1..L,
% where length(Bins, L).
%
% Generally, this predicate will be invoked with the length of Bins
% fixed, but its elements uninstantiated.
posints_bins(Ns, Bins) :-
    length(Bins, L),
    findall(B, (B in 1..L, indomain(B)), Bs),
    append(Ns, Bs, N1s),  % each B ∈ 1..L occurs at least once in N1s
    samsort(N1s, SN1s),
    list_rle(SN1s, NC1s), % NC1s now overcounts each bin by +1
    pairs_values(NC1s, Bins1),
    maplist(\F1^F^(#F1 #= #F + 1), Bins1, Bins).

?- length(Bins, 7), posints_bins([5,2,7,5,3,5,7,5,6,7], Bins).
   Bins = [0,1,1,0,4,1,3]
;  false.

?- nth1(2, [a,b,c,d,e], C, R).
   C = b, R = "acde".

%% samsort(+Ls0, Ls)
%
% See https://github.com/mthom/scryer-prolog/issues/1163#issuecomment-1006135163
% HT @triska
samsort(Ls0, Ls) :-
        same_length(Ls0, Pairs0), % https://github.com/mthom/scryer-prolog/issues/192
        pairs_keys(Pairs0, Ls0),
        keysort(Pairs0, Pairs),
        pairs_keys(Pairs, Ls).

?- samsort([4,2,4,2,3,5], SXs).
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

