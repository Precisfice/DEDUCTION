% Exploring idioms for modeling arrivals processes and their servicing

:- use_module(library(random)).
:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(lambda)).
:- use_module(library(dif)).
:- use_module(library(pairs)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(debug)).
:- use_module(library(format)).

clpz:monotonic.

:- use_module(probdist).
:- use_module(intlist).
:- use_module(tally).
:- use_module(cascade).
:- use_module(run33).

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

?- phrase(poisson_arrival_times(0.5, 100), [T1,T2,T3]).
   T1 = 100.11587652773626, T2 = 101.69887792696088, T3 = 102.37692287870219
;  false.
   T1 = 100.09816887003277, T2 = 101.6810724566522, T3 = 104.13660078747704
;  false.
   T1 = 102.48350649365024, T2 = 105.24997093111844, T3 = 106.39690116093654
;  false.

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


round(D, R, Rd) :- Rd is round(10^D*R)/10^D.

?- round(3, pi, Pi).
   Pi = 3.142.

% TODO: Should I make a meta_predicate declaration?
arrivals(Rate, MTD_2) --> arrivals(Rate, MTD_2, 0.0).
arrivals(_, _, _) --> [].
arrivals(Rate, MTD_1, T) --> [T1 - arr(MTDi)],
                             { rexp(Rate, Δt), T1_ is T + Δt,
                               call(MTD_1, MTDi_),
                               % Rounding is just a convenience for testing,
                               % as it yields less noisy answer descriptions.
                               round(4, T1_, T1),
                               round(2, MTDi_, MTDi)
                             },
                             arrivals(Rate, MTD_1, T1).

?- length(Arrivals, 4), phrase(arrivals(0.5, rlognorm(log(6), log(2))), Arrivals).
   Arrivals = [7.3401-arr(10.94),8.9332-arr(19.19),9.9591-arr(6.64),10.9729-arr(4.61)]
;  false.

?- d_joinscascade(3, Gs).
   Gs = [[0/3,0/6,0/0],[0/6,0/0,0/0],[2/6,0/0,0/0]]. % (**)

%% reclD3(+Q, -Rx) is det
%
% A dose-recommendation function implementing a lower-Galois
% rectification of the 3+3 protocol for D = 3.
reclD3(Q, Rx) :-
    Gs = [[0/3,0/6,0/0],[0/6,0/0,0/0],[2/6,0/0,0/0]], % see above (**)
    cascade_tally_ladjoint(Gs, Q, Rx).

?- d_init(3, Init), reclD3(Init, Rx1).
   Init = [0/0,0/0,0/0], Rx1 = 1.

?- findall(N, (N in 0..10, indomain(N), reclD3([0/N,0/0,0/0], 2)), Ns).
   Ns = [7,8,9].

?- reclD3([0/10,0/0,0/0], Rx1).
   Rx1 = 3. % A consequence of R=2?

/*
?- Next+\((d_init(3,Q0), length(Arrivals, 40), set_random(seed(2025)),
           phrase(arrivals(0.5, rlognorm(log(6), log(2))), Arrivals),
           phrase(rolling(reclD3, Q0, [], Arrivals), Events),
           phrase((... , [next(Next)]), Events))).
   Next = 3
;  false.
*/

% Now, at long last, we need a queue servicing function that takes a
% current trial state to a new one upon admitting a new participant.
% Of course, this requires that we specify what this state is!

%% rolling(Rec_2, Q, Ws, As)//4
%
% Describes events of a rolling-enrollment trial defined by the
% dose-recommendation rule Rec_2, given a current state consisting of:
% - Q ∈ 𝒬, a realized tally from assessments completed up to now
% - Ws, a queue of enrolled participants Waiting for dose assignments
% - As, a keysort/2-ed list of Time-A for future Arrivals/Assessments:
%   - Arrivals are denoted arr(MTD)
%   - Assessments are denoted ao(d) or ax(d).
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
%
% TODO: Ideally, this would be condensed & formatted to fit on 1 page
%       of the monograph -- or at most two facing pages.
%%%%rolling(_, _, _, _) --> []. % 'stepper' for debugging
% Note that we terminate with next(Rx), leaving aside the question of
% whether this next-dose recommendation should be called an RP2D, as
% indeed there remains some question whether 'RP2D' is even a coherent
% concept.  (The point here is to define an incremental enrollment in
% abstraction from trial-termination questions.)
rolling(Rec_2, Q,    [], []) --> { call(Rec_2, Q, Rx) }, [next(Rx)].
rolling(Rec_2, Q, [_|_], []) --> { call(Rec_2, Q, 0)  }, [next(0)].
rolling(Rec_2, Q,     [], [now(_)|As]) --> rolling(Rec_2, Q, [], As).
rolling(Rec_2, Q, [W|Ws], [now(_)|As]) --> { rec(Rec_2, Q, As, 0) },
                                           rolling(Rec_2, Q, [W|Ws], As).
rolling(Rec_2, Q, [MTD|Ws], [now(Z)|As]) -->
    { rec(Rec_2, Q, As, Rx), Rx > 0 },
    dose(dequeue(Z,MTD,Rx), As, As1),
    rolling(Rec_2, Q, Ws, [now(Z)|As1]).
rolling(Rec_2, Q, Ws, [Z-arr(MTD)|As]) -->
    { rec(Rec_2, Q, As, 0) },
    enqueue(Z, MTD, Ws, Ws1),
    rolling(Rec_2, Q, Ws1, As).
rolling(Rec_2, Q, [], [Z-arr(MTD)|As]) -->
    { rec(Rec_2, Q, As, Rx), Rx > 0 },
    dose(enroll(Z,MTD,Rx), As, As1),
    rolling(Rec_2, Q, [], As1).
rolling(Rec_2, Q, Ws, [Z-ax(Dose)|As]) -->
    tallyx(Z, Q, Dose, Q1),
    rolling(Rec_2, Q1, Ws, As).
rolling(Rec_2, Q, [], [Z-ao(Dose)|As]) -->
    tallyo(Z, Q, Dose, Q1),
    rolling(Rec_2, Q1, [], As).
rolling(Rec_2, Q, [W|Ws], [Z-ao(Dose)|As]) -->
    tallyo(Z, Q, Dose, Q1),
    rolling(Rec_2, Q1, [W|Ws], [now(Z)|As]).

enqueue(Z, MTD, Ws, Ws1) --> { append(Ws, [MTD], Ws1) },
                             [enqueue(Z,MTD)].

dose(Event, As, As1) --> { Event =.. [_, Z, MTD, Rx],
                           (   MTD <  Rx, A = ax(Rx), Za is Z + MTD/Rx
                           ;   MTD >= Rx, A = ao(Rx), Za is Z + 1.0
                           ),
                           sched(As, Za-A, As1) },
                         [Event].

sched(As, Za-A, As1) :- keysort([Za-A|As], As1).

tallyo(Z, Q, Dose, Q1) --> { tallyo(Q, Dose, Q1) }, [o(Z,Dose)].
tallyx(Z, Q, Dose, Q1) --> { tallyx(Q, Dose, Q1) }, [x(Z,Dose)].

%% rec(+Rec_2, +Q, +As, -Rx)
%
% Given dose-recommendation rule Rec_2 : 𝒬 → 0..D, a realized tally Q,
% and list As that includes pending assessments of the form Z-a_(Dose)
% (where Z > 0 is a time, and a_ is ax or ao), Rx is the recommended
% dose based on a 'pessimistic' tally assuming all pending assessments
% will resolve as toxicities.
rec(Rec_2, Q, As, Rx) :-
    tally_pending_pesstally(Q, As, Qp),
    call(Rec_2, Qp, Rx).

% TODO: Basic tally-arithmetic predicates belong in tally.pl!
%       But let's hold off defining these there, until we see
%       how the construction of a 'pessimistic' tally works.

% Implementing the monoidal (+)/3 operation on 𝒬 might serve me best!
% Can we define that in a syncactically appealing way?

%% tally_pending_pesstally(+Q, +As, -Qp)
%
% Given the current tally Q and As, a [Time-A|_] pairlist of upcoming
% events, Qp is the 'pessimistic' tally obtaining in the worst-case
% scenario where all pending assessments in As turn out as toxicities.
tally_pending_pesstally(Q, As, Qp) :-
    findall(Dose, (member(_-A, As), member(A, [ao(Dose), ax(Dose)])), Ps),
    same_length(Q, Ns),
    posints_bins(Ps, Ns),
    qs_ts_ns(ΔQ, Ns, Ns),
    qsum_(Q, ΔQ, Qp).

?- tally_pending_pesstally([0/3,2/3], [0.1-ax(2), 0.3-arr(4.5), 0.5-ao(1)], Qp).
   Qp = [1/4,3/4]
;  false.

