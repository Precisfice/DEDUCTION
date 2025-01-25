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
rolling(Rec_2, Q, Rx, Ws, [Z-arr(MTD)|As]) -->
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
rolling(Rec_2, Q, Rx, [], [Z-arr(MTD)|As]) -->
    { Rx > 0,
      (   MTD <  Rx, A = ax(Rx), Za is Z + MTD/Rx
      ;   MTD >= Rx, A = ao(Rx), Za is Z + 1.0
      ),
      % Although `Za is min(MTD/Rx, 1.0)` would yield Za in one go,
      % the elementary branches above seem clearer.
      sched(As, Za-A, As1),
      tally_pending_pesstally(Q, As1, Qp),
      call(Rec_2, Qp, Rx1)
    },
    [enroll(Z,MTD)],
    rolling(Rec_2, Q, Rx1, [], As1).
rolling(Rec_2, Q, Rx, Ws, [Z-ax(Dose)|As]) -->
    {
        tallyx(Q, Dose, Q1),
        % Tallying an 'x' has no effect on Qpess,
        % and therefore leaves Rx unchanged.
        tally_pending_pesstally(Q, As, Qp),
        call(Rec_2, Qp, Rx1)
    },
    [x(Dose)],
    rolling(Rec_2, Q1, Rx1, Ws, As).
rolling(Rec_2, Q, Rx, Ws, [Z-ao(Dose)|As]) -->
    {
        tallyo(Q, Dose, Q1),
        % Tallying an 'o' DOES affect Qpess,
        % so Rx may have changed, and requires
        % recalculation.
        tally_pending_pesstally(Q1, As, Q1p),
        call(Rec_2, Q1p, Rx1)
    },
    [o(Dose)],
    rolling(Rec_2, Q1, Rx1, Ws, As).

% TODO: Basic tally-arithmetic predicates belong in tally.pl!
%       But let's hold off defining these there, until we see
%       how the construction of a 'pessimistic' tally works.

% Implementing the monoidal (+)/3 operation on 𝒬 might serve me best!
% Can we define that in a syncactically appealing way?

%% qsum_(?Q0s, ?ΔQs, ?Qs)
%
% Akin to clpz:max_, but taking Q0s, ΔQs, Qs ∈ 𝒬 as arguments, so that
% Qs = Q0s + ΔQs, '+' here being the 𝒬's symmetric monoidal operation.
%
% TODO: Since this aims to extend declarative integer arithmetic to 𝒬,
%       we might do well to pursue this more vigorously, including to
%       the full MGQ, with attention to fair enumeration, etc.
qsum_(Q0s, ΔQs, Qs) :-
    same_length(Q0s, ΔQs), % Needed for
    same_length(Q0s, Qs),  % termination
    qs_ts_ns(Q0s, T0s, N0s),
    qs_ts_ns(ΔQs, ΔTs, ΔNs),
    qs_ts_ns(Qs, Ts, Ns),
    maplist(sum_, T0s, ΔTs, Ts),
    maplist(sum_, N0s, ΔNs, Ns).

sum_(X, Y, Z) :- #Z #= #X + #Y.

?- qsum_([0/1,1/1], [0/0,0/1], Qs).
   Qs = [0/1,1/2].

%% d_x_qs(+D, +X, -Qs)
%
% X in 1..D and Qs = <1/1>ₓ per Notation 2.5 of the monograph.  That
% is, Qs is a length-D list of 0/0 *except* that nth1(X, Qs, 1/1).
d_x_qs(D, X, Qs) :-
    0 #< #X, #X #=< #D,
    length(Qs, D),
    qs_ts_ns(Qs, Ns, Ns),
    d_unitvec_x(D, X, Ns),
    % Now we just need Ns as a 'unit vector' in X direction
    false.

d_unitvec_x(D, O1s, X) :-
    length(O1s, D),
    0 #< #X, #X #< D,
    countup(D, Ix),
    maplist(=(X), Ix, TFs), % NB: this is reif:(=)/3
    maplist(clpz:zo_t, O1s, TFs).

?- d_unitvec_x(5, O1s, 2).
   O1s = [0,1,0,0,0].

% TODO: Use this instead, wherever I've done a findall/3,
%       to obtain this kind of sequence.
countup(N, Ns) :- N > 0, countup_(N, [], Ns).
countup_(M, Ns, Ns_) :-
    M > 1, M_ is M - 1,
    countup_(M_, [M|Ns], Ns_).
countup_(1, Ns, [1|Ns]).

?- countup(5, Ns).
   Ns = [1,2,3,4,5].

tallyx(Q, Dose, Q1) :-
    length(Q, D),
    d_unitvec_x(D, Ns, Dose),
    qs_ts_ns(ΔQ, Ns, Ns),
    qsum_(Q, ΔQ, Q1).
tallyo(Q, Dose, Q1) :-
    length(Q, D),
    d_unitvec_x(D, Ns, Dose),
    same_length(Q, Ts),
    maplist(=(0), Ts),
    qs_ts_ns(ΔQ, Ts, Ns),
    qsum_(Q, ΔQ, Q1).

?- Q = [0/3,0/3,2/3], tallyo(Q, 2, Qo), tallyx(Q, 2, Qx). 
   Q = [0/3,0/3,2/3], Qo = [0/3,0/4,2/3], Qx = [0/3,1/4,2/3].

sched(As, Za-A, As1) :- keysort([Za-A|As], As1).

%% tally_pending_pesstally(+Q, +As, -Qp)
%
% Given the current tally Q and As, a [Time-A|_] pairlist of upcoming
% events, Qp is the 'pessimistic' tally obtaining in the worst-case
% scenario where all pending assessments in As turn out as toxicities.
tally_pending_pesstally(Q, As, Qp) :-
    findall(Dose, (member(Z-A, As), member(A, [ao(Dose), ax(Dose)])), Ps),
    same_length(Q, Ns),
    posints_bins(Ps, Ns),
    qs_ts_ns(ΔQ, Ns, Ns),
    qsum_(Q, ΔQ, Qp).

?- tally_pending_pesstally([0/3,2/3], [0.1-ax(2), 0.3-arr(4.5), 0.5-ao(1)], Qp).
   Qp = [1/4,3/4]
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

