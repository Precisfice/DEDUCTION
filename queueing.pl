% Exploring idioms for modeling arrivals processes and their servicing

:- use_module(library(random)).
:- use_module(library(error)).
:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(lambda)).

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
