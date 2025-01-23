% probdist.pl
% Probability distributions as partial goals

:- module(probdist, [
              runif/3, dunif/4, qunif/4, unif_q_p/4, runif/1,
              rnorm/3, dnorm/4, qnorm/4, norm_q_p/4, rnorm/1,
              rlognorm/3, dlognorm/4, qlognorm/4, lognorm_q_p/4,
              rexp/2, dexp/3, qexp/3, exp_q_p/3
              % Under development, not yet ready for export:
              % ,rpois/3, dpois/4, qpois/4, pois_k_p/4
              % Planned:
              % TODO: Beware name conflicts, e.g. with
              %       special_functions:gamma_P_Q/4!
              % ,rbeta/3, dbeta/4, qbeta/4, beta_q_p/4
              % ,rgamma/3, dgamma/4, qgamma/4, gamma_q_p/4
              % ,rinvgamma/3, dinvgamma/4, qinvgamma/4, invgamma_q_p/4
	  ]).

:- use_module(library(random)).
:- use_module(library(lists)).
:- use_module(library(error)).
:- use_module(library(lambda)).
:- use_module(library(clpz)).
:- use_module(library(numerics/special_functions)).

clpz:monotonic.

?- set_random(seed(2025)).
   true.

% We should be able to approximate R's well-established Distributions
% interface, although the ordering of args (as well as their default
% values) may need adaptation to the typical Prolog idioms.
%
% From R's help page ?dunif:
% --------------------------------------------------------------------
%% Usage:

%%      dunif(x, min = 0, max = 1, log = FALSE)
%%      punif(q, min = 0, max = 1, lower.tail = TRUE, log.p = FALSE)
%%      qunif(p, min = 0, max = 1, lower.tail = TRUE, log.p = FALSE)
%%      runif(n, min = 0, max = 1)
% --------------------------------------------------------------------
%
% For example, it seems most natural in Prolog to use partial goals to
% instantiate distributions with given parameters, and this requires
% us to move the parameters first.
%
% Most especially, however, the idiom of working-in-several-directions
% has obvious (and maybe _profound_) application here.  Most simply,
% we can unify the p<dist>, q<dist> and r<dist> functions under the
% aegis of a single <dist>_q_p predicate.  But the deeper potential
% for Bayesian inference on the distributional parameters from data
% (say, with Q argument being a list) seems worth exploring as well.

runif(A, B, X) :- unif_q_p(A, B, X, _). % dont-care P => draw a sample
runif(U) :- runif(0, 1, U).
% NB: The very triviality of these translations is the point!
dunif(A, B, X, P) :- unif_q_p(A, B, X, P). % dunif(A,B) : [A,B]-->[0,1]
qunif(A, B, P, X) :- unif_q_p(A, B, X, P). % qunif(A,B) : [0,1]-->[A,B]

%% unif_q_p(+A, +B, +Q, -P) yields the CDF P
%% unif_q_p(+A, +B, -Q, +P) yields the quantile Q
%% unif_q_p(+A, +B, -Q, -P) draws P ~ U[0,1], Q ~ U[A,B]
%
% Although overwrought per se, this implementation serves as a
% template for the nontrivial distributions below.
unif_q_p(A, B, Q, P) :-
    (   var(P) ->
        (   var(Q) -> random(P), unif_q_p(A, B, Q, P)
        ;   T is (Q - A)/(B - A),
            P is max(0, min(T, 1))
        )
    ;   must_be(var,Q),
        0 =< P, P =< 1, %TBD: can domain_error apply to floats?
        Q is A + (B-A)*P
    ).

?- unif_q_p(0, 10, Q, 0.23).
   Q = 2.3000000000000003.

?- unif_q_p(0, 10, 2.3, P).
   P = 0.22999999999999998.

?- unif_q_p(0, 10, Q, _).
   Q = 8.10900915381696.
   Q = 9.786948305034713.
   Q = 3.703330930961668.
   Q = 4.109197763705126.
   Q = 4.460102895071234.
   Q = 2.775912051234659.
   Q = 8.383827418645913.
   Q = 5.844769980350311.
   Q = 2.3607406052894486.

% -------------------- Normal --------------------

rnorm(Mu, Sigma, X) :- norm_q_p(Mu, Sigma, X, _).
rnorm(Z) :- rnorm(1, 0, Z).
dnorm(Mu, Sigma, X, P) :- norm_q_p(Mu, Sigma, X, P). % dnorm(Mu,Sigma) : ℝ → [0,1]
qnorm(Mu, Sigma, P, X) :- norm_q_p(Mu, Sigma, X, P). % qnorm(Mu,Sigma) : [0,1] → ℝ

?- erf(0.5, Erf).
   Erf = 0.5204998778130465.

?- erf(-0.5, Erf).
   Erf = -0.5204998778130465.

?- inverf(0.5205, Erfinv).
   Erfinv = 0.5000001390411746.

%% norm_q_p(+Mu, +Sigma, +Q, -P) yields the CDF P
%% norm_q_p(+Mu, +Sigma, -Q, +P) yields the quantile Q
%% norm_q_p(+Mu, +Sigma, -Q, -P) draws P ~ U[0,1], Q ~ N(Mean, SD)
%
% For ground Mu and Sigma, these various modes of norm_q_p/4 offer a
% unified interface to the Normal distribution.
norm_q_p(Mu, Sigma, Q, P) :-
    (   var(P) ->
        (   var(Q) -> random(P), norm_q_p(Mu, Sigma, Q, P)
        ;   Q_ is (Q - Mu)/sqrt(2*Sigma*Sigma),
            erf(Q_, Erf),
            P is (1 + Erf)/2
        )
    ;   must_be(var, Q),
        P_ is 2*P - 1,
        inverf(P_, Erfinv),
        Q is Mu + Sigma*sqrt(2)*Erfinv
    ).

?- norm_q_p(0, 1, 1.65, P).
   P = 0.9505285319663519.

?- norm_q_p(0, 1, Q, 0.95).
   Q = 1.6448536269514724.

?- norm_q_p(0, 1, Q, _).
   Q = 0.5737400857054019.
   Q = 1.834178622857291.
   Q = -0.3375860616265074.
   Q = -0.42389517755214.
   Q = 0.8468028856552989.

?- length(Qs, 10), maplist(norm_q_p(0, 1), Qs, _).
   Qs = [-0.8901070303146362,-1.6685438430081538,-1.1442368908003369,1.5092518739138532,-1.9538937275879835,0.02802546040576495,-0.2423579972120645,0.28459369501907034,0.18467399520799904,0.19012852831990895].

?- runif(0, 1, U).
   U = 0.6854498501154458.

?- runif(0, 100, X).
   X = 18.456504133332352.

?- runif(U).
   U = 0.35922687284121935.

?- maybe.
   true.
   false.
   true.
   false.
   true.
   true.
   false.

% -------------------- Lognormal --------------------

rlognorm(Mu, Sigma, X) :- lognorm_q_p(Mu, Sigma, X, _).
rlognorm(Z) :- rlnorm(1, 0, Z).
dlognorm(Mu, Sigma, X, P) :- lognorm_q_p(Mu, Sigma, X, P).
qlognorm(Mu, Sigma, P, X) :- lognorm_q_p(Mu, Sigma, X, P).

?- erf(0.5, Erf).
   Erf = 0.5204998778130465.

?- erf(-0.5, Erf).
   Erf = -0.5204998778130465.

?- inverf(0.5205, Erfinv).
   Erfinv = 0.5000001390411746.

%% lognorm_q_p(+Mu, +Sigma, +Q, -P) yields the CDF P
%% lognorm_q_p(+Mu, +Sigma, -Q, +P) yields the quantile Q
%% lognorm_q_p(+Mu, +Sigma, -Q, -P) draws P ~ U[0,1], Q ~ N(Mean, SD)
%
% For ground Mu and Sigma, these various modes of lognorm_q_p/4 offer
% a unified interface to the Lognormal distribution.
lognorm_q_p(Mu, Sigma, Q, P) :-
    (   var(P) ->
        (   var(Q) -> random(P), lognorm_q_p(Mu, Sigma, Q, P)
        ;   LogQ is log(Q),
            norm_q_p(Mu, Sigma, LogQ, P)
        )
    ;   must_be(var, Q),
        norm_q_p(Mu, Sigma, LogQ, P),
        Q is exp(LogQ)
    ).

% ------------------- Exponential -------------------

%% exp_q_p(+Rate, +Q, -P) the CDF : Q ↦ P = P(Q)
%% exp_q_p(+Rate, -Q, -P) draws Q ~ Expon(Rate) via P ~ U[0,1)
%% exp_q_p(+Rate, -Q, +P) the quantile function CDF⁻¹ : P ↦ Q = Q(P)
%
exp_q_p(Rate, Q, P) :-
    (   var(P) ->
        (   var(Q) -> random(P), exp_q_p(Rate, Q, P)
        ;   P is 1 - exp(-Rate*Q) % CDF
        )
    ;   must_be(var,Q),
        Q is -log(1 - P)/Rate % Quantile function
    ).

rexp(Rate, X) :- exp_q_p(Rate, X, _).
dexp(Rate, X, P) :- exp_q_p(Rate, X, P).
qexp(Rate, P, X) :- exp_q_p(Rate, X, P).

?- rexp(0.5, Δt).
   Δt = 2.8996122115440346.
   Δt = 2.9516288957770347.
   Δt = 0.03765519737105278.
   Δt = 1.3501997254779419.
   Δt = 0.5384090937489835.
   Δt = 1.6933931996260316.
   Δt = 4.076821738014785.
   Δt = 0.11148921192604783.
   Δt = 3.6039168731144624.
   Δt = 0.5991237334555809.
   Δt = 3.6055417155635294.
   Δt = 2.6431865877689176.

% --------------------- Poisson ---------------------

%% rpois(+Rate, -K) draws random K ~ Pois(Rate)
%
%HACK: A simple algorithm due to Knuth is used, as described at
%      https://en.wikipedia.org/wiki/Poisson_distribution#Computational_methods.
rpois(Rate, K) :-
    L is exp(-Rate),
    rpois_(L, 0, 1, K).
rpois_(L, K0, P_, K) :-
    random(U),
    P is P_ * U,
    (   P =< L -> K = K0
    ;   K1 is K + 1,
        rpois(L, K1, P, K)
    ).

?- rpois(2, K).
   error(instantiation_error,(is)/2).

dpois(Rate, K, P) :- pois_k_p(Rate, K, P). % dpois(λ) : ℕ → (0,1)
qpois(Rate, P, K) :- pois_k_p(Rate, K, P). % qpois(λ) : [0,1) → ℕ

%% pois_k_p(+Rate, +K, -P) yields the CDF P(K):ℕ → (0,1)
%% pois_k_p(+Rate, -K, +P) yields right-continuous K(P):[0,1) → ℕ
%% pois_k_p(+Rate, -K, -P) draws P ~ U[0,1], K ~ Pois(λ)
%
% For ground Rate (λ) parameter, these various modes of pois_k_p/4
% offer a unified interface to the Poisson distribution.
%
%TBD: Check that the limiting case λ = 0 is supported.
%
% (**) Interestingly, here is a case where inverting the CDF is _not_
%      our ticket to simulation!  Of course, this is an implementation
%      detail that we need not expose.  (OTOH, discrete distributions
%      might be distinct enough that we gain little practical benefit
%      from placing them on the Procrustean bed of our rubric for the
%      continuous distributions.)
pois_k_p(Rate, K, P) :-
    (   var(P) ->
        (   var(K) -> rpois(Rate, K), pois_k_p(Rate, K, P) % (**)
        ;   must_be(integer, K),
            must_be(not_less_than_zero, K),
            pois_cdf(Rate, K, P)
        )
    ;   must_be(var,K),
        % We are seeking the smallest integer K such that P(K) ≥ P.
        0 =< P, P =< 1,
        error(unimplemented, pois_k_p/3)
    ).

?- D is gcd(120, 52).
   D = 4.

pois_pmf(Rate, K, F) :- % probability mass function
    K1 is K + 1,
    log_gamma(K1, LnGammaK1),
    F is exp(K*log(Rate) - Rate - LnGammaK1).

pois_cdf(Rate, K, P) :-
    #K #>= 0, indomain(K),
    findall(J, (J in 0..K, indomain(J)), Js),
    maplist(pois_pmf(Rate), Js, Fs),
    foldl(\X^Y^Z^(Z is X + Y), Fs, 0, P).

