% enst.pl
% Evidently-no-safer-than relation and friends

:- module(enst, [
              % Pending https://github.com/mthom/scryer-prolog/issues/2547,
              % we cannot export some pretty operators.  Client modules may
              % however access these by explicit qualification, and assign
              % these operators locally.
              %% op(900, xfx, '≼'),
              %% op(900, xfx, '⋠'),
              %% op(900, xfx, '≽'),
              %% op(900, xfx, '≺'),
              %% op(900, xfx, '⊁'),
              join/3,
              meet/3,
              joinof/3,
              meetof/3,
              qs_int/2,
              po_qs_sorted/3,
              qs_maxs/2,
              qs_mins/2
	  ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(lambda)).
:- use_module(library(iso_ext)).
:- use_module(library(time)).
:- use_module(intlist).
:- use_module(tally).
:- use_module(freebase).
:- use_module(comprehension).
:- use_module(library(pairs)).

clpz:monotonic.

:- op(900, xfx, '≼').
:- op(900, xfx, '⋠').
:- op(900, xfx, '≽').

:- op(900, xfx, '≺').
:- op(900, xfx, '⊁').


% Impose global default for R here:
coefs(Qs, Ys, Hs) :- coefs(2, Qs, Ys, Hs).
etas_enc(Hs, HK) :- r_etas_enc(2, Hs, HK).

%?- [1/6,1/3] '≼' [1/6,0/0].
%@    false. % with R=1
%?- [1/6,1/3] '≼' [1/6,0/0].
%@    true. % with R=2

% Find the unique coefficients of ≼ᵣ-generators for given q ∈ Qᴰ.
coefs(R, Qs, Ys, Hs) :-
    #R #> 0,
    same_length(Qs, Ys), % allows usage (+R, -Qs, +Ys, +Hs)
    maplist(\Q^T^N^(Q = T/N), Qs, Ts, Ns),
    % We will set Ys = [γs] (of length D), with γᴅ being coef of ≼₁﹕ᵣ.
    % Our first D equations are simply that Ys is minus partial sums of Ts.
    intlist_negated(Ts, NegTs), intlist_partsums(NegTs, Ys),
    reverse(Ys, [YD|_]),
    % Our next set of equations is η₀ = ΣU - rΣTρ = ΣU + r·γᴅ,
    % and then recursively ηₖ = ηₖ₋₁ - nₖ for k in 1..D-1.
    % But an even simpler expression of this, which dispenses
    % altogether with the Us, is to reverse-partial-sum the Ns,
    % then add Yᴅ*(R+1)!
    reverse(Ns, Иs),
    intlist_partsums(Иs, ΣИs),
    reverse(ΣИs, ΞNs),
    #RhoR1 #= #YD * (#R + 1),
    maplist(sum_(RhoR1), ΞNs, Hs).

sum_(Z1, Z2, Sum) :- #Sum #= #Z1 + #Z2.
diff_(Z1, Z2, Diff) :- #Diff #= #Z1 - #Z2.

%?- coefs(1, [0/0,0/0,0/0], Ys, Hs).
%@    Ys = [0,0,0], Hs = [0,0,0].

%?- transform([0/0,0/0,0/0], [1/2,3/4,4/5], Ys, Hs).
%@    Ys = [-1,-4,-8], Hs = [-13,-15,-19]. % R=2
%@    Ys = [-1,-4,-8], Hs = [-5,-7,-11].   % R=1
%?- coefs(1, [1/2,3/4,4/5], Ys, Hs).
%@    Ys = [-1,-4,-8], Hs = [-5,-7,-11].

% I've now worked out in detail a unique transformation of pair
% Q1,Q2 ∈ Qᴰ into 2✕D parameters, *all* nonnegative iff Q1 ⊑ Q2.
transform(Q1s, Q2s, ΔHs, ΔOs) :-
    same_length(Q1s, Q2s),
    coefs(Q1s, H1s, O1s),
    coefs(Q2s, H2s, O2s),
    maplist(diff_, H2s, H1s, ΔHs),
    maplist(diff_, O2s, O1s, ΔOs).

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

#>(X, Y, Truth) :- clpz_t(X #> Y, Truth). % counterpart to clpz:(#<)/3

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


'≺'(Q1s, Q2s, Truth) :-
    if_((Q1s '≼' Q2s, dif(Q1s, Q2s)),
        Truth = true,
        Truth = false
        ).

'⋠'(Q1s, Q2s, Truth) :- '≼'(Q1s, Q2s, Falsity),
                        reif:non(Falsity, Truth).

'≽'(Q2s, Q1s, Truth) :-'≼'(Q1s, Q2s, Truth).

'≼'(Q1s, Q2s) :- '≼'(Q1s, Q2s, true).
'⋠'(Q1s, Q2s) :- '≼'(Q1s, Q2s, false).
'≽'(Q2s, Q1s) :- '≼'(Q1s, Q2s, true).

'≺'(Q1s, Q2s) :- '≺'(Q1s, Q2s, true).
'⊁'(Q2s, Q1s) :- '≺'(Q1s, Q2s, false).

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

meet_(Q1s, Q2s, Ys, Hs) :-
    same_length(Q1s, Q2s),
    coefs(Q1s, Y1s, H1s),
    coefs(Q2s, Y2s, H2s),
    mins(Y1s, Y2s, Ys),
    mins(H1s, H2s, Hs).

meet_(Q1s, Q2s, Qs) :- % 'formal meet'
    meet_(Q1s, Q2s, Ys, Hs),
    coefs(Qs, Ys, Hs).

%?- meet_([3/3,4/4], [4/6,0/0], M).
%@    M = [4/3,3/4]. % Not a valid tally!

% Let's try to find some very small examples!
meet_invalid(Q1, Q2, M) :-
    qs_d_nmax(Q1, D, Nmax),
    qs_d_nmax(Q2, D, Nmax),
    meet_(Q1, Q2, M),
    member(T/N, M),
    #T #> #N.

%?- meet_invalid(Q1, Q2, M).
%@    Q1 = [0/0,1/1], Q2 = [1/1,0/1], M = [1/0,0/1]
%@ ;  Q1 = [1/1,0/1], Q2 = [0/0,1/1], M = [1/0,0/1]
%@ ;  Q1 = [0/0,1/2], Q2 = [1/1,0/2], M = [1/0,0/2]
%@ ;  Q1 = [0/0,1/2], Q2 = [1/2,0/2], M = [1/0,0/2]
%@ ;  Q1 = [0/0,2/2], Q2 = [1/1,0/2], M = [1/0,1/2]
%@ ;  Q1 = [0/0,2/2], Q2 = [1/1,1/2], M = [1/0,1/2]
%@ ;  Q1 = [0/0,2/2], Q2 = [1/2,0/0], M = [1/0,1/2]
%@ ;  Q1 = [0/0,2/2], Q2 = [1/2,0/1], M = [1/0,1/2]
%@ ;  Q1 = [0/0,2/2], Q2 = [2/2,0/1], M = [2/1,0/1]
%@ ;  Q1 = [0/0,2/2], Q2 = [1/2,0/2], M = [1/0,1/2]
%@ ;  Q1 = [0/0,2/2], Q2 = [1/2,1/2], M = [1/0,1/2]
%@ ;  Q1 = [0/0,2/2], Q2 = [2/2,0/2], M = [2/0,0/2]
%@ ;  Q1 = [0/1,2/2], Q2 = [2/2,0/2], M = [2/1,0/2]
%@ ;  Q1 = [1/1,0/2], Q2 = [0/0,1/2], M = [1/0,0/2]
%@ ;  Q1 = [1/1,0/2], Q2 = [0/0,2/2], M = [1/0,1/2]
%@ ;  Q1 = [1/1,1/2], Q2 = [0/0,2/2], M = [1/0,1/2]
%@ ;  Q1 = [1/1,1/2], Q2 = [2/2,0/2], M = [2/1,0/2]
%@ ;  Q1 = [1/1,2/2], Q2 = [2/2,0/0], M = [2/1,1/2]
%@ ;  Q1 = [1/1,2/2], Q2 = [2/2,0/1], M = [2/1,1/2]
%@ ;  Q1 = [1/1,2/2], Q2 = [2/2,0/2], M = [2/1,1/2]
%@ ;  Q1 = [1/1,2/2], Q2 = [2/2,1/2], M = [2/1,1/2]
%@ ;  Q1 = [1/2,0/0], Q2 = [0/0,2/2], M = [1/0,1/2]
%@ ;  Q1 = [2/2,0/0], Q2 = [1/1,2/2], M = [2/1,1/2]
%@ ;  Q1 = [1/2,0/1], Q2 = [0/0,2/2], M = [1/0,1/2]
%@ ;  Q1 = [2/2,0/1], Q2 = [0/0,2/2], M = [2/1,0/1]
%@ ;  Q1 = [2/2,0/1], Q2 = [1/1,2/2], M = [2/1,1/2]
%@ ;  Q1 = [1/2,0/2], Q2 = [0/0,1/2], M = [1/0,0/2]
%@ ;  Q1 = [1/2,0/2], Q2 = [0/0,2/2], M = [1/0,1/2]
%@ ;  Q1 = [1/2,1/2], Q2 = [0/0,2/2], M = [1/0,1/2]
%@ ;  Q1 = [2/2,0/2], Q2 = [0/0,2/2], M = [2/0,0/2]
%@ ;  Q1 = [2/2,0/2], Q2 = [0/1,2/2], M = [2/1,0/2]
%@ ;  Q1 = [2/2,0/2], Q2 = [1/1,1/2], M = [2/1,0/2]
%@ ;  Q1 = [2/2,0/2], Q2 = [1/1,2/2], M = [2/1,1/2]
%@ ;  Q1 = [2/2,1/2], Q2 = [1/1,2/2], M = [2/1,1/2]
%@ ;  Q1 = [0/0,0/0,1/1], Q2 = [0/0,1/1,0/1], M = [0/0,1/0,0/1]
%@ ;  Q1 = [0/0,0/0,1/1], Q2 = [1/1,0/0,0/1], M = [1/0,0/0,0/1]
%@ ;  Q1 = [0/0,0/0,1/1], Q2 = [1/1,0/1,0/0], M = [1/0,0/1,0/0]
%@ ;  Q1 = [0/0,0/0,1/1], Q2 = [0/1,1/1,0/1], M = [0/0,1/0,0/1]
%@ ;  Q1 = [0/0,0/0,1/1], Q2 = [1/1,0/1,0/1], M = [1/0,0/0,0/1]
%@ ;  Q1 = [0/0,1/1,0/0], Q2 = [1/1,0/0,0/1], M = [1/0,0/1,0/0]
%@ ;  ... . % Exactly the kind of near-the-origin search I'd hoped for!

% So we now have some very simple examples of tally pairs
% that do not have a valid meet.

% Unlike meet_/3, which allows for 'imaginary' meets,
% this predicate succeeds only if a valid meet obtains.
meet(Q1s, Q2s, Qs) :-
    meet_(Q1s, Q2s, Qs),
    maplist(\Q^(Q=T/N, #T #=< #N), Qs).

join(Q1s, Q2s, Ys, Hs) :-
    same_length(Q1s, Q2s),
    coefs(Q1s, Y1s, H1s),
    coefs(Q2s, Y2s, H2s),
    maxs(Y1s, Y2s, Ys),
    maxs(H1s, H2s, Hs).

% NB: If, as I believe, 𝒬 = (Qᴰ,≼) is an upper semilattice,
%     then these joins will always exist and are unique.
join(Q1s, Q2s, Qs) :-
    join(Q1s, Q2s, Ys, Hs),
    coefs(Qs, Ys, Hs).

:- meta_predicate(joinof(?, 0, ?)).
:- meta_predicate(meetof(?, 0, ?)).

joinof(X, Goal, J) :- reduce(join, X, Goal, J).
meetof(X, Goal, M) :- reduce(meet, X, Goal, M).

% ---------- Embedding 𝒬 ↪ (ℕ,≤) ----------

qs_int(Qs, K) :-
    coefs(Qs, Ys, Hs),
    gammas_enc(Ys, YK),
    etas_enc(Hs, HK),
    same_length(Ys, _s), placevalues([P|_s]),
    #K #= #HK * #P + #YK.

%?- qs_int([1/1,2/3], K).
%@    K = -17403.

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
%@    % CPU time: 10.157s, 50_278_434 inferences
%@    false.
%?- time(d_nmax_wrongway(2, 4, Q1, Q2)).
%@    % CPU time: 48.824s, 255_477_892 inferences
%@    false.
%?- time(d_nmax_wrongway(2, 5, Q1, Q2)).
%@    % CPU time: 193.112s, 978_666_671 inferences
%@    false.
%?- time(d_nmax_wrongway(2, 6, Q1, Q2)).
%@    % CPU time: 614.967s, 3_077_569_171 inferences
%@    false.
%?- time(d_nmax_wrongway(3, 1, Q1, Q2)).
%@    % CPU time: 0.922s, 4_783_641 inferences
%@    false.
%?- time(d_nmax_wrongway(3, 2, Q1, Q2)).
%@    % CPU time: 56.801s, 301_275_822 inferences
%@    false.
%?- time(d_nmax_wrongway(3, 3, Q1, Q2)).
%@    % CPU time: 1147.127s, 4_811_099_116 inferences
%@    false.

% ---------- Sorting ----------

po_qs_sorted('≼', Qs, AscQs) :-
    maplist(qs_int, Qs, Ks),
    pairs_keys_values(KQs, Ks, Qs),
    sort(KQs, SKQs),
    pairs_values(SKQs, AscQs).

po_qs_sorted('≽', Qs, DescQs) :-
    po_qs_sorted('≼', Qs, AscQs),
    reverse(AscQs, DescQs).

% ---------- Maximal & Minimal sets ----------

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

