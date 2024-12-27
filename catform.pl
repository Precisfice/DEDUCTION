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

reduce(P_3, [X|Xs], R) :- foldl(P_3, Xs, X, R).
reduce(P_3, X, Goal, R) :-
    setof(X, Goal, Xs),
    reduce(P_3, Xs, R).

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
:- op(900, xfx, '⋠'). % d_starts1/1 uses '⋠'/2
:- op(900, xfx, '≽').

:- op(900, xfx, '≺'). % in_cover_t/4 uses '≺'/2 and between_t/4 uses '≺'/3
:- op(900, xfx, '⊁'). % minimal_in/2 uses '⊁'/2

q_r(T/N, T:U) :- 0 #=< #T, 0 #=< #U, #N #= #T + #U.

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

maxs(N1s, N2s, Ns) :- maplist(\N1^N2^N^(#N #= max(#N1, #N2)), N1s, N2s, Ns).
mins(N1s, N2s, Ns) :- maplist(\N1^N2^N^(#N #= min(#N1, #N2)), N1s, N2s, Ns).

%?- maxs([1,2,6], [3,4,5], Maxs).
%@    Maxs = [3,4,6].
%?- mins([1,2,6], [3,4,5], Mins).
%@    Mins = [1,2,5].

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
    Nmax in 0..3, indomain(Nmax),
    N1 in 0..Nmax, indomain(N1),
    N2 in 0..Nmax, indomain(N2),
    qs_d_nmax(Q1, 2, N1),
    qs_d_nmax(Q2, 2, N2),
    meet_(Q1, Q2, M),
    member(T/N, M),
    #T #> #N.

%?- meet_invalid(Q1, Q2, M).
%@    Q1 = [0/0,1/1], Q2 = [1/1,0/1], M = [1/0,0/1]
%@ ;  Q1 = [1/1,0/1], Q2 = [0/0,1/1], M = [1/0,0/1]
%@ ;  Q1 = [0/0,1/1], Q2 = [1/1,0/1], M = [1/0,0/1]
%@ ;  Q1 = [1/1,0/1], Q2 = [0/0,1/1], M = [1/0,0/1]
%@ ;  Q1 = [0/0,1/1], Q2 = [1/1,0/1], M = [1/0,0/1]
%@ ;  Q1 = [0/0,1/1], Q2 = [1/1,0/2], M = [1/0,0/1]
%@ ;  ... . % Well, that's more like it!

% So we now have some very simple examples of tally pairs
% that do not have a valid meet.

%?- transform([1/1,1/1], [0/0,1/1], Ys, Hs).
%@    Ys = [1,1], Hs = [2,3].
%?- transform([1/1,1/1], [1/1,0/1], Ys, Hs).
%@    Ys = [0,1], Hs = [3,3].
%?- transform([1/1,1/1], M, [0,1], [2,3]).
%@    M = [1/0,0/1].

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
/*
d_endtally_rec(D, FinalTally, Rec) :-
    length(Init, D), maplist(=(0/0), Init), Init = [I|Is],
    phrase(path([I]-Is), Path),
    phrase((..., [Endstate,stop,recommend_dose(Rec)]), Path),
    state_tallies(Endstate, FinalTally).
*/
d_endtally_rec(D, FinalTally, Rec) :-
    d_tally_nextdose_final(D, FinalTally, Rec, true).

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

% To encode the γs, we can reuse existing infrastructure, as-is
gammas_enc(Ys, K) :- ws_int(Ys, K).

% To encode ηs, we need only encode a base-(6*D*(R+1)+1) integer.
% (Note that we need not even insist on non-negative 'digits',
% since any bias in a given digit will bias the whole encoding
% consistently, with no effect on the _order_.)
r_etas_enc(R, Hs, K) :-
    r_etas_base(R, Hs, B),
    foldl(base_(B), Hs, 0, K).

r_etas_base(R, Hs, B) :-
    #R #> 0, length(Hs, D),
    #B #= 6 * #D * (#R+1) + 1.

base_(B, A, N0, N) :- #N #= #B * #N0 + #A.

%?- foldl(base_(10), [1,2,3,4], 0, N).
%@    N = 1234.

%?- Hs = [18,12,6], r_etas_enc(1, Hs, K).
%@    Hs = [18,12,6], K = 25092.

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
    po_qs_sorted('≽', Qs, SQs).

po_qs_sorted('≼', Qs, AscQs) :-
    maplist(qs_int, Qs, Ks),
    pairs_keys_values(KQs, Ks, Qs),
    sort(KQs, SKQs),
    pairs_values(SKQs, AscQs).
    
po_qs_sorted('≽', Qs, DescQs) :-
    po_qs_sorted('≼', Qs, AscQs),
    reverse(AscQs, DescQs).
    

%?- D=2, Nmax=3, L+\(findall(Q, qs_d_nmax(Q, D, Nmax), Qs), po_qs_sorted('≽', Qs, SQs), length(SQs, L)).
%@    D = 2, Nmax = 3, L = 100.
%?- D=2, Nmax=6, L+\(findall(Q, qs_d_nmax(Q, D, Nmax), Qs), po_qs_sorted('≽', Qs, SQs), length(SQs, L)).
%@    D = 2, Nmax = 6, L = 784.
%?- D=3, Nmax=6, L+\(findall(Q, qs_d_nmax(Q, D, Nmax), Qs), po_qs_sorted('≽', Qs, SQs), length(SQs, L)).
%@    D = 3, Nmax = 6, L = 21952.

%?- D=2, L+\(d_sortedQfs(D, SQs), length(SQs, L)).
%@    D = 2, L = 29.

%?- D=3, L+\(d_sortedQfs(D, SQs), length(SQs, L)).
%@    D = 3, L = 93.

%?- D=4, L+\(d_sortedQfs(D, SQs), length(SQs, L)).
%@    D = 4, L = 261.

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
%@ [[0/3,0/6]].
%@ [[0/3,1/6],[1/6,0/6]].
%@ [[0/6,2/6]].
%@ [[0/6,2/3],[1/6,1/6]].
%@ [[2/6,0/0],[0/6,3/6]].
%@ [[2/3,0/0],[0/6,3/3],[1/6,2/6]].
%@ [[0/6,4/6],[1/6,2/3]].
%@ [[3/6,0/0],[1/6,3/6]].
%@ [[3/3,0/0],[1/6,3/3],[2/6,2/6]].
%@ [[1/6,4/6],[2/6,2/3]].
%@ [[4/6,0/0],[2/6,3/6]].
%@ [[2/6,3/3],[3/6,2/6]].
%@ [[2/6,4/6],[3/6,2/3]].
%@ [[3/6,3/6]].
%@ [[3/6,3/3]].
%@ [[3/6,4/6]].
%@    S = 16.

%?- S+\(d_strata(3, Qss), maplist(portray_clause, Qss), length(Qss, S)).
%@ [[0/3,0/3,0/6]].
%@ [[0/3,0/3,1/6],[0/3,1/6,0/6]].
%@ [[0/3,0/6,2/6],[1/6,0/3,0/6]].
%@ [[0/3,0/6,2/3],[0/3,1/6,1/6],[1/6,1/6,0/6]].
%@ [[0/6,2/6,0/0],[0/3,0/6,3/6],[1/6,0/3,1/6]].
%@ [[0/6,2/3,0/0],[0/3,0/6,3/3],[0/3,1/6,2/6],[1/6,0/6,2/6]].
%@ [[2/6,0/0,0/0],[0/3,0/6,4/6],[0/3,1/6,2/3],[0/6,2/6,2/6],[1/6,0/6,2/3],[1/6,1/6,1/6]].
%@ [[2/3,0/0,0/0],[0/6,3/6,0/0],[0/3,1/6,3/6],[1/6,0/6,3/6]].
%@ [[0/6,3/3,0/0],[0/3,1/6,3/3],[0/6,2/6,2/3],[1/6,0/6,3/3],[1/6,2/6,0/0],[1/6,1/6,2/6]].
%@ [[0/6,4/6,0/0],[1/6,2/3,0/0],[0/3,1/6,4/6],[0/6,2/6,3/6],[1/6,0/6,4/6],[1/6,1/6,2/3]].
%@ [[3/6,0/0,0/0],[0/6,2/6,3/3],[1/6,3/6,0/0],[0/6,3/6,2/6],[1/6,1/6,3/6]].
%@ [[3/3,0/0,0/0],[1/6,3/3,0/0],[0/6,2/6,4/6],[0/6,3/6,2/3],[1/6,1/6,3/3],[2/6,2/6,0/0],[1/6,2/6,2/6]].
%@ [[2/6,2/3,0/0],[0/6,3/6,3/6],[1/6,1/6,4/6],[1/6,2/6,2/3]].
%@ [[4/6,0/0,0/0],[0/6,3/6,3/3],[1/6,4/6,0/0],[1/6,2/6,3/6]].
%@ [[0/6,3/6,4/6],[1/6,2/6,3/3],[2/6,3/6,0/0],[1/6,3/6,2/6]].
%@ [[2/6,3/3,0/0],[1/6,2/6,4/6],[1/6,3/6,2/3],[3/6,2/6,0/0],[2/6,2/6,2/6]].
%@ [[3/6,2/3,0/0],[1/6,3/6,3/6],[2/6,2/6,2/3]].
%@ [[1/6,3/6,3/3],[2/6,4/6,0/0],[2/6,2/6,3/6]].
%@ [[1/6,3/6,4/6],[2/6,2/6,3/3],[3/6,3/6,0/0],[2/6,3/6,2/6]].
%@ [[3/6,3/3,0/0],[2/6,2/6,4/6],[2/6,3/6,2/3],[3/6,2/6,2/6]].
%@ [[2/6,3/6,3/6],[3/6,2/6,2/3]].
%@ [[2/6,3/6,3/3],[3/6,4/6,0/0],[3/6,2/6,3/6]].
%@ [[2/6,3/6,4/6],[3/6,2/6,3/3],[3/6,3/6,2/6]].
%@ [[3/6,2/6,4/6],[3/6,3/6,2/3]].
%@ [[3/6,3/6,3/6]].
%@ [[3/6,3/6,3/3]].
%@ [[3/6,3/6,4/6]].
%@    S = 27.

% Write out Hasse diagram as (GraphViz) DOT file.
d_writehassedot(D) :-
    phrase(format_("HasseD~d.dot", [D]), Filename),
    atom_chars(File, Filename),
    format("Opening file ~q...~n", [File]), % feedback to console
    setup_call_cleanup(open(File, write, OS),
		       (   format("Collecting final tallies ..", []),
                           % NB: We use _unrectified_ d_endtally_rec/3 to exhibit
                           %     the non-functoriality of default 3+3 dose recs.
                           setof(Q-X, d_endtally_rec(D,Q,X), QXs),
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

%?- d_writehassedot(2).
%@ Opening file 'HasseD2.dot'...
%@ Collecting final tallies ..
%@  sorting 29 final tallies ..
%@  stratifying ..
%@ [[0/3,0/6]].
%@ [[0/3,1/6],[1/6,0/6]].
%@ [[0/6,2/6]].
%@ [[0/6,2/3],[1/6,1/6]].
%@ [[2/6,0/0],[0/6,3/6]].
%@ [[2/3,0/0],[0/6,3/3],[1/6,2/6]].
%@ [[0/6,4/6],[1/6,2/3]].
%@ [[3/6,0/0],[1/6,3/6]].
%@ [[3/3,0/0],[1/6,3/3],[2/6,2/6]].
%@ [[1/6,4/6],[2/6,2/3]].
%@ [[4/6,0/0],[2/6,3/6]].
%@ [[2/6,3/3],[3/6,2/6]].
%@ [[2/6,4/6],[3/6,2/3]].
%@ [[3/6,3/6]].
%@ [[3/6,3/3]].
%@ [[3/6,4/6]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 6.579s, 34_157_755 inferences
%@ .. done.
%@    true.

%?- d_writehassedot(3).
%@ Opening file 'HasseD3.dot'...
%@ Collecting final tallies ..
%@  sorting 93 final tallies ..
%@  stratifying ..
%@ [[0/3,0/3,0/6]].
%@ [[0/3,0/3,1/6],[0/3,1/6,0/6]].
%@ [[0/3,0/6,2/6],[1/6,0/3,0/6]].
%@ [[0/3,0/6,2/3],[0/3,1/6,1/6],[1/6,1/6,0/6]].
%@ [[0/6,2/6,0/0],[0/3,0/6,3/6],[1/6,0/3,1/6]].
%@ [[0/6,2/3,0/0],[0/3,0/6,3/3],[0/3,1/6,2/6],[1/6,0/6,2/6]].
%@ [[2/6,0/0,0/0],[0/3,0/6,4/6],[0/3,1/6,2/3],[0/6,2/6,2/6],[1/6,0/6,2/3],[1/6,1/6,1/6]].
%@ [[2/3,0/0,0/0],[0/6,3/6,0/0],[0/3,1/6,3/6],[1/6,0/6,3/6]].
%@ [[0/6,3/3,0/0],[0/3,1/6,3/3],[0/6,2/6,2/3],[1/6,0/6,3/3],[1/6,2/6,0/0],[1/6,1/6,2/6]].
%@ [[0/6,4/6,0/0],[1/6,2/3,0/0],[0/3,1/6,4/6],[0/6,2/6,3/6],[1/6,0/6,4/6],[1/6,1/6,2/3]].
%@ [[3/6,0/0,0/0],[0/6,2/6,3/3],[1/6,3/6,0/0],[0/6,3/6,2/6],[1/6,1/6,3/6]].
%@ [[3/3,0/0,0/0],[1/6,3/3,0/0],[0/6,2/6,4/6],[0/6,3/6,2/3],[1/6,1/6,3/3],[2/6,2/6,0/0],[1/6,2/6,2/6]].
%@ [[2/6,2/3,0/0],[0/6,3/6,3/6],[1/6,1/6,4/6],[1/6,2/6,2/3]].
%@ [[4/6,0/0,0/0],[0/6,3/6,3/3],[1/6,4/6,0/0],[1/6,2/6,3/6]].
%@ [[0/6,3/6,4/6],[1/6,2/6,3/3],[2/6,3/6,0/0],[1/6,3/6,2/6]].
%@ [[2/6,3/3,0/0],[1/6,2/6,4/6],[1/6,3/6,2/3],[3/6,2/6,0/0],[2/6,2/6,2/6]].
%@ [[3/6,2/3,0/0],[1/6,3/6,3/6],[2/6,2/6,2/3]].
%@ [[1/6,3/6,3/3],[2/6,4/6,0/0],[2/6,2/6,3/6]].
%@ [[1/6,3/6,4/6],[2/6,2/6,3/3],[3/6,3/6,0/0],[2/6,3/6,2/6]].
%@ [[3/6,3/3,0/0],[2/6,2/6,4/6],[2/6,3/6,2/3],[3/6,2/6,2/6]].
%@ [[2/6,3/6,3/6],[3/6,2/6,2/3]].
%@ [[2/6,3/6,3/3],[3/6,4/6,0/0],[3/6,2/6,3/6]].
%@ [[2/6,3/6,4/6],[3/6,2/6,3/3],[3/6,3/6,2/6]].
%@ [[3/6,2/6,4/6],[3/6,3/6,2/3]].
%@ [[3/6,3/6,3/6]].
%@ [[3/6,3/6,3/3]].
%@ [[3/6,3/6,4/6]].
%@ Writing strata to DOT file ..
%@  writing covering relation ..   % CPU time: 180.070s, 882_405_576 inferences
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


%?- time(d_gs(3, Gs)).
%@    % CPU time: 2.937s, 13_867_327 inferences
%@    Gs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]]. % R=2
%@    % CPU time: 2.971s, 13_925_621 inferences
%@    Gs = [[2/6,0/4,0/0],[0/6,2/6,0/2],[0/4,0/6,2/6],[0/4,0/4,0/6]]. % R=1

%?- time(d_gs(4, Gs)).
%@    % CPU time: 9.263s, 44_024_332 inferences
%@    Gs = [[2/6,0/0,0/0,0/0],[0/6,2/6,0/0,0/0],[0/3,0/6,2/6,0/0],[0/3,0/3,0/6,2/6],[0/3,0/3,0/3,0/6]].

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

d_gs(D, Gs) :-
    d_Qfstratamax(D, Mss),
    maplist(\Ms^J^(reduce(join, Ms, J)), Mss, Gs).

%?- time(d_gs(2, OMGs)).
%@    % CPU time: 0.744s, 3_400_549 inferences
%@    OMGs = [[2/6,0/0],[0/6,2/6],[0/3,0/6]].

%?- time(d_gs(3, OMGs)).
%@    % CPU time: 2.946s, 13_867_385 inferences
%@    OMGs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]].

%?- time(d_gs(4, OMGs)).
%@    % CPU time: 9.294s, 44_024_350 inferences
%@    OMGs = [[2/6,0/0,0/0,0/0],[0/6,2/6,0/0,0/0],[0/3,0/6,2/6,0/0],[0/3,0/3,0/6,2/6],[0/3,0/3,0/3,0/6]].

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
%@    D = 3, X = 3, Maxs = [[0/3,0/3,0/6]].

%?- d_Qfstratamax(2, Mss), maplist(portray_clause, Mss).
%@ [[2/6,0/0]].
%@ [[0/6,2/6]].
%@ [[0/3,0/6]].
%@    Mss = [[[2/6,0/0]],[[0/6,2/6]],[[0/3,0/6]]]. % R=2
%@ [[2/6,0/0],[2/6,2/6]].
%@ [[0/6,2/6]].
%@ [[0/3,0/6],[1/6,0/6]].
%@    Mss = [[[2/6,0/0],[2/6,2/6]],[[0/6,2/6]],[[0/3,0/6],[1/6,0/6]]]. % R=1

%?- d_Qfstratamax(3, Mss), maplist(portray_clause, Mss).
%@ [[2/6,0/0,0/0]].
%@ [[0/6,2/6,0/0]].
%@ [[0/3,0/6,2/6]].
%@ [[0/3,0/3,0/6]].
%@    Mss = [[[2/6,0/0,0/0]],[[0/6,2/6,0/0]],[[0/3,0/6,2/6]],[[0/3,0/3,0/6]]].
%@ [[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]].
%@ [[0/6,2/6,0/0],[0/6,2/6,2/6]].
%@ [[0/3,0/6,2/6],[1/6,0/6,2/6]].
%@ [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]].
%@    Mss = [[[2/6,0/0,0/0],[2/6,2/6,0/0],[2/6,2/6,2/6]],[[0/6,2/6,0/0],[0/6,2/6,2/6]],[[0/3,0/6,2/6],[1/6,0/6,2/6]],[[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,1/6,0/6]]]. % R=1

%?- d_Qfstratamax(4, Mss), maplist(portray_clause, Mss).
%@ [[2/6,0/0,0/0,0/0]].
%@ [[0/6,2/6,0/0,0/0]].
%@ [[0/3,0/6,2/6,0/0]].
%@ [[0/3,0/3,0/6,2/6]].
%@ [[0/3,0/3,0/3,0/6]].
%@    Mss = [[[2/6,0/0,0/0,0/0]],[[0/6,2/6,0/0,0/0]],[[0/3,0/6,2/6,0/0]],[[0/3,0/3,0/6,2/6]],[[0/3,0/3,0/3,0/6]]]. % R=2
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
    d_tally_nextdose_final(D, Tally, X, _).

%?- d_tally_dose(3, [0/0,0/0,0/0], X).
%@    false. % before adding (**) clause of d_tally_nextdose_final/4
%@    X = 1. % with (**) clause

joinof(X, Goal, J) :- reduce(join, X, Goal, J).
meetof(X, Goal, M) :- reduce(meet, X, Goal, M).

d_rx_join(D, X, Jx) :-
    joinof(Q, d_tally_dose(D, Q, X), Jx).

d_rx_meet(D, X, Mx) :-
    meetof(Q, d_tally_dose(D, Q, X), Mx).

%?- d_rx_join(2, 2, J2).
%@    J2 = [0/3,0/6].

%?- d_rx_meet(2, 2, M2).
%@    M2 = [1/6,1/3].

%% binsof(-(K-V), +Goal_2, -Bins) is det
%
% Given Goal_2 with free variables K-V, unifies Bins with
% the K-sorted list of sets of the form {V : Goal(K,V)}.
% In the special case where K in 0..(N-1), Bins will be
% a length-N list-of-lists such that nth0(K, Bins, Vs)
% iff setof(V, Goal_2(K), Vs).
% TODO: Given that this implementation ultimately depends
%       on !/0 (via same_key/4 via group_pairs_by_key/2),
%       and that my intended use at the moment is precisely
%       the special case documented above, consider a more
%       specialized and _purer_ recursive implementation.
binsof(K-V, Goal, Bins) :-
    setof(K-V, Goal, KVs),
    group_pairs_by_key(KVs, Ps), % uses same_key/4, which has a !/0
    pairs_values(Ps, Bins).

%?- true+\(D=2, binsof(X-Q, d_tally_nextdose_final(D, Q, X, _), Bins), maplist(portray_clause, Bins)).
%@ [[0/3,2/3],[0/3,2/6],[0/3,3/3],[0/3,3/6],[0/3,4/6],[1/3,0/0]].
%@ [[0/3,0/0],[0/3,0/3],[0/3,1/3],[1/6,0/0],[1/6,0/3],[1/6,1/3]].
%@    true
%@ ;  [[2/3,0/0],[2/6,0/0],[2/6,2/3],[2/6,2/6],[2/6,3/3],[2/6,3/6],[2/6,4/6],[3/3,0/0],[3/6,0/0],[3/6,2/3],[3/6,2/6],[3/6,3/3],[3/6,3/6],[3/6,4/6],[4/6,0/0]].
%@ [[0/6,2/3],[0/6,2/6],[0/6,3/3],[0/6,3/6],[0/6,4/6],[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]].
%@ [[0/3,0/6],[0/3,1/6],[1/6,0/6],[1/6,1/6]].
%@ true.
%?- true+\(D=2, binsof(X-Q, Q^X+\d_tally_nextdose_final(D, Q, X, _), Bins), maplist(portray_clause, Bins)).
%@ [[2/3,0/0],[2/6,0/0],[2/6,2/3],[2/6,2/6],[2/6,3/3],[2/6,3/6],[2/6,4/6],[3/3,0/0],[3/6,0/0],[3/6,2/3],[3/6,2/6],[3/6,3/3],[3/6,3/6],[3/6,4/6],[4/6,0/0]].
%@ [[0/3,2/3],[0/3,2/6],[0/3,3/3],[0/3,3/6],[0/3,4/6],[0/6,2/3],[0/6,2/6],[0/6,3/3],[0/6,3/6],[0/6,4/6],[1/3,0/0],[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]].
%@ [[0/3,0/0],[0/3,0/3],[0/3,0/6],[0/3,1/3],[0/3,1/6],[1/6,0/0],[1/6,0/3],[1/6,0/6],[1/6,1/3],[1/6,1/6]].
%@    true.

d_joins(D, Js) :-
    findall(X, (X in 0..D, indomain(X)), Xs),
    maplist(d_rx_join(D), Xs, Js).

d_meets(D, Ms) :-
    findall(X, (X in 0..D, indomain(X)), Xs),
    maplist(d_rx_meet(D), Xs, Ms).

%?- D in 2..6, indomain(D), time(d_meets(D, Ms)).
%@    % CPU time: 2.092s, 9_651_008 inferences
%@    D = 2, Ms = [[4/6,3/6],[1/6,4/6],[1/6,1/3]]
%@ ;  % CPU time: 10.853s, 52_053_657 inferences
%@    D = 3, Ms = [[4/6,3/6,3/6],[1/6,4/6,3/6],[1/6,1/6,4/6],[1/6,1/6,1/3]]
%@ ;  % CPU time: 45.079s, 204_291_858 inferences
%@    D = 4, Ms = [[4/6,3/6,3/6,3/6],[1/6,4/6,3/6,3/6],[1/6,1/6,4/6,3/6],[1/6,1/6,1/6,4/6],[1/6,1/6,1/6,1/3]]
%@ ;  % CPU time: 150.619s, 681_728_248 inferences
%@    D = 5, Ms = [[4/6,3/6,3/6,3/6,3/6],[1/6,4/6,3/6,3/6,3/6],[1/6,1/6,4/6,3/6,3/6],[1/6,1/6,1/6,4/6,3/6],[1/6,1/6,1/6,1/6,4/6],[1/6,1/6,1/6,1/6,1/3]]
%@ ;  % CPU time: 516.718s, 2_062_296_022 inferences
%@    D = 6, Ms = [[4/6,3/6,3/6,3/6,3/6,3/6],[1/6,4/6,3/6,3/6,3/6,3/6],[1/6,1/6,4/6,3/6,3/6,3/6],[1/6,1/6,1/6,4/6,3/6,3/6],[1/6,1/6,1/6,1/6,4/6,3/6],[1/6,1/6,1/6,1/6,1/6,4/6],[1/6,1/6,1/6,1/6,1/6,1/3]].
% NB: Diffs from earlier are due solely to R=2 vs (previously) R=1

% Do all these partitions start the trial enrolling at 1?

% The degenerate case D=1 does NOT make a 'clean start' from [0/0]:
%?- d_rx_meet(1, 1, M1).
%@    M1 = [1/3].
%?- d_rx_meet(1, 1, M1), M1 '≼' [0/0].
%@    false.
% But happily, this turns out to be the exception!

d_starts1(D) :-
    D #> 1, % D=1 case is exceptional, in NOT starting cleanly from [0/0].
    d_init(D, Init),
    d_rx_meet(D, 1, M1), M1 '≼' Init, % <- (indeed this fails in D=1 case)
    d_rx_meet(D, 2, M2), M2 '⋠' Init.

%?- D in 2..6, indomain(D), time(d_starts1(D)).
%@    % CPU time: 1.382s, 6_444_663 inferences
%@    D = 2
%@ ;  % CPU time: 5.492s, 26_237_713 inferences
%@    % CPU time: 17.256s, 82_656_098 inferences
%@    % CPU time: 47.797s, 229_889_428 inferences
%@    % CPU time: 122.517s, 595_570_903 inferences
%@    false.
%@    % CPU time: 1.394s, 6_436_270 inferences
%@    D = 2
%@ ;  % CPU time: 5.645s, 26_224_221 inferences
%@    % CPU time: 17.866s, 82_637_504 inferences
%@    % CPU time: 49.344s, 229_865_729 inferences
%@    % CPU time: 139.378s, 595_542_096 inferences
%@    false.
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
%@    Gs = [[0/3,0/6,0/0],[0/6,0/0,0/0],[2/6,0/0,0/0]]. % same
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
    d_init(D, [I|Is]),
    phrase(path([I]-Is), Path).

%?- d_path(2, Path).
%@    Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[0/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[1/6,0/3]-[],stop,recommend_dose(2)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[0/6]-[2/6],stop,recommend_dose(1)]
%@ ;  Path = [sta,[0/3]-[0/0],esc,[0/3,0/3]-[],sta,[2/6,0/3]-[],des,[1/6]-[2/6],stop,recommend_dose(1)]
%@ ;  ... .

%?- J+\(findall(Path, user:d_path(2, Path), Paths), lists:length(Paths, J)).
%@    J = 46.

%% d_tally_nextdose_final(+D, ?Q, ?X, ?Final) is nondet
%
% Describes the interim [Final=false] and final [Final=true] tallies
% and subsequent next-dose recommendations which terminate the paths
% of the D-dose 3+3 design as described by our DCG.
% Memoizing it via *tabling* achieves a _complete_ description at the
% cost of only a single, one-off comprehensive elaboration of the DCG.
:- table d_tally_nextdose_final/3.
d_tally_nextdose_final(D, Q, X, Final) :-
    d_path(D, Path),
    (   Final = false,
        phrase((..., [State0,E,Ls-_], ...), Path),
        member(E, [esc,des,sta]),
        state_tallies(State0, Q),
        length(Ls, X)
    ;   Final = true,
        phrase((..., [Endstate,stop,recommend_dose(X)]), Path),
        state_tallies(Endstate, Q)
    ).
d_tally_nextdose_final(D, Q, 1, false) :- d_init(D, Q). % (**)

% Let's enable checking all the interim tallies and dose recs
d_tally_next(D, Tally, Next) :-
    d_tally_nextdose_final(D, Tally, Next, false).

% Let's make sure to gain access to upper-Galois enrollments, too.
% These correspond to the lower (left) adjoint L of Def 4.2.

d_ls(D, Ls) :-
    d_Qfstratamin(D, Mss),
    maplist(\Ms^M^(reduce(meet, Ms, M)), Mss, Ls).

%?- d_ls(2, Ls).
%@    Ls = [[1/6,1/6],[1/6,4/6],[4/6,3/6]].

%?- d_ls(3, Ls).
%@    Ls = [[1/6,1/6,1/6],[1/6,1/6,4/6],[1/6,4/6,3/6],[4/6,3/6,3/6]].

%?- d_ls(4, Ls).
%@    Ls = [[1/6,1/6,1/6,1/6],[1/6,1/6,1/6,4/6],[1/6,1/6,4/6,3/6],[1/6,4/6,3/6,3/6],[4/6,3/6,3/6,3/6]].

% TODO: Having now clarified the status of d_gs/2 and d_ls/2 as
%       (respectively) joins|meets of maximal|minimal strata,
%       let's next define how they compare with d_joinscascade/2
%       and d_meetscascade/2.  This clarification should also
%       investigate whether _rectification_ changes either of
%       these computations.  (I believe that *at least* meets
%       should not be affected, since rectification relocates
%       only tallies located 'interior' to the strata, leaving
%       their minimal sets unaffected.  This also seems quite
%       likely to hold, at least in practice, for joins also.)
% The simplest approach might be just to define these cascades
% as arising from taking meets or joins of certain well-defined
% partitions of tallies.  Maybe the only thing we really need
% to define is whether we're dealing with final tallies only,
% or also the interim ones.
%
% Or perhaps what I really need is a more general interface to
% the DCGs, parametrizing away any 'distinction' between d_gs/2
% and d_joinscascade/2, say?

%?- [0/0,0/0] '≽' [1/6,1/6]. % L2
%@    false.
%?- [0/0,0/0] '≽' [1/6,4/6]. % L1
%@    true.
% So we would start at dose level 1, from initial tally [0/0,0/0].

%?- [1/3,0/0] '≽' [1/6,4/6].
%@    true. % => X=1
%?- [2/3,0/0] '≽' [1/6,4/6].
%@    false. % => X=0
% And furthermore, we would stop the trial at the expected point.

d_Qfstratamin(D, Mss) :-
    d_Qfstrata(D, Qss),
    reverse(Qss, DescQss),
    maplist(qs_mins, DescQss, Mss).

%?- D = 3, time(d_Qfstratamin(D, Mss)).
%@    % CPU time: 0.292s, 1_456_793 inferences
%@    D = 3, Mss = [[[1/6,1/6,1/6]],[[1/6,1/6,4/6]],[[1/6,4/6,0/0],[1/6,3/6,4/6]],[[4/6,0/0,0/0],[3/6,4/6,0/0],[3/6,3/6,4/6]]].

%?- d_ls(3, Ls).
%@ Listing Qs......    % CPU time: 1.564s, 6_773_188 inferences
%@ Stratifying Qf..    % CPU time: 2.981s, 13_964_951 inferences
%@ Finding l's ..
%@ ↑[1/6,1/6,1/6] ⊇ [[1/6,1/6,1/6]].
%@ ↑[1/6,1/6,4/6] ⊇ [[1/6,1/6,4/6]].
%@ ↑[1/6,4/6,3/6] ⊇ [[1/6,4/6,0/0],[1/6,3/6,4/6]].
%@ ↑[4/6,3/6,3/6] ⊇ [[4/6,0/0,0/0],[3/6,4/6,0/0],[3/6,3/6,4/6]].
%@    % CPU time: 25.780s, 132_984_158 inferences
%@    Ls = [[1/6,1/6,1/6],[1/6,1/6,4/6],[1/6,4/6,3/6],[4/6,3/6,3/6]].

/*
TODO:

1. Simulate and visualize rolling-enrollment trials.

*/
