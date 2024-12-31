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

:- use_module(intlist).
:- use_module(enst).
:- use_module(tally).
:- use_module(run33).
:- use_module(comprehension).
:- use_module(cascade).

clpz:monotonic.

% Pending https://github.com/mthom/scryer-prolog/issues/2547,
% some pretty operators resist export, and require 'extraction':
:- op(900, xfx, '≼').
:- op(900, xfx, '⋠').
:- op(900, xfx, '≽').

'≼'(X,Y,T) :- enst:'≼'(X,Y,T).
'≽'(X,Y,T) :- enst:'≽'(X,Y,T).
'≼'(X,Y) :- enst:'≼'(X,Y).
'≽'(X,Y) :- enst:'≽'(X,Y).
'⋠'(X,Y) :- enst:'⋠'(X,Y). % used by d_starts1/1


/*
It's time now to investigate what trial designs arise from
a rectified tally-dose mapping.  We are looking for all
incremental enrollments that are consistent with the
preorder obtained 
*/

/*
We now seek the parameters (g₀, g₁, g₂) of a lower-Galois enrollment for D=2,
as defined in Eq (15).

  F(q) ≤ x ⟹ q ≼ gₓ  ∀ q ∈ 𝒬f, 0 ≤ x ≤ D.

We are looking also for *minimal* such values of the gₓ ∈ 𝒬.
*/

%?- D=3, X=3, findall(Qf, d_endtally_rec(D, Qf, X), Qfs), qs_maxs(Qfs, Maxs).
%@    D = 3, X = 3, Qfs = [[0/3,0/3,0/6],[0/3,0/3,1/6],[0/3,1/6,0/6],[0/3,1/6,1/6],[1/6,0/3,0/6],[1/6,0/3,1/6],[1/6,1/6,0/6],[1/6,1/6,1/6]], Maxs = [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].

%?- time(d_gs(3, Gs)).
%@    % CPU time: 3.469s, 17_700_472 inferences
%@    Gs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]].
%@    % CPU time: 2.937s, 13_867_327 inferences
%@    Gs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]]. % R=2
%@    % CPU time: 2.971s, 13_925_621 inferences
%@    Gs = [[2/6,0/4,0/0],[0/6,2/6,0/2],[0/4,0/6,2/6],[0/4,0/4,0/6]]. % R=1

%?- time(d_gs(4, Gs)).
%@    % CPU time: 10.664s, 55_203_992 inferences
%@    Gs = [[2/6,0/0,0/0,0/0],[0/6,2/6,0/0,0/0],[0/3,0/6,2/6,0/0],[0/3,0/3,0/6,2/6],[0/3,0/3,0/3,0/6]].

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

% TODO:
% Clarify the status of d_gs/2 and d_ls/2 vis-à-vis
% cascade:d_joins/2 and cascade:d_meets/2.  I believe
% the former are just the special cases where _final_
% tallies only are considered.

% Aiming to exhibit d_gs/2 as a special case of d_joins/2,
% we generalize cascade:d_joins/2 and cascade:d_rx_join/3
% by injecting a _final_ boolean to the argument lists.
d_joins_final(D, Js, Final) :-
    findall(X, (X in 0..D, indomain(X)), Xs),
    maplist(d_final_rx_join(D,Final), Xs, Js).

d_final_rx_join(D, Final, X, Jx) :-
    joinof(Q, d_tally_nextdose_final(D, Q, X, Final), Jx).

d_gs_final(D, Gs, Final) :-
    d_joins_final(D, Gs, Final). % TODO: Trim the resulting list?

%?- d_gs_final(3, Gs, true).
%@    Gs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]].
%?- d_gs(3, Gs).
%@    Gs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]].
/*
?- D in 2..6, indomain(D),
   format("D = ~d", [D]),
   time((d_joins_final(D, Gs, true),
         d_gs(D, Gs0),
         Gs \== Gs0
        )).
%@ D = 2   % CPU time: 2.831s, 13_035_697 inferences
%@ D = 3   % CPU time: 13.776s, 65_528_000 inferences
%@ D = 4   % CPU time: 51.344s, 245_252_251 inferences
%@ D = 5   % CPU time: 165.334s, 789_070_050 inferences
%@ D = 6   % CPU time: 483.069s, 2_314_696_548 inferences
%@    false.
*/

d_gs(D, Gs) :-
    d_Qfstratamax(D, Mss),
    maplist(\Ms^J^(reduce(join, Ms, J)), Mss, Gs).
    %%maplist(\Ms^J^(reduce(join, Ms, J)), Mss, Gs).

%?- time(d_gs(2, OMGs)).
%@    % CPU time: 0.726s, 3_374_590 inferences
%@    OMGs = [[2/6,0/0],[0/6,2/6],[0/3,0/6]].
%@    % CPU time: 0.897s, 4_510_253 inferences
%@    OMGs = [[2/6,0/0],[0/6,2/6],[0/3,0/6]].

%?- time(d_gs(3, OMGs)).
%@    % CPU time: 3.447s, 17_700_495 inferences
%@    OMGs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]].

%?- time(d_gs(4, OMGs)).
%@    % CPU time: 10.651s, 55_203_992 inferences
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

%?- d_tally_dose(2, Q, 1).
%@    Q = [0/3,2/6]
%@ ;  Q = [0/6,2/6]
%@ ;  Q = [0/3,2/6]
%@ ;  ... .

% Do all these partitions start the trial enrolling at 1?

d_starts1(D) :-
    D #> 1, % D=1 case is exceptional, in NOT starting cleanly from [0/0].
    d_init(D, Init),
    d_rx_meet(D, 1, M1), M1 '≼' Init, % <- (indeed this fails in D=1 case)
    d_rx_meet(D, 2, M2), M2 '⋠' Init.

%?- D in 2..6, indomain(D), time(d_starts1(D)).
%@    % CPU time: 1.407s, 6_615_957 inferences
%@    D = 2
%@ ;  % CPU time: 5.568s, 27_051_973 inferences
%@    % CPU time: 17.289s, 85_399_086 inferences
%@    % CPU time: 47.473s, 237_469_384 inferences
%@    % CPU time: 127.682s, 614_642_575 inferences
%@    false.

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
%@ Found partition M1..M2 = [[1/6,4/6],[1/6,1/3]]
%@    X = 0, Mx = [1/6,4/6]
%@ ;  X = 1, Mx = [1/6,1/3].

d_x_escapees(D, X, Qs) :-
    d_x_mx(D, X, Mx),
    #Xplus1 #= #X + 1,
    format("Checking against M~d = ~w..~n", [Xplus1,Mx]),
    setof(Q, (d_tally_dose(D, Q, X), Mx '≼' Q), Qs).

%?- d_x_escapees(2, X, Qs).
%@ Found partition M1..M2 = [[1/6,4/6],[1/6,1/3]]
%@ Checking against M1 = [1/6,4/6]..
%@ Checking against M2 = [1/6,1/3]..
%@    X = 1, Qs = [[0/3,2/6],[0/6,2/3],[0/6,2/6]].

%?- d_x_escapees(3, X, Qs).
%@ Found partition M1..M3 = [[1/6,4/6,3/6],[1/6,1/6,4/6],[1/6,1/6,1/3]]
%@ Checking against M1 = [1/6,4/6,3/6]..
%@ Checking against M2 = [1/6,1/6,4/6]..
%@    X = 1, Qs = [[0/0,0/0,0/0],[0/3,2/3,0/0],[0/3,2/6,0/0],[0/3,2/6,2/3],[0/3,2/6,2/6],[0/3,2/6,3/6],[0/6,2/3,0/0],[0/6,2/6,0/0],[0/6,2/6,2/3],[0/6,2/6,2/6],[0/6,2/6,3/3],[0/6,2/6,3/6],[0/6,2/6,4/6],[1/3,0/0,0/0]]
%@ ;  Checking against M3 = [1/6,1/6,1/3]..
%@ X = 2, Qs = [[0/3,0/3,2/6],[0/3,0/6,2/3],[0/3,0/6,2/6],[0/3,0/6,3/6],[0/3,1/6,2/6],[1/6,0/3,2/6],[1/6,0/6,2/3],[1/6,0/6,2/6]].

%?- d_x_escapees(4, X, Qs).
%@ Found partition M1..M4 = [[1/6,4/6,3/6,3/6],[1/6,1/6,4/6,3/6],[1/6,1/6,1/6,4/6],[1/6,1/6,1/6,1/3]]
%@ Checking against M1 = [1/6,4/6,3/6,3/6]..
%@ Checking against M2 = [1/6,1/6,4/6,3/6]..
%@    X = 1, Qs = [[0/0,0/0,0/0,0/0],[0/3,2/3,0/0,0/0],[0/3,2/6,0/0,0/0],[0/3,2/6,2/3,0/0],[0/3,2/6,2/6,0/0],[0/3,2/6,2/6,2/3],[0/3,2/6,2/6,2/6],[0/3,2/6,2/6,3/3],[0/3,2/6,2/6,3/6],[0/3,2/6,2/6,4/6],[0/3,2/6,3/3,0/0],[0/3,2/6,3/6,0/0],[0/3,2/6,3/6,2/3],[0/3,2/6,3/6,2/6],[0/3,2/6,3/6,3/6],[0/3,2/6,4/6,0/0],[0/6,2/3,0/0,... / ...],[0/6,2/6,... / ...|...],[0/6,... / ...|...],[... / ...|...]|...]
%@ ;  Checking against M3 = [1/6,1/6,1/6,4/6]..
%@ X = 2, Qs = [[0/3,0/0,0/0,0/0],[0/3,0/3,2/3,0/0],[0/3,0/3,2/6,0/0],[0/3,0/3,2/6,2/3],[0/3,0/3,2/6,2/6],[0/3,0/3,2/6,3/6],[0/3,0/3,3/6,0/0],[0/3,0/3,3/6,2/6],[0/3,0/6,2/3,0/0],[0/3,0/6,2/6,0/0],[0/3,0/6,2/6,2/3],[0/3,0/6,2/6,2/6],[0/3,0/6,2/6,3/3],[0/3,0/6,2/6,3/6],[0/3,0/6,2/6,4/6],[0/3,0/6,3/3,0/0],[0/3,0/6,3/6,... / ...],[0/3,0/6,... / ...|...],[0/3,... / ...|...],[... / ...|...]|...]
%@ ;  Checking against M4 = [1/6,1/6,1/6,1/3]..
%@ X = 3, Qs = [[0/3,0/3,0/3,2/6],[0/3,0/3,0/6,2/3],[0/3,0/3,0/6,2/6],[0/3,0/3,0/6,3/6],[0/3,0/3,1/6,2/6],[0/3,1/6,0/3,2/6],[0/3,1/6,0/6,2/3],[0/3,1/6,0/6,2/6],[0/3,1/6,0/6,3/6],[0/3,1/6,1/6,2/6],[1/6,0/3,0/3,2/6],[1/6,0/3,0/6,2/3],[1/6,0/3,0/6,2/6],[1/6,0/3,0/6,3/6],[1/6,0/3,1/6,2/6],[1/6,1/6,0/3,2/6],[1/6,1/6,0/6,... / ...],[1/6,1/6,... / ...|...]].

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
%@    M2s = [[1/6,1/3]].

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

/*
TODO:

1. Simulate and visualize rolling-enrollment trials.

*/
