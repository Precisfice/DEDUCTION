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

?- time(d_gs(3, Gs)).
   % CPU time: 2.988s, 14_367_085 inferences
   Gs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]].

?- time(d_gs(4, Gs)).
   % CPU time: 9.381s, 45_446_084 inferences
   Gs = [[2/6,0/0,0/0,0/0],[0/6,2/6,0/0,0/0],[0/3,0/6,2/6,0/0],[0/3,0/3,0/6,2/6],[0/3,0/3,0/3,0/6]].

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
    binsof(X-Q, d_tally_nextdose_final(D, Q, X, Final), Bins),
    maplist(join, Bins, Js).

d_final_rx_join(D, Final, X, Jx) :-
    joinof(Q, d_tally_nextdose_final(D, Q, X, Final), Jx).

d_gs_final(D, Gs, Final) :-
    d_joins_final(D, Gs, Final). % TODO: Trim the resulting list?

?- d_gs_final(3, Gs, true).
   Gs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]].
?- d_gs(3, Gs).
   Gs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]].
/*
?- D in 2..6, indomain(D),
   format("D = ~d", [D]),
   time((d_joins_final(D, Gs, true),
         d_gs(D, Gs0),
         Gs \== Gs0
        )).
D = 2   % CPU time: 1.535s, 7_206_792 inferences
D = 3   % CPU time: 6.120s, 29_532_214 inferences
D = 4   % CPU time: 19.377s, 94_275_310 inferences
D = 5   % CPU time: 57.447s, 266_465_552 inferences
D = 6   % CPU time: 145.016s, 701_214_527 inferences
   false.
*/

% TODO:
% Now what of _performance_?  Does the sorting employed
% in d_gs/2 confer some advantage which I might profitably
% carry over into cascade:d_joins/2?
/* After reimplementing d_joins_final/3 using binsof/3 ..
?- D in 2..6, indomain(D),
   format("D = ~d~n", [D]),
   time(d_joins_final(D, Gs, true)),
   time(d_gs(D, Gs0)),
   Gs \== Gs0.
D = 2
   % CPU time: 0.768s, 3_662_436 inferences
   % CPU time: 0.751s, 3_544_397 inferences
D = 3
   % CPU time: 3.086s, 15_165_170 inferences
   % CPU time: 3.005s, 14_367_085 inferences
D = 4
   % CPU time: 9.814s, 48_829_267 inferences
   % CPU time: 9.423s, 45_446_084 inferences
D = 5
   % CPU time: 27.517s, 139_058_125 inferences
   % CPU time: 26.277s, 127_407_468 inferences
D = 6
   % CPU time: 82.381s, 368_432_783 inferences
   % CPU time: 75.748s, 332_781_785 inferences
   false.
*/
% These timing differences are meaningful, and the
% ratios (2.9, 3.75, 4.6, 5.45, 5.9) grow roughly
% linearly with D.

d_gs(D, Gs) :-
    d_Qfstratamax(D, Mss),
    maplist(\Ms^J^(reduce(join, Ms, J)), Mss, Gs).

?- time(d_gs(2, OMGs)).
   % CPU time: 0.762s, 3_544_374 inferences
   OMGs = [[2/6,0/0],[0/6,2/6],[0/3,0/6]].

?- time(d_gs(3, OMGs)).
   % CPU time: 2.985s, 14_367_062 inferences
   OMGs = [[2/6,0/0,0/0],[0/6,2/6,0/0],[0/3,0/6,2/6],[0/3,0/3,0/6]].

?- time(d_gs(4, OMGs)).
   % CPU time: 9.335s, 45_446_084 inferences
   OMGs = [[2/6,0/0,0/0,0/0],[0/6,2/6,0/0,0/0],[0/3,0/6,2/6,0/0],[0/3,0/3,0/6,2/6],[0/3,0/3,0/3,0/6]].

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
?- D=3, X=3, Maxs+\(findall(Qf, d_endtally_rec(D, Qf, X), Qfs), qs_maxs(Qfs, Maxs)).
   D = 3, X = 3, Maxs = [[0/3,0/3,0/6]].

/*
?- d_Qfstratamax(2, Mss), maplist(portray_clause, Mss).
[[2/6,0/0]].
[[0/6,2/6]].
[[0/3,0/6]].
   Mss = [[[2/6,0/0]],[[0/6,2/6]],[[0/3,0/6]]].
*/

/*
?- d_Qfstratamax(3, Mss), maplist(portray_clause, Mss).
[[2/6,0/0,0/0]].
[[0/6,2/6,0/0]].
[[0/3,0/6,2/6]].
[[0/3,0/3,0/6]].
   Mss = [[[2/6,0/0,0/0]],[[0/6,2/6,0/0]],[[0/3,0/6,2/6]],[[0/3,0/3,0/6]]].
*/

/*
?- d_Qfstratamax(4, Mss), maplist(portray_clause, Mss).
[[2/6,0/0,0/0,0/0]].
[[0/6,2/6,0/0,0/0]].
[[0/3,0/6,2/6,0/0]].
[[0/3,0/3,0/6,2/6]].
[[0/3,0/3,0/3,0/6]].
   Mss = [[[2/6,0/0,0/0,0/0]],[[0/6,2/6,0/0,0/0]],[[0/3,0/6,2/6,0/0]],[[0/3,0/3,0/6,2/6]],[[0/3,0/3,0/3,0/6]]].
*/

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

?- d_tally_dose(2, Q, 1).
   Q = [0/3,2/6]
;  Q = [0/6,2/6]
;  Q = [0/3,2/6]
;  ... .

% Do all these partitions start the trial enrolling at 1?

d_starts1(D) :-
    d_joins(D, [J0,J1|_]),
    d_init(D, Init),
    J0 '≼' Init,
    J1 '⋠' Init.

?- D in 1..6, indomain(D), time(d_starts1(D)).
   % CPU time: 0.068s, 254_773 inferences
   D = 1
;  % CPU time: 0.793s, 3_904_411 inferences
   D = 2
;  % CPU time: 3.227s, 16_404_290 inferences
   D = 3
;  % CPU time: 10.418s, 53_760_420 inferences
   D = 4
;  % CPU time: 29.586s, 155_933_534 inferences
   D = 5
;  % CPU time: 84.775s, 420_803_191 inferences
   D = 6.

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
    format("% Found partition M1..M~d = ~w~n", [D,Ms]),
    nth0(X, Ms, Mx). % Thus, X in 0..(D-1)

?- d_x_mx(2, X, Mx).
% Found partition M1..M2 = [[1/6,4/6],[1/6,1/3]]
   X = 0, Mx = [1/6,4/6]
;  X = 1, Mx = [1/6,1/3].

d_x_escapees(D, X, Qs) :-
    d_x_mx(D, X, Mx),
    #Xplus1 #= #X + 1,
    format("% Checking against M~d = ~w..~n", [Xplus1,Mx]),
    setof(Q, (d_tally_dose(D, Q, X), Mx '≼' Q), Qs).

?- d_x_escapees(2, X, Qs).
% Found partition M1..M2 = [[1/6,4/6],[1/6,1/3]]
% Checking against M1 = [1/6,4/6]..
% Checking against M2 = [1/6,1/3]..
   X = 1, Qs = [[0/3,2/6],[0/6,2/3],[0/6,2/6]].

?- d_x_escapees(3, X, Qs).
% Found partition M1..M3 = [[1/6,4/6,3/6],[1/6,1/6,4/6],[1/6,1/6,1/3]]
% Checking against M1 = [1/6,4/6,3/6]..
% Checking against M2 = [1/6,1/6,4/6]..
   X = 1, Qs = [[0/0,0/0,0/0],[0/3,2/3,0/0],[0/3,2/6,0/0],[0/3,2/6,2/3],[0/3,2/6,2/6],[0/3,2/6,3/6],[0/6,2/3,0/0],[0/6,2/6,0/0],[0/6,2/6,2/3],[0/6,2/6,2/6],[0/6,2/6,3/3],[0/6,2/6,3/6],[0/6,2/6,4/6],[1/3,0/0,0/0]]
;  % Checking against M3 = [1/6,1/6,1/3]..
X = 2, Qs = [[0/3,0/3,2/6],[0/3,0/6,2/3],[0/3,0/6,2/6],[0/3,0/6,3/6],[0/3,1/6,2/6],[1/6,0/3,2/6],[1/6,0/6,2/3],[1/6,0/6,2/6]].

?- d_x_escapees(4, X, Qs).
% Found partition M1..M4 = [[1/6,4/6,3/6,3/6],[1/6,1/6,4/6,3/6],[1/6,1/6,1/6,4/6],[1/6,1/6,1/6,1/3]]
% Checking against M1 = [1/6,4/6,3/6,3/6]..
% Checking against M2 = [1/6,1/6,4/6,3/6]..
   X = 1, Qs = [[0/0,0/0,0/0,0/0],[0/3,2/3,0/0,0/0],[0/3,2/6,0/0,0/0],[0/3,2/6,2/3,0/0],[0/3,2/6,2/6,0/0],[0/3,2/6,2/6,2/3],[0/3,2/6,2/6,2/6],[0/3,2/6,2/6,3/3],[0/3,2/6,2/6,3/6],[0/3,2/6,2/6,4/6],[0/3,2/6,3/3,0/0],[0/3,2/6,3/6,0/0],[0/3,2/6,3/6,2/3],[0/3,2/6,3/6,2/6],[0/3,2/6,3/6,3/6],[0/3,2/6,4/6,0/0],[0/6,2/3,0/0,... / ...],[0/6,2/6,... / ...|...],[0/6,... / ...|...],[... / ...|...]|...]
;  % Checking against M3 = [1/6,1/6,1/6,4/6]..
X = 2, Qs = [[0/3,0/0,0/0,0/0],[0/3,0/3,2/3,0/0],[0/3,0/3,2/6,0/0],[0/3,0/3,2/6,2/3],[0/3,0/3,2/6,2/6],[0/3,0/3,2/6,3/6],[0/3,0/3,3/6,0/0],[0/3,0/3,3/6,2/6],[0/3,0/6,2/3,0/0],[0/3,0/6,2/6,0/0],[0/3,0/6,2/6,2/3],[0/3,0/6,2/6,2/6],[0/3,0/6,2/6,3/3],[0/3,0/6,2/6,3/6],[0/3,0/6,2/6,4/6],[0/3,0/6,3/3,0/0],[0/3,0/6,3/6,... / ...],[0/3,0/6,... / ...|...],[0/3,... / ...|...],[... / ...|...]|...]
;  % Checking against M4 = [1/6,1/6,1/6,1/3]..
X = 3, Qs = [[0/3,0/3,0/3,2/6],[0/3,0/3,0/6,2/3],[0/3,0/3,0/6,2/6],[0/3,0/3,0/6,3/6],[0/3,0/3,1/6,2/6],[0/3,1/6,0/3,2/6],[0/3,1/6,0/6,2/3],[0/3,1/6,0/6,2/6],[0/3,1/6,0/6,3/6],[0/3,1/6,1/6,2/6],[1/6,0/3,0/3,2/6],[1/6,0/3,0/6,2/3],[1/6,0/3,0/6,2/6],[1/6,0/3,0/6,3/6],[1/6,0/3,1/6,2/6],[1/6,1/6,0/3,2/6],[1/6,1/6,0/6,... / ...],[1/6,1/6,... / ...|...]].

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

?- d_rx_mins(2, 2, M2s).
   M2s = [[1/6,1/3]].

d_minsets(D, Mss) :-
    findall(X, (X in 0..D, indomain(X)), Xs),
    maplist(d_rx_mins(D), Xs, Rss),
    reverse(Rss, Mss). % Top-to-bottom cascade

?- d_minsets(2, Mss). % now with R=2 (more arrows!)
   Mss = [[[1/6,1/3]],[[1/6,4/6]],[[4/6,0/0],[3/6,4/6]]].

?- d_minsets(3, Mss). % now with R=2 (more arrows!)
   Mss = [[[1/6,1/6,1/3]],[[1/6,1/6,4/6]],[[1/6,4/6,0/0],[1/6,3/6,4/6]],[[4/6,0/0,0/0],[3/6,4/6,0/0],[3/6,3/6,4/6]]].

% As anticipated, adding more arrows has allowed
% more parsimonious description of the partitions.
?- qs_mins([[1/6,1/6,1/3],[1/6,1/6,0/0],[1/6,0/3,0/0],[0/3,0/3,0/0]], Mins3).
   Mins3 = [[1/6,1/6,1/3]]. % from 4 descriptors to 1
?- qs_mins([[1/6,1/6,1/6],[1/6,1/3,0/0],[1/6,0/3,4/6],[1/6,0/3,3/3],[0/3,0/3,3/3]], Mins2).
   Mins2 = [[1/6,1/6,1/6],[1/6,1/3,0/0],[1/6,0/3,4/6]]. % 5 ~~> 3 descriptors
?- qs_mins([[1/6,4/6,0/0],[1/6,3/6,4/6],[1/6,3/6,3/3],[0/3,3/6,3/3]], Mins1).
   Mins1 = [[1/6,4/6,0/0],[1/6,3/6,4/6]]. % 4 ~~> 2 descriptors
?- [3/6,3/6,4/6]'≼'[3/6,3/6,3/3].
   true. % ..enabling the RHS to be dropped from R=1 4-descriptor list for dose 0.
?- reduce(meet, [[1/6,1/6,1/6],[1/6,1/3,0/0],[1/6,0/3,4/6]], Meet).
   Meet = [1/6,1/3,3/6].

/*
?- d_minsets(4, Mss). % now with R=2 (more arrows!)
   Mss = [[[1/6,1/6,1/6,1/3]],
          [[1/6,1/6,1/6,4/6]],
          [[1/6,1/6,4/6,0/0],[1/6,1/6,3/6,4/6]],
          [[1/6,4/6,0/0,0/0],[1/6,3/6,4/6,0/0],[1/6,3/6,3/6,4/6]],
          [[4/6,0/0,0/0,0/0],[3/6,4/6,0/0,0/0],[3/6,3/6,4/6,0/0],[3/6,3/6,3/6,4/6]]].
*/

% Apparently, I had already anticipated this possibility,
% and had implemented d_meets/2!

?- time(d_meets(2, Ms)).
   % CPU time: 0.796s, 3_885_890 inferences
   Ms = [[4/6,3/6],[1/6,4/6],[1/6,1/3]].
?- time(d_meets(3, Ms)).
   % CPU time: 3.260s, 16_364_046 inferences
   Ms = [[4/6,3/6,3/6],[1/6,4/6,3/6],[1/6,1/6,4/6],[1/6,1/6,1/3]].
?- time(d_meets(4, Ms)).
   % CPU time: 10.464s, 53_665_828 inferences
   Ms = [[4/6,3/6,3/6,3/6],[1/6,4/6,3/6,3/6],[1/6,1/6,4/6,3/6],[1/6,1/6,1/6,4/6],[1/6,1/6,1/6,1/3]].

% Let's make sure to gain access to upper-Galois enrollments, too.
% These correspond to the lower (left) adjoint L of Def 4.2.

d_ls(D, Ls) :-
    d_Qfstratamin(D, Mss),
    maplist(\Ms^M^(reduce(meet, Ms, M)), Mss, Ls).

?- d_ls(2, Ls).
   Ls = [[1/6,1/6],[1/6,4/6],[4/6,3/6]].

?- d_ls(3, Ls).
   Ls = [[1/6,1/6,1/6],[1/6,1/6,4/6],[1/6,4/6,3/6],[4/6,3/6,3/6]].

?- d_ls(4, Ls).
   Ls = [[1/6,1/6,1/6,1/6],[1/6,1/6,1/6,4/6],[1/6,1/6,4/6,3/6],[1/6,4/6,3/6,3/6],[4/6,3/6,3/6,3/6]].

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

?- [0/0,0/0] '≽' [1/6,1/6]. % L2
   false.
?- [0/0,0/0] '≽' [1/6,4/6]. % L1
   true.
% So we would start at dose level 1, from initial tally [0/0,0/0].

?- [1/3,0/0] '≽' [1/6,4/6].
   true. % => X=1
?- [2/3,0/0] '≽' [1/6,4/6].
   false. % => X=0
% And furthermore, we would stop the trial at the expected point.

d_Qfstratamin(D, Mss) :-
    d_Qfstrata(D, Qss),
    reverse(Qss, DescQss),
    maplist(qs_mins, DescQss, Mss).

?- D = 3, time(d_Qfstratamin(D, Mss)).
   % CPU time: 3.012s, 14_466_474 inferences
   D = 3, Mss = [[[1/6,1/6,1/6]],[[1/6,1/6,4/6]],[[1/6,4/6,0/0],[1/6,3/6,4/6]],[[4/6,0/0,0/0],[3/6,4/6,0/0],[3/6,3/6,4/6]]].

% TODO:

% 1. Simulate and summarize rolling-enrollment trials.
% (a) generate tally sequences with a DCG

% TODO: Does meta_predicate apply to DCGs?
% :- meta_predicate(galois(?, 0, ?)).

%% galois//3
%
% Describes realizations of a dose-escalation trial
% with protocol determined by 3 parameters:
%
% - Rec_2(+Q, -X) :- X is recommended enrolling dose from tally Q
% - Enr_3(+Q0, +X, -Q) :- Tally Q0 allows enrollment of 1 participant at dose X,
%                         and this yields [post-assessment] tally Q.
% - Q0, an initial tally typically initialized via d_init(D, Q0) for some D > 0.
%
% The trial realization consist of a sequence of pairs X-Q,
% with X being an enrolling dose and Q the resulting tally.
galois(Rec_2, Enr_3, Q0) --> { call(Rec_2, Q0, X),
                               call(Enr_3, Q0, X, Q) },
                             [X-Q],
                             galois(Rec_2, Enr_3, Q).
galois(_, _, _) --> []. %TBD: Emit the final dose recommendation?


%% genl33(+D, +MaxN, -Path) is multi
%
% Describes paths of a lower-Galois rectification of the D-dose 3+3 protocol.
genl33(D, MaxN, Path) :-
    d_joinscascade(D, Gs),
    Rec_2 = cascade_tally_ladjoint(Gs),
    Enr_3 = max_enroll(MaxN),
    d_init(D, Init),
    phrase(galois(Rec_2, Enr_3, Init), Path).

?- genl33(2, 12, Path).
   Path = [1-[0/1,0/0],1-[0/2,0/0],1-[0/3,0/0],1-[0/4,0/0],1-[0/5,0/0],1-[0/6,0/0],1-[0/7,0/0],2-[0/7,0/1],2-[0/7,0/2],2-[0/7,0/3],2-[0/7,0/4],2-[0/7,0/5]]
;  Path = [1-[0/1,0/0],1-[0/2,0/0],1-[0/3,0/0],1-[0/4,0/0],1-[0/5,0/0],1-[0/6,0/0],1-[0/7,0/0],2-[0/7,0/1],2-[0/7,0/2],2-[0/7,0/3],2-[0/7,0/4],2-[0/7,1/5]]
;  Path = [1-[0/1,0/0],1-[0/2,0/0],1-[0/3,0/0],1-[0/4,0/0],1-[0/5,0/0],1-[0/6,0/0],1-[0/7,0/0],2-[0/7,0/1],2-[0/7,0/2],2-[0/7,0/3],2-[0/7,0/4]]
;  Path = [1-[0/1,0/0],1-[0/2,0/0],1-[0/3,0/0],1-[0/4,0/0],1-[0/5,0/0],1-[0/6,0/0],1-[0/7,0/0],2-[0/7,0/1],2-[0/7,0/2],2-[0/7,0/3],2-[0/7,1/4],2-[0/7,1/5]]
;  Path = [1-[0/1,0/0],1-[0/2,0/0],1-[0/3,0/0],1-[0/4,0/0],1-[0/5,0/0],1-[0/6,0/0],1-[0/7,0/0],2-[0/7,0/1],2-[0/7,0/2],2-[0/7,0/3],2-[0/7,1/4],2-[0/7,2/5]]
;  Path = [1-[0/1,0/0],1-[0/2,0/0],1-[0/3,0/0],1-[0/4,0/0],1-[0/5,0/0],1-[0/6,0/0],1-[0/7,0/0],2-[0/7,0/1],2-[0/7,0/2],2-[0/7,0/3],2-[0/7,1/4]]
;  ... .

% Why didn't escalation occur sooner?
?- d_joinscascade(2, Gs).
   Gs = [[0/6,0/0],[2/6,0/0]].

?- d_meetscascade(2, Gs).
   Gs = [[1/6,1/3],[1/6,4/6]].

% Could I have used the meets cascade instead?
% Would that make any sense?

%% max_enroll(+MaxN, +Q0, +X, -Q) is multi
%
% For use as a partial goal max_enroll(MaxN)/3 in arg 2 of galois//3.
% Importantly, the nondeterminism here embodies the unknown resolution
% of toxicity assessment at the time of enrollment.
max_enroll(MaxN, Qs0, X, Qs) :-
    tally_netn(Qs0, N0),
    #N0 #< #MaxN,
    T in 0..1,
    nth1(X, Qs0, Tx0/Nx0),
    #Tx #= #Tx0 + T,
    #Nx #= #Nx0 + 1,
    nth1(X, Qs0, _, Qs0_),    %TBD: Excessive effort, merely to
    nth1(X, Qs, Tx/Nx, Qs0_), %     replace 1 element of a list?
    indomain(T). %TBD: Could I defer labeling of T?

?- max_enroll(12, [1/6,2/3], 1, Qs).
   Qs = [1/7,2/3]
;  Qs = [2/7,2/3].

tally_netn(Qs, ΣN) :- % net enrollment
    qs_ts_ns(Qs, _, Ns),
    sum(Ns, #=, #ΣN).

qs_ts_ns([T/N|Qs], [T|Ts], [N|Ns]) :- qs_ts_ns(Qs, Ts, Ns).
qs_ts_ns([], [], []).

?- qs_ts_ns([1/6,2/3], Ts, Ns).
   Ts = [1,2], Ns = [6,3].

?- tally_netn([1/6,2/3], N).
   N = 9.

/*
?- d_gs(2,Gs), d_init(Init),
   phrase(lgalois(cascade_tally_ladjoint(Gs), Enroller(Emax), Init), Path).
*/

% (b) define a probability function on *instances* of final tallies
% (c) show probabilities add to 1

% 2. Introduce delayed toxicity assessment
% (a) define an arrivals process (qua DCG?)
% (b) define a DCG that receives arrivals process as _input_
% (c) develop a clear viz incorporating pending assessments

