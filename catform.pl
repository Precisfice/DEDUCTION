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

clpz:monotonic.

reduce(P_3, [X|Xs], R) :- foldl(P_3, Xs, X, R).
reduce(P_3, X, Goal, R) :-
    setof(X, Goal, Xs),
    reduce(P_3, Xs, R).

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

% Some good visualizations would seem to be necessary now
% to promote efficient progress.  What Hasse diagrams could
% we draw for the partial order ≼ restricted to final tallies?
% Note that it could be interesting to define Hasse diagrams
% declaratively, and have Prolog find *all* of them for me.
% But to begin, let's explore some special solutions yielded
% by specific heuristics.

% At least for the D=2 case, a useful Hasse diagram for 𝒬f seems within reach.
% One thing that could be of special help would be finding small sets of q's
% that share the same covered and covering elements, since these could be
% collected into single nodes of the Hasse diagram.
% As a step toward finding any such little collections, let me partition 𝒬f
% into a list of recursively peeled-off minimal sets.

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

%?- D=2, Nmax=3, L+\(findall(Q, qs_d_nmax(Q, D, Nmax), Qs), po_qs_sorted('≽', Qs, SQs), length(SQs, L)).
%@    D = 2, Nmax = 3, L = 100.
%?- D=2, Nmax=6, L+\(findall(Q, qs_d_nmax(Q, D, Nmax), Qs), po_qs_sorted('≽', Qs, SQs), length(SQs, L)).
%@    D = 2, Nmax = 6, L = 784.
%?- D=3, Nmax=6, L+\(findall(Q, qs_d_nmax(Q, D, Nmax), Qs), po_qs_sorted('≽', Qs, SQs), length(SQs, L)).
%@    D = 3, Nmax = 6, L = 21952.

% The guarantee I have regarding such a sorted Qf list is that,
% if I process its elements front-to-back, each next element
% cannot be below any of those previously processed.
% In particular, I do NOT have a guarantee that all minimal
% elements are contiguous in the front of the list!
% Nevertheless, this weaker guarantee is able to support
% an efficient stratification of the list into recursively
% peeled-off maximal sets.

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
%@  writing covering relation ..   % CPU time: 6.705s, 34_157_755 inferences
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
%@  writing covering relation ..   % CPU time: 170.194s, 882_405_553 inferences
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

%?- D=3, X=3, findall(Qf, d_endtally_rec(D, Qf, X), Qfs), qs_maxs(Qfs, Maxs).
%@    D = 3, X = 3, Qfs = [[0/3,0/3,0/6],[0/3,0/3,1/6],[0/3,1/6,0/6],[0/3,1/6,1/6],[1/6,0/3,0/6],[1/6,0/3,1/6],[1/6,1/6,0/6],[1/6,1/6,1/6]], Maxs = [[0/3,0/3,0/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,1/6,0/6]].

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
