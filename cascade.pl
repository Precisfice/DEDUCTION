% cascade.pl
% Galois enrollments defined by tally cascades

:- module(cascade, [
              d_meets/2
              ,d_joins/2
              ,d_meetscascade/2
              ,d_joinscascade/2
              ,cascade_tally_ladjoint/3
              ,cascade_tally_uadjoint/3
          ]).

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(time)).
:- use_module(library(debug)).

:- use_module(enst).
:- use_module(run33).
:- use_module(comprehension).

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

d_meets(D, Ms) :-
    binsof(X-Q, d_tally_dose(D, Q, X), Bins),
    maplist(meet, Bins, Ms).

?- D in 2..6, indomain(D), time(d_meets(D, Ms)).
   % CPU time: 0.814s, 3_885_890 inferences
   D = 2, Ms = [[4/6,3/6],[1/6,4/6],[1/6,1/3]]
;  % CPU time: 3.301s, 16_364_097 inferences
   D = 3, Ms = [[4/6,3/6,3/6],[1/6,4/6,3/6],[1/6,1/6,4/6],[1/6,1/6,1/3]]
;  % CPU time: 10.570s, 53_665_879 inferences
   D = 4, Ms = [[4/6,3/6,3/6,3/6],[1/6,4/6,3/6,3/6],[1/6,1/6,4/6,3/6],[1/6,1/6,1/6,4/6],[1/6,1/6,1/6,1/3]]
;  % CPU time: 31.553s, 155_701_757 inferences
   D = 5, Ms = [[4/6,3/6,3/6,3/6,3/6],[1/6,4/6,3/6,3/6,3/6],[1/6,1/6,4/6,3/6,3/6],[1/6,1/6,1/6,4/6,3/6],[1/6,1/6,1/6,1/6,4/6],[1/6,1/6,1/6,1/6,1/3]]
;  % CPU time: 80.417s, 420_231_102 inferences
   D = 6, Ms = [[4/6,3/6,3/6,3/6,3/6,3/6],[1/6,4/6,3/6,3/6,3/6,3/6],[1/6,1/6,4/6,3/6,3/6,3/6],[1/6,1/6,1/6,4/6,3/6,3/6],[1/6,1/6,1/6,1/6,4/6,3/6],[1/6,1/6,1/6,1/6,1/6,4/6],[1/6,1/6,1/6,1/6,1/6,1/3]].

?- d_meetscascade(3, Ls).
   Ls = [[1/6,1/6,1/3],[1/6,1/6,4/6],[1/6,4/6,3/6]].

ug3(Q, X) :-
    cascade_tally_uadjoint(
        [[1/6,1/6,1/3],[1/6,1/6,4/6],[1/6,4/6,3/6]],
        Q, X).

?- ug3([0/0,0/0,0/0], StartD).
   StartD = 2.

d_joinscascade(D, Gs) :-
    d_joins(D, Js),
    reverse(Js, [_|Gs]). % drop trivial top join qua 𝟙

d_joins(D, Js) :-
    binsof(X-Q, d_tally_dose(D, Q, X), Bins),
    maplist(join, Bins, Js).

?- d_joinscascade(3, Gs).
   Gs = [[0/3,0/6,0/0],[0/6,0/0,0/0],[2/6,0/0,0/0]].

lg3(Q, X) :-
    cascade_tally_ladjoint(
        [[0/3,0/6,0/0],[0/6,0/0,0/0],[2/6,0/0,0/0]],
        Q, X).

?- lg3([0/0,0/0,0/0], StartD).
   StartD = 1.

?- d_joinscascade(4, Gs).
   Gs = [[0/3,0/3,0/6,0/0],[0/3,0/6,0/0,0/0],[0/6,0/0,0/0,0/0],[2/6,0/0,0/0,0/0]].

lg4(Q, X) :-
    cascade_tally_ladjoint(
        [[0/3,0/3,0/6,0/0],[0/3,0/6,0/0,0/0],[0/6,0/0,0/0,0/0],[2/6,0/0,0/0,0/0]],
        Q, X).

?- lg4([0/0,0/0,0/0,0/0], StartD).
   StartD = 1.

% Of course with the (**) clause of run33:d_tally_nextdose_final/4
% now providing explicit direction as to initial dosing, and our
% *lower*-Galois construction guaranteeing approximation of any
% given protocol from the _cautious_ side, protocols lg3/2 and lg/4
% _must_ enroll initially into a dose ≤ 1.
% Conversely, it would be surprising [perhaps] if the 'aggressive'
% *upper*-Galois enrollment did so! 

% Since if anything we ought to be interested in protocols
% that are SAFER than 3+3, let us focus on the behavior of
% the *lower*-Galois enrollments.

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
%@    QXs = [[0/3,0/3,0/0]-3,
%            [0/3,0/3,1/3]-3, (a)
%            [0/3,1/6,0/0]-3,
%            [0/3,1/6,0/3]-3,
%            [0/3,1/6,1/3]-3, (b)
%            [0/3,1/6,1/6]-3,
%            [1/6,0/3,0/3]-3,
%            [1/6,0/3,1/6]-3,
%            [1/6,1/6,0/3]-3,
%            [1/6,1/6,1/6]-3].
% What do we learn here?
% We find at least one case (a) where lg3 backs away from quite
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
% This puts a premium on advancing the visualization.
