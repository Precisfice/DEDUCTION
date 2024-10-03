% Inline code for Categorical sketch

:- use_module(library(lists)).
:- use_module(library(clpz)).
:- use_module(library(reif)).
:- use_module(library(dcgs)).
:- use_module(library(error)).
:- use_module(library(si)).
:- use_module(library(lambda)).
:- use_module(library(pairs)).
:- use_module(library(time)).
:- use_module(library(format)).
:- use_module(library(debug)).
:- use_module(library(tabling)).

:- use_module(rcpearl).
:- use_module(rectify).

:- table d_endtally_rec/3.

% This predicate describes precisely the final tallies and dose recommendations
% which terminate the paths of the D-dose 3+3 design as described by our DCG.
% Memoizing it via *tabling* supports a _complete_ description at the cost of
% only a single comprehensive elaboration of the DCG.
d_endtally_rec(D, FinalTally, Rec) :-
    length(Init, D), maplist(=(0/0), Init), Init = [I|Is],
    phrase(path([I]-Is), Path),
    phrase((..., [Endstate,stop,recommend_dose(Rec)]), Path),
    state_tallies(Endstate, FinalTally).
    
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
   Q1 =<$ Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% A different way to put this would be:
/*
?- d_endtally_rec(2, Q1, D1),
   d_endtally_rec(2, Q2, D2),
      Q1 =<$ Q2,  % Q1 is evidently no safer than Q2,
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
?- Tally^Npaths+\(setof(Q-Path, endtally_path(Q, Path), QPaths),
                   group_pairs_by_key(QPaths, QGroups),
                   maplist(\QP^QN^(QP=Qi-Pi, length(Pi,Ni), QN=Qi-Ni),
                           QGroups, QNs),
    member(Tally-Npaths, QNs)).
%@    Tally = [0/3,0/6], Npaths = 1
%@ ;  Tally = [0/3,1/6], Npaths = 2
%@ ;  Tally = [0/6,2/3], Npaths = 1
%@ ;  Tally = [0/6,2/6], Npaths = 2
%@ ;  Tally = [0/6,3/3], Npaths = 1
%@ ;  Tally = [0/6,3/6], Npaths = 2
%@ ;  Tally = [0/6,4/6], Npaths = 1
%@ ;  Tally = [1/6,0/6], Npaths = 1
%@ ;  Tally = [1/6,1/6], Npaths = 2
%@ ;  Tally = [1/6,2/3], Npaths = 2
%@ ;  Tally = [1/6,2/6], Npaths = 4
%@ ;  Tally = [1/6,3/3], Npaths = 2
%@ ;  Tally = [1/6,3/6], Npaths = 4
%@ ;  Tally = [1/6,4/6], Npaths = 2
%@ ;  Tally = [2/3,0/0], Npaths = 1
%@ ;  Tally = [2/6,0/0], Npaths = 1
%@ ;  Tally = [2/6,2/3], Npaths = 1
%@ ;  Tally = [2/6,2/6], Npaths = 2
%@ ;  Tally = [2/6,3/3], Npaths = 1
%@ ;  Tally = [2/6,3/6], Npaths = 2
%@ ;  Tally = [2/6,4/6], Npaths = 1
%@ ;  Tally = [3/3,0/0], Npaths = 1
%@ ;  Tally = [3/6,0/0], Npaths = 1
%@ ;  Tally = [3/6,2/3], Npaths = 1
%@ ;  Tally = [3/6,2/6], Npaths = 2
%@ ;  Tally = [3/6,3/3], Npaths = 1
%@ ;  Tally = [3/6,3/6], Npaths = 2
%@ ;  Tally = [3/6,4/6], Npaths = 1
%@ ;  Tally = [4/6,0/0], Npaths = 1.
*/
% Thus, we fully account for 46 distinct paths by observing that
% two final tallies obtain on 4 paths, 11 obtain on 2 paths,
% and each of the remaining 16 obtains on a unique path:
%?- #J #= 2*4 + 11*2 + 16.
%@    J = 46.

% What if we expand the information extracted from the 3+3 design
% to include *all* next-dose recommendations?

:- table tally_nextdose/2.

tally_nextdose(Tally, D) :-
    Init = [0/0]-[0/0],
    phrase(path(Init), Path),
    phrase((..., [Ls-Hs,E], ...), [Init|Path]),
    length(Ls, D0),
    (   E = esc, #D #= D0 + 1
    ;   E = sta, #D #= D0
    ;   E = des, #D #= D0 - 1
    ),
    state_tallies(Ls-Hs, Tally).

%?- tally_nextdose(Q, D).
%@    Q = [0/0,0/0], D = 1
%@ ;  Q = [0/3,0/0], D = 2
%@ ;  Q = [0/3,0/3], D = 2
%@ ;  Q = [0/3,1/3], D = 2
%@ ;  Q = [0/3,2/3], D = 1
%@ ;  Q = [0/3,2/6], D = 1
%@ ;  Q = [0/3,3/3], D = 1
%@ ;  Q = [0/3,3/6], D = 1
%@ ;  Q = [0/3,4/6], D = 1
%@ ;  Q = [1/3,0/0], D = 1
%@ ;  Q = [1/6,0/0], D = 2
%@ ;  Q = [1/6,0/3], D = 2
%@ ;  Q = [1/6,1/3], D = 2
%@ ;  false. % 13 answers if we exclude final tallies

% Let us include all of the Final recs also:
tally_nextdose(Tally, D) :- d_endtally_rec(2, Tally, D).

/*
%?- tally_nextdose(Tally, D).
%@    Tally = [0/0,0/0], D = 1
%@ ;  Tally = [0/3,0/0], D = 2
%@ ;  Tally = [0/3,0/3], D = 2
%@ ;  Tally = [0/3,0/6], D = 2
%@ ;  Tally = [0/3,1/3], D = 2
%@ ;  Tally = [0/3,1/6], D = 2
%@ ;  Tally = [0/3,2/3], D = 1
%@ ;  Tally = [0/3,2/6], D = 1
%@ ;  Tally = [0/3,3/3], D = 1
%@ ;  Tally = [0/3,3/6], D = 1
%@ ;  Tally = [0/3,4/6], D = 1
%@ ;  Tally = [0/6,2/3], D = 1
%@ ;  Tally = [0/6,2/6], D = 1
%@ ;  Tally = [0/6,3/3], D = 1
%@ ;  Tally = [0/6,3/6], D = 1
%@ ;  Tally = [0/6,4/6], D = 1
%@ ;  Tally = [1/3,0/0], D = 1
%@ ;  Tally = [1/6,0/0], D = 2
%@ ;  Tally = [1/6,0/3], D = 2
%@ ;  Tally = [1/6,0/6], D = 2
%@ ;  Tally = [1/6,1/3], D = 2
%@ ;  Tally = [1/6,1/6], D = 2
%@ ;  Tally = [1/6,2/3], D = 1
%@ ;  Tally = [1/6,2/6], D = 1
%@ ;  Tally = [1/6,3/3], D = 1
%@ ;  Tally = [1/6,3/6], D = 1
%@ ;  Tally = [1/6,4/6], D = 1
%@ ;  Tally = [2/3,0/0], D = 0
%@ ;  Tally = [2/6,0/0], D = 0
%@ ;  Tally = [2/6,2/3], D = 0
%@ ;  Tally = [2/6,2/6], D = 0
%@ ;  Tally = [2/6,3/3], D = 0
%@ ;  Tally = [2/6,3/6], D = 0
%@ ;  Tally = [2/6,4/6], D = 0
%@ ;  Tally = [3/3,0/0], D = 0
%@ ;  Tally = [3/6,0/0], D = 0
%@ ;  Tally = [3/6,2/3], D = 0
%@ ;  Tally = [3/6,2/6], D = 0
%@ ;  Tally = [3/6,3/3], D = 0
%@ ;  Tally = [3/6,3/6], D = 0
%@ ;  Tally = [3/6,4/6], D = 0
%@ ;  Tally = [4/6,0/0], D = 0
%@ ;  false. % NB: We get 29+13=42 answers.
*/

% Suppose we search again for all non-functoriality
% implicit in these now-expanded tally-dose mappings.
/*
?- tally_nextdose(Q1, D1),
   tally_nextdose(Q2, D2),
   Q1 =<$ Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    Q1 = [1/6,1/3], D1 = 2, Q2 = [0/6,2/3], D2 = 1 % <- 2 new
%@ ;  Q1 = [1/6,1/3], D1 = 2, Q2 = [0/6,2/6], D2 = 1 % <- solutions
%@ ;  Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/
% The first 2 solutions are new, but notably they compare
% an *interim* tally Q1 against a *final* tally Q2.
% Because of how the consideration of interim tallies is
% entangled with questions of trial progress, these new
% solutions do not speak quite so clearly as our earlier
% finding (the 3rd solution here) to the 3+3 protocol's
% underlying pharmacologic intuitions.

/*
It's time now to investigate what trial designs arise from
a rectified tally-dose mapping.  We are looking for all
incremental enrollments that are consistent with the
preorder obtained 
*/

% Let us begin by producing a rectified, dose-monotone version
% of endtally_rec/2.  While we /could/ do this by hard-coding
% the exclusion of the DM-violating solution from endtally_rec/2,
% I prefer to proceed using a more general approach.

table mendtally_rec/2.
mendtally_rec(Q, D) :- mendtally_rec(Q, D, _).

mendtally_rec(Q, D, Ds) :- % prefixed "m" for (dose-)monotone
    endtally_rec(Q, D0),
    findall(Di, (endtally_rec(Qi, Di),
                 Q =<$ Qi,  % Q is no safer than Qi,
                 D0 #> Di), % yet its rec exceeds Di.
            Ds),
    foldl(clpz:min_, Ds, D0, D).

%?- mendtally_rec(Q, D, [_|_]).
%@    Q = [1/6,1/6], D = 1
%@ ;  false.

/*
?- mendtally_rec(Q1, D1),
   mendtally_rec(Q2, D2),
   Q1 =<$ Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    false. % Rectification was successful.
*/

% Now we are in position to explore something resembling a
% 'converse' to our search for non-functorialities.
% Specifically, instead of looking for arrows in 𝒬 that
% force adjustment of dose recommendations yielded by 3+3,
% we could look instead for 'missing' arrows which these
% dose recommendations might be taken to 'suggest adding'.
/*
?- mendtally_rec(Q1, D1),
   mendtally_rec(Q2, D2),
   #D1 #< #D2,
   \+ Q1 =<$ Q2. % <-- TODO: Avoid \+ by implementing ⋠
%@    Q1 = [0/6,2/3], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [0/6,2/3], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [0/6,2/3], D1 = 1, Q2 = [1/6,0/6], D2 = 2
%@ ;  Q1 = [0/6,2/6], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [0/6,2/6], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [0/6,2/6], D1 = 1, Q2 = [1/6,0/6], D2 = 2
%@ ;  Q1 = [0/6,3/3], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [0/6,3/3], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [0/6,3/3], D1 = 1, Q2 = [1/6,0/6], D2 = 2
%@ ;  Q1 = [0/6,3/6], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [0/6,3/6], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [0/6,3/6], D1 = 1, Q2 = [1/6,0/6], D2 = 2
%@ ;  Q1 = [0/6,4/6], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [0/6,4/6], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [0/6,4/6], D1 = 1, Q2 = [1/6,0/6], D2 = 2
%@ ;  Q1 = [1/6,1/6], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [1/6,1/6], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [1/6,2/3], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [1/6,2/3], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [1/6,2/6], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [1/6,2/6], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [1/6,3/3], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [1/6,3/3], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [1/6,3/6], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [1/6,3/6], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [1/6,4/6], D1 = 1, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [1/6,4/6], D1 = 1, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [2/3,0/0], D1 = 0, Q2 = [0/6,3/3], D2 = 1
%@ ;  Q1 = [2/3,0/0], D1 = 0, Q2 = [0/6,3/6], D2 = 1
%@ ;  Q1 = [2/3,0/0], D1 = 0, Q2 = [0/6,4/6], D2 = 1
%@ ;  Q1 = [2/3,0/0], D1 = 0, Q2 = [1/6,2/3], D2 = 1
%@ ;  Q1 = [2/3,0/0], D1 = 0, Q2 = [1/6,2/6], D2 = 1
%@ ;  Q1 = [2/3,0/0], D1 = 0, Q2 = [1/6,3/3], D2 = 1
%@ ;  Q1 = [2/3,0/0], D1 = 0, Q2 = [1/6,3/6], D2 = 1
%@ ;  Q1 = [2/3,0/0], D1 = 0, Q2 = [1/6,4/6], D2 = 1
%@ ;  Q1 = [2/6,0/0], D1 = 0, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [2/6,0/0], D1 = 0, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [2/6,0/0], D1 = 0, Q2 = [0/6,3/3], D2 = 1
%@ ;  Q1 = [2/6,0/0], D1 = 0, Q2 = [0/6,3/6], D2 = 1
%@ ;  Q1 = [2/6,0/0], D1 = 0, Q2 = [0/6,4/6], D2 = 1
%@ ;  Q1 = [2/6,0/0], D1 = 0, Q2 = [1/6,2/3], D2 = 1
%@ ;  Q1 = [2/6,0/0], D1 = 0, Q2 = [1/6,2/6], D2 = 1
%@ ;  Q1 = [2/6,0/0], D1 = 0, Q2 = [1/6,3/3], D2 = 1
%@ ;  Q1 = [2/6,0/0], D1 = 0, Q2 = [1/6,3/6], D2 = 1
%@ ;  Q1 = [2/6,0/0], D1 = 0, Q2 = [1/6,4/6], D2 = 1
%@ ;  Q1 = [2/6,2/3], D1 = 0, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [2/6,2/3], D1 = 0, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [2/6,2/3], D1 = 0, Q2 = [1/6,4/6], D2 = 1
%@ ;  Q1 = [2/6,2/6], D1 = 0, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [2/6,2/6], D1 = 0, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [2/6,2/6], D1 = 0, Q2 = [0/6,2/3], D2 = 1
%@ ;  Q1 = [2/6,2/6], D1 = 0, Q2 = [0/6,3/3], D2 = 1
%@ ;  Q1 = [2/6,2/6], D1 = 0, Q2 = [1/6,2/3], D2 = 1
%@ ;  Q1 = [2/6,2/6], D1 = 0, Q2 = [1/6,3/3], D2 = 1
%@ ;  Q1 = [2/6,2/6], D1 = 0, Q2 = [1/6,4/6], D2 = 1
%@ ;  Q1 = [2/6,3/3], D1 = 0, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [2/6,3/3], D1 = 0, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [2/6,3/6], D1 = 0, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [2/6,3/6], D1 = 0, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [2/6,3/6], D1 = 0, Q2 = [0/6,3/3], D2 = 1
%@ ;  Q1 = [2/6,3/6], D1 = 0, Q2 = [1/6,2/3], D2 = 1
%@ ;  Q1 = [2/6,3/6], D1 = 0, Q2 = [1/6,3/3], D2 = 1
%@ ;  Q1 = [2/6,4/6], D1 = 0, Q2 = [0/3,0/6], D2 = 2
%@ ;  Q1 = [2/6,4/6], D1 = 0, Q2 = [0/3,1/6], D2 = 2
%@ ;  Q1 = [2/6,4/6], D1 = 0, Q2 = [1/6,3/3], D2 = 1
%@ ;  Q1 = [3/3,0/0], D1 = 0, Q2 = [0/6,4/6], D2 = 1
%@ ;  Q1 = [3/3,0/0], D1 = 0, Q2 = [1/6,3/3], D2 = 1
%@ ;  Q1 = [3/3,0/0], D1 = 0, Q2 = [1/6,3/6], D2 = 1
%@ ;  Q1 = [3/3,0/0], D1 = 0, Q2 = [1/6,4/6], D2 = 1
%@ ;  Q1 = [3/6,0/0], D1 = 0, Q2 = [0/6,4/6], D2 = 1
%@ ;  Q1 = [3/6,0/0], D1 = 0, Q2 = [1/6,3/3], D2 = 1
%@ ;  Q1 = [3/6,0/0], D1 = 0, Q2 = [1/6,3/6], D2 = 1
%@ ;  Q1 = [3/6,0/0], D1 = 0, Q2 = [1/6,4/6], D2 = 1
%@ ;  Q1 = [3/6,2/6], D1 = 0, Q2 = [0/6,3/3], D2 = 1
%@ ;  Q1 = [3/6,2/6], D1 = 0, Q2 = [1/6,2/3], D2 = 1
%@ ;  Q1 = [3/6,2/6], D1 = 0, Q2 = [1/6,3/3], D2 = 1
%@ ;  Q1 = [3/6,3/6], D1 = 0, Q2 = [1/6,3/3], D2 = 1
%@ ;  Q1 = [4/6,0/0], D1 = 0, Q2 = [1/6,4/6], D2 = 1
%@ ;  false. % 78 'missing' arrows!
*/

% So, for example:
%?- [4/6,0/0] =<$ [1/6,4/6].
%@    false.
% While this may *feel* surprising at first, observe that
%?- [4/6,0/0] =<$ [1/6,3/6].
%@    true.

% This underscores that the preorder ≼ is very much a 'bare minimum',
% logically *necessary* content for any pharmacologically rational
% ordering of tallies, but still _insufficient_ to express all of a
% dose-escalation design's underlying intuitions.  (Such intuitions
% generally may depend on the magnitudes and spacing of the doses,
% relative to anticipated population-level variation in PKPD.)

% Surely, not all 78 'missing' arrows would have to be explicitly
% added to this monoidal preorder, either.  It could be interesting
% to find some minimal set of additions that generates all 78.

% Does the existence of these 'missing' arrows tell us that there
% can be no right adjoint to the incremental escalation defined by
% mendtally_rec/2?  That is, if we take E:Q²⟶{0,1,2} to be any IE
% obeying mendtally_rec(Q, E(Q)), then a right adjoint F:{0,1,2}⟶Q²
% would obey E(q) ≤ d iff q ≼ F(d).  This would give us 3 elements
% q₀,q₁,q₂ ∈ Q² that partition all accessible tallies in Q² into
% 3 sets such that:
%       q ≼ q₀ ⟹ E(q) = 0,
%  else q ≼ q₁ ⟹ E(q) = 1,
%  else q ≼ q₂ ⟹ E(q) = 2. (*)
%
% (Observe that q₂ would then be the safest tally accessible under
% the trial protocol, corresponding to the trivial [0/6,0/6] case
% of full enrollment with no observed toxicities.  Only the first
% 2 elements q₀ and q₁ are really needed to effect the partition,
% with the last case above (*) handled as an 'otherwise' clause.)
%
% Now I suspect that the fact of these 'missing' arrows shows that
% we do not have enough arrows in the basic preorder to separate
% the domain.  But let's just search overtly for q₀ and q₁.
q0(Q) :-
    mendtally_rec(Q, 0),
    findall(Q0, mendtally_rec(Q0, 0), Q0s),
    maplist(\Qi^(Q =<$ Qi), Q0s).

%?- q0(Q).
%@    false. % Too bad!

q1(Q) :-
    mendtally_rec(Q, 1),
    findall(Q1, mendtally_rec(Q1, 1), Q1s),
    maplist(\Qi^(Q =<$ Qi), Q1s).

%?- q1(Q).
%@    false.

% But what if I searched over all of Q², instead of just
% the accessible part of it?
q1A(Q) :-
    % To begin, let's simply partition the accessible tallies:
    findall(Q0, mendtally_rec(Q0, 0), Q0s),
    findall(Q1, mendtally_rec(Q1, 1), Q1s),
    %findall(Q2, mendtally_rec(Q2, 2), Q2s),
    length(Q, 2),
    maplist(\Qi^(Qi =<$ Q), Q0s),
    maplist(\Qi^(\+ Qi =<$ Q), Q1s).

%?- q1A(Q).
%@    false. % As expected.

% Could I have *proven* that my suspicion was correct,
% without having to run these queries?
% Perhaps not!  But instead of searching for counterexamples
% to the supposed [but likely false] theorems here, let us
% instead set out to identify *possible* adjunctions, and
% then enlarge ≼ just enough to support them.

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
    maplist(\Q^(M = Q; \+ Q =<$ M), Qs).

/*
?- Ms+\(findall(Q, mendtally_rec(Q,_), FinalTallies),
        findall(M, minimal_in(M, FinalTallies), Ms)).
%@    Ms = [[3/3,0/0],[3/6,3/3],[3/6,4/6],[4/6,0/0]].
*/

% Thus, these 4 final tallies are worst-case observations,
% being at-least-as-safe-as *no* other final tally.
% But what happens if I now *remove* these, and ask the
% same question of the remaining tallies?
% Or perhaps that's an overly procedural/imperative POV?
% Why not state what holds for the Hasse diagram?
hasse_t(Q1, Q2, Qi, Truth) :-
    findall(Q, mendtally_rec(Q,_), Qs),
    mendtally_rec(Q1, _),
    mendtally_rec(Q2, _),
    dif(Q1, Q2, true),
    Q1 =<$ Q2,
    if_((memberd_t(Qi, Qs),
         Q1 =<$ Qi, Qi =<$ Q2, % NB: These invoke *reified* (=<$)/3
         dif(Q1, Qi), dif(Qi, Q2)
        ), Truth = false,
        (Qi = nil, Truth = true)
       ).

%?- hasse_t(Q1, Q2, Qi, Atomic).
%@    Q1 = [0/3,1/6], Q2 = [0/3,0/6], Qi = nil, Atomic = true
%@ ;  Q1 = [0/6,2/3], Q2 = [0/6,2/6], Qi = nil, Atomic = true
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,2/3], Qi = nil, Atomic = true
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,2/6], Qi = [0/6,2/3], Atomic = false
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,2/6], Qi = [0/6,3/6], Atomic = false
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,2/6], Qi = nil, Atomic = true
%@ ;  Q1 = [0/6,3/3], Q2 = [0/6,3/6], Qi = nil, Atomic = true
%@ ;  ... .

%?- N+\(findall(Q1-Q2, hasse_t(Q1, Q2, nil, true), Arrows), length(Arrows, N)).
%@    N = 249. % Ouch!  Could there really be SO MANY arrows in the transitive reduction?

%?- N+\(findall(Q1-Q2, hasse_t(Q1, Q2, nil, true), Arrows), list_to_set(Arrows, UniqueArrows), length(UniqueArrows, N)).
%@    N = 249. % So that N is real, not due to duplicate solutions.

%?- N+\(findall(Q, mendtally_rec(Q,_), Qs), length(Qs, N)).
%@    N = 29.

%?- #MaxN*2 #= 29*(29-1).
%@    MaxN = 406.

%?- N+\(findall(Q1-Q2, hasse_t(Q1, Q2, _, _), Arrows), list_to_set(Arrows, UniqueArrows), length(UniqueArrows, N)).
%@    N = 249. % Ah!  This nicely corroborates my other query.

%?- N+\(findall(Q1-Q2, hasse_t(Q1, Q2, _, _), Arrows), length(Arrows, N)).
%@    N = 1192. % CAUTION!  This might not even count anything sensible.

/*
Thus, it would seem that the 'obvious' visualization will be too complicated
to yield new insight or intuition.  I may do better to search systematically
for all possible enlargements of ≼ that would support an adjoint IE.

If we call the enlargement ≼*, then we must search for (g₀, g₁) such that

  q ≼ g₀ ⟹ E(q) = 0  ∀ final tallies q
        and
  q ≼ g₁ ⟹ E(q) ≤ 1  ∀ final tallies q,

_and_ such that adding whatever new arrows are required by,

  E(q) = 0 ⟹ q ≼* g₀  ∀ final tallies q
         and
  E(q) = 1 ⟹ q ≼* g₁  ∀ final tallies q

doesn't break 𝒬* = (Qᴰ, ≼*,〈0/0〉, +) as a monoidal preorder.

What constraints does this put on (g₀, g₁)?  Let me not insist that they be
drawn from the set of final tallies; they can be general elements of Q².
To begin, the relation (— ≼ g₀) must not falsely hold for any final tally
having a dose recommendation above 0.  It need NOT correctly identify ALL
final tallies q with rec = 0, however; we expect that the enlargement of ≼
to ≼* will be needed to achieve this.  Nevertheless, good candidate g₀'s
will not be needlessly unsafe, and should be maximal among such.

Let's begin by exploring how many (if any!) such (g₀, g₁) exist.
*/

% But first, let's check for non-functorialities in the D=3 trial:

/*
?- d_endtally_rec(3, Q1, D1),
   d_endtally_rec(3, Q2, D2),
   Q1 =<$ Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    Q1 = [0/3,1/6,1/6], D1 = 3, Q2 = [0/3,0/6,2/6], D2 = 2
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
%@ ;  false. % 15 non-functorial pairs in D=3 trial!
*/

% Are any of these pharmacologic non-monotonicities genuinely new?
% How many reduce to the lone D=2 case of [1/6,1/6] vs [0/6,2/6],
% after projecting off one dose?
% All of them, in fact!  The first two solutions reduce thus upon
% projecting off the lowest dose, and the remaining 13 do so when
% the top dose is removed.

%:- table d_mendtally_rec/3. % TODO: Understand why I cannot table this.
% (I can hardly use tabling safely, if I don't understand why it failed here!)
d_mendtally_rec(D, Q, X) :- d_mendtally_rec_(D, Q, X, _).

d_mendtally_rec_(D, Q, X, Xls) :-
    d_endtally_rec(D, Q, Xu), % Q-Xu is a final tally w/ *unrectified* rec, from a D-dose 3+3
    findall(Xl, (d_endtally_rec(D, Ql, Xl),
                 Xu #> Xl,  % Final tally Ql received a rec *lower* than Xu,
                 Q =<$ Ql), % although it is evidently at least as safe as Q.
            Xls),
    foldl(clpz:min_, Xls, Xu, X).

%?- d_mendtally_rec_(3, Q, D, [_|_]).
%@    Q = [0/3,1/6,1/6], D = 2
%@ ;  Q = [1/6,1/6,1/6], D = 2
%@ ;  Q = [1/6,1/6,2/3], D = 1
%@ ;  Q = [1/6,1/6,2/6], D = 1
%@ ;  Q = [1/6,1/6,3/3], D = 1
%@ ;  Q = [1/6,1/6,3/6], D = 1
%@ ;  Q = [1/6,1/6,4/6], D = 1
%@ ;  false.
% NB: Indeed there were only 7 unique Q1's
%     among the 15 solutions found above.

qs_d_nmax(Qs, D, Nmax) :-
    length(Qs, D),
    maplist(\Q^T^N^(Q = T/N), Qs, Ts, Ns),
    Ns ins 0..Nmax, label(Ns),
    maplist(\T^N^(T in 0..N), Ts, Ns), label(Ts).

%?- N+\(setof(Q, qs_d_nmax(Q, 2, 3), Qs), length(Qs, N)).
%@    N = 100.

% Generate the several relevant subsets of 𝒬f
d_qfs_rec(D, Qfs, Xrange) :-
    findall(Qf, (d_mendtally_rec(D, Qf, X), X in Xrange), Qfs).

%?- d_qfs_rec(2, Q0s, 0), length(Q0s, L0).
%@    Q0s = [[2/3,0/0],[2/6,0/0],[2/6,2/3],[2/6,2/6],[2/6,3/3],[2/6,3/6],[2/6,4/6],[3/3,0/0],[3/6,0/0],[3/6,2/3],[3/6,2/6],[3/6,3/3],[3/6,3/6],[3/6,4/6],[4/6,0/0]], L0 = 15.

%?- d_qfs_rec(2, Q12s, 1..2), length(Q12s, L12).
%@    Q12s = [[0/3,0/6],[0/3,1/6],[0/6,2/3],[0/6,2/6],[0/6,3/3],[0/6,3/6],[0/6,4/6],[1/6,0/6],[1/6,1/6],[1/6,2/3],[1/6,2/6],[1/6,3/3],[1/6,3/6],[1/6,4/6]], L12 = 14.

% candidate g₀'s for D=2 case..
g0(G) :-
    d_qfs_rec(2, Q0s, 0), d_qfs_rec(2, Qps, 1..2),
    qs_d_nmax(G, 2, 6),
    tfilter(\Q^(Q =<$ G), Qps, []), % no false identifications
    tpartition(\Q^(Q =<$ G), Q0s, _, []).

%?- setof(G0, g0(G0), G0s).
%@    G0s = [[0/4,2/6],[1/5,0/4],[1/5,0/5],[1/5,0/6],[1/5,1/5],[1/5,1/6],[2/6,0/4],[2/6,0/5],[2/6,0/6]].

% candidate g₁'s ..
g1(G) :-
    d_qfs_rec(2, Q1s, 1), d_qfs_rec(2, Q2s, 2),
    qs_d_nmax(G, 2, 6),
    tfilter(\Q^(Q =<$ G), Q2s, []), % no false identifications
    tpartition(\Q^(Q =<$ G), Q1s, _, []).

%?- setof(G1, g1(G1), G1s).
%@    G1s = [[0/6,2/6]].

qs_maxs([], []).
qs_maxs([Q|Qs], Maxs) :-
    tpartition(\Qi^(Qi =<$ Q), Qs, _, Qs1),
    if_(tmember_t(=<$(Q), Qs1), % ∃ Q' ∈ Qs s.t. Q ≼ Q' ?
        qs_maxs(Qs1, Maxs), % if so, Q is not maximal
        (   Maxs = [Q|Maxs1], % otherwise, it is
            qs_maxs(Qs1, Maxs1)
        )
       ).

qs_mins([], []).
qs_mins([Q|Qs], Mins) :-
    tpartition(=<$(Q), Qs, _, Qs1),
    if_(tmember_t(\Ql^(Ql =<$ Q), Qs1), % ∃ Q' ∈ Qs s.t. Q' ≼ Q ?
        qs_mins(Qs1, Mins), % if so, Q is not minimal
        (   Mins = [Q|Mins1], % otherwise, it is
            qs_mins(Qs1, Mins1)
        )
       ).

% Let's test it now..
%?- N+\(d_qfs_rec(3, Qls, 0..1), length(Qls, N)).
%@    N = 70.

% Generalize to any D
d_g_rec(D, G, X, Nmax) :-
    X in 0..D, indomain(X),
    d_qfs_rec(D, Qls, 0..X),
    #Xplus1 #= X + 1,
    d_qfs_rec(D, Qhs, Xplus1..D),
    qs_maxs(Qls, Qls1),
    qs_mins(Qhs, Qhs1),
    qs_d_nmax(G, D, Nmax),
    maplist(\Ql^(Ql =<$ G), Qls1),
    maplist(\Qh^(=<$(Qh, G, false)), Qhs1).

d_g_rec(D, G, X) :- d_g_rec(D, G, X, 6).

%?- d_g_rec(2, Gd, X).
%@    Gd = [0/4,2/6], X = 0
%@ ;  Gd = [1/5,0/4], X = 0
%@ ;  Gd = [1/5,0/5], X = 0
%@ ;  Gd = [1/5,1/5], X = 0
%@ ;  Gd = [1/5,0/6], X = 0
%@ ;  Gd = [1/5,1/6], X = 0
%@ ;  Gd = [2/6,0/4], X = 0
%@ ;  Gd = [2/6,0/5], X = 0
%@ ;  Gd = [2/6,0/6], X = 0
%@ ;  Gd = [0/6,2/6], X = 1
%@ ;  Gd = [0/6,0/5], X = 2
%@ ;  Gd = [0/6,0/6], X = 2
%@ ;  false.

% Might we find an adjunction (g₀, g₁, g₂) for the D=3 case as well?

%?- time(N+\(setof(G0, d_g_rec(3, G0, 0), G0s), length(G0s, N))).
%@    % CPU time: 46.689s, 239_030_535 inferences
%@    N = 43.

/*
?- X^N+\(X in 0..3, indomain(X),
         time(findall(Gx, d_g_rec(3, Gx, X), Gxs)),
         length(Gxs, N)).
%@    % CPU time: 46.731s, 239_030_248 inferences
%@    X = 0, N = 43
%@ ;  % CPU time: 35.628s, 184_445_551 inferences
%@    X = 1, N = 1
%@ ;  % CPU time: 35.139s, 182_183_755 inferences
%@    X = 2, N = 0 % Aha! ∄ g₂ for the 3-dose 3+3 trial.
%@ ;  % CPU time: 35.282s, 183_621_992 inferences
%@    X = 3, N = 5.
*/

/*
?- X^N+\(D = 2, X in 0..D, indomain(X),
         time(findall(Gx, d_g_rec(D, Gx, X), Gxs)),
         length(Gxs, N)).
%@    % CPU time: 2.309s, 11_426_733 inferences
%@    X = 0, N = 9
%@ ;  % CPU time: 1.247s, 6_371_451 inferences
%@    X = 1, N = 1
%@ ;  % CPU time: 1.300s, 6_523_869 inferences
%@    X = 2, N = 2.
*/

/*
?- X^N+\(D = 4, X in 0..D, indomain(X),
         time(findall(Gx, d_g_rec(D, Gx, X), Gxs)),
         length(Gxs, N)).
%@    % CPU time: 1190.674s, 6_233_199_963 inferences
%@    X = 0, N = 232
%@ ;  % CPU time: 1033.972s, 5_422_743_224 inferences
%@    X = 1, N = 0
%@ ;  % CPU time: 1020.932s, 5_339_744_598 inferences
%@    X = 2, N = 0
%@ ;  % CPU time: 1007.768s, 5_320_285_487 inferences
%@    X = 3, N = 0
%@ ;  % CPU time: 1003.634s, 5_319_840_324 inferences
%@    X = 4, N = 14.
*/

% For the D=3 case, let us investigate how closely we approximate
% an ideal g₂ value, both from above and below.

/*
Since every candidate g₂ will be a [possibly poor] approximation,
We'll need some heuristic initially to focus on the best ones.
To begin, then, let's find g₂ values that err only 'to one side'.

Recall how we defined g₂:

  q ≼ g₂ ⟺ Rec(q) ≤ 2.  (**)

Best-approximations to gₓ from below bₓ and above aₓ will be
(respectively) the maximal or minimal elements of the sets,

    { bₓ ∈ Qᴰ | q ≼ bₓ ⟹ Rec(q) ≤ x }
and
    { aₓ ∈ Qᴰ | Rec(q) ≤ x ⟹ q ≼ aₓ }

which support separately the (⟹) and (⟸) directions of (**).

Given that we hope to enlarge ≼ as a way to improve our approximation,
we should examine the half that may miss some q's for which Rec(q) = 2
but that does not falsely capture any X=3 final tallies.  (Adding more
arrows to ≼ will help it to 'catch' the missed q's, but cannot release
any false captures.)

Thus, we should be looking for values b₂ ≼ g₂ that might not be
high enough up the ≼ ladder to catch every q with Rec(q) ≤ 2,
but that don't mis-identify any q for which Rec(q) > 2.
*/

% bₓ ∈ Qᴰ, q ≼ bₓ ⟹ Rec(q) ≤ x
% .. or /equivalently/ ..
% bₓ ∈ Qᴰ, Rec(q) > x ⟹ q ⋠ bₓ.
d_b_rec(D, B, X) :-
    X in 0..D, indomain(X),
    #Xplus1 #= X + 1,
    d_qfs_rec(D, Qhs, Xplus1..D),
    length(Qhs, Nqh), format("Nqh = ~d~n", [Nqh]),
    qs_mins(Qhs, Qhs1),
    length(Qhs1, Nqh1), format("Nqh1 = ~d~n", [Nqh1]),
    qs_d_nmax(B, D, 6),
    maplist(\Qh^(=<$(Qh, B, false)), Qhs1).

/*
?- N+\(findall(B, d_b_rec(3, B, 2), Bs),
       length(Bs, NBs), format("#Bs = ~d~n", [NBs]),
       qs_maxs(Bs, Bmaxs),
       length(Bmaxs, N)).
%@ Nqh = 6
%@ Nqh1 = 4
%@ #Bs = 21699
% ~~ memory use starts growing unboundedly here ~~
%@    error('$interrupt_thrown',repl/0).
*/

% This represents the vast bulk of the search-space,
% since 7+6+...+1 = 28 and 28^3 = 21952 = 21699 + 253.
% So only 253 (very safe) tallies don't qualify as b₂'s.
% This shouldn't be terribly surprising, tho!  The X=3
% final tallies are indeed rather exceptional, and we
% should expect nearly all 'random' tallies must fall
% below all of them.

% Still, I would like to find the maximal b₂'s despite
% this difficulty of unbounded memory usage.  Could I
% possibly find a much smaller set to maximize?
% Do I know anything /a priori/ about the maximal b₂'s?
% Intuititvely, shouldn't any b₂ of interest exceed g₁?

%?- d_g_rec(3, G1, 1).
%@    G1 = [0/6,2/6,0/4]
%@ ;  false.

/*
?- Bs^Bmaxs+\(findall(B, ( d_b_rec(3, B, 2),
                         [0/6,2/6,0/4] =<$ B
                         ), Bs),
              qs_maxs(Bs, Bmaxs)).
%@ Nqh = 6
%@ Nqh1 = 4
%@    Bs = [[0/6,2/6,0/4],[0/6,2/6,0/5]], Bmaxs = [[0/6,2/6,0/5]].
*/

% Thus we obtain a single, unambiguously best b₂ tally.
% Note that it would not ever be admissible in a 3+3 trial,
% although the question remains open whether it would be
% reachable in the generalized (rolling-enrollment) trial
% protocol obtained from the Galois incremental enrollment
% we are trying to construct.

% Now we must ask which final tallies get 'missed' by this b₂
% value.

/*
?- B2 = [0/6,2/6,0/5], d_qfs_rec(3, Q2s, 2),
   tpartition(\Q2^(Q2 =<$ B2), Q2s, U2s, M2s),
   length(U2s, NU2), length(M2s, NM2).
%@    B2 = [0/6,2/6,0/5], Q2s = [[0/3,0/6,2/3],[0/3,0/6,2/6],[0/3,0/6,3/3],[0/3,0/6,3/6],[0/3,0/6,4/6],[0/3,1/6,1/6],[0/3,1/6,2/3],[0/3,1/6,2/6],[0/3,1/6,3/3],[0/3,1/6,3/6],[0/3,1/6,4/6],[1/6,0/6,2/3],[1/6,0/6,2/6],[1/6,0/6,3/3],[1/6,0/6,3/6],[1/6,0/6,4/6],[1/6,1/6,1/6]], U2s = [[1/6,1/6,1/6]], M2s = [[0/3,0/6,2/3],[0/3,0/6,2/6],[0/3,0/6,3/3],[0/3,0/6,3/6],[0/3,0/6,4/6],[0/3,1/6,1/6],[0/3,1/6,2/3],[0/3,1/6,2/6],[0/3,1/6,3/3],[0/3,1/6,3/6],[0/3,1/6,4/6],[1/6,0/6,2/3],[1/6,0/6,2/6],[1/6,0/6,3/3],[1/6,0/6,3/6],[1/6,0/6,4/6]], NU2 = 1, NM2 = 16.
*/

% This suggests our 'single best' b₂ is not at all good!

% What if we search beyond the dosewise enrollment cap of 6?
% Intuitively, the 'finer mesh' created by higher denominators
% might yield more resolving power.

%?- X = 2, Nmax = 15, time(d_g_rec(3, Gx, X, Nmax)).
%@    % CPU time: 2985.707s, 15_619_649_976 inferences
%@    false. % Nmax = 15
%@    % CPU time: 944.134s, 4_778_510_796 inferences
%@    false. % Nmax = 12
%@    % CPU time: 596.195s, 3_041_791_660 inferences
%@    false. % Nmax = 11
%@    % CPU time: 364.981s, 1_869_461_823 inferences
%@    false. % Nmax = 10
%@    % CPU time: 227.915s, 1_104_576_495 inferences
%@    false. % Nmax = 9
%@    % CPU time: 132.135s, 638_137_634 inferences
%@    false. % Nmax = 8
%@    false.

% No luck here, either!

% Even if it doesn't look logical right now, let me orient myself
% by starting with a search for all q's that sit above all of the
% rec-2 final tallies.
% aₓ ∈ Qᴰ, Rec(q) ≤ x ⟹ q ≼ aₓ.
d_a_rec(D, A, X) :-
    X in 0..D, indomain(X),
    d_qfs_rec(D, Qls, 0..X),
    length(Qls, Nql), format("Nql = ~d~n", [Nql]),
    qs_maxs(Qls, Qls1),
    length(Qls1, Nql1), format("Nql1 = ~d~n", [Nql1]),
    qs_d_nmax(A, D, 6),
    maplist(\Ql^(Ql =<$ A), Qls1).

%?- findall(A, d_a_rec(3, A, 2), As), qs_mins(As, MinAs).
%@ Nql = 87
%@ Nql1 = 4
%@    As = [[0/6,0/5,0/4],[0/6,0/5,0/5],[0/6,0/5,1/5],[0/6,0/5,0/6],[0/6,0/5,1/6],[0/6,0/5,2/6],[0/6,0/6,0/3],[0/6,0/6,0/4],[0/6,0/6,1/4],[0/6,0/6,0/5],[0/6,0/6,1/5],[0/6,0/6,2/5],[0/6,0/6,0/6],[0/6,0/6,1/6],[0/6,0/6,2/6]], MinAs = [[0/6,0/5,2/6]].

% This is at least a rather simple result: this single tally
% is minimal among those that exceed all the X=2 final tallies.

% What errors does this a₂ make?  Which final tallies q with Rec(q) = 3
% sit below a₂?

%?- A2 = [0/6,0/5,2/6], d_qfs_rec(3, Q3s, 3), tfilter(\Q^(Q =<$ A2), Q3s, Oops).
%@    A2 = [0/6,0/5,2/6], Q3s = [[0/3,0/3,0/6],[0/3,0/3,1/6],[0/3,1/6,0/6],[1/6,0/3,0/6],[1/6,0/3,1/6],[1/6,1/6,0/6]], Oops = [[1/6,0/3,1/6]].

% Aha, so for Q3 = [1/6,0/3,1/6] we find that Q3 =<$ A2.
%?- A2 = [0/6,0/5,2/6], Q3 = [1/6,0/3,1/6], Q3 =<$ A2.
%@    A2 = [0/6,0/5,2/6], Q3 = [1/6,0/3,1/6].

% This ordering looks worth examining for its reasonableness...
% Indeed, it DOES make sense: one cannot simply 'take a mulligan'
% on Q3's 1/6 toxicity at dose level 1!
% Notice how A2 logs 11/11 non-toxicities across dose levels 1..2,
% its 2 toxicities occurring only at the *top* dose.  By contrast,
% Q3 demonstrates a toxicity already at the _bottom_ dose.  Thus
% Q3 represents a 'worse showing' for the drug's safety than A2.

% Considering that A2 'looks' unsuitable for Rec=3, one might think
% that this vitiates our rectification step.  But notice that A2 is
% not a FINAL 3+3 tally, so 'rectification' does not apply *directly*.
% Rather, it applies *indirectly* through transitivity:
%
%   A2 ≽ Q3 and Rec(Q3)=3 ==> Rec(A2)=3.
%
% Any attempt to reverse the direction of this implication, say to
% suggest that Rec(A2)=2 ==> Rec(Q3)≤2, amounts to a criticism of
% the 3+3 final dose recommendations themselves.  While of course
% a legitimate pursuit, that is out-of-scope for an attempt to
% derive a Galois enrollment that captures the 3+3 design.
% (Moreover, the fact that A2 *does* get a [next-dose] rec of 3
% may help propel the generalized trial forward.)

/*
I do need to keep in mind, in all this, that especially
in higher dimensions, this tally space may not admit
simple partitioning by _≼q for any one fixed q.
Thus, pace 'adjunct functors arise everywhere', perhaps
there is good reason *not* to expect adjoint enrollments.
*/
