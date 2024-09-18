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

:- table endtally_rec/2.

% This predicate describes precisely the final tallies and dose recommendations
% which terminate the paths of the 2-dose 3+3 design as described by our DCG.
% Memoizing it via *tabling* supports a _complete_ description at the cost of
% only a single comprehensive elaboration of the DCG.
endtally_rec(FinalTally, Rec) :-
    phrase(path([0/0]-[0/0]), Path),
    phrase((..., [Endstate,stop,recommend_dose(Rec)]), Path),
    state_tallies(Endstate, FinalTally).
    
%?- endtally_rec(Q, D).
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
?- endtally_rec(Q1, D1),
   endtally_rec(Q2, D2),
   Q1 =<$ Q2, % Q1 evidently no safer than Q2,
   D1 #>  D2. % yet recommended D1 exceeds D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% A different way to put this would be:
/*
?- endtally_rec(Q1, D1),
   endtally_rec(Q2, D2),
      Q1 =<$ Q2,  % Q1 is evidently no safer than Q2,
   #\(D1 #=< D2). % yet D1 is NOT likewise related to D2.
%@    Q1 = [1/6,1/6], D1 = 2, Q2 = [0/6,2/6], D2 = 1
%@ ;  false.
*/

% That initial listing in Section 4.1 ought to have been done with
% this predicate too!
/*
?- N+\(setof(Q-Rec, endtally_rec(Q, Rec), QRecs),
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
tally_nextdose(Tally, D) :- endtally_rec(Tally, D).

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

If we call the enlargement ≼*, then we must search for (q₀, q₁) such that

  q ≼ q₀ ⟹ E(q) = 0  ∀ final tallies q
        and
  q ≼ q₁ ⟹ E(q) ≤ 1  ∀ final tallies q,

_and_ such that adding whatever new arrows are required by,

  E(q) = 0 ⟹ q ≼* q₀  ∀ final tallies q
         and
  E(q) = 1 ⟹ q ≼* q₁  ∀ final tallies q

doesn't 'break' anything.  (I'm not even sure what I mean by that yet!)

What constraints does this put on (q₀, q₁)?  Let me not insist that they be
drawn from the set of final tallies; they can be general elements of Q².
To begin, the relation (— ≼ q₀) must not falsely hold for any final tally
having a dose recommendation above 0.  It need NOT correctly identify ALL
final tallies q with rec = 0, however; we expect that the enlargement of ≼
to ≼* will be needed to achieve this.  Nevertheless, good candidate q₀'s
will not be needlessly unsafe, and should be maximal among such.

Let's begin by exploring how many (if any!) such (q₀, q₁) exist.
*/

% candidate q0's ..
cq0(Q) :-
    findall(Q0, mendtally_rec(Q0, 0), Q0s),
    findall(Qp, (mendtally_rec(Qp, D), D #> 0), Qps),
    Q = [T1/N1, T2/N2],
    N1 in 0..6, N2 in 0..6, label([N1,N2]),
    T1 in 0..N1, T2 in 0..N2, label([T1,T2]),
    tfilter(\Qi^(Qi =<$ Q), Qps, []), % no false identifications
    %maplist(\Qi^(=<$(Qi,Q,false)), Qps),
    % The tfilter/3 and maplist/2 above perform equivalently.
    % Would there be any reason to prefer one over the other?
    tpartition(\Qi^(Qi =<$ Q), Q0s, _, []).

%?- time(setof(Q0, cq0(Q0), Q0s)).
%@    % CPU time: 12.790s, 63_221_526 inferences
%@    Q0s = [[0/4,2/6],[1/5,0/4],[1/5,0/5],[1/5,0/6],[1/5,1/5],[1/5,1/6],[2/6,0/4],[2/6,0/5],[2/6,0/6]].
%@    % CPU time: 14.067s, 66_314_481 inferences % using maplist/2 above
%@    Q0s = [[0/4,2/6],[1/5,0/4],[1/5,0/5],[1/5,0/6],[1/5,1/5],[1/5,1/6],[2/6,0/4],[2/6,0/5],[2/6,0/6]].
%@    % CPU time: 12.788s, 63_221_444 inferences % using tfilter/3 above
%@    Q0s = [[0/4,2/6],[1/5,0/4],[1/5,0/5],[1/5,0/6],[1/5,1/5],[1/5,1/6],[2/6,0/4],[2/6,0/5],[2/6,0/6]].
%@    % CPU time: 13.619s, 66_314_399 inferences % using tfilter/3 above
%@    Q0s = [[0/4,2/6],[1/5,0/4],[1/5,0/5],[1/5,0/6],[1/5,1/5],[1/5,1/6],[2/6,0/4],[2/6,0/5],[2/6,0/6]].
%@    Q0s = [[0/4,2/6],[1/5,0/4],[1/5,0/5],[1/5,0/6],[1/5,1/5],[1/5,1/6],[2/6,0/4],[2/6,0/5],[2/6,0/6]].
%@    Q0s = [[0/4,2/6],[1/5,0/4],[1/5,0/5],[1/5,0/6],[1/5,1/5],[1/5,1/6],[2/6,0/4],[2/6,0/5],[2/6,0/6]].
%@    Q0s = [[0/4,2/6],[1/5,0/4],[1/5,0/5],[1/5,0/6],[1/5,1/5],[1/5,1/6],[2/6,0/4],[2/6,0/5],[2/6,0/6]].
% Well, well!  Somewhat to my surprise, we do get some 'perfect' q₀ candidates.

% candidate q1's ..
cq1(Q) :-
    findall(Q1, mendtally_rec(Q1, 1), Q1s),
    findall(Q2, mendtally_rec(Q2, 2), Q2s),
    Q = [T1/N1, T2/N2],
    N1 in 0..6, N2 in 0..6, label([N1,N2]),
    T1 in 0..N1, T2 in 0..N2, label([T1,T2]),
    tfilter(\Qi^(Qi =<$ Q), Q2s, []), % no false identifications
    tpartition(\Qi^(Qi =<$ Q), Q1s, _, []).

%?- setof(Q1, cq1(Q1), Q1s).
%@    Q1s = [[0/6,2/6]]. % Wow, non-empty!

